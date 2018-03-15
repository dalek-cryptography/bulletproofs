#![allow(non_snake_case)]

use rand::Rng;

use std::iter;

use sha2::{Digest, Sha256, Sha512};

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::{Identity, IsIdentity};
use curve25519_dalek::scalar::Scalar;

// XXX rename this maybe ?? at least `inner_product_proof::Proof` is too long.
// maybe `use inner_product_proof::IPProof` would be better?
use inner_product_proof;

use proof_transcript::ProofTranscript;

use util;

use generators::{Generators, GeneratorsView};

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

/// The `RangeProof` struct represents a single range proof.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the value
    // XXX this should not be included, so that we can prove about existing commitments
    // included for now so that it's easier to test
    V: RistrettoPoint,
    /// Commitment to the bits of the value
    A: RistrettoPoint,
    /// Commitment to the blinding factors
    S: RistrettoPoint,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: RistrettoPoint,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: RistrettoPoint,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: inner_product_proof::Proof,
}

impl RangeProof {
    /// Create a rangeproof.
    pub fn generate_proof<R: Rng>(
        generators: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
        v: u64,
        v_blinding: &Scalar,
    ) -> RangeProof {
        let B = generators.B;
        let B_blinding = generators.B_blinding;

        // Create copies of G, H, so we can pass them to the
        // (consuming) IPP API later.
        let G = generators.G.to_vec();
        let H = generators.H.to_vec();

        let V =
            ristretto::multiscalar_mult(&[Scalar::from_u64(v), *v_blinding], &[*B, *B_blinding]);

        let a_blinding = Scalar::random(rng);

        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding.
        let mut A = B_blinding * a_blinding;
        for i in 0..n {
            let v_i = (v >> i) & 1;
            // XXX replace this with a conditional move
            if v_i == 0 {
                A -= H[i];
            } else {
                A += G[i];
            }
        }

        let s_blinding = Scalar::random(rng);
        let s_L: Vec<_> = (0..n).map(|_| Scalar::random(rng)).collect();
        let s_R: Vec<_> = (0..n).map(|_| Scalar::random(rng)).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding.
        let S = ristretto::multiscalar_mult(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(B_blinding).chain(G.iter()).chain(H.iter()),
        );

        // Commit to V, A, S and get challenges y, z
        transcript.commit(V.compress().as_bytes());
        transcript.commit(A.compress().as_bytes());
        transcript.commit(S.compress().as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        // Compute l, r
        let mut l_poly = VecPoly2::zero(n);
        let mut r_poly = VecPoly2::zero(n);
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let zz = z * z;

        for i in 0..n {
            let a_L_i = Scalar::from_u64((v >> i) & 1);
            let a_R_i = a_L_i - Scalar::one();

            l_poly.0[i] = a_L_i - z;
            l_poly.1[i] = s_L[i];
            r_poly.0[i] = exp_y * (a_R_i + z) + zz * exp_2;
            r_poly.1[i] = exp_y * s_R[i];

            exp_y *= y; // y^i -> y^(i+1)
            exp_2 += exp_2; // 2^i -> 2^(i+1)
        }

        // Compute t(x) = <l(x),r(x)>
        let t_poly = l_poly.inner_product(&r_poly);

        // Form commitments T_1, T_2 to t.1, t.2
        let t_1_blinding = Scalar::random(rng);
        let t_2_blinding = Scalar::random(rng);
        let T_1 = ristretto::multiscalar_mult(&[t_poly.1, t_1_blinding], &[*B, *B_blinding]);
        let T_2 = ristretto::multiscalar_mult(&[t_poly.2, t_2_blinding], &[*B, *B_blinding]);

        // Commit to T_1, T_2 to get the challenge point x
        transcript.commit(T_1.compress().as_bytes());
        transcript.commit(T_2.compress().as_bytes());
        let x = transcript.challenge_scalar();

        // Evaluate t at x and run the IPP
        let t_x = t_poly.0 + x * (t_poly.1 + x * t_poly.2);
        let t_x_blinding = z * z * v_blinding + x * (t_1_blinding + x * t_2_blinding);
        let e_blinding = a_blinding + x * s_blinding;

        transcript.commit(t_x.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * B_blinding;

        // Generate the IPP proof
        let ipp_proof = inner_product_proof::Proof::create(
            transcript,
            &Q,
            util::exp_iter(y.invert()),
            G,
            H,
            l_poly.eval(x),
            r_poly.eval(x),
        );

        RangeProof {
            V,
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        }
    }

    pub fn verify<R: Rng>(
        &self,
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Result<(), ()> {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        transcript.commit(self.V.compress().as_bytes());
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();

        // Check that t(x) is consistent with commitments V, T_1, T_2
        let poly_check = ristretto::vartime::multiscalar_mult(
            &[
                z * z,
                x,
                x * x,
                (delta(n, &y, &z) - self.t_x),
                -self.t_x_blinding,
            ],
            &[self.V, self.T_1, self.T_2, *gens.B, *gens.B_blinding],
        );

        if !poly_check.is_identity() {
            return Err(());
        }

        // Recompute P + t(x)Q = P + t(x)w B_blinding

        // XXX later we will need to fold this into the IPP api
        let G_sum = gens.G
            .iter()
            .fold(RistrettoPoint::identity(), |acc, G_i| acc + G_i);

        let y_inv = y.invert();
        let two_over_y = Scalar::from_u64(2) * y_inv;
        let zz = z * z;

        let H_scalars = util::exp_iter(two_over_y)
            .take(n)
            .map(|exp_two_over_y| z + zz * exp_two_over_y);

        let P_plus_tx_Q = &self.A
            + &ristretto::vartime::multiscalar_mult(
                [w * self.t_x - self.e_blinding, x, -z]
                    .iter()
                    .cloned()
                    .chain(H_scalars),
                [*gens.B_blinding, self.S, G_sum]
                    .iter()
                    .chain(gens.H.iter()),
            );

        // XXX eliminate this when merging into a single multiscalar mult
        let Q = w * gens.B_blinding;

        // Return the result of IPP verification using the recomputed P + t(x) Q
        self.ipp_proof.verify(
            transcript,
            util::exp_iter(y_inv).take(n),
            &P_plus_tx_Q,
            &Q,
            gens.G,
            gens.H,
        )
    }
}

/// Compute
/// $$
/// \\delta(y,z) = (z - z^2)<1, y^n> + z^3 <1, 2^n>
/// $$
fn delta(n: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let two = Scalar::from_u64(2);

    // XXX this could be more efficient, esp for powers of 2
    let sum_of_powers_of_y = util::exp_iter(*y)
        .take(n)
        .fold(Scalar::zero(), |acc, x| acc + x);

    let sum_of_powers_of_2 = util::exp_iter(two)
        .take(n)
        .fold(Scalar::zero(), |acc, x| acc + x);

    let zz = z * z;

    (z - zz) * sum_of_powers_of_y - z * zz * sum_of_powers_of_2
}

impl VecPoly2 {
    pub fn zero(n: usize) -> VecPoly2 {
        VecPoly2(vec![Scalar::zero(); n], vec![Scalar::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly2) -> PolyDeg3 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        PolyDeg3(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::zero(); n];
        for i in 0..n {
            out[i] += self.0[i] + self.1[i] * x;
        }
        out
    }
}

pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        // throw some error
        println!("lengths of vectors don't match for inner product multiplication");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut out = Vec::new();
    if a.len() != b.len() {
        // throw some error
        println!("lengths of vectors don't match for vector addition");
    }
    for i in 0..a.len() {
        out.push(a[i] + b[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    #[test]
    fn test_delta() {
        let mut rng = OsRng::new().unwrap();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        assert_eq!(power_g, delta(n, &y, &z),);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from_u64(1),
            Scalar::from_u64(2),
            Scalar::from_u64(3),
            Scalar::from_u64(4),
        ];
        let b = vec![
            Scalar::from_u64(2),
            Scalar::from_u64(3),
            Scalar::from_u64(4),
            Scalar::from_u64(5),
        ];
        assert_eq!(Scalar::from_u64(40), inner_product(&a, &b));
    }

    fn create_and_verify_helper(n: usize) {
        let generators = Generators::new(n, 1);
        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let mut rng = OsRng::new().unwrap();

        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        let range_proof = RangeProof::generate_proof(
            generators.share(0),
            &mut transcript,
            &mut rng,
            n,
            v,
            &v_blinding,
        );

        let mut transcript = ProofTranscript::new(b"RangeproofTest");

        assert!(
            range_proof
                .verify(generators.share(0), &mut transcript, &mut rng, n)
                .is_ok()
        );
    }

    #[test]
    fn create_and_verify_8() {
        create_and_verify_helper(8);
    }

    #[test]
    fn create_and_verify_16() {
        create_and_verify_helper(16);
    }

    #[test]
    fn create_and_verify_32() {
        create_and_verify_helper(32);
    }

    #[test]
    fn create_and_verify_64() {
        create_and_verify_helper(64);
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    use rand::{OsRng, Rng};
    use test::Bencher;

    fn bench_create_helper(n: usize, b: &mut Bencher) {
        let generators = Generators::new(n, 1);
        let mut rng = OsRng::new().unwrap();

        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        b.iter(|| {
            // Each proof creation requires a clean transcript.
            let mut transcript = ProofTranscript::new(b"RangeproofTest");

            RangeProof::generate_proof(
                generators.share(0),
                &mut transcript,
                &mut rng,
                n,
                v,
                &v_blinding,
            )
        });
    }

    fn bench_verify_helper(n: usize, b: &mut Bencher) {
        let generators = Generators::new(n, 1);
        let mut rng = OsRng::new().unwrap();

        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        let rp = RangeProof::generate_proof(
            generators.share(0),
            &mut transcript,
            &mut rng,
            n,
            v,
            &v_blinding,
        );

        b.iter(|| {
            // Each verification requires a clean transcript.
            let mut transcript = ProofTranscript::new(b"RangeproofTest");

            rp.verify(generators.share(0), &mut transcript, &mut rng, n)
        });
    }

    #[bench]
    fn create_rp_64(b: &mut Bencher) {
        bench_create_helper(64, b);
    }

    #[bench]
    fn create_rp_32(b: &mut Bencher) {
        bench_create_helper(32, b);
    }

    #[bench]
    fn create_rp_16(b: &mut Bencher) {
        bench_create_helper(32, b);
    }

    #[bench]
    fn create_rp_8(b: &mut Bencher) {
        bench_create_helper(32, b);
    }

    #[bench]
    fn verify_rp_64(b: &mut Bencher) {
        bench_verify_helper(64, b);
    }

    #[bench]
    fn verify_rp_32(b: &mut Bencher) {
        bench_verify_helper(32, b);
    }

    #[bench]
    fn verify_rp_16(b: &mut Bencher) {
        bench_verify_helper(32, b);
    }

    #[bench]
    fn verify_rp_8(b: &mut Bencher) {
        bench_verify_helper(32, b);
    }
}
