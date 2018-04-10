#![allow(non_snake_case)]

use rand::Rng;

use std::iter;
use core::borrow::Borrow;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::IsIdentity;
use curve25519_dalek::scalar::Scalar;

// XXX rename this maybe ?? at least `inner_product_proof::Proof` is too long.
// maybe `use inner_product_proof::IPProof` would be better?
use inner_product_proof;

use proof_transcript::ProofTranscript;

use util;

use generators::GeneratorsView;

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

/// The `RangeProof` struct represents a single range proof.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Number of bits in the proof
    n: usize,
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

struct Verification {
    static_base_scalars: Vec<Scalar>,
    dynamic_base_scalars: Vec<Scalar>,
    dynamic_bases: Vec<RistrettoPoint>,
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
        use subtle::{Choice, ConditionallyAssignable};

        let B = generators.B;
        let B_blinding = generators.B_blinding;

        // Create copies of G, H, so we can pass them to the
        // (consuming) IPP API later.
        let G = generators.G.to_vec();
        let H = generators.H.to_vec();

        let V = ristretto::multiscalar_mul(&[Scalar::from_u64(v), *v_blinding], &[*B, *B_blinding]);

        let a_blinding = Scalar::random(rng);

        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding.
        let mut A = B_blinding * a_blinding;
        for i in 0..n {
            // If v_i = 0, we add a_L[i] * G[i] + a_R[i] * H[i] = - H[i]
            // If v_i = 1, we add a_L[i] * G[i] + a_R[i] * H[i] =   G[i]
            let v_i = Choice::from(((v >> i) & 1) as u8);
            let mut point = -H[i];
            point.conditional_assign(&G[i], v_i);
            A += point;
        }

        let s_blinding = Scalar::random(rng);
        let s_L: Vec<_> = (0..n).map(|_| Scalar::random(rng)).collect();
        let s_R: Vec<_> = (0..n).map(|_| Scalar::random(rng)).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding.
        let S = ristretto::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(B_blinding).chain(G.iter()).chain(H.iter()),
        );

        // Commit to V, A, S and get challenges y, z
        transcript.commit(V.compress().as_bytes());
        transcript.commit(A.compress().as_bytes());
        transcript.commit(S.compress().as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;

        // Compute l, r
        let mut l_poly = VecPoly2::zero(n);
        let mut r_poly = VecPoly2::zero(n);
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1

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
        let T_1 = ristretto::multiscalar_mul(&[t_poly.1, t_1_blinding], &[*B, *B_blinding]);
        let T_2 = ristretto::multiscalar_mul(&[t_poly.2, t_2_blinding], &[*B, *B_blinding]);

        // Commit to T_1, T_2 to get the challenge point x
        transcript.commit(T_1.compress().as_bytes());
        transcript.commit(T_2.compress().as_bytes());
        let x = transcript.challenge_scalar();

        // Evaluate t at x and run the IPP
        let t_x = t_poly.0 + x * (t_poly.1 + x * t_poly.2);
        let t_x_blinding = zz * v_blinding + x * (t_1_blinding + x * t_2_blinding);
        let e_blinding = a_blinding + x * s_blinding;

        transcript.commit(t_x.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * B;

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
            n,
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
    ) -> Result<(), ()> {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        transcript.commit(self.V.compress().as_bytes());
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;
        let minus_z = -z;

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(Scalar::from_u64(2)))
            .zip(util::exp_iter(y.invert()))
            .map(|((s_i_inv, exp_2), exp_y_inv)| z + exp_y_inv * (zz * exp_2 - b * s_i_inv));

        let mega_check = ristretto::vartime::multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(c * zz))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(
                    w * (self.t_x - a * b) + c * (delta(self.n, &y, &z) - self.t_x),
                ))
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(g)
                .chain(h),
            iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(iter::once(&self.V))
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter())
                .chain(iter::once(gens.B))
                .chain(iter::once(gens.B_blinding))
                .chain(gens.G.iter())
                .chain(gens.H.iter()),
        );

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }
    }

    /// Seems like this is as fast as normal `verify`,
    /// but I'd like to have a second opinion.
    pub fn verify_via_batch<R: Rng>(
        &self,
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    ) -> Result<(), ()> {
        RangeProof::verify_batch(&[self][..], gens, transcript, rng)
    }

    /// Produces a verifiable `RangeProofResult` object that
    /// can be verified as a part of a batch
    fn prepare_verification<R: Rng>(
        &self,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Verification {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        transcript.commit(self.V.compress().as_bytes());
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;
        let minus_z = -z;

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(Scalar::from_u64(2)))
            .zip(util::exp_iter(y.invert()))
            .map(|((s_i_inv, exp_2), exp_y_inv)| z + exp_y_inv * (zz * exp_2 - b * s_i_inv));

        Verification {
            static_base_scalars: (iter::once(
                    w * (self.t_x - a * b) + c * (delta(n, &y, &z) - self.t_x),
                ))
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(g)
                .chain(h)
                .collect(),
            dynamic_base_scalars: iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(c * zz))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .collect(),
            dynamic_bases: iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(iter::once(&self.V))
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter())
                .cloned()
                .collect(),
        }
    }

    pub fn verify_batch<R: Rng, P: Borrow<RangeProof>>(
        proofs: &[P],
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    ) -> Result<(), ()> {
        
        if proofs.len() == 0 {
            return Ok(())
        }

        let n = proofs[0].borrow().n;

        // Make sure all proofs use the same range
        if proofs.iter().any(|p| p.borrow().n != n) {
            return Err(())
        }

        let verification = proofs[0].borrow().prepare_verification(&mut transcript.clone(), rng, n);
        let mut static_base_scalars: Vec<Scalar> = verification.static_base_scalars;
        let mut dynamic_base_scalars: Vec<Scalar> = verification.dynamic_base_scalars;
        let mut dynamic_bases: Vec<RistrettoPoint> = verification.dynamic_bases;

        // first statement is applied w/o a random factor
        for proof in &proofs[1..] {
            let verification = proof.borrow().prepare_verification(&mut transcript.clone(), rng, n);
            let batch_challenge = Scalar::random(rng);
            static_base_scalars = static_base_scalars.iter()
                    .zip(verification.static_base_scalars.iter())
                    .map(|(total, s)| total + batch_challenge*s )
                    .collect();

            dynamic_base_scalars = dynamic_base_scalars.iter()
                .cloned()
                .chain(verification.dynamic_base_scalars.iter().map(|s| batch_challenge*s ))
                .collect();

            dynamic_bases = dynamic_bases.iter()
                .chain(verification.dynamic_bases.iter())
                .cloned()
                .collect();
        }

        let mega_check = ristretto::vartime::multiscalar_mul(
                static_base_scalars.iter()
                .chain(dynamic_base_scalars.iter()),

                iter::once(gens.B)
                .chain(iter::once(gens.B_blinding))
                .chain(gens.G.iter())
                .chain(gens.H.iter())
                .chain(dynamic_bases.iter())
        );

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }            
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

        let t0 = util::inner_product(&l.0, &r.0);
        let t2 = util::inner_product(&l.1, &r.1);

        let l0_plus_l1 = util::add_vec(&l.0, &l.1);
        let r0_plus_r1 = util::add_vec(&r.0, &r.1);

        let t1 = util::inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;
    use generators::Generators;

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

    fn create_rp_helper(n: usize) -> RangeProof {
        let generators = Generators::new(n, 1);
        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let mut rng = OsRng::new().unwrap();

        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        RangeProof::generate_proof(
            generators.share(0),
            &mut transcript,
            &mut rng,
            n,
            v,
            &v_blinding,
        )
    }

    fn create_and_verify_helper(n: usize) {
        let range_proof = create_rp_helper(n);
        let generators = Generators::new(n, 1);
        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let mut rng = OsRng::new().unwrap();
        assert!(
            range_proof
                .verify(generators.share(0), &mut transcript, &mut rng)
                .is_ok()
        );
    }

    fn batch_verify_helper(n: usize, m: usize) {
        let rps: Vec<_> = (0..m).map(|_| {
            create_rp_helper(n)
        }).collect();

        let generators = Generators::new(n, 1);
        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"RangeproofTest");

        assert!(
            RangeProof::verify_batch(
                rps.as_slice(), 
                generators.share(0), 
                &mut transcript, 
                &mut rng
            ).is_ok()
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

    #[test]
    fn batch_verify_64_0() {
        batch_verify_helper(64, 0);
    }

    #[test]
    fn batch_verify_64_1() {
        batch_verify_helper(64, 1);
    }

    #[test]
    fn batch_verify_64_2() {
        batch_verify_helper(64, 2);
    }

    #[test]
    fn batch_verify_64_4() {
        batch_verify_helper(64, 4);
    }

    #[test]
    fn batch_verify_64_7() {
        batch_verify_helper(64, 7);
    }

    #[test]
    fn batch_over_differently_sized_proofs_is_not_supported() {
        let rp8_1 = create_rp_helper(8);
        let rp8_2 = create_rp_helper(8);
        let rp64_1 = create_rp_helper(64);
        let rp64_2 = create_rp_helper(64);

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"RangeproofTest");

        // 8,8 -> good
        assert!(RangeProof::verify_batch(
            &[&rp8_1, &rp8_2][..],
            Generators::new(8, 1).share(0),
            &mut transcript,
            &mut rng
        ).is_ok());

        // 64,64 -> good
        assert!(RangeProof::verify_batch(
            &[&rp64_1, &rp64_2][..],
            Generators::new(64, 1).share(0),
            &mut transcript,
            &mut rng
        ).is_ok());

        // 8,64,64 -> bad
        assert!(RangeProof::verify_batch(
            &[&rp8_1, &rp64_1, &rp64_2][..],
            Generators::new(8, 1).share(0),
            &mut transcript,
            &mut rng
        ).is_err());

        // 64,8,8 -> bad
        assert!(RangeProof::verify_batch(
            &[&rp64_1, &rp8_1, &rp8_2][..],
            Generators::new(64, 1).share(0),
            &mut transcript,
            &mut rng
        ).is_err());
    }
}
