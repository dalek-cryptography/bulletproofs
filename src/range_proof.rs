#![allow(non_snake_case)]

#![doc(include = "../docs/range-proof-protocol.md")]

use rand::Rng;

use std::iter;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::IsIdentity;
use curve25519_dalek::scalar::Scalar;

use inner_product_proof::InnerProductProof;

use proof_transcript::ProofTranscript;

use util;

use generators::GeneratorsView;

/// The `RangeProof` struct represents a single range proof.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct RangeProof {
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
    ipp_proof: InnerProductProof,
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

        // Commit the range size to domain-separate from rangeproofs of different lengths.
        transcript.commit_u64(n as u64);

        // Create copies of G, H, so we can pass them to the
        // (consuming) IPP API later.
        let G = generators.G.to_vec();
        let H = generators.H.to_vec();

        let V = generators.pedersen_generators.commit(Scalar::from_u64(v), *v_blinding);

        let a_blinding = Scalar::random(rng);

        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding.
        let mut A = generators.pedersen_generators.B_blinding * a_blinding;
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
            iter::once(&generators.pedersen_generators.B_blinding).chain(G.iter()).chain(H.iter()),
        );

        // Commit to V, A, S and get challenges y, z
        transcript.commit(V.compress().as_bytes());
        transcript.commit(A.compress().as_bytes());
        transcript.commit(S.compress().as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;

        // Compute l, r
        let mut l_poly = util::VecPoly1::zero(n);
        let mut r_poly = util::VecPoly1::zero(n);
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
        let T_1 = generators.pedersen_generators.commit(t_poly.1, t_1_blinding);
        let T_2 = generators.pedersen_generators.commit(t_poly.2, t_2_blinding);

        // Commit to T_1, T_2 to get the challenge point x
        transcript.commit(T_1.compress().as_bytes());
        transcript.commit(T_2.compress().as_bytes());
        let x = transcript.challenge_scalar();

        // Evaluate t at x and run the IPP
        let t_x = t_poly.eval(x);
        let t_x_blinding = zz * v_blinding + x * (t_1_blinding + x * t_2_blinding);
        let e_blinding = a_blinding + x * s_blinding;

        transcript.commit(t_x.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * generators.pedersen_generators.B;

        // Generate the IPP proof
        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            util::exp_iter(y.invert()),
            G,
            H,
            l_poly.eval(x),
            r_poly.eval(x),
        );

        RangeProof {
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
        V: &RistrettoPoint,
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Result<(), ()> {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        transcript.commit_u64(n as u64);
        transcript.commit(V.compress().as_bytes());
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
                .chain(iter::once(
                    w * (self.t_x - a * b) + c * (delta(n, &y, &z) - self.t_x),
                ))
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(g)
                .chain(h)
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned()),
            iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(iter::once(V))
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(iter::once(&gens.pedersen_generators.B))
                .chain(iter::once(&gens.pedersen_generators.B_blinding))
                .chain(gens.G.iter())
                .chain(gens.H.iter())
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter()),
        );

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle 1, {\mathbf{y}}^{n} \rangle + z^{3} \langle \mathbf{1}, {\mathbf{2}}^{n} \rangle
/// \\]
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

    /// Given a bitsize `n`, test the full trip:
    ///
    /// 1. Generate a random value and create a proof that it's in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn create_and_verify_helper(n: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        use bincode;

        // Both prover and verifier have access to the generators and the proof
        use generators::{PedersenGenerators,Generators};
        let generators = Generators::new(PedersenGenerators::default(), n, 1);

        // Serialized proof data
        let proof_bytes: Vec<u8>;
        let value_commitment: RistrettoPoint;

        // Prover's scope
        {
            // Use a customization label for testing proofs
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

            // 2. Serialize
            proof_bytes = bincode::serialize(&range_proof).unwrap();

            let gens = generators.share(0);
            value_commitment = gens.pedersen_generators.commit(Scalar::from_u64(v), v_blinding);
        }

        println!(
            "Rangeproof with {} bits has size {} bytes",
            n,
            proof_bytes.len()
        );

        // Verifier's scope
        {
            // 3. Deserialize
            let range_proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();
            let mut rng = OsRng::new().unwrap();

            // 4. Use the same customization label as above to verify
            let mut transcript = ProofTranscript::new(b"RangeproofTest");
            assert!(
                range_proof
                    .verify(
                        &value_commitment,
                        generators.share(0),
                        &mut transcript,
                        &mut rng,
                        n)
                    .is_ok()
            );

            // Verification with a different label fails
            let mut transcript = ProofTranscript::new(b"");
            assert!(
                range_proof
                    .verify(
                        &value_commitment,
                        generators.share(0),
                        &mut transcript,
                        &mut rng,
                        n)
                    .is_err()
            );
        }
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
