#![allow(non_snake_case)]
#![doc(include = "../docs/range-proof-protocol.md")]

use rand::Rng;

use std::iter;

use curve25519_dalek::ristretto;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use generators::{Generators, GeneratorsView};
use inner_product_proof::InnerProductProof;
use proof_transcript::ProofTranscript;
use util;

// Modules for MPC protocol

pub mod dealer;
pub mod messages;
pub mod party;

/// The `RangeProof` struct represents a single range proof.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    pub(crate) A: RistrettoPoint,
    /// Commitment to the blinding factors
    pub(crate) S: RistrettoPoint,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(crate) T_1: RistrettoPoint,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    pub(crate) T_2: RistrettoPoint,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(crate) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    pub(crate) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    pub(crate) e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub(crate) ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    ///
    /// XXX add doctests
    pub fn prove_multiple_single<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
    ) -> Result<RangeProof, &'static str> {
        RangeProof::prove_multiple(generators, transcript, rng, &[v], &[*v_blinding], n)
    }

    /// Create a rangeproof for a set of values.
    ///
    /// XXX add doctests
    pub fn prove_multiple<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<RangeProof, &'static str> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err("mismatched values and blindings len");
        }

        let dealer = Dealer::new(generators.all(), n, values.len(), transcript)?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| {
                Party::new(v, v_blinding, n, &generators)
            })
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>,_>>()?;

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, value_challenge) = dealer.receive_value_commitments(&value_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(&poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            .collect();

        dealer.receive_trusted_shares(&proof_shares)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify` for the `m=1` case.
    ///
    /// XXX add doctests
    pub fn verify_single<R: Rng>(
        &self,
        V: &RistrettoPoint,
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Result<(), ()> {
        self.verify(&[*V], gens, transcript, rng, n, 1)
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    ///
    /// XXX add doctests
    pub fn verify<R: Rng>(
        &self,
        value_commitments: &[RistrettoPoint],
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
        m: usize,
    ) -> Result<(), ()> {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        for V in value_commitments.iter() {
            transcript.commit(V.compress().as_bytes());
        }
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

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from_u64(2)).take(n).collect();
        let powers_of_z = util::exp_iter(z).take(m);
        let concat_z_and_2 =
            powers_of_z.flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z));

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2)
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        let mega_check = ristretto::vartime::multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(value_commitment_scalars)
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h)
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned()),
            iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(value_commitments.iter())
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(iter::once(&gens.pedersen_generators.B_blinding))
                .chain(iter::once(&gens.pedersen_generators.B))
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
/// \delta(y,z) = (z - z^{2}) \langle 1, {\mathbf{y}}^{nm} \rangle + z^{3} \langle \mathbf{1}, {\mathbf{2}}^{nm} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from_u64(2), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    use generators::PedersenGenerators;

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

        assert_eq!(power_g, delta(n, 1, &y, &z),);
    }

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        use bincode;

        // Both prover and verifier have access to the generators and the proof
        let generators = Generators::new(PedersenGenerators::default(), n, m);

        // Serialized proof data
        let proof_bytes: Vec<u8>;
        let value_commitments: Vec<RistrettoPoint>;

        // Prover's scope
        {
            // 1. Generate the proof

            let mut rng = OsRng::new().unwrap();
            let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            let proof = RangeProof::prove_multiple(
                &generators,
                &mut transcript,
                &mut rng,
                &values,
                &blindings,
                n,
            ).unwrap();

            // 2. Serialize
            proof_bytes = bincode::serialize(&proof).unwrap();

            let pg = &generators.all().pedersen_generators;

            // XXX would be nice to have some convenience API for this
            value_commitments = values
                .iter()
                .zip(blindings.iter())
                .map(|(&v, &v_blinding)| pg.commit(Scalar::from_u64(v), v_blinding))
                .collect();
        }

        println!(
            "Aggregated rangeproof of m={} proofs of n={} bits has size {} bytes",
            m,
            n,
            proof_bytes.len(),
        );

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut rng = OsRng::new().unwrap();
            let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

            assert!(
                proof
                    .verify(
                        &value_commitments,
                        generators.all(),
                        &mut transcript,
                        &mut rng,
                        n,
                        m
                    )
                    .is_ok()
            );
        }
    }

    #[test]
    fn create_and_verify_n_32_m_1() {
        singleparty_create_and_verify_helper(32, 1);
    }

    #[test]
    fn create_and_verify_n_32_m_2() {
        singleparty_create_and_verify_helper(32, 2);
    }

    #[test]
    fn create_and_verify_n_32_m_4() {
        singleparty_create_and_verify_helper(32, 4);
    }

    #[test]
    fn create_and_verify_n_32_m_8() {
        singleparty_create_and_verify_helper(32, 8);
    }

    #[test]
    fn create_and_verify_n_64_m_1() {
        singleparty_create_and_verify_helper(64, 1);
    }

    #[test]
    fn create_and_verify_n_64_m_2() {
        singleparty_create_and_verify_helper(64, 2);
    }

    #[test]
    fn create_and_verify_n_64_m_4() {
        singleparty_create_and_verify_helper(64, 4);
    }

    #[test]
    fn create_and_verify_n_64_m_8() {
        singleparty_create_and_verify_helper(64, 8);
    }

    #[test]
    fn detect_dishonest_party_during_aggregation() {
        use self::dealer::*;
        use self::party::*;

        // Simulate four parties, two of which will be dishonest and use a 64-bit value.
        let m = 4;
        let n = 32;

        let generators = Generators::new(PedersenGenerators::default(), n, m);

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        // Parties 0, 2 are honest and use a 32-bit value
        let v0 = rng.next_u32() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(v0, v0_blinding, n, &generators).unwrap();

        let v2 = rng.next_u32() as u64;
        let v2_blinding = Scalar::random(&mut rng);
        let party2 = Party::new(v2, v2_blinding, n, &generators).unwrap();

        // Parties 1, 3 are dishonest and use a 64-bit value
        let v1 = rng.next_u64();
        let v1_blinding = Scalar::random(&mut rng);
        let party1 = Party::new(v1, v1_blinding, n, &generators).unwrap();

        let v3 = rng.next_u64();
        let v3_blinding = Scalar::random(&mut rng);
        let party3 = Party::new(v3, v3_blinding, n, &generators).unwrap();

        let dealer = Dealer::new(generators.all(), n, m, &mut transcript).unwrap();

        let (party0, value_com0) = party0.assign_position(0, &mut rng);
        let (party1, value_com1) = party1.assign_position(1, &mut rng);
        let (party2, value_com2) = party2.assign_position(2, &mut rng);
        let (party3, value_com3) = party3.assign_position(3, &mut rng);

        let (dealer, value_challenge) = dealer
            .receive_value_commitments(&[value_com0, value_com1, value_com2, value_com3])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&value_challenge, &mut rng);
        let (party1, poly_com1) = party1.apply_challenge(&value_challenge, &mut rng);
        let (party2, poly_com2) = party2.apply_challenge(&value_challenge, &mut rng);
        let (party3, poly_com3) = party3.apply_challenge(&value_challenge, &mut rng);

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(&[poly_com0, poly_com1, poly_com2, poly_com3])
            .unwrap();

        let share0 = party0.apply_challenge(&poly_challenge);
        let share1 = party1.apply_challenge(&poly_challenge);
        let share2 = party2.apply_challenge(&poly_challenge);
        let share3 = party3.apply_challenge(&poly_challenge);

        match dealer.receive_shares(&mut rng, &[share0, share1, share2, share3]) {
            Ok(_proof) => {
                panic!("The proof was malformed, but it was not detected");
            }
            Err(e) => {
                // XXX when we have error types, check that it was party 1 that did it
                assert_eq!(e, "proof failed to verify");
            }
        }
    }
}
