#![allow(non_snake_case)]

use rand::Rng;

use curve25519_dalek::scalar::Scalar;

use generators::Generators;
use proof_transcript::ProofTranscript;

pub mod dealer;
pub mod messages;
pub mod party;

pub use self::messages::AggregatedProof;

pub struct SinglePartyAggregator {}

impl SinglePartyAggregator {
    /// Create an aggregated rangeproof of multiple values.
    ///
    /// This performs the same proof aggregation MPC protocol, but
    /// with one party playing all roles.
    ///
    /// The length of `values` must be a power of 2.
    pub fn generate_proof<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<AggregatedProof, &'static str> {
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
}

#[cfg(test)]
mod tests {
    use rand::OsRng;

    use curve25519_dalek::ristretto::RistrettoPoint;

    use generators::PedersenGenerators;

    use super::*;

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

            let proof = SinglePartyAggregator::generate_proof(
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
            let proof: AggregatedProof = bincode::deserialize(&proof_bytes).unwrap();

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
