#![allow(non_snake_case)]

use rand::Rng;

use curve25519_dalek::scalar::Scalar;

use generators::Generators;
use proof_transcript::ProofTranscript;

pub mod dealer;
pub mod messages;
pub mod party;

pub use self::messages::AggregatedProof;

struct SinglePartyAggregator {}

impl SinglePartyAggregator {
    /// Create an aggregated rangeproof of multiple values.
    ///
    /// This performs the same proof aggregation MPC protocol, but
    /// with one party playing all roles.
    ///
    /// The length of `values` must be a power of 2.
    ///
    /// XXX this should allow proving about existing commitments.
    fn generate_proof<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        values: &[u64],
        n: usize,
    ) -> Result<AggregatedProof, &'static str> {
        use self::dealer::*;
        use self::messages::*;
        use self::party::*;

        let dealer = Dealer::new(n, values.len(), transcript)?;

        let parties: Vec<_> = values
            .iter()
            .map(|&v| {
                let v_blinding = Scalar::random(rng);
                Party::new(v, v_blinding, n, &generators)
            })
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>,_>>()?;

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, value_challenge) =
            dealer.receive_value_commitments(&value_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) =
            dealer.receive_poly_commitments(&poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            .collect();

        let (proof, _) = dealer.receive_shares(&proof_shares, &generators.all())?;

        Ok(proof)
    }
}

#[cfg(test)]
mod tests {
    use rand::OsRng;

    use super::*;

    use generators::PedersenGenerators;

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

        // Prover's scope
        {
            // 1. Generate the proof

            let mut rng = OsRng::new().unwrap();
            let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();

            let proof = SinglePartyAggregator::generate_proof(
                &generators,
                &mut transcript,
                &mut rng,
                &values,
                n,
            ).unwrap();

            // 2. Serialize
            proof_bytes = bincode::serialize(&proof).unwrap();
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

            assert!(proof.verify(&mut rng, &mut transcript).is_ok());
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
}
