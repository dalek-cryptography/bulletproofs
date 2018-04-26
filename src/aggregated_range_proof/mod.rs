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
            dealer.receive_value_commitments(&value_commitments, transcript)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) =
            dealer.receive_poly_commitments(&poly_commitments, transcript)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            .collect();

        let (proof, _) = dealer.receive_shares(&proof_shares, &generators.all(), transcript)?;

        Ok(proof)
    }
}

#[cfg(test)]
mod tests {
    use std::iter;

    use rand::{OsRng, Rng};

    use curve25519_dalek::scalar::Scalar;
    use proof_transcript::ProofTranscript;

    use super::dealer::*;
    use super::messages::*;
    use super::party::*;

    fn create_multi<R: Rng>(
        rng: &mut R,
        values: Vec<u64>,
        n: usize,
    ) -> (AggregatedProof, Vec<ProofShareVerifier>) {
        use generators::{Generators, PedersenGenerators};

        let m = values.len();
        let generators = Generators::new(PedersenGenerators::default(), n, m);
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let parties: Vec<_> = values
            .iter()
            .map(|&v| {
                let v_blinding = Scalar::random(rng);
                Party::new(v, v_blinding, n, &generators).unwrap()
            })
            .collect();

        let dealer = Dealer::new(n, m, &mut transcript).unwrap();

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, value_challenge) = dealer
            .receive_value_commitments(&value_commitments, &mut transcript)
            .unwrap();

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(&poly_commitments, &mut transcript)
            .unwrap();

        let proof_shares: Vec<ProofShare> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            .collect();

        dealer
            .receive_shares(&proof_shares, &generators.all(), &mut transcript)
            .unwrap()
    }

    fn test_u32(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u32() as u64)
            .take(m)
            .collect();
        let (proof, share_verifiers) = create_multi(&mut rng, v, 32);
        assert!(proof.verify(&mut rng, &mut transcript).is_ok());
        share_verifiers
            .iter()
            .map(|sv| assert!(sv.verify_share().is_ok()))
            .last();
    }

    fn test_u64(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let v: Vec<u64> = iter::repeat(()).map(|()| rng.next_u64()).take(m).collect();
        let (proof, share_verifiers) = create_multi(&mut rng, v, 64);
        assert!(proof.verify(&mut rng, &mut transcript).is_ok());
        share_verifiers
            .iter()
            .map(|sv| assert!(sv.verify_share().is_ok()))
            .last();
    }

    #[test]
    fn one_value() {
        test_u32(1);
        test_u64(1);
    }

    #[test]
    fn two_values() {
        test_u32(2);
        test_u64(2);
    }

    #[test]
    fn four_values() {
        test_u32(4);
        test_u64(4);
    }

    #[test]
    fn eight_values() {
        test_u32(8);
        test_u64(8);
    }
}
