#![allow(non_snake_case)]

pub mod dealer;
pub mod messages;
pub mod party;

#[cfg(test)]
mod tests {
    use std::iter;

    use rand::{Rng, OsRng};

    use curve25519_dalek::scalar::Scalar;
    use proof_transcript::ProofTranscript;

    use super::*;

    use super::dealer::*;
    use super::messages::*;
    use super::party::*;

    fn create_multi<R: Rng>(rng: &mut R, values: Vec<u64>, n: usize) -> Proof {
        use generators::{Generators, PedersenGenerators};

        let m = values.len();
        let generators = Generators::new(PedersenGenerators::default(), n, m);
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let parties: Vec<_> = values
            .iter()
            .map(|&v| {
                let v_blinding = Scalar::random(rng);
                Party::new(v, v_blinding, n, &generators)
            })
            .collect();

        let dealer = Dealer::new(&mut transcript, n, m).unwrap();

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, value_challenge) =
            dealer.receive_value_commitments(&mut transcript, &value_commitments);

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) =
            dealer.receive_poly_commitments(&mut transcript, &poly_commitments);

        let proof_shares: Vec<ProofShare> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            .collect();

        dealer.receive_shares(
            &mut transcript,
            &proof_shares,
            &generators.all(),
            value_challenge.y,
        )
    }

    fn test_u32(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u32() as u64)
            .take(m)
            .collect();
        let rp = create_multi(&mut rng, v, 32);
        assert!(rp.verify(&mut rng, &mut transcript).is_ok());
    }

    fn test_u64(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let v: Vec<u64> = iter::repeat(()).map(|()| rng.next_u64()).take(m).collect();
        let rp = create_multi(&mut rng, v, 64);
        assert!(rp.verify(&mut rng, &mut transcript).is_ok());
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
