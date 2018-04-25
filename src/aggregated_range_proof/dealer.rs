use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use generators::GeneratorsView;
use inner_product_proof;
use proof_transcript::ProofTranscript;
use util;

use super::messages::*;

/// Dealer is an entry-point API for setting up a dealer
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer coordinating `m` parties proving `n`-bit ranges.
    pub fn new(
        transcript: &mut ProofTranscript,
        n: usize,
        m: usize,
    ) -> DealerAwaitingValueCommitments {
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        DealerAwaitingValueCommitments { n, m }
    }
}

/// When the dealer is initialized, it only knows the size of the set.
pub struct DealerAwaitingValueCommitments {
    n: usize,
    m: usize,
}

impl DealerAwaitingValueCommitments {
    /// Combines commitments and computes challenge variables.
    pub fn receive_value_commitments(
        self,
        transcript: &mut ProofTranscript,
        vc: &Vec<ValueCommitment>,
    ) -> (DealerAwaitingPolyCommitments, ValueChallenge) {
        assert!(vc.len() == self.m);
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();

        for commitment in vc.iter() {
            // Commit each V individually
            transcript.commit(commitment.V.compress().as_bytes());

            // Commit sums of As and Ss.
            A += commitment.A;
            S += commitment.S;
        }

        transcript.commit(A.compress().as_bytes());
        transcript.commit(S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        (
            DealerAwaitingPolyCommitments { n: self.n },
            ValueChallenge { y, z },
        )
    }
}

pub struct DealerAwaitingPolyCommitments {
    n: usize,
}

impl DealerAwaitingPolyCommitments {
    pub fn receive_poly_commitments(
        self,
        transcript: &mut ProofTranscript,
        poly_commitments: &Vec<PolyCommitment>,
    ) -> (DealerAwaitingProofShares, PolyChallenge) {
        // Commit sums of T1s and T2s.
        let mut T1 = RistrettoPoint::identity();
        let mut T2 = RistrettoPoint::identity();
        for commitment in poly_commitments.iter() {
            T1 += commitment.T_1;
            T2 += commitment.T_2;
        }
        transcript.commit(T1.compress().as_bytes());
        transcript.commit(T2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        (DealerAwaitingProofShares { n: self.n }, PolyChallenge { x })
    }
}

pub struct DealerAwaitingProofShares {
    n: usize,
}

impl DealerAwaitingProofShares {
    pub fn receive_shares(
        self,
        transcript: &mut ProofTranscript,
        proof_shares: &Vec<ProofShare>,
        gen: &GeneratorsView,
        y: Scalar,
    ) -> Proof {
        let value_commitments = proof_shares
            .iter()
            .map(|ps| ps.value_commitment.V)
            .collect();
        let A = proof_shares
            .iter()
            .fold(RistrettoPoint::identity(), |A, ps| {
                A + ps.value_commitment.A
            });
        let S = proof_shares
            .iter()
            .fold(RistrettoPoint::identity(), |S, ps| {
                S + ps.value_commitment.S
            });
        let T_1 = proof_shares
            .iter()
            .fold(RistrettoPoint::identity(), |T_1, ps| {
                T_1 + ps.poly_commitment.T_1
            });
        let T_2 = proof_shares
            .iter()
            .fold(RistrettoPoint::identity(), |T_2, ps| {
                T_2 + ps.poly_commitment.T_2
            });
        let t = proof_shares
            .iter()
            .fold(Scalar::zero(), |acc, ps| acc + ps.t_x);
        let t_x_blinding = proof_shares
            .iter()
            .fold(Scalar::zero(), |acc, ps| acc + ps.t_x_blinding);
        let e_blinding = proof_shares
            .iter()
            .fold(Scalar::zero(), |acc, ps| acc + ps.e_blinding);
        transcript.commit(t.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * gen.pedersen_generators.B;

        let l_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();
        let ipp_proof = inner_product_proof::InnerProductProof::create(
            transcript,
            &Q,
            util::exp_iter(y.invert()),
            gen.G.to_vec(),
            gen.H.to_vec(),
            l_vec.clone(),
            r_vec.clone(),
        );

        Proof {
            n: self.n,
            value_commitments,
            A,
            S,
            T_1,
            T_2,
            t_x: t,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        }
    }
}
