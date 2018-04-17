use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use std::clone::Clone;
use proof_transcript::ProofTranscript;
use generators::GeneratorsView;
use util::{self};
use inner_product_proof;

use super::messages::*;


/// Dealer is an entry-point API for setting up a dealer
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer with the given parties and a number of bits
    pub fn new(
        n: usize,
        m: usize,
    ) -> Result<DealerAwaitingValues, &'static str> {
        let mut transcript = ProofTranscript::new(b"MultiRangeProof");
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        Ok(DealerAwaitingValues { transcript, n })
    }
}

/// When the dealer is initialized, it only knows the size of the set.
pub struct DealerAwaitingValues {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingValues {
    /// Combines commitments and computes challenge variables.
    pub fn present_value_commitments(
        mut self,
        vc: &Vec<ValueCommitment>,
    ) -> (DealerAwaitingPoly, Scalar, Scalar) {
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();

        for commitment in vc.iter() {
            // Commit each V individually
            self.transcript.commit(commitment.V.compress().as_bytes());

            // Commit sums of As and Ss.
            A += commitment.A;
            S += commitment.S;
        }

        self.transcript.commit(A.compress().as_bytes());
        self.transcript.commit(S.compress().as_bytes());

        let y = self.transcript.challenge_scalar();
        let z = self.transcript.challenge_scalar();

        (
            DealerAwaitingPoly {
                transcript: self.transcript,
                n: self.n,
            },
            y,
            z,
        )
    }
}

pub struct DealerAwaitingPoly {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingPoly {
    pub fn present_poly_commitments(
        mut self,
        poly_commitments: &Vec<PolyCommitment>,
    ) -> (DealerAwaitingShares, Scalar) {
        // Commit sums of T1s and T2s.
        let mut T1 = RistrettoPoint::identity();
        let mut T2 = RistrettoPoint::identity();
        for commitment in poly_commitments.iter() {
            T1 += commitment.T_1;
            T2 += commitment.T_2;
        }
        self.transcript.commit(T1.compress().as_bytes());
        self.transcript.commit(T2.compress().as_bytes());

        let x = self.transcript.challenge_scalar();

        (
            DealerAwaitingShares {
                transcript: self.transcript,
                n: self.n,
            },
            x,
        )
    }
}

pub struct DealerAwaitingShares {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingShares {
    pub fn present_shares(
        mut self,
        proof_shares: &Vec<ProofShare>,
        gen: &GeneratorsView,
        y: Scalar,
    ) -> Proof {
        let value_commitments = proof_shares
            .iter()
            .map(|ps| ps.value_commitment.V.clone())
            .collect();
        let A = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |A, ps| A + ps.value_commitment.A,
        );
        let S = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |S, ps| S + ps.value_commitment.S,
        );
        let T_1 = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |T_1, ps| T_1 + ps.poly_commitment.T_1,
        );
        let T_2 = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |T_2, ps| T_2 + ps.poly_commitment.T_2,
        );
        let t = proof_shares.iter().fold(
            Scalar::zero(),
            |acc, ps| acc + ps.t_x,
        );
        let t_x_blinding = proof_shares.iter().fold(Scalar::zero(), |acc, ps| {
            acc + ps.t_x_blinding
        });
        let e_blinding = proof_shares.iter().fold(Scalar::zero(), |acc, ps| {
            acc + ps.e_blinding
        });
        self.transcript.commit(t.as_bytes());
        self.transcript.commit(t_x_blinding.as_bytes());
        self.transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar();
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
            &mut self.transcript,
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
            l: l_vec,
            r: r_vec,
        }
    }
}