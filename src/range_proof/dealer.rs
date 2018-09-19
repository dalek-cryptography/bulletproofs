//! The `dealer` module contains the API for the dealer state while the dealer is
//! engaging in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::MPCError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof;
use range_proof::RangeProof;
use transcript::TranscriptProtocol;

use util;

use super::messages::*;

/// Dealer is an entry-point API for setting up a dealer
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer coordinating `m` parties proving `n`-bit ranges.
    pub fn new<'a, 'b>(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        n: usize,
        m: usize,
    ) -> Result<DealerAwaitingValueCommitments<'a, 'b>, MPCError> {
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(MPCError::InvalidBitsize);
        }
        if !m.is_power_of_two() {
            return Err(MPCError::InvalidAggregation);
        }
        if bp_gens.gens_capacity < n {
            return Err(MPCError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        // At the end of the protocol, the dealer will attempt to
        // verify the proof, and if it fails, determine which party's
        // shares were invalid.
        //
        // However, verifying the proof requires either knowledge of
        // all of the challenges, or a copy of the initial transcript
        // state.
        //
        // The dealer has all of the challenges, but using them for
        // verification would require duplicating the verification
        // logic.  Instead, we keep a copy of the initial transcript
        // state.
        let initial_transcript = transcript.clone();

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        Ok(DealerAwaitingValueCommitments {
            bp_gens,
            pc_gens,
            transcript,
            initial_transcript,
            n,
            m,
        })
    }
}

/// The initial dealer state, waiting for the parties to send value
/// commitments.
pub struct DealerAwaitingValueCommitments<'a, 'b> {
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    transcript: &'a mut Transcript,
    /// The dealer keeps a copy of the initial transcript state, so
    /// that it can attempt to verify the aggregated proof at the end.
    initial_transcript: Transcript,
    n: usize,
    m: usize,
}

impl<'a, 'b> DealerAwaitingValueCommitments<'a, 'b> {
    /// Combines commitments and computes challenge variables.
    pub fn receive_value_commitments(
        self,
        value_commitments: Vec<ValueCommitment>,
    ) -> Result<(DealerAwaitingPolyCommitments<'a, 'b>, ValueChallenge), MPCError> {
        if self.m != value_commitments.len() {
            return Err(MPCError::WrongNumValueCommitments);
        }

        // XXX value commitments should be compressed
        // Commit each V_j individually
        for vc in value_commitments.iter() {
            self.transcript.commit_point(b"V", &vc.V_j.compress());
        }

        let A: RistrettoPoint = value_commitments.iter().map(|vc| vc.A_j).sum();
        let S: RistrettoPoint = value_commitments.iter().map(|vc| vc.S_j).sum();

        // Commit aggregated A_j, S_j
        self.transcript.commit_point(b"A", &A.compress());
        self.transcript.commit_point(b"S", &S.compress());

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");
        let value_challenge = ValueChallenge { y, z };

        Ok((
            DealerAwaitingPolyCommitments {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                value_challenge,
                value_commitments,
                A,
                S,
            },
            value_challenge,
        ))
    }
}

pub struct DealerAwaitingPolyCommitments<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    value_challenge: ValueChallenge,
    value_commitments: Vec<ValueCommitment>,
    /// Aggregated commitment to the parties' bits
    A: RistrettoPoint,
    /// Aggregated commitment to the parties' bit blindings
    S: RistrettoPoint,
}

impl<'a, 'b> DealerAwaitingPolyCommitments<'a, 'b> {
    pub fn receive_poly_commitments(
        self,
        poly_commitments: Vec<PolyCommitment>,
    ) -> Result<(DealerAwaitingProofShares<'a, 'b>, PolyChallenge), MPCError> {
        if self.m != poly_commitments.len() {
            return Err(MPCError::WrongNumPolyCommitments);
        }

        // Commit sums of T_1_j's and T_2_j's
        let T_1: RistrettoPoint = poly_commitments.iter().map(|pc| pc.T_1_j).sum();
        let T_2: RistrettoPoint = poly_commitments.iter().map(|pc| pc.T_2_j).sum();

        self.transcript.commit_point(b"T_1", &T_1.compress());
        self.transcript.commit_point(b"T_2", &T_2.compress());

        let x = self.transcript.challenge_scalar(b"x");
        let poly_challenge = PolyChallenge { x };

        Ok((
            DealerAwaitingProofShares {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                value_challenge: self.value_challenge,
                value_commitments: self.value_commitments,
                A: self.A,
                S: self.S,
                poly_challenge,
                poly_commitments,
                T_1,
                T_2,
            },
            poly_challenge,
        ))
    }
}

pub struct DealerAwaitingProofShares<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    value_challenge: ValueChallenge,
    value_commitments: Vec<ValueCommitment>,
    poly_challenge: PolyChallenge,
    poly_commitments: Vec<PolyCommitment>,
    A: RistrettoPoint,
    S: RistrettoPoint,
    T_1: RistrettoPoint,
    T_2: RistrettoPoint,
}

impl<'a, 'b> DealerAwaitingProofShares<'a, 'b> {
    /// Assembles proof shares into an `RangeProof`.
    ///
    /// Used as a helper function by `receive_trusted_shares` (which
    /// just hands back the result) and `receive_shares` (which
    /// validates the proof shares.
    fn assemble_shares(&mut self, proof_shares: &[ProofShare]) -> Result<RangeProof, MPCError> {
        if self.m != proof_shares.len() {
            return Err(MPCError::WrongNumProofShares);
        }

        let t_x: Scalar = proof_shares.iter().map(|ps| ps.t_x).sum();
        let t_x_blinding: Scalar = proof_shares.iter().map(|ps| ps.t_x_blinding).sum();
        let e_blinding: Scalar = proof_shares.iter().map(|ps| ps.e_blinding).sum();

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let l_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();

        let ipp_proof = inner_product_proof::InnerProductProof::create(
            self.transcript,
            &Q,
            util::exp_iter(self.value_challenge.y.invert()),
            self.bp_gens.G(self.n, self.m).cloned().collect(),
            self.bp_gens.H(self.n, self.m).cloned().collect(),
            l_vec,
            r_vec,
        );

        Ok(RangeProof {
            A: self.A.compress(),
            S: self.S.compress(),
            T_1: self.T_1.compress(),
            T_2: self.T_2.compress(),
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }

    /// Assemble the final aggregated proof from the given
    /// `proof_shares`, and validate that all input shares and the
    /// aggregated proof are well-formed.  If the aggregated proof is
    /// not well-formed, this function detects which party submitted a
    /// malformed share and returns that information as part of the
    /// error.
    ///
    /// XXX define error types so we can surface the blame info
    pub fn receive_shares(mut self, proof_shares: &[ProofShare]) -> Result<RangeProof, MPCError> {
        let proof = self.assemble_shares(proof_shares)?;

        let V: Vec<_> = self.value_commitments.iter().map(|vc| vc.V_j).collect();

        // See comment in `Dealer::new` for why we use `initial_transcript`
        let transcript = &mut self.initial_transcript;
        if proof
            .verify(self.bp_gens, self.pc_gens, transcript, &V, self.n)
            .is_ok()
        {
            Ok(proof)
        } else {
            // Proof verification failed. Now audit the parties:
            let mut bad_shares = Vec::new();
            for j in 0..self.m {
                match proof_shares[j].audit_share(
                    &self.bp_gens,
                    &self.pc_gens,
                    j,
                    &self.value_commitments[j],
                    &self.value_challenge,
                    &self.poly_commitments[j],
                    &self.poly_challenge,
                ) {
                    Ok(_) => {}
                    Err(_) => bad_shares.push(j),
                }
            }
            Err(MPCError::MalformedProofShares { bad_shares })
        }
    }

    /// Assemble the final aggregated proof from the given
    /// `proof_shares`, but does not validate that they are well-formed.
    ///
    /// ## WARNING
    ///
    /// This function does **NOT** validate the proof shares.  It is
    /// suitable for creating aggregated proofs when all parties are
    /// known by the dealer to be honest (for instance, when there's
    /// only one party playing all roles).
    ///
    /// Otherwise, use `receive_shares`, which validates that all
    /// shares are well-formed, or else detects which party(ies)
    /// submitted malformed shares.
    pub fn receive_trusted_shares(
        mut self,
        proof_shares: &[ProofShare],
    ) -> Result<RangeProof, MPCError> {
        self.assemble_shares(proof_shares)
    }
}
