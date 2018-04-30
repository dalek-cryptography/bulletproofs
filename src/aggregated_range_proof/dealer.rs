use rand::Rng;

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
    pub fn new<'a, 'b>(
        gens: GeneratorsView<'b>,
        n: usize,
        m: usize,
        transcript: &'a mut ProofTranscript,
    ) -> Result<DealerAwaitingValueCommitments<'a, 'b>, &'static str> {
        if !n.is_power_of_two() || n > 64 {
            return Err("n is not valid: must be a power of 2, and less than or equal to 64");
        }
        if !m.is_power_of_two() {
            return Err("m is not valid: must be a power of 2");
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

        // Commit to aggregation parameters
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        Ok(DealerAwaitingValueCommitments {
            n,
            m,
            transcript,
            initial_transcript,
            gens,
        })
    }
}

/// The initial dealer state, waiting for the parties to send value
/// commitments.
pub struct DealerAwaitingValueCommitments<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut ProofTranscript,
    /// The dealer keeps a copy of the initial transcript state, so
    /// that it can attempt to verify the aggregated proof at the end.
    initial_transcript: ProofTranscript,
    gens: GeneratorsView<'b>,
}

impl<'a, 'b> DealerAwaitingValueCommitments<'a, 'b> {
    /// Combines commitments and computes challenge variables.
    pub fn receive_value_commitments(
        self,
        value_commitments: &[ValueCommitment],
    ) -> Result<(DealerAwaitingPolyCommitments<'a, 'b>, ValueChallenge), &'static str> {
        if self.m != value_commitments.len() {
            return Err("Length of value commitments doesn't match expected length m");
        }

        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();

        for commitment in value_commitments.iter() {
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
        let value_challenge = ValueChallenge { y, z };

        Ok((
            DealerAwaitingPolyCommitments {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                gens: self.gens,
                value_challenge: value_challenge.clone(),
            },
            value_challenge,
        ))
    }
}

pub struct DealerAwaitingPolyCommitments<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut ProofTranscript,
    initial_transcript: ProofTranscript,
    gens: GeneratorsView<'b>,
    value_challenge: ValueChallenge,
}

impl<'a, 'b> DealerAwaitingPolyCommitments<'a, 'b> {
    pub fn receive_poly_commitments(
        self,
        poly_commitments: &[PolyCommitment],
    ) -> Result<(DealerAwaitingProofShares<'a, 'b>, PolyChallenge), &'static str> {
        if self.m != poly_commitments.len() {
            return Err("Length of poly commitments doesn't match expected length m");
        }

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
        let poly_challenge = PolyChallenge { x };

        Ok((
            DealerAwaitingProofShares {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                gens: self.gens,
                value_challenge: self.value_challenge,
                poly_challenge: poly_challenge.clone(),
            },
            poly_challenge,
        ))
    }
}

pub struct DealerAwaitingProofShares<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut ProofTranscript,
    initial_transcript: ProofTranscript,
    gens: GeneratorsView<'b>,
    value_challenge: ValueChallenge,
    poly_challenge: PolyChallenge,
}

impl<'a, 'b> DealerAwaitingProofShares<'a, 'b> {
    /// Assembles proof shares into an `AggregatedProof`.
    ///
    /// Used as a helper function by `receive_trusted_shares` (which
    /// just hands back the result) and `receive_shares` (which
    /// validates the proof shares.
    fn assemble_shares(
        &mut self,
        proof_shares: &[ProofShare],
    ) -> Result<AggregatedProof, &'static str> {
        if self.m != proof_shares.len() {
            return Err("Length of proof shares doesn't match expected length m");
        }

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

        self.transcript.commit(t.as_bytes());
        self.transcript.commit(t_x_blinding.as_bytes());
        self.transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar();
        let Q = w * self.gens.pedersen_generators.B;

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
            self.gens.G.to_vec(),
            self.gens.H.to_vec(),
            l_vec.clone(),
            r_vec.clone(),
        );

        Ok(AggregatedProof {
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
    pub fn receive_shares<R: Rng>(
        mut self,
        rng: &mut R,
        proof_shares: &[ProofShare],
    ) -> Result<AggregatedProof, &'static str> {
        let proof = self.assemble_shares(proof_shares)?;

        // See comment in `Dealer::new` for why we use `initial_transcript`
        if proof.verify(rng, &mut self.initial_transcript).is_ok() {
            Ok(proof)
        } else {
            // Create a list of bad shares
            let mut bad_shares = Vec::new();
            for (j, share) in proof_shares.iter().enumerate() {
                match share.verify_share(self.n, j, &self.value_challenge, &self.poly_challenge) {
                    Ok(_) => {}
                    Err(_) => bad_shares.push(j),
                }
            }
            // XXX pass this upwards
            println!("bad shares: {:?}", bad_shares);
            Err("proof failed to verify")
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
    ) -> Result<AggregatedProof, &'static str> {
        self.assemble_shares(proof_shares)
    }
}
