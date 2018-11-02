#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use super::{
    ScalarValue,
    OpaqueScalar,
    Assignment,
    Variable,
    VariableIndex,
    Constraint,
    ConstraintSystem,
    cs::ConstraintSystemState,
    R1CSProof,
};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use transcript::TranscriptProtocol;

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The lifecycle of a `VerifierCS` is as follows. The verification
/// code assembles the commitments to the external inputs to the
/// constraint system, then passes them, along with generators and a
/// transcript, to [`VerifierCS::new`].  This initializes the
/// `VerifierCS` and returns [`Variable`]s corresponding to the
/// inputs.
///
/// The verifier can then pass the `VerifierCS` and the external
/// variables to the same gadget code as the prover, using
/// `Assignment::Missing` for witness variables, to build an identical
/// constraint system to the one the prover built.  Finally, they pass
/// the prover's [`R1CSProof`] to [`VerifierCS::verify`], which
/// consumes the `VerifierCS` and verifies the proof.
pub struct VerifierCS<'a, 'b> {
    V: Vec<CompressedRistretto>,
    cs_state: ConstraintSystemState<'a>,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    variables_count: usize,
}

impl<'a, 'b> ConstraintSystem for VerifierCS<'a, 'b> {

    fn assign_multiplier<S: ScalarValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {
        self.variables_count += 1;
        self.cs_state.assign_multiplier(left,right,out)
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        self.cs_state.add_constraint(constraint);
    }

    fn challenge_scalar<F>(&mut self, label: &'static [u8], callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(OpaqueScalar)-> Result<(), R1CSError> {
        self.cs_state.challenge_scalar(label, callback)
    }
}


impl<'a, 'b> VerifierCS<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`VariableIndex`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        commitments: Vec<CompressedRistretto>,
    ) -> Self {

        let cs_state = ConstraintSystemState::new(transcript, &commitments[..]);

        VerifierCS {
            V: commitments,
            cs_state,
            bp_gens,
            pc_gens,
            variables_count: 0,
        }
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    pub fn verify<F>(mut self, proof: &R1CSProof, builder: F) -> Result<(), R1CSError> 
    where
        F: FnOnce(&mut Self, Vec<Variable<Scalar>>) -> Result<(), R1CSError>
    {
        use inner_product_proof::inner_product;
        use std::iter;
        use util;

        // 0. Convert the external commitments into the variables
        let variables = self.V.iter().enumerate().map(|(i,_)| {
            Variable {
                index: VariableIndex::Committed(i),
                assignment: Assignment::Missing()
            }
        }).collect::<Vec<_>>();

        // 1. Build the constraint system.
        builder(&mut self, variables)?;

        let n1 = self.variables_count;
        self.cs_state.transcript.commit_point(b"A_I1", &proof.A_I1);
        self.cs_state.transcript.commit_point(b"A_O1", &proof.A_O1);
        self.cs_state.transcript.commit_point(b"S1", &proof.S1);

        // 3. Process the second phase of the CS, allocating more variables
        //    and adding more constraints.
        self.cs_state.complete_constraints()?;

        self.cs_state.transcript.commit_point(b"A_I2", &proof.A_I2);
        self.cs_state.transcript.commit_point(b"A_O2", &proof.A_O2);
        self.cs_state.transcript.commit_point(b"S2", &proof.S2);

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.variables_count;
        let n2 = n - n1;
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;
        
        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }
        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.bp_gens.share(0);

        let y = self.cs_state.transcript.challenge_scalar(b"y");
        let z = self.cs_state.transcript.challenge_scalar(b"z");

        self.cs_state.transcript.commit_point(b"T_1", &proof.T_1);
        self.cs_state.transcript.commit_point(b"T_3", &proof.T_3);
        self.cs_state.transcript.commit_point(b"T_4", &proof.T_4);
        self.cs_state.transcript.commit_point(b"T_5", &proof.T_5);
        self.cs_state.transcript.commit_point(b"T_6", &proof.T_6);

        // Challenges for evaluating the polynomial and combining two phases of the protocol.
        let e = self.cs_state.transcript.challenge_scalar(b"e");
        let x = self.cs_state.transcript.challenge_scalar(b"x");

        self.cs_state.transcript.commit_scalar(b"t_x", &proof.t_x);
        self.cs_state.transcript
            .commit_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.cs_state.transcript
            .commit_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.cs_state.transcript.challenge_scalar(b"w");

        let (wL, wR, wO, wV, wc) = self.cs_state.flattened_constraints::<Scalar>(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof.ipp_proof.verification_scalars(self.cs_state.transcript);

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.invert();
        let y_inv_vec = util::exp_iter(y_inv)
            .take(padded_n)
            .collect::<Vec<Scalar>>();
        let yneg_wR = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(Scalar::zero()).take(pad))
            .collect::<Vec<Scalar>>();

        let delta = inner_product(&yneg_wR[0..n], &wL);

        // define parameters for P check
        let g_scalars = yneg_wR
            .iter()
            .zip(s.iter().take(padded_n))
            .map(|(yneg_wRi, s_i)| x * yneg_wRi - a * s_i);

        let h_scalars = y_inv_vec
            .iter()
            .zip(s.iter().rev().take(padded_n))
            .zip(wL.into_iter().chain(iter::repeat(Scalar::zero()).take(pad)))
            .zip(wO.into_iter().chain(iter::repeat(Scalar::zero()).take(pad)))
            .map(|(((y_inv_i, s_i_inv), wLi), wOi)| {
                y_inv_i * (x * wLi + wOi - b * s_i_inv) - Scalar::one()
            });

        // Create a `TranscriptRng` from the transcript
        use rand::thread_rng;
        let mut rng = self.cs_state.transcript.build_rng().finalize(&mut thread_rng());
        let r = Scalar::random(&mut rng);

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(x) // A_I
                .chain(iter::once(xx)) // A_O
                .chain(iter::once(xxx)) // S
                .chain(wV.iter().map(|wVi| wVi * rxx)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * (wc + delta) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g_scalars) // G
                .chain(h_scalars) // H
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()), // ipp_proof.R_vec
            iter::once(Some(proof.A_I1.decompress()? + proof.A_I2.decompress()?))
                .chain(iter::once(Some(proof.A_O1.decompress()? + proof.A_O2.decompress()?)))
                .chain(iter::once(Some(proof.S1.decompress()? + proof.S2.decompress()?)))
                .chain(self.V.iter().map(|V_i| V_i.decompress()))
                .chain(T_points.iter().map(|T_i| T_i.decompress()))
                .chain(iter::once(Some(self.pc_gens.B)))
                .chain(iter::once(Some(self.pc_gens.B_blinding)))
                .chain(gens.G(padded_n).map(|&G_i| Some(G_i)))
                .chain(gens.H(padded_n).map(|&H_i| Some(H_i)))
                .chain(proof.ipp_proof.L_vec.iter().map(|L_i| L_i.decompress()))
                .chain(proof.ipp_proof.R_vec.iter().map(|R_i| R_i.decompress())),
        )
        .ok_or_else(|| R1CSError::VerificationError)?;

        use curve25519_dalek::traits::IsIdentity;

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}
