#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use transcript::TranscriptProtocol;

/// An entry point for verifying a R1CS proof.
///
/// The lifecycle of a `Verifier` is as follows. The verifying code
/// provides high-level commitments one by one,
/// `Verifier` adds them to the transcript and returns
/// the corresponding variables.
///
/// After all variables are committed, the verifying code calls `finalize_inputs`,
/// which consumes `Verifier` and returns `VerifierCS`.
/// The verifying code then allocates low-level variables and adds constraints to the `VerifierCS`.
///
/// When all constraints are added, the verifying code calls `verify`
/// on the instance of the constraint system to check the proof.
pub struct Verifier<'a, 'b> {
    /// Number of high-level variables
    m: u64,

    /// Constraint system implementation
    cs: VerifierCS<'a, 'b>,
}

/// A [`ConstraintSystem`] implementation for use by the verifier.
pub struct VerifierCS<'a, 'b> {
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    transcript: &'a mut Transcript,
    constraints: Vec<LinearCombination>,
    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<CompressedRistretto>,
}

impl<'a, 'b> ConstraintSystem for VerifierCS<'a, 'b> {
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Verifier<'a, 'b> {
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
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Verifier {
            m: 0,
            cs: VerifierCS {
                bp_gens,
                pc_gens,
                transcript,
                num_vars: 0,
                V: Vec::new(),
                constraints: Vec::new(),
            },
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: CompressedRistretto) -> Variable {
        let i = self.m as usize;
        self.m += 1;
        self.cs.V.push(commitment);

        // Add the commitment to the transcript.
        self.cs.transcript.append_point(b"V", &commitment);

        Variable::Committed(i)
    }

    /// Consume the `Verifier`, provide the `ConstraintSystem` implementation to the closure,
    /// and verify the proof against the resulting constraint system.
    pub fn finalize_inputs(self) -> VerifierCS<'a, 'b> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.cs.transcript.append_u64(b"m", self.m);
        self.cs
    }
}

impl<'a, 'b> VerifierCS<'a, 'b> {
    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let n = self.num_vars;
        let m = self.V.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];
        let mut wc = Scalar::zero();

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wc)
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    pub fn verify(mut self, proof: &R1CSProof) -> Result<(), R1CSError> {
        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.num_vars;
        let padded_n = self.num_vars.next_power_of_two();
        let pad = padded_n - n;

        use inner_product_proof::inner_product;
        use std::iter;
        use util;

        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }
        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.bp_gens.share(0);

        self.transcript.append_point(b"A_I", &proof.A_I);
        self.transcript.append_point(b"A_O", &proof.A_O);
        self.transcript.append_point(b"S", &proof.S);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.transcript.append_point(b"T_1", &proof.T_1);
        self.transcript.append_point(b"T_3", &proof.T_3);
        self.transcript.append_point(b"T_4", &proof.T_4);
        self.transcript.append_point(b"T_5", &proof.T_5);
        self.transcript.append_point(b"T_6", &proof.T_6);

        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.append_scalar(b"t_x", &proof.t_x);
        self.transcript
            .append_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript
            .append_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.transcript.challenge_scalar(b"w");

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

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

        // Create a `TranscriptRng` from the transcript. The verifier
        // has no witness data to commit, so this just mixes external
        // randomness into the existing transcript.
        use rand::thread_rng;
        let mut rng = self.transcript.build_rng().finalize(&mut thread_rng());
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
            iter::once(proof.A_I.decompress())
                .chain(iter::once(proof.A_O.decompress()))
                .chain(iter::once(proof.S.decompress()))
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
