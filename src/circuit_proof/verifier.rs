#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use super::assignment::Assignment;
use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::Generators;
use transcript::TranscriptProtocol;

pub struct VerifierCS<'a, 'b> {
    transcript: &'a mut Transcript,
    generators: &'b Generators,
    constraints: Vec<LinearCombination>,
    num_vars: usize,
    V: Vec<CompressedRistretto>,
}

impl<'a, 'b> ConstraintSystem for VerifierCS<'a, 'b> {
    fn assign_multiplier(
        &mut self,
        _left: Assignment,
        _right: Assignment,
        _out: Assignment,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let var = self.num_vars;
        self.num_vars += 1;

        Ok((
            Variable::MultiplierLeft(var),
            Variable::MultiplierRight(var),
            Variable::MultiplierOutput(var),
        ))
    }

    fn assign_uncommitted(
        &mut self,
        val_1: Assignment,
        val_2: Assignment,
    ) -> Result<(Variable, Variable), R1CSError> {
        let (left, right, _) = self.assign_multiplier(val_1, val_2, Assignment::Missing())?;
        Ok((left, right))
    }

    fn add_constraint(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> VerifierCS<'a, 'b> {
    pub fn new(
        transcript: &'a mut Transcript,
        generators: &'b Generators,
        commitments: Vec<CompressedRistretto>,
    ) -> (Self, Vec<Variable>) {
        let m = commitments.len();
        transcript.r1cs_domain_sep(m as u64);

        let mut variables = Vec::with_capacity(m);
        for (i, commitment) in commitments.iter().enumerate() {
            // Commit the commitment to the transcript
            transcript.commit_point(b"V", &commitment);

            // Allocate and return a variable for the commitment
            variables.push(Variable::Committed(i));
        }

        let cs = VerifierCS {
            transcript,
            generators,
            num_vars: 0,
            V: commitments,
            constraints: Vec::new(),
        };

        (cs, variables)
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (z_zQ_WL, z_zQ_WR, z_zQ_WO, z_zQ_WV, z_zQ_c)
    /// ```
    /// where `z_zQ_WL` is \\( z \cdot z^Q \cdot W_L \\), etc.
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let n = self.num_vars;
        let m = self.V.len();

        let mut z_zQ_WL = vec![Scalar::zero(); n];
        let mut z_zQ_WR = vec![Scalar::zero(); n];
        let mut z_zQ_WO = vec![Scalar::zero(); n];
        let mut z_zQ_WV = vec![Scalar::zero(); m];
        let mut z_zQ_c = Scalar::zero();

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        z_zQ_WL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        z_zQ_WR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        z_zQ_WO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        z_zQ_WV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        z_zQ_c -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (z_zQ_WL, z_zQ_WR, z_zQ_WO, z_zQ_WV, z_zQ_c)
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn verify(mut self, proof: &R1CSProof) -> Result<(), R1CSError> {
        let temp_n = self.num_vars;
        if !(temp_n == 0 || temp_n.is_power_of_two()) {
            let pad = temp_n.next_power_of_two() - temp_n;
            for _ in 0..pad {
                self.assign_multiplier(Assignment::zero(), Assignment::zero(), Assignment::zero())?;
            }
        }

        use inner_product_proof::inner_product;
        use std::iter;
        use util;

        let n = self.num_vars;
        if self.generators.gens_capacity < n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }
        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.generators.share(0);

        // Create a `TranscriptRng` from the transcript
        use rand::thread_rng;
        let mut rng = self
            .transcript
            .fork_transcript()
            .reseed_from_rng(&mut thread_rng());

        self.transcript.commit_point(b"A_I", &proof.A_I);
        self.transcript.commit_point(b"A_O", &proof.A_O);
        self.transcript.commit_point(b"S", &proof.S);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (z_zQ_WL, z_zQ_WR, z_zQ_WO, z_zQ_WV, z_zQ_c) = self.flattened_constraints(&z);

        self.transcript.commit_point(b"T_1", &proof.T_1);
        self.transcript.commit_point(b"T_3", &proof.T_3);
        self.transcript.commit_point(b"T_4", &proof.T_4);
        self.transcript.commit_point(b"T_5", &proof.T_5);
        self.transcript.commit_point(b"T_6", &proof.T_6);

        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.commit_scalar(b"t_x", &proof.t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript
            .commit_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.transcript.challenge_scalar(b"w");

        let r = Scalar::random(&mut rng);
        let xx = x * x;
        let y_inv = y.invert();

        // Calculate points that represent the matrices
        let H_prime: Vec<RistrettoPoint> = gens
            .H(n)
            .zip(util::exp_iter(y_inv))
            .map(|(H_i, exp_y_inv)| H_i * exp_y_inv)
            .collect();

        // W_L_point = <h * y^-n , z * z^Q * W_L>, line 81
        let W_L_point = RistrettoPoint::vartime_multiscalar_mul(&z_zQ_WL, &H_prime);

        // W_R_point = <g , y^-n * z * z^Q * W_R>, line 82
        let y_n_z_zQ_WR = z_zQ_WR
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(W_R_right_i, exp_y_inv)| W_R_right_i * exp_y_inv)
            .collect::<Vec<Scalar>>();
        let W_R_point = RistrettoPoint::vartime_multiscalar_mul(&y_n_z_zQ_WR, gens.G(n));

        // W_O_point = <h * y^-n , z * z^Q * W_O>, line 83
        let W_O_point = RistrettoPoint::vartime_multiscalar_mul(&z_zQ_WO, &H_prime);

        // Get IPP variables
        let (x_sq, x_inv_sq, s) = proof.ipp_proof.verification_scalars(self.transcript);
        let s_inv = s.iter().rev().take(n);
        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        // define parameters for P check
        let g = s.iter().take(n).map(|s_i| -a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .map(|(s_i_inv, exp_y_inv)| -exp_y_inv * b * s_i_inv - Scalar::one());

        // define parameters for t check
        let delta = inner_product(&y_n_z_zQ_WR, &z_zQ_WL);
        let rxx = r * xx;
        let V_coeff = z_zQ_WV.iter().map(|W_V_i| rxx * W_V_i);

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xx * x, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(x) // A_I
                .chain(iter::once(xx)) // A_O
                .chain(iter::once(x)) // W_L_point
                .chain(iter::once(x)) // W_R_point
                .chain(iter::once(Scalar::one())) // W_O_point
                .chain(iter::once(x * xx)) // S
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * (delta + z_zQ_c) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g) // G
                .chain(h) // H
                .chain(x_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(x_inv_sq.iter().cloned()) // ipp_proof.R_vec
                .chain(V_coeff) // V
                .chain(T_scalars.iter().cloned()), // T_points
            iter::once(proof.A_I.decompress())
                .chain(iter::once(proof.A_O.decompress()))
                .chain(iter::once(Some(W_L_point)))
                .chain(iter::once(Some(W_R_point)))
                .chain(iter::once(Some(W_O_point)))
                .chain(iter::once(proof.S.decompress()))
                .chain(iter::once(Some(gens.pedersen_gens.B)))
                .chain(iter::once(Some(gens.pedersen_gens.B_blinding)))
                .chain(gens.G(n).map(|&G_i| Some(G_i)))
                .chain(gens.H(n).map(|&H_i| Some(H_i)))
                .chain(proof.ipp_proof.L_vec.iter().map(|L_i| L_i.decompress()))
                .chain(proof.ipp_proof.R_vec.iter().map(|R_i| R_i.decompress()))
                .chain(self.V.iter().map(|V_i| V_i.decompress()))
                .chain(T_points.iter().map(|T_i| T_i.decompress())),
        ).ok_or_else(|| R1CSError::VerificationError)?;

        use curve25519_dalek::traits::IsIdentity;

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}
