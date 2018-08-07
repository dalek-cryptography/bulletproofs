#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use generators::Generators;
use proof_transcript::ProofTranscript;

use std::iter;

use curve25519_dalek::traits::{IsIdentity, MultiscalarMul, VartimeMultiscalarMul};
use inner_product_proof::{inner_product, InnerProductProof};
use util;

#[derive(Clone, Debug)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

// This is a stripped-down version of the Bellman r1cs representation, for the purposes of
// learning / understanding. The eventual goal is to write this as a BulletproofsConstraintSystem
// that implements the Bellman ConstraintSystem trait, so we can use that code/logic.
// (That would require the bellman code to be decoupled from the underlying pairings.)

/// Represents a variable in our constraint system, where the value represents the index.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Variable(usize);

/// Represents a linear combination of some variables multiplied with their scalar coefficients,
/// plus a scalar. E.g. LC = variable[0]*scalar[0] + variable[1]*scalar[1] + scalar
#[derive(Clone, Debug)]
pub struct LinearCombination {
    variables: Vec<(Variable, Scalar)>,
    constant: Scalar,
}

impl LinearCombination {
    // TODO: make constructor with iterators
    // see FromIterator trait - [(a1, v1), (a2, v2)].iter().collect() (pass in the iterator, collect to get LC)
    pub fn new(variables: Vec<(Variable, Scalar)>, constant: Scalar) -> Self {
        LinearCombination {
            variables,
            constant,
        }
    }

    pub fn zero() -> Self {
        LinearCombination {
            variables: vec![],
            constant: Scalar::zero(),
        }
    }

    pub fn get_variables(&self) -> Vec<(Variable, Scalar)> {
        self.variables.clone()
    }

    pub fn get_constant(&self) -> Scalar {
        self.constant.clone()
    }
}

/// Represents a vector of groups of 3 linear combinations, where a * b = c
pub struct ConstraintSystem {
    // a[i] * b[i] = c[i] for all i
    a: Vec<LinearCombination>,
    b: Vec<LinearCombination>,
    c: Vec<LinearCombination>,

    // Assignments of witness variables
    witness_assignment: Vec<Result<Scalar, R1CSError>>,
}

impl ConstraintSystem {
    pub fn new() -> Self {
        ConstraintSystem {
            a: vec![],
            b: vec![],
            c: vec![],
            witness_assignment: vec![],
        }
    }

    // Allocate a variable and do value assignment at the same time
    // Prover uses this function
    pub fn alloc_assign_variable(&mut self, val: Scalar) -> Variable {
        self.witness_assignment.push(Ok(val));
        Variable(self.witness_assignment.len() - 1)
    }

    // Allocate a variable with an Err value
    // Verifier uses this function
    pub fn alloc_variable(&mut self) -> Variable {
        self.witness_assignment
            .push(Err(R1CSError::InvalidVariableAssignment));
        Variable(self.witness_assignment.len() - 1)
    }

    // get number of multiplications
    pub fn get_n(&self) -> usize {
        let n = self.a.len();
        if n == 0 || n.is_power_of_two() {
            return n;
        }
        return n.next_power_of_two();
    }

    pub fn get_m(&self) -> usize {
        self.witness_assignment.len()
    }

    pub fn make_V(
        &self,
        gen: &Generators,
        v_blinding: &Vec<Scalar>,
    ) -> Result<Vec<RistrettoPoint>, R1CSError> {
        if v_blinding.len() != self.witness_assignment.len() {
            return Err(R1CSError::IncorrectInputSize);
        }
        self.witness_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| Ok(gen.pedersen_gens.commit((v_i.clone())?, *v_blinding_i)))
            .collect()
    }

    // Push one set of linear constraints (a, b, c) to the constraint system.
    // Pushing a, b, c together prevents mismatched constraints.
    pub fn constrain(
        &mut self,
        lc_a: LinearCombination,
        lc_b: LinearCombination,
        lc_c: LinearCombination,
    ) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, belong to this constraint system).
        self.a.push(lc_a);
        self.b.push(lc_b);
        self.c.push(lc_c);
    }

    fn eval_lc(&self, lc: &LinearCombination) -> Result<Scalar, R1CSError> {
        let sum_vars = lc
            .variables
            .iter()
            .map(|(var, scalar)| Ok(scalar * self.witness_assignment[var.0].clone()?))
            .sum::<Result<Scalar, R1CSError>>()?;
        Ok(sum_vars + lc.constant)
    }

    // for r1cs -> direct
    fn get_circuit_params(&self) -> (usize, usize, usize, Vec<Scalar>, Vec<Vec<Scalar>>) {
        let n = self.a.len();
        let m = self.witness_assignment.len();
        let q = self.a.len() * 3;

        let zer = Scalar::zero();
        // TODO: create / append to c on the fly instead
        let mut c = vec![zer; q]; // length q vector of constants.
        let mut W_V = vec![vec![zer; m]; q]; // qxm matrix of commitments.
        for (i, lc) in self
            .a
            .iter()
            .chain(self.b.iter())
            .chain(self.c.iter())
            .enumerate()
        {
            for (var, scalar) in lc.get_variables() {
                W_V[i][var.0] = scalar;
            }
            c[i] = lc.get_constant();
        }
        (n, m, q, c, W_V)
    }

    // temporarily copied over from `circuit.rs`, while working out how to get rid of matrices
    // Computes z * z^Q * W, where W is a qx(n or m) matrix and z is a scalar.
    // Input: Qx(n or m) matrix of scalars and scalar z
    // Output: length (n or m) vector of Scalars
    // Note: output_dim parameter is necessary in case W is `qxn` where `q=0`,
    //       such that it is not possible to derive `n` from looking at W.
    pub fn matrix_flatten_temp(
        &self,
        W: &Vec<Vec<Scalar>>,
        z: Scalar,
        output_dim: usize,
    ) -> Vec<Scalar> {
        let mut result = vec![Scalar::zero(); output_dim];
        let mut exp_z = z; // z^n starting at n=1

        for row in 0..W.len() {
            for col in 0..output_dim {
                result[col] += exp_z * W[row][col];
            }
            exp_z = exp_z * z; // z^n -> z^(n+1)
        }
        result
    }

    // Return flattened (rows multiplied by the vector z*z^q) versions of W_L, W_R, W_O
    // Linear constraints are ordered as follows:
    // a[0], a[1], ... b[0], b[1], ... c[0], c[1], ...
    // s.t. W_L || W_R || W_O || c || W_V matrix is in reduced row echelon form
    // Flattening only works if we have a diagonal matrix: naive R1CS -> matrix conversion
    fn get_flattened_matrices(
        &self,
        z: Scalar,
        n: usize,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let mut W_L_flat = vec![Scalar::zero(); n];
        let mut W_R_flat = vec![Scalar::zero(); n];
        let mut W_O_flat = vec![Scalar::zero(); n];

        let z_Q = z * util::exp_iter(z).take(n).last().unwrap(); // TODO: propogate err instead
        let mut z_exp_W_L = z;
        let mut z_exp_W_R = z * z_Q;
        let mut z_exp_W_O = z * z_Q * z_Q;
        for i in 0..n {
            W_L_flat[i] = z_exp_W_L;
            W_R_flat[i] = z_exp_W_R;
            W_O_flat[i] = z_exp_W_O;
            z_exp_W_L = z_exp_W_L * z;
            z_exp_W_R = z_exp_W_R * z;
            z_exp_W_O = z_exp_W_O * z;
        }

        (W_L_flat, W_R_flat, W_O_flat)
    }

    pub fn prove<R: Rng + CryptoRng>(
        mut self,
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        v_blinding: Vec<Scalar>,
    ) -> Result<(R1CSProof, Vec<RistrettoPoint>), R1CSError> {
        // CREATE CIRCUIT PARAMS
        let n_temp = self.a.len();
        if !(n_temp == 0 || n_temp.is_power_of_two()) {
            let pad = n_temp.next_power_of_two() - n_temp;
            self.a.append(&mut vec![LinearCombination::zero(); pad]);
            self.b.append(&mut vec![LinearCombination::zero(); pad]);
            self.c.append(&mut vec![LinearCombination::zero(); pad]);
        }
        let (n, m, q, _c, W_V) = self.get_circuit_params();

        // CREATE PROVER INPUTS
        let a_L = self
            .a
            .iter()
            .map(|lc| Ok(self.eval_lc(&lc)?))
            .collect::<Result<Vec<Scalar>, R1CSError>>()?;
        let a_R = self
            .b
            .iter()
            .map(|lc| Ok(self.eval_lc(&lc)?))
            .collect::<Result<Vec<Scalar>, R1CSError>>()?;
        let a_O = self
            .c
            .iter()
            .map(|lc| Ok(self.eval_lc(&lc)?))
            .collect::<Result<Vec<Scalar>, R1CSError>>()?;

        // CREATE THE PROOF
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        transcript.commit_u64(q as u64);

        let i_blinding = Scalar::random(rng);
        let o_blinding = Scalar::random(rng);
        let s_blinding = Scalar::random(rng);
        let s_L: Vec<Scalar> = (0..n).map(|_| Scalar::random(rng)).collect();
        let s_R: Vec<Scalar> = (0..n).map(|_| Scalar::random(rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding).chain(a_L.iter()).chain(a_R.iter()),
            iter::once(&gen.pedersen_gens.B_blinding)
                .chain(gen.G.iter())
                .chain(gen.H.iter()),
        ).compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding).chain(a_O.iter()),
            iter::once(&gen.pedersen_gens.B_blinding).chain(gen.G.iter()),
        ).compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(&gen.pedersen_gens.B_blinding)
                .chain(gen.G.iter())
                .chain(gen.H.iter()),
        ).compress();

        transcript.commit(A_I.as_bytes());
        transcript.commit(A_O.as_bytes());
        transcript.commit(S.as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        let (W_L_flat, W_R_flat, W_O_flat) = self.get_flattened_matrices(z, n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let mut exp_y_inv = Scalar::one(); // y^-n starting at n=0
        let y_inv = y.invert();

        for i in 0..n {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = a_L[i] + exp_y_inv * W_R_flat[i];
            // l_poly.2 = a_O
            l_poly.2[i] = a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = s_L[i];
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = W_O_flat[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * a_R[i] + W_L_flat[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * s_R[i];

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_y_inv = exp_y_inv * y_inv; // y^-i -> y^-(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

        let t_1_blinding = Scalar::random(rng);
        let t_3_blinding = Scalar::random(rng);
        let t_4_blinding = Scalar::random(rng);
        let t_5_blinding = Scalar::random(rng);
        let t_6_blinding = Scalar::random(rng);

        let T_1 = gen.pedersen_gens.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = gen.pedersen_gens.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = gen.pedersen_gens.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = gen.pedersen_gens.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = gen.pedersen_gens.commit(t_poly.t6, t_6_blinding).compress();

        transcript.commit(T_1.as_bytes());
        transcript.commit(T_3.as_bytes());
        transcript.commit(T_4.as_bytes());
        transcript.commit(T_5.as_bytes());
        transcript.commit(T_6.as_bytes());
        let x = transcript.challenge_scalar();

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = W_V
            .iter()
            .zip(util::exp_iter(z))
            .map(|(W_V_i, exp_z)| z * exp_z * inner_product(&W_V_i, &v_blinding))
            .sum();

        let t_blinding_poly = util::Poly6 {
            t1: t_1_blinding,
            t2: t_2_blinding,
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let l_vec = l_poly.eval(x);
        let r_vec = r_poly.eval(x);
        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        transcript.commit(t_x.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * gen.pedersen_gens.B;

        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            util::exp_iter(y.invert()),
            gen.G.to_vec(),
            gen.H.to_vec(),
            l_vec.clone(),
            r_vec.clone(),
        );

        let V = self
            .witness_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| Ok(gen.pedersen_gens.commit((v_i.clone())?, v_blinding_i)))
            .collect::<Result<Vec<RistrettoPoint>, R1CSError>>()?;

        Ok((
            R1CSProof {
                A_I,
                A_O,
                S,
                T_1,
                T_3,
                T_4,
                T_5,
                T_6,
                t_x,
                t_x_blinding,
                e_blinding,
                ipp_proof,
            },
            V,
        ))
    }

    pub fn verify<R: Rng + CryptoRng>(
        mut self,
        proof: &R1CSProof,
        V: &Vec<RistrettoPoint>,
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    ) -> Result<(), R1CSError> {
        // CREATE CIRCUIT PARAMS
        let n_temp = self.a.len();
        if !(n_temp == 0 || n_temp.is_power_of_two()) {
            let pad = n_temp.next_power_of_two() - n_temp;
            self.a.append(&mut vec![LinearCombination::zero(); pad]);
            self.b.append(&mut vec![LinearCombination::zero(); pad]);
            self.c.append(&mut vec![LinearCombination::zero(); pad]);
        }
        let (n, m, q, c, W_V) = self.get_circuit_params();

        // Linear constraints are ordered as follows:
        // a[0], a[1], ... b[0], b[1], ... c[0], c[1], ...
        // s.t. W_L || W_R || W_O || c || W_V matrix is in reduced row echelon form
        let zer = Scalar::zero();
        let one = Scalar::one();
        let mut W_L = vec![vec![zer; n]; q]; // qxn matrix which corresponds to a.
        let mut W_R = vec![vec![zer; n]; q]; // qxn matrix which corresponds to b.
        let mut W_O = vec![vec![zer; n]; q]; // qxn matrix which corresponds to c.
        for i in 0..n {
            W_L[i][i] = one;
            W_R[i + n][i] = one;
            W_O[i + 2 * n][i] = one;
        }

        if V.len() != m || gen.n != n {
            return Err(R1CSError::IncorrectInputSize);
        }

        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        transcript.commit_u64(q as u64);
        transcript.commit(proof.A_I.as_bytes());
        transcript.commit(proof.A_O.as_bytes());
        transcript.commit(proof.S.as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        transcript.commit(proof.T_1.as_bytes());
        transcript.commit(proof.T_3.as_bytes());
        transcript.commit(proof.T_4.as_bytes());
        transcript.commit(proof.T_5.as_bytes());
        transcript.commit(proof.T_6.as_bytes());
        let x = transcript.challenge_scalar();

        transcript.commit(proof.t_x.as_bytes());
        transcript.commit(proof.t_x_blinding.as_bytes());
        transcript.commit(proof.e_blinding.as_bytes());
        let w = transcript.challenge_scalar();

        let r = Scalar::random(rng);
        let xx = x * x;

        // Decompress points
        let S = proof
            .S
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let A_I = proof
            .A_I
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let A_O = proof
            .A_O
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let T_1 = proof
            .T_1
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let T_3 = proof
            .T_3
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let T_4 = proof
            .T_4
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let T_5 = proof
            .T_5
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;
        let T_6 = proof
            .T_6
            .decompress()
            .ok_or_else(|| R1CSError::InvalidProofPoint)?;

        // Calculate points that represent the matrices
        let H_prime: Vec<RistrettoPoint> = gen
            .H
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(H_i, exp_y_inv)| H_i * exp_y_inv)
            .collect();

        let (W_L_flat, W_R_flat, W_O_flat) = self.get_flattened_matrices(z, n);

        // W_L_point = <h * y^-n , z * z^Q * W_L>, line 81
        let W_L_point = RistrettoPoint::vartime_multiscalar_mul(W_L_flat.clone(), H_prime.iter());

        // W_R_point = <g , y^-n * z * z^Q * W_R>, line 82
        let W_R_flat_yinv: Vec<Scalar> = W_R_flat
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(W_R_right_i, exp_y_inv)| W_R_right_i * exp_y_inv)
            .collect();
        let W_R_point =
            RistrettoPoint::vartime_multiscalar_mul(W_R_flat_yinv.clone(), gen.G.iter());

        // W_O_point = <h * y^-n , z * z^Q * W_O>, line 83
        let W_O_point = RistrettoPoint::vartime_multiscalar_mul(W_O_flat, H_prime.iter());

        // Get IPP variables
        let (x_sq, x_inv_sq, s) = proof.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev().take(n);
        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        // define parameters for P check
        let g = s.iter().take(n).map(|s_i| -a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .map(|(s_i_inv, exp_y_inv)| -exp_y_inv * b * s_i_inv - Scalar::one());

        // define parameters for t check
        let delta = inner_product(&W_R_flat_yinv, &W_L_flat);
        let powers_of_z: Vec<Scalar> = util::exp_iter(z).take(q).collect();
        let z_c = z * inner_product(&powers_of_z, &c);
        let W_V_flatten: Vec<Scalar> = self.matrix_flatten_temp(&W_V, z, m);
        let V_multiplier = W_V_flatten.iter().map(|W_V_i| r * xx * W_V_i);

        // group the T_scalars and T_points together
        let T_scalars = [
            r * x,
            r * xx * x,
            r * xx * xx,
            r * xx * xx * x,
            r * xx * xx * xx,
        ];
        let T_points = [T_1, T_3, T_4, T_5, T_6];

        // Decompress L and R points from inner product proof
        let Ls = proof
            .ipp_proof
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(R1CSError::InvalidProofPoint))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = proof
            .ipp_proof
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(R1CSError::InvalidProofPoint))
            .collect::<Result<Vec<_>, _>>()?;

        let mega_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(x) // A_I
                .chain(iter::once(xx)) // A_O
                .chain(iter::once(x)) // W_L_point
                .chain(iter::once(x)) // W_R_point
                .chain(iter::once(Scalar::one())) // W_O_point
                .chain(iter::once(x * xx)) // S
                .chain(iter::once(w * (proof.t_x - a * b) + r * (xx * (delta + z_c) - proof.t_x))) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g) // G
                .chain(h) // H
                .chain(x_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(x_inv_sq.iter().cloned()) // ipp_proof.R_vec
                .chain(V_multiplier) // V
                .chain(T_scalars.iter().cloned()), // T_points
            iter::once(&A_I)
                .chain(iter::once(&A_O))
                .chain(iter::once(&W_L_point))
                .chain(iter::once(&W_R_point))
                .chain(iter::once(&W_O_point))
                .chain(iter::once(&S))
                .chain(iter::once(&gen.pedersen_gens.B))
                .chain(iter::once(&gen.pedersen_gens.B_blinding))
                .chain(gen.G.iter())
                .chain(gen.H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter())
                .chain(V.iter())
                .chain(T_points.iter()),
        );

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use generators::PedersenGenerators;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        prover_cs: ConstraintSystem,
        verifier_cs: ConstraintSystem,
    ) -> Result<(), R1CSError> {
        let generators = Generators::new(PedersenGenerators::default(), prover_cs.get_n(), 1);
        let mut prover_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        let mut rng = OsRng::new().unwrap();

        let v_blinding: Vec<Scalar> = (0..prover_cs.get_m())
            .map(|_| Scalar::random(&mut rng))
            .collect();

        let (circuit_proof, V) = prover_cs
            .prove(&generators, &mut prover_transcript, &mut rng, v_blinding)
            .unwrap();

        let mut verifier_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        verifier_cs.verify(
            &circuit_proof,
            &V,
            &generators,
            &mut verifier_transcript,
            &mut rng,
        )
    }

    // Trivial case: a(const) * b(const) = c(const)
    // Purpose of this test is to see how a cs with no variables behaves
    fn mul_circuit_constants_helper(a: u64, b: u64, c: u64) -> Result<(), R1CSError> {
        let mut prover_cs = ConstraintSystem::new();
        let lc_a = LinearCombination::new(vec![], Scalar::from(a));
        let lc_b = LinearCombination::new(vec![], Scalar::from(b));
        let lc_c = LinearCombination::new(vec![], Scalar::from(c));
        prover_cs.constrain(lc_a, lc_b, lc_c);

        let mut verifier_cs = ConstraintSystem::new();
        let lc_a = LinearCombination::new(vec![], Scalar::from(a));
        let lc_b = LinearCombination::new(vec![], Scalar::from(b));
        let lc_c = LinearCombination::new(vec![], Scalar::from(c));
        verifier_cs.constrain(lc_a, lc_b, lc_c);

        create_and_verify_helper(prover_cs, verifier_cs)
    }

    #[test]
    fn mul_circuit_constants() {
        // 3 (const) * 4 (const) = 12 (const)
        assert!(mul_circuit_constants_helper(3u64, 4u64, 12u64).is_ok());
        // 3 (const) * 4 (const) != 10 (const)
        assert!(mul_circuit_constants_helper(3u64, 4u64, 10u64).is_err());
    }

    // ( a_v(var) * a_c(const) ) * ( b_v(var) * b_c(const) ) = ( c_v(var) * c_c(const) )
    fn mul_circuit_helper(
        a_v: u64,
        a_c: u64,
        b_v: u64,
        b_c: u64,
        c_v: u64,
        c_c: u64,
    ) -> Result<(), R1CSError> {
        let mut prover_cs = ConstraintSystem::new();
        let var_a = prover_cs.alloc_assign_variable(Scalar::from(a_v));
        let var_b = prover_cs.alloc_assign_variable(Scalar::from(b_v));
        let var_c = prover_cs.alloc_assign_variable(Scalar::from(c_v));
        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from(a_c))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from(b_c))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::from(c_c))], Scalar::zero());
        prover_cs.constrain(lc_a, lc_b, lc_c);

        let mut verifier_cs = ConstraintSystem::new();
        let var_a = verifier_cs.alloc_variable();
        let var_b = verifier_cs.alloc_variable();
        let var_c = verifier_cs.alloc_variable();
        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from(a_c))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from(b_c))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::from(c_c))], Scalar::zero());
        verifier_cs.constrain(lc_a, lc_b, lc_c);

        create_and_verify_helper(prover_cs, verifier_cs)
    }

    #[test]
    fn mul_circuit_variables() {
        // 3 (var) * 4 (var) = 12 (var)
        assert!(mul_circuit_helper(3u64, 1u64, 4u64, 1u64, 12u64, 1u64).is_ok());
        // 3 (var) * 4 (var) != 10 (var)
        assert!(mul_circuit_helper(3u64, 1u64, 4u64, 1u64, 10u64, 1u64).is_err());
    }

    #[test]
    fn mul_circuit_mixed() {
        // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) = 120 (var)
        assert!(mul_circuit_helper(3u64, 2u64, 4u64, 5u64, 120u64, 1u64).is_ok());
        // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) != 121 (var)
        assert!(mul_circuit_helper(3u64, 2u64, 4u64, 5u64, 121u64, 1u64).is_err());
    }

    // a (var) + b (var) + d (const) = c (var)
    fn add_circuit_helper(a: u64, b: u64, c: u64, d: u64) -> Result<(), R1CSError> {
        let mut prover_cs = ConstraintSystem::new();
        let var_a = prover_cs.alloc_assign_variable(Scalar::from(a));
        let var_b = prover_cs.alloc_assign_variable(Scalar::from(b));
        let var_c = prover_cs.alloc_assign_variable(Scalar::from(c));
        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(d),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        prover_cs.constrain(lc_a, lc_b, lc_c);

        let mut verifier_cs = ConstraintSystem::new();
        let var_a = verifier_cs.alloc_variable();
        let var_b = verifier_cs.alloc_variable();
        let var_c = verifier_cs.alloc_variable();
        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(d),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        verifier_cs.constrain(lc_a, lc_b, lc_c);
        create_and_verify_helper(prover_cs, verifier_cs)
    }

    #[test]
    fn add_circuit_variables() {
        // 3 (var) + 4 (var) = 7 (var)
        assert!(add_circuit_helper(3u64, 4u64, 7u64, 0u64).is_ok());
        // 3 (var) + 4 (var) != 10 (var)
        assert!(add_circuit_helper(3u64, 4u64, 10u64, 0u64).is_err());
    }

    #[test]
    fn add_circuit_mixed() {
        // 3 (var) + 4 (var) + 8 (const) = 15 (var)
        assert!(add_circuit_helper(3u64, 4u64, 15u64, 8u64).is_ok());
        // 3 (var) + 4 (var) + 8 (const) != 16 (var)
        assert!(add_circuit_helper(3u64, 4u64, 16u64, 8u64).is_err());
    }

    // ( a_v(var) + a_c(const) ) * ( b_v(var) + b_c(var) ) = c_v(var) + c_c(const)
    fn add_and_multiply_helper(
        a_v: u64,
        a_c: u64,
        b_v: u64,
        b_c: u64,
        c_v: u64,
        c_c: u64,
    ) -> Result<(), R1CSError> {
        let mut prover_cs = ConstraintSystem::new();
        let var_a = prover_cs.alloc_assign_variable(Scalar::from(a_v));
        let var_b = prover_cs.alloc_assign_variable(Scalar::from(b_v));
        let var_c = prover_cs.alloc_assign_variable(Scalar::from(c_v));
        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::from(a_c));
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::from(b_c));
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::from(c_c));
        prover_cs.constrain(lc_a, lc_b, lc_c);

        let mut verifier_cs = ConstraintSystem::new();
        let var_a = verifier_cs.alloc_variable();
        let var_b = verifier_cs.alloc_variable();
        let var_c = verifier_cs.alloc_variable();
        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::from(a_c));
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::from(b_c));
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::from(c_c));
        verifier_cs.constrain(lc_a, lc_b, lc_c);

        create_and_verify_helper(prover_cs, verifier_cs)
    }

    #[test]
    fn add_multiply_mixed() {
        // ( 3(var) + 8(const) ) * ( 5(var) + 2 (const) ) = 1(var) + 76(const)
        assert!(add_and_multiply_helper(3u64, 8u64, 5u64, 2u64, 1u64, 76u64).is_ok());
        // ( 3(var) + 8(const) ) * ( 5(var) + 2 (const) ) != 1(var) + 75(const)
        assert!(add_and_multiply_helper(3u64, 8u64, 5u64, 2u64, 1u64, 75u64).is_err());
    }

    #[test]
    // 3 (const) * 4 (var) = 12 (const)
    // 2 (const) * 5 (var) = 10 (const)
    // 10 (var) * 20 (var) = 200 (const)
    fn n_not_power_of_two() {
        let mut prover_cs = ConstraintSystem::new();

        let var_a = prover_cs.alloc_assign_variable(Scalar::from(4u64));
        let var_b = prover_cs.alloc_assign_variable(Scalar::from(5u64));
        let var_c = prover_cs.alloc_assign_variable(Scalar::from(20u64));

        let lc_a_1 = LinearCombination::new(vec![], Scalar::from(3u64));
        let lc_b_1 = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_c_1 = LinearCombination::new(vec![], Scalar::from(12u64));
        prover_cs.constrain(lc_a_1, lc_b_1, lc_c_1);

        let lc_a_2 = LinearCombination::new(vec![], Scalar::from(2u64));
        let lc_b_2 = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c_2 = LinearCombination::new(vec![], Scalar::from(10u64));
        prover_cs.constrain(lc_a_2, lc_b_2, lc_c_2);

        let lc_a_3 = LinearCombination::new(vec![], Scalar::from(10u64));
        let lc_b_3 = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        let lc_c_3 = LinearCombination::new(vec![], Scalar::from(200u64));
        prover_cs.constrain(lc_a_3, lc_b_3, lc_c_3);

        let mut verifier_cs = ConstraintSystem::new();

        let var_a = verifier_cs.alloc_variable();
        let var_b = verifier_cs.alloc_variable();
        let var_c = verifier_cs.alloc_variable();

        let lc_a_1 = LinearCombination::new(vec![], Scalar::from(3u64));
        let lc_b_1 = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_c_1 = LinearCombination::new(vec![], Scalar::from(12u64));
        verifier_cs.constrain(lc_a_1, lc_b_1, lc_c_1);

        let lc_a_2 = LinearCombination::new(vec![], Scalar::from(2u64));
        let lc_b_2 = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c_2 = LinearCombination::new(vec![], Scalar::from(10u64));
        verifier_cs.constrain(lc_a_2, lc_b_2, lc_c_2);

        let lc_a_3 = LinearCombination::new(vec![], Scalar::from(10u64));
        let lc_b_3 = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        let lc_c_3 = LinearCombination::new(vec![], Scalar::from(200u64));
        verifier_cs.constrain(lc_a_3, lc_b_3, lc_c_3);

        assert!(create_and_verify_helper(prover_cs, verifier_cs).is_ok());
    }
}
