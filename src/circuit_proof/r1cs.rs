#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use std::ops::Try;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{MultiscalarMul, VartimeMultiscalarMul};
use merlin::Transcript;
use rand::{CryptoRng, Rng};

use super::assignment::Assignment;

use errors::R1CSError;
use generators::{Generators, PedersenGenerators};
use inner_product_proof::InnerProductProof;
use transcript::TranscriptProtocol;

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

/// The variables used in the `LinearCombination` and `ConstraintSystem` structs.
#[derive(Copy, Clone, Debug)]
pub enum Variable {
    Committed(usize),        // high-level variable
    MultiplierLeft(usize),   // low-level variable, left input of multiplication gate
    MultiplierRight(usize),  // low-level variable, right input of multiplication gate
    MultiplierOutput(usize), // low-level variable, output multiplication gate
}

/// Represents a linear combination of some variables multiplied with their scalar coefficients,
/// plus a scalar. `ConstraintSystem` expects all linear combinations to evaluate to zero.
/// E.g. LC = variable[0]*scalar[0] + variable[1]*scalar[1] + scalar
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

pub struct ConstraintSystem<'a> {
    transcript: &'a mut Transcript,
    constraints: Vec<LinearCombination>,

    // variable assignments
    aL_assignments: Vec<Assignment>,
    aR_assignments: Vec<Assignment>,
    aO_assignments: Vec<Assignment>,
    v_assignments: Vec<Assignment>,

    /// Holds the blinding factors for the input wires, if used by the
    /// prover.
    v_blinding: Option<Vec<Scalar>>,
    V: Vec<RistrettoPoint>,
}

impl<'a> ConstraintSystem<'a> {
    pub fn prover_new(
        transcript: &'a mut Transcript,
        v: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
        pedersen_gens: PedersenGenerators,
    ) -> (Self, Vec<Variable>, Vec<RistrettoPoint>) {
        // Check that the input lengths are consistent
        assert_eq!(v.len(), v_blinding.len());
        let m = v.len();
        transcript.r1cs_domain_sep(m as u64);

        let mut v_assignments = Vec::with_capacity(m);
        let mut variables = Vec::with_capacity(m);
        let mut commitments = Vec::with_capacity(m);

        for i in 0..m {
            // Generate pedersen commitment and commit it to the transcript
            let V = pedersen_gens.commit(v[i], v_blinding[i]);
            transcript.commit_point(b"V", &V.compress());
            commitments.push(V);

            // Allocate and assign and return a variable for v_i
            v_assignments.push(Assignment::from(v[i]));
            variables.push(Variable::Committed(i));
        }

        let cs = ConstraintSystem {
            transcript,
            constraints: vec![],
            aL_assignments: vec![],
            aR_assignments: vec![],
            aO_assignments: vec![],
            v_assignments,
            v_blinding: Some(v_blinding),
            V: commitments.clone(),
        };

        (cs, variables, commitments)
    }

    pub fn verifier_new(
        transcript: &'a mut Transcript,
        // XXX should these take compressed points?
        commitments: Vec<RistrettoPoint>,
    ) -> (Self, Vec<Variable>) {
        let m = commitments.len();
        transcript.r1cs_domain_sep(m as u64);

        let mut variables = Vec::with_capacity(m);
        for (i, commitment) in commitments.iter().enumerate() {
            // Commit the commitment to the transcript
            transcript.commit_point(b"V", &commitment.compress());

            // Allocate and return a variable for the commitment
            variables.push(Variable::Committed(i));
        }

        let cs = ConstraintSystem {
            transcript,
            constraints: vec![],
            aL_assignments: vec![],
            aR_assignments: vec![],
            aO_assignments: vec![],
            v_assignments: vec![Assignment::Missing(); m],
            v_blinding: None,
            V: commitments,
        };

        (cs, variables)
    }

    // Allocate variables for left, right, and output wires of multiplication,
    // and assign them the Assignments that are passed in.
    // Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    pub fn assign_multiplier(
        &mut self,
        left: Assignment,
        right: Assignment,
        out: Assignment,
    ) -> (Variable, Variable, Variable) {
        self.aL_assignments.push(left);
        let left_var = Variable::MultiplierLeft(self.aL_assignments.len() - 1);

        self.aR_assignments.push(right);
        let right_var = Variable::MultiplierRight(self.aR_assignments.len() - 1);

        self.aO_assignments.push(out);
        let out_var = Variable::MultiplierOutput(self.aO_assignments.len() - 1);

        (left_var, right_var, out_var)
    }

    // Allocate two uncommitted variables, and assign them the Assignments passed in.
    // Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    pub fn assign_uncommitted(
        &mut self,
        val_1: Assignment,
        val_2: Assignment,
    ) -> (Variable, Variable) {
        let val_3 = val_1 * val_2;

        let (left, right, _) = self.assign_multiplier(val_1, val_2, val_3);
        (left, right)
    }

    pub fn commitments_count(&self) -> usize {
        self.v_assignments.len()
    }

    // Returns the number of multiplications in the circuit after the circuit has been
    // padded (such that the number of multiplications is either 0 or a power of two.)
    pub fn multiplications_count(&self) -> usize {
        let n = self.aL_assignments.len();
        if n == 0 || n.is_power_of_two() {
            return n;
        }
        return n.next_power_of_two();
    }

    pub fn add_constraint(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    pub fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }

    /// XXX refactor this
    fn create_circuit_data(
        &mut self,
        z: &Scalar,
    ) -> (
        Vec<Scalar>,
        Vec<Scalar>,
        Vec<Scalar>,
        Vec<Scalar>,
        Vec<Scalar>,
    ) {
        let n = self.aL_assignments.len();
        let m = self.v_assignments.len();
        let q = self.constraints.len();

        let zer = Scalar::zero();
        let mut W_L = vec![vec![zer; n]; q]; // qxn matrix which corresponds to a.
        let mut W_R = vec![vec![zer; n]; q]; // qxn matrix which corresponds to b.
        let mut W_O = vec![vec![zer; n]; q]; // qxn matrix which corresponds to c.
        let mut W_V = vec![vec![zer; m]; q]; // qxm matrix which corresponds to v
        let mut c = vec![zer; q]; // length q vector of constants.

        for (lc_index, lc) in self.constraints.iter().enumerate() {
            for (var, coeff) in lc.variables.clone() {
                match var {
                    Variable::MultiplierLeft(var_index) => W_L[lc_index][var_index] = -coeff,
                    Variable::MultiplierRight(var_index) => W_R[lc_index][var_index] = -coeff,
                    Variable::MultiplierOutput(var_index) => W_O[lc_index][var_index] = -coeff,
                    Variable::Committed(var_index) => W_V[lc_index][var_index] = coeff,
                };
            }
            c[lc_index] = lc.constant
        }

        (
            matrix_flatten(&W_L, z, n).unwrap(),
            matrix_flatten(&W_R, z, n).unwrap(),
            matrix_flatten(&W_O, z, n).unwrap(),
            matrix_flatten(&W_V, z, m).unwrap(),
            c,
        )
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(mut self, gen: &Generators) -> Result<R1CSProof, R1CSError> {
        use std::iter;
        use util;

        // 0. Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let temp_n = self.aL_assignments.len();
        if !(temp_n == 0 || temp_n.is_power_of_two()) {
            let pad = temp_n.next_power_of_two() - temp_n;
            for _ in 0..pad {
                self.assign_multiplier(Assignment::zero(), Assignment::zero(), Assignment::zero());
            }
        }

        let n = self.aL_assignments.len();
        assert_eq!(n, gen.n);

        // 1. Create a `TranscriptRng` from the high-level witness data

        let mut rng = {
            let mut ctor = self.transcript.fork_transcript();

            // Commit the blinding factors for the input wires
            for v_b in self.v_blinding.as_ref().unwrap() {
                ctor = ctor.commit_witness_bytes(b"v_blinding", v_b.as_bytes());
            }

            use rand::thread_rng;
            ctor.reseed_from_rng(&mut thread_rng())
        };

        // 2. Construct the low-level witness data a_L, a_R, a_O

        let a_L = self
            .aL_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;
        let a_R = self
            .aR_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;
        let a_O = self
            .aO_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;

        // 3. Choose blinding factors and form commitments to low-level witness data

        let i_blinding = Scalar::random(&mut rng);
        let o_blinding = Scalar::random(&mut rng);
        let s_blinding = Scalar::random(&mut rng);

        let s_L: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let s_R: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

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

        self.transcript.commit_point(b"A_I", &A_I);
        self.transcript.commit_point(b"A_O", &A_O);
        self.transcript.commit_point(b"S", &S);

        // 4. ???

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        // note: c is not used by the prover -- optimization opportunity?
        let (z_zQ_WL, z_zQ_WR, z_zQ_WO, z_zQ_WV, _c) = self.create_circuit_data(&z);

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let mut exp_y_inv = Scalar::one(); // y^-n starting at n=0
        let y_inv = y.invert();

        for i in 0..n {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = a_L[i] + exp_y_inv * z_zQ_WR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = s_L[i];
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = z_zQ_WO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * a_R[i] + z_zQ_WL[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * s_R[i];

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_y_inv = exp_y_inv * y_inv; // y^-i -> y^-(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

        let t_1_blinding = Scalar::random(&mut rng);
        let t_3_blinding = Scalar::random(&mut rng);
        let t_4_blinding = Scalar::random(&mut rng);
        let t_5_blinding = Scalar::random(&mut rng);
        let t_6_blinding = Scalar::random(&mut rng);

        let pg = &gen.pedersen_gens;

        let T_1 = pg.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = pg.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = pg.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = pg.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = pg.commit(t_poly.t6, t_6_blinding).compress();

        self.transcript.commit_point(b"T_1", &T_1);
        self.transcript.commit_point(b"T_3", &T_3);
        self.transcript.commit_point(b"T_4", &T_4);
        self.transcript.commit_point(b"T_5", &T_5);
        self.transcript.commit_point(b"T_6", &T_6);

        let x = self.transcript.challenge_scalar(b"x");

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = z_zQ_WV
            .iter()
            .zip(self.v_blinding.as_ref().unwrap().iter())
            .map(|(c, v_blinding)| c * v_blinding)
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

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * gen.pedersen_gens.B;

        let ipp_proof = InnerProductProof::create(
            self.transcript,
            &Q,
            util::exp_iter(y.invert()),
            gen.G.to_vec(),
            gen.H.to_vec(),
            l_vec,
            r_vec,
        );

        Ok(R1CSProof {
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
        })
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn verify<R: Rng + CryptoRng>(
        mut self,
        proof: &R1CSProof,
        gen: &Generators,
        rng: &mut R,
    ) -> Result<(), &'static str> {
        let temp_n = self.aL_assignments.len();
        if !(temp_n == 0 || temp_n.is_power_of_two()) {
            let pad = temp_n.next_power_of_two() - temp_n;
            for _ in 0..pad {
                self.assign_multiplier(Assignment::zero(), Assignment::zero(), Assignment::zero());
            }
        }

        use inner_product_proof::inner_product;
        use std::iter;
        use util;

        let n = self.aL_assignments.len();
        assert_eq!(n, gen.n);

        self.transcript.commit_point(b"A_I", &proof.A_I);
        self.transcript.commit_point(b"A_O", &proof.A_O);
        self.transcript.commit_point(b"S", &proof.S);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (z_zQ_WL, z_zQ_WR, z_zQ_WO, z_zQ_WV, c) = self.create_circuit_data(&z);

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

        let r = Scalar::random(rng);
        let xx = x * x;

        // Decompress points
        let S = proof.S.decompress().ok_or_else(|| "Invalid proof point")?;
        let A_I = proof
            .A_I
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let A_O = proof
            .A_O
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let T_1 = proof
            .T_1
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let T_3 = proof
            .T_3
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let T_4 = proof
            .T_4
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let T_5 = proof
            .T_5
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;
        let T_6 = proof
            .T_6
            .decompress()
            .ok_or_else(|| "Invalid proof point")?;

        let y_inv = y.invert();

        // Calculate points that represent the matrices
        let H_prime: Vec<RistrettoPoint> = gen
            .H
            .iter()
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
        let W_R_point = RistrettoPoint::vartime_multiscalar_mul(&y_n_z_zQ_WR, gen.G.iter());

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
        let z_c = z * util::exp_iter(z)
            .zip(c.iter())
            .map(|(a, b)| a * b)
            .sum::<Scalar>();
        let rxx = r * xx;
        let V_coeff = z_zQ_WV.iter().map(|W_V_i| rxx * W_V_i);

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xx * x, rxx * xx * xx];
        let T_points = [T_1, T_3, T_4, T_5, T_6];

        // Decompress L and R points from inner product proof
        let Ls = proof
            .ipp_proof
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or("RangeProof's L point is invalid"))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = proof
            .ipp_proof
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or("RangeProof's R point is invalid"))
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
                .chain(V_coeff) // V
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
                .chain(self.V.iter())
                .chain(T_points.iter()),
        );

        use curve25519_dalek::traits::IsIdentity;

        if !mega_check.is_identity() {
            return Err("Circuit did not verify correctly.");
        }

        Ok(())
    }
}

// Computes z * z^Q * W, where W is a qx(n or m) matrix and z is a scalar.
// Input: Qx(n or m) matrix of scalars and scalar z
// Output: length (n or m) vector of Scalars
// Note: output_dim parameter is necessary in case W is `qxn` where `q=0`,
//       such that it is not possible to derive `n` from looking at W.
pub fn matrix_flatten(
    W: &Vec<Vec<Scalar>>,
    z: &Scalar,
    output_dim: usize,
) -> Result<Vec<Scalar>, &'static str> {
    let mut result = vec![Scalar::zero(); output_dim];
    let mut exp_z = *z; // z^n starting at n=1

    for row in 0..W.len() {
        if W[row].len() != output_dim {
            return Err("Matrix size doesn't match specified parameters in matrix_flatten");
        }
        for col in 0..output_dim {
            result[col] += exp_z * W[row][col];
        }
        exp_z = exp_z * z; // z^n -> z^(n+1)
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        prover_cs: ConstraintSystem,
        verifier_cs: ConstraintSystem,
        expected_result: Result<(), ()>,
    ) -> Result<(), R1CSError> {
        let mut rng = OsRng::new().unwrap();
        let gen = Generators::new(
            PedersenGenerators::default(),
            prover_cs.multiplications_count(),
            1,
        );

        let proof = prover_cs.prove(&gen)?;

        let actual_result = verifier_cs.verify(&proof, &gen, &mut rng);

        match expected_result {
            Ok(_) => assert!(actual_result.is_ok()),
            Err(_) => assert!(actual_result.is_err()),
        }

        Ok(())
    }

    fn blinding_helper(len: usize) -> Vec<Scalar> {
        let mut rng = OsRng::new().unwrap();
        (0..len).map(|_| Scalar::random(&mut rng)).collect()
    }

    // a * b =? c
    // The purpose of this test is to see how a multiplication gate with no
    // variables (no corresponding v commitments) and no linear constraints behaves.
    fn mul_circuit_basic_helper(a: u64, b: u64, c: u64, expected_result: Result<(), ()>) {
        let mut prover_transcript = Transcript::new(b"R1CSProofTest");
        // empty commitments vec because there are no commitments in this test
        let v = vec![];
        let v_blinding = vec![];
        let (mut prover_cs, _prover_committed_variables, commitments) =
            ConstraintSystem::prover_new(
                &mut prover_transcript,
                v,
                v_blinding,
                PedersenGenerators::default(),
            );
        prover_cs.assign_multiplier(
            Assignment::from(a),
            Assignment::from(b),
            Assignment::from(c),
        );

        let mut verifier_transcript = Transcript::new(b"R1CSProofTest");
        let (mut verifier_cs, _verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        verifier_cs.assign_multiplier(
            Assignment::Missing(),
            Assignment::Missing(),
            Assignment::Missing(),
        );

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn mul_circuit_basic() {
        mul_circuit_basic_helper(3, 4, 12, Ok(())); // 3 * 4 = 12
        mul_circuit_basic_helper(3, 4, 10, Err(())); // 3 * 4 != 10
    }

    // (a * a_coeff) * (b * b_coeff) =? c * c_coeff
    // Where we define a, b, c as low-level variables (aL and aR variables) then then
    // tie those to high-level variables (v variables). The purpose of this test is to
    // see if we can successfully tie the low-level and high-level variables together.
    fn mul_circuit_helper(
        a: u64,
        a_coeff: u64,
        b: u64,
        b_coeff: u64,
        c: u64,
        c_coeff: u64,
        expected_result: Result<(), ()>,
    ) {
        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut prover_transcript = Transcript::new(b"R1CSProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding,
            PedersenGenerators::default(),
        );

        let (aL, aR, aO) = prover_cs.assign_multiplier(
            Assignment::from(a * a_coeff),
            Assignment::from(b * b_coeff),
            Assignment::from(c * c_coeff),
        );
        let v_a = prover_committed_variables[0];
        let v_b = prover_committed_variables[1];
        let v_c = prover_committed_variables[2];

        prover_cs.add_constraint(LinearCombination::new(
            vec![(aL, -one), (v_a, Scalar::from(a_coeff))],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aR, -one), (v_b, Scalar::from(b_coeff))],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aO, -one), (v_c, Scalar::from(c_coeff))],
            zer,
        ));

        let mut verifier_transcript = Transcript::new(b"R1CSProofTest");
        let (mut verifier_cs, verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        let (aL, aR, aO) = verifier_cs.assign_multiplier(
            Assignment::Missing(),
            Assignment::Missing(),
            Assignment::Missing(),
        );
        let v_a = verifier_committed_variables[0];
        let v_b = verifier_committed_variables[1];
        let v_c = verifier_committed_variables[2];

        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aL, -one), (v_a, Scalar::from(a_coeff))],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aR, -one), (v_b, Scalar::from(b_coeff))],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aO, -one), (v_c, Scalar::from(c_coeff))],
            zer,
        ));

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn mul_circuit() {
        // test multiplication without coefficients
        mul_circuit_helper(3, 1, 4, 1, 12, 1, Ok(())); // (3*1) * (4*1) = (12*1)
        mul_circuit_helper(3, 1, 4, 1, 10, 1, Err(())); // (3*1) * (4*1) != (10*1)

        // test multiplication with coefficients
        mul_circuit_helper(3, 2, 4, 5, 120, 1, Ok(())); // (3*2) * (4*5) = (120*1)
        mul_circuit_helper(3, 2, 4, 5, 121, 1, Err(())); // (3*2) * (4*5) != (121*1)

        // test multiplication with zeros
        mul_circuit_helper(0, 2, 4, 5, 120, 0, Ok(())); // (0*2) * (4*5) = (120*0)
        mul_circuit_helper(0, 2, 4, 5, 120, 1, Err(())); // (0*2) * (4*5) = (120*1)
    }

    // a + b =? c
    // The purpose of this test is to see how a circuit with no multiplication gates,
    // and one addition gate, behaves.
    fn add_circuit_basic_helper(a: u64, b: u64, c: u64, expected_result: Result<(), ()>) {
        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut prover_transcript = Transcript::new(b"R1CSProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding,
            PedersenGenerators::default(),
        );

        let v_a = prover_committed_variables[0];
        let v_b = prover_committed_variables[1];
        let v_c = prover_committed_variables[2];
        prover_cs.add_constraint(LinearCombination::new(
            vec![(v_a, one), (v_b, one), (v_c, -one)],
            zer,
        ));

        let mut verifier_transcript = Transcript::new(b"R1CSProofTest");
        let (mut verifier_cs, verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        let v_a = verifier_committed_variables[0];
        let v_b = verifier_committed_variables[1];
        let v_c = verifier_committed_variables[2];
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(v_a, one), (v_b, one), (v_c, -one)],
            zer,
        ));

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn add_circuit_basic() {
        add_circuit_basic_helper(3, 4, 7, Ok(())); // 3 + 4 = 7
        add_circuit_basic_helper(3, 4, 10, Err(())); // 3 + 4 != 10
    }

    // a + b =? c
    // Where we define a, b, c as low-level variables (aL and aR variables) then then
    // tie those to high-level variables (v variables). The purpose of this test is to
    // check that low-level variable allocation works, and see that we can successfully
    // tie the low-level and high-level variables together.
    fn add_circuit_helper(a: u64, b: u64, c: u64, expected_result: Result<(), ()>) {
        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut prover_transcript = Transcript::new(b"R1CSProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding,
            PedersenGenerators::default(),
        );
        // Make high-level variables
        let v_a = prover_committed_variables[0];
        let v_b = prover_committed_variables[1];
        let v_c = prover_committed_variables[2];
        // Make low-level variables (aL_0 = v_a, aR_0 = v_b, aL_1 = v_c)
        let (aL_0, aR_0) = prover_cs.assign_uncommitted(Assignment::from(a), Assignment::from(b));
        let (aL_1, _) = prover_cs.assign_uncommitted(Assignment::from(c), Assignment::zero());
        // Tie high-level and low-level variables together
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aL_0.clone(), -one), (v_a, one)],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aR_0.clone(), -one), (v_b, one)],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aL_1.clone(), -one), (v_c, one)],
            zer,
        ));
        // Addition logic (using low-level variables)
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aL_0, one), (aR_0, one), (aL_1, -one)],
            zer,
        ));

        let mut verifier_transcript = Transcript::new(b"R1CSProofTest");
        let (mut verifier_cs, verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        // Make high-level variables
        let v_a = verifier_committed_variables[0];
        let v_b = verifier_committed_variables[1];
        let v_c = verifier_committed_variables[2];
        // Make low-level variables (aL_0 = v_a, aR_0 = v_b, aL_1 = v_c)
        let (aL_0, aR_0) =
            verifier_cs.assign_uncommitted(Assignment::Missing(), Assignment::Missing());
        let (aL_1, _) =
            verifier_cs.assign_uncommitted(Assignment::Missing(), Assignment::Missing());
        // Tie high-level and low-level variables together
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aL_0.clone(), -one), (v_a, one)],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aR_0.clone(), -one), (v_b, one)],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aL_1.clone(), -one), (v_c, one)],
            zer,
        ));
        // Addition logic (using low-level variables)
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aL_0, one), (aR_0, one), (aL_1, -one)],
            zer,
        ));

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn add_circuit() {
        add_circuit_helper(3, 4, 7, Ok(())); // 3 + 4 = 7
        add_circuit_helper(3, 4, 10, Err(())); // 3 + 4 != 10
    }

    // (a1 + a2) * (b1 + b2) =? (c1 + c2)
    // Where a1, a2, b1, b2, c1, c2 are all allocated as high-level variables
    fn mixed_circuit_helper(
        a1: u64,
        a2: u64,
        b1: u64,
        b2: u64,
        c1: u64,
        c2: u64,
        expected_result: Result<(), ()>,
    ) {
        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut prover_transcript = Transcript::new(b"R1CSProofTest");
        let v = vec![
            Scalar::from(a1),
            Scalar::from(a2),
            Scalar::from(b1),
            Scalar::from(b2),
            Scalar::from(c1),
            Scalar::from(c2),
        ];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding,
            PedersenGenerators::default(),
        );
        // Make high-level variables
        let v_a1 = prover_committed_variables[0];
        let v_a2 = prover_committed_variables[1];
        let v_b1 = prover_committed_variables[2];
        let v_b2 = prover_committed_variables[3];
        let v_c1 = prover_committed_variables[4];
        let v_c2 = prover_committed_variables[5];
        // Make low-level variables (aL = v_a1 + v_a2, aR = v_b1 + v_b2, aO = v_c1 + v_c2)
        let (aL, aR, aO) = prover_cs.assign_multiplier(
            Assignment::from(a1 + a2),
            Assignment::from(b1 + b2),
            Assignment::from(c1 + c2),
        );
        // Tie high-level and low-level variables together
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aL, -one), (v_a1, one), (v_a2, one)],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aR, -one), (v_b1, one), (v_b2, one)],
            zer,
        ));
        prover_cs.add_constraint(LinearCombination::new(
            vec![(aO, -one), (v_c1, one), (v_c2, one)],
            zer,
        ));

        let mut verifier_transcript = Transcript::new(b"R1CSProofTest");
        let (mut verifier_cs, verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        // Make high-level variables
        let v_a1 = verifier_committed_variables[0];
        let v_a2 = verifier_committed_variables[1];
        let v_b1 = verifier_committed_variables[2];
        let v_b2 = verifier_committed_variables[3];
        let v_c1 = verifier_committed_variables[4];
        let v_c2 = verifier_committed_variables[5];
        // Make low-level variables (aL = v_a1 + v_a2, aR = v_b1 + v_b2, aO = v_c1 + v_c2)
        let (aL, aR, aO) = verifier_cs.assign_multiplier(
            Assignment::Missing(),
            Assignment::Missing(),
            Assignment::Missing(),
        );
        // Tie high-level and low-level variables together
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aL, -one), (v_a1, one), (v_a2, one)],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aR, -one), (v_b1, one), (v_b2, one)],
            zer,
        ));
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(aO, -one), (v_c1, one), (v_c2, one)],
            zer,
        ));

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn mixed_circuit() {
        mixed_circuit_helper(3, 4, 6, 1, 40, 9, Ok(())); // (3 + 4) * (6 + 1) = (40 + 9)
        mixed_circuit_helper(3, 4, 6, 1, 40, 10, Err(())); // (3 + 4) * (6 + 1) != (40 + 10)
    }
}
