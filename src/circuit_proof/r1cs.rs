#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use generators::{Generators, PedersenGenerators};
use proof_transcript::ProofTranscript;

// use circuit::{Circuit, ProverInput, VerifierInput};
use super::circuit::{Circuit, CircuitProof, ProverInput, VerifierInput};

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

    // Assignments of variables
    var_assignment: Vec<Scalar>,
}

impl ConstraintSystem {
    pub fn new() -> Self {
        ConstraintSystem {
            a: vec![],
            b: vec![],
            c: vec![],
            var_assignment: vec![],
        }
    }
    // Allocate a variable and do value assignment at the same time
    pub fn alloc_variable(&mut self, val: Scalar) -> Variable {
        self.var_assignment.push(val);
        Variable(self.var_assignment.len() - 1)
    }

    // Push one set of linear constraints (a, b, c) to the constraint system.
    // Pushing a, b, c together prevents mismatched constraints.
    pub fn constrain(
        &mut self,
        lc_a: LinearCombination,
        lc_b: LinearCombination,
        lc_c: LinearCombination,
    ) -> Result<(), &'static str> {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, belong to this constraint system).
        self.a.push(lc_a);
        self.b.push(lc_b);
        self.c.push(lc_c);
        Ok(())
    }

    fn eval_lc(&self, lc: &LinearCombination) -> Scalar {
        let sum_vars: Scalar = lc
            .variables
            .iter()
            .map(|(var, scalar)| scalar * self.var_assignment[var.0])
            .sum();
        sum_vars + lc.constant
    }

    fn create_verifier_input(
        &self,
        v_blinding: &Vec<Scalar>,
        pedersen_gens: &PedersenGenerators,
    ) -> VerifierInput {
        let V: Vec<RistrettoPoint> = self
            .var_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| pedersen_gens.commit(*v_i, *v_blinding_i))
            .collect();
        VerifierInput::new(V)
    }

    fn create_prover_input(&self, v_blinding: &Vec<Scalar>) -> ProverInput {
        // eval a, b, c and assign results to a_L, a_R, a_O respectively
        let a_L: Vec<Scalar> = self.a.iter().map(|lc| self.eval_lc(&lc)).collect();
        let a_R: Vec<Scalar> = self.b.iter().map(|lc| self.eval_lc(&lc)).collect();
        let a_O: Vec<Scalar> = self.c.iter().map(|lc| self.eval_lc(&lc)).collect();
        ProverInput::new(a_L, a_R, a_O, v_blinding.to_vec())
    }

    fn create_circuit(&self) -> Circuit {
        let n = self.a.len();
        let m = self.var_assignment.len();
        let q = self.a.len() * 3;

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

        Circuit::new(n, m, q, c, W_L, W_R, W_O, W_V)
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn create_proof_input<R: Rng + CryptoRng>(
        mut self,
        pedersen_gens: &PedersenGenerators,
        rng: &mut R,
    ) -> (Circuit, ProverInput, VerifierInput) {
        // If `n`, the number of multiplications, is not 0 or 2, then pad the circuit.
        let n = self.a.len();
        if !(n == 0 || n.is_power_of_two()) {
            let pad = n.next_power_of_two() - n;
            self.a.append(&mut vec![LinearCombination::zero(); pad]);
            self.b.append(&mut vec![LinearCombination::zero(); pad]);
            self.c.append(&mut vec![LinearCombination::zero(); pad]);
        }

        let m = self.var_assignment.len();
        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(rng)).collect();

        let circuit = self.create_circuit();
        let prover_input = self.create_prover_input(&v_blinding);
        let verifier_input = self.create_verifier_input(&v_blinding, pedersen_gens);

        (circuit, prover_input, verifier_input)
    }

    fn get_flattened_matrices(
        &self,
        z: Scalar,
        n: usize,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), &'static str> {
        use super::circuit::matrix_flatten;
        let q = self.a.len() * 3;

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

        let z_zQ_WL: Vec<Scalar> = matrix_flatten(&W_L, z, n)?;
        let z_zQ_WR: Vec<Scalar> = matrix_flatten(&W_R, z, n)?;
        let z_zQ_WO: Vec<Scalar> = matrix_flatten(&W_O, z, n)?;
        Ok((z_zQ_WL, z_zQ_WR, z_zQ_WO))
    }

    pub fn prove<R: Rng + CryptoRng>(
        mut self,
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    ) -> Result<CircuitProof, &'static str> {
        use std::iter;

        use curve25519_dalek::ristretto::RistrettoPoint;
        use curve25519_dalek::traits::MultiscalarMul;
        use inner_product_proof::{inner_product, InnerProductProof};
        use util;

        // CREATE CIRCUIT PARAMS
        let n_temp = self.a.len();
        if !(n_temp == 0 || n_temp.is_power_of_two()) {
            let pad = n_temp.next_power_of_two() - n_temp;
            self.a.append(&mut vec![LinearCombination::zero(); pad]);
            self.b.append(&mut vec![LinearCombination::zero(); pad]);
            self.c.append(&mut vec![LinearCombination::zero(); pad]);
        }
        let n = self.a.len();
        let m = self.var_assignment.len();
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

        // CREATE PROVER INPUTS
        let a_L: Vec<Scalar> = self.a.iter().map(|lc| self.eval_lc(&lc)).collect();
        let a_R: Vec<Scalar> = self.b.iter().map(|lc| self.eval_lc(&lc)).collect();
        let a_O: Vec<Scalar> = self.c.iter().map(|lc| self.eval_lc(&lc)).collect();
        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(rng)).collect();

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

        let (z_zQ_WL, z_zQ_WR, z_zQ_WO) = self.get_flattened_matrices(z, n)?;

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

        Ok(CircuitProof::new(
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
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::super::circuit::CircuitProof;
    use super::*;
    use generators::Generators;
    use proof_transcript::ProofTranscript;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        circuit: Circuit,
        prover_input: ProverInput,
        verifier_input: VerifierInput,
    ) -> Result<(), &'static str> {
        let generators = Generators::new(PedersenGenerators::default(), circuit.n, 1);
        let mut proof_transcript = ProofTranscript::new(b"CircuitProofTest");
        let mut rng = OsRng::new().unwrap();

        let circuit_proof = CircuitProof::prove(
            &generators,
            &mut proof_transcript,
            &mut rng,
            &circuit.clone(),
            &prover_input,
        ).unwrap();

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest");

        circuit_proof.verify(
            &generators,
            &mut verify_transcript,
            &mut rng,
            &circuit,
            &verifier_input,
        )
    }

    #[test]
    // 3 (const) * 4 (const) = 12 (const)
    fn mul_circuit_constants_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let lc_a = LinearCombination::new(vec![], Scalar::from(3u64));
        let lc_b = LinearCombination::new(vec![], Scalar::from(4u64));
        let lc_c = LinearCombination::new(vec![], Scalar::from(12u64));
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (const) * 4 (const) != 10 (const)
    fn mul_circuit_constants_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let lc_a = LinearCombination::new(vec![], Scalar::from(3u64));
        let lc_b = LinearCombination::new(vec![], Scalar::from(4u64));
        let lc_c = LinearCombination::new(vec![], Scalar::from(10u64));
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) * 4 (var) = 12 (var)
    fn mul_circuit_variables_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(12u64));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) * 4 (var) != 10 (var)
    fn mul_circuit_variables_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(10u64));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) = 120 (var)
    fn mul_circuit_mixed_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(120u64));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from(2u64))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from(5u64))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) != 121 (var)
    fn mul_circuit_mixed_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(121u64));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from(2u64))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from(5u64))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) + 4 (var) = 7 (var)
    fn add_circuit_variables_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(7u64));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::zero(),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) + 4 (var) != 10 (var)
    fn add_circuit_variables_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(10u64));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::zero(),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) + 4 (var) + 8 (const) = 15 (var)
    fn add_circuit_mixed_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(15u64));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(8u64),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) + 4 (var) + 8 (const) != 16 (var)
    fn add_circuit_mixed_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(16u64));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(8u64),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // ( 3 (var) + 4 (var) + 8 (const) - 13 (var) ) * 2 (const) = 1 (var) * 4 (const)
    fn add_and_multiply_circuit_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(13u64));
        let var_d = cs.alloc_variable(Scalar::one());

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(8u64),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::from(2u64));
        let lc_c = LinearCombination::new(vec![(var_d, Scalar::from(4u64))], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // ( 3 (var) + 4 (var) + 8 (const) - 13 (var) ) * 2 (const) = 1 (var) * 3 (const)
    fn add_and_multiply_circuit_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from(3u64));
        let var_b = cs.alloc_variable(Scalar::from(4u64));
        let var_c = cs.alloc_variable(Scalar::from(13u64));
        let var_d = cs.alloc_variable(Scalar::one());

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from(8u64),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::from(2u64));
        let lc_c = LinearCombination::new(vec![(var_d, Scalar::from(3u64))], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (const) * 4 (const) = 12 (const)
    // 2 (const) * 5 (var) = 10 (var)
    // 10 (var) * 20 (var) = 200 (const)
    fn n_not_power_of_two() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_five = cs.alloc_variable(Scalar::from(5u64));
        let var_ten = cs.alloc_variable(Scalar::from(10u64));
        let var_twenty = cs.alloc_variable(Scalar::from(20u64));

        let lc_a_1 = LinearCombination::new(vec![], Scalar::from(3u64));
        let lc_b_1 = LinearCombination::new(vec![], Scalar::from(4u64));
        let lc_c_1 = LinearCombination::new(vec![], Scalar::from(12u64));
        assert!(cs.constrain(lc_a_1, lc_b_1, lc_c_1).is_ok());

        let lc_a_2 = LinearCombination::new(vec![], Scalar::from(2u64));
        let lc_b_2 = LinearCombination::new(vec![(var_five, Scalar::one())], Scalar::zero());
        let lc_c_2 = LinearCombination::new(vec![(var_ten, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a_2, lc_b_2, lc_c_2).is_ok());

        let lc_a_3 = LinearCombination::new(vec![(var_ten, Scalar::one())], Scalar::zero());
        let lc_b_3 = LinearCombination::new(vec![(var_twenty, Scalar::one())], Scalar::zero());
        let lc_c_3 = LinearCombination::new(vec![], Scalar::from(200u64));
        assert!(cs.constrain(lc_a_3, lc_b_3, lc_c_3).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    // Creates a 2 in 2 out shuffle circuit.
    fn shuffle_circuit_helper(
        in_0: Scalar,
        in_1: Scalar,
        out_0: Scalar,
        out_1: Scalar,
    ) -> Result<(), &'static str> {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();
        let z = Scalar::random(&mut rng);

        let var_in_0 = cs.alloc_variable(in_0);
        let var_in_1 = cs.alloc_variable(in_1);
        let var_out_0 = cs.alloc_variable(out_0);
        let var_out_1 = cs.alloc_variable(out_1);
        let var_mul = cs.alloc_variable((in_0 - z) * (in_1 - z));

        // lc_0: (var_in_0 - z) * (var_in_1 - z) = var_mul
        let lc_0_a = LinearCombination::new(vec![(var_in_0, Scalar::one())], -z);
        let lc_0_b = LinearCombination::new(vec![(var_in_1, Scalar::one())], -z);
        let lc_0_c = LinearCombination::new(vec![(var_mul.clone(), Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_0_a, lc_0_b, lc_0_c).is_ok());

        // lc_1: (var_out_0 - z) * (var_out_1 - z) = var_mul
        let lc_1_a = LinearCombination::new(vec![(var_out_0, Scalar::one())], -z);
        let lc_1_b = LinearCombination::new(vec![(var_out_1, Scalar::one())], -z);
        let lc_1_c = LinearCombination::new(vec![(var_mul, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_1_a, lc_1_b, lc_1_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        create_and_verify_helper(circuit, prover_input, verifier_input)
    }

    #[test]
    // Test that a 2 in 2 out shuffle circuit behaves as expected
    fn shuffle_circuit() {
        let three = Scalar::from(3u64);
        let seven = Scalar::from(7u64);
        assert!(shuffle_circuit_helper(three, seven, three, seven).is_ok());
        assert!(shuffle_circuit_helper(three, seven, seven, three).is_ok());
        assert!(shuffle_circuit_helper(three, seven, seven, seven).is_err());
        assert!(shuffle_circuit_helper(three, Scalar::one(), seven, three).is_err());
    }

    // Creates a 2 in 2 out merge circuit.
    // (Is equivalent to a split circuit if you switch inputs and outputs.)
    // Either the assets are unaltered: ￥30 + $42 = ￥30 + $42
    // Or the assets are merged. This is allowed when:
    // the types are the same, the asset values are merged into out_1, and out_0 is zero: $30 + $42 = $0 + $72
    fn merge_circuit_helper(
        type_0: Scalar,
        type_1: Scalar,
        val_in_0: Scalar,
        val_in_1: Scalar,
        val_out_0: Scalar,
        val_out_1: Scalar,
    ) -> Result<(), &'static str> {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();
        let c = Scalar::random(&mut rng);

        let t_0 = cs.alloc_variable(type_0);
        let t_1 = cs.alloc_variable(type_1);
        let in_0 = cs.alloc_variable(val_in_0);
        let in_1 = cs.alloc_variable(val_in_1);
        let out_0 = cs.alloc_variable(val_out_0);
        let out_1 = cs.alloc_variable(val_out_1);

        // lc_a: in_0 * (-1) + in_1 * (-c) + out_0 + out_1 * (c)
        let lc_a = LinearCombination::new(
            vec![
                (in_0.clone(), -Scalar::one()),
                (in_1.clone(), -c),
                (out_0.clone(), Scalar::one()),
                (out_1.clone(), c),
            ],
            Scalar::zero(),
        );
        // lc_b: in_0 + in_1 + out_1 * (-1) + out_0 * (c) + t_0 * (-c*c) + t_1 * (c*c)
        let lc_b = LinearCombination::new(
            vec![
                (in_0, Scalar::one()),
                (in_1, Scalar::one()),
                (out_1, -Scalar::one()),
                (out_0, c),
                (t_0, -c * c),
                (t_1, c * c),
            ],
            Scalar::zero(),
        );
        let lc_c = LinearCombination::new(vec![], Scalar::zero());

        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_gens, &mut rng);
        create_and_verify_helper(circuit, prover_input, verifier_input)
    }

    #[test]
    fn merge_circuit() {
        let buck = Scalar::from(32u64);
        let yuan = Scalar::from(86u64);
        let a = Scalar::from(24u64);
        let b = Scalar::from(76u64);
        let a_plus_b = Scalar::from(100u64);
        let zero = Scalar::zero();

        assert!(merge_circuit_helper(buck, buck, a, a, a, a).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, a_plus_b).is_ok());
        assert!(merge_circuit_helper(buck, yuan, a, b, a, b).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, a, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, yuan, a, b, zero, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, zero).is_err());
    }
}
