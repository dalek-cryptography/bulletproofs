#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use rand::{CryptoRng, Rng};

use super::circuit::{Circuit, ProverInput, VerifierInput};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use generators::PedersenGenerators;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum VariableType {
    v,
    aL,
    aR,
    aO,
}

/// Represents a V variable in our constraint system, where the value represents the index.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Variable {
    var_type: VariableType,
    index: usize,
}

#[derive(Clone)]
pub struct Wire(Result<Scalar, R1CSError>);

impl Wire {
    pub fn with_secret(scalar: Scalar) -> Self {
        Wire(Ok(scalar))
    }

    pub fn without_secret() -> Self {
        Wire(Err(R1CSError::InvalidVariableAssignment))
    }
}

/// Represents a linear combination of some variables multiplied with their scalar coefficients,
/// plus a scalar. The linear combination is supposed to evaluate to zero.
/// E.g. LC = 0 = variable[0]*scalar[0] + variable[1]*scalar[1] + scalar
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

pub struct ConstraintSystem {
    lc_vec: Vec<LinearCombination>,

    // variable assignments
    aL_assignment: Vec<Wire>,
    aR_assignment: Vec<Wire>,
    aO_assignment: Vec<Wire>,
    v_assignment: Vec<Wire>,
}

impl ConstraintSystem {
    pub fn new() -> Self {
        ConstraintSystem {
            lc_vec: vec![],
            aL_assignment: vec![],
            aR_assignment: vec![],
            aO_assignment: vec![],
            v_assignment: vec![],
        }
    }

    // Allocate variables for aL, aR, aO, and assign them the Result values that are passed in.
    // Prover will pass in Ok(Scalar)s, and Verifier will pass in R1CSErrors.
    pub fn assign_a(
        &mut self,
        aL_val: Wire,
        aR_val: Wire,
        aO_val: Wire,
    ) -> (Variable, Variable, Variable) {
        let aL_var = self.make_variable(VariableType::aL, aL_val);
        let aR_var = self.make_variable(VariableType::aR, aR_val);
        let aO_var = self.make_variable(VariableType::aO, aO_val);
        (aL_var, aR_var, aO_var)
    }

    // Allocate a variable for v, and assign it the Result value passed in.
    // Prover will pass in Ok(Scalar), and Verifier will pass in R1CSError.
    pub fn assign_v(&mut self, v_val: Wire) -> Variable {
        self.make_variable(VariableType::v, v_val)
    }

    fn make_variable(
        &mut self,
        var_type: VariableType,
        value: Wire,
    ) -> Variable {
        let index = match var_type {
            VariableType::aL => {
                self.aL_assignment.push(value);
                self.aL_assignment.len() - 1
            }
            VariableType::aR => {
                self.aR_assignment.push(value);
                self.aR_assignment.len() - 1
            }
            VariableType::aO => {
                self.aO_assignment.push(value);
                self.aO_assignment.len() - 1
            }
            VariableType::v => {
                self.v_assignment.push(value);
                self.v_assignment.len() - 1
            }
        };
        Variable { var_type, index }
    }

    // Get number of multiplications.
    pub fn get_n(&self) -> usize {
        let n = self.aL_assignment.len();
        if n == 0 || n.is_power_of_two() {
            return n;
        }
        return n.next_power_of_two();
    }

    // Get number of high-level witness variables.
    pub fn get_m(&self) -> usize {
        self.v_assignment.len()
    }

    pub fn make_V(
        &self,
        pedersen_gens: &PedersenGenerators,
        v_blinding: &Vec<Scalar>,
    ) -> Result<Vec<RistrettoPoint>, R1CSError> {
        if v_blinding.len() != self.get_m() {
            return Err(R1CSError::IncorrectInputSize);
        }
        self.v_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| Ok(pedersen_gens.commit(v_i.0.clone()?, *v_blinding_i)))
            .collect()
    }

    pub fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.lc_vec.push(lc);
    }

    fn create_prover_input(&self, v_blinding: &Vec<Scalar>) -> Result<ProverInput, R1CSError> {
        let aL = self
            .aL_assignment
            .iter()
            .map(|aL_i| aL_i.0.clone())
             .collect::<Result<Vec<_>, _>>()?;
        let aR = self
            .aR_assignment
            .iter()
            .map(|aR_i| aR_i.0.clone())
            .collect::<Result<Vec<_>, _>>()?;
        let aO = self
            .aO_assignment
            .iter()
            .map(|aO_i| aO_i.0.clone())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(ProverInput::new(aL, aR, aO, v_blinding.to_vec()))
    }

    fn create_verifier_input(
        &self,
        pedersen_gens: &PedersenGenerators,
        v_blinding: &Vec<Scalar>,
    ) -> Result<VerifierInput, R1CSError> {
        Ok(VerifierInput::new(self.make_V(pedersen_gens, v_blinding)?))
    }

    fn create_circuit(&self) -> Circuit {
        let n = self.get_n();
        let m = self.v_assignment.len();
        let q = self.lc_vec.len();

        let zer = Scalar::zero();
        let mut W_L = vec![vec![zer; n]; q]; // qxn matrix which corresponds to a.
        let mut W_R = vec![vec![zer; n]; q]; // qxn matrix which corresponds to b.
        let mut W_O = vec![vec![zer; n]; q]; // qxn matrix which corresponds to c.
        let mut W_V = vec![vec![zer; m]; q]; // qxm matrix which corresponds to v
        let mut c = vec![zer; q]; // length q vector of constants.

        for (index, lc) in self.lc_vec.iter().enumerate() {
            for (var, coeff) in lc.variables.clone() {
                match var.var_type {
                    VariableType::aL => W_L[index][var.index] = -coeff,
                    VariableType::aR => W_R[index][var.index] = -coeff,
                    VariableType::aO => W_O[index][var.index] = -coeff,
                    VariableType::v => W_V[index][var.index] = coeff,
                };
            }
            c[index] = lc.constant
        }

        Circuit::new(n, m, q, c, W_L, W_R, W_O, W_V)
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn create_proof_input<R: Rng + CryptoRng>(
        mut self,
        pedersen_gens: &PedersenGenerators,
        rng: &mut R,
    ) -> (
        Circuit,
        Result<ProverInput, R1CSError>,
        Result<VerifierInput, R1CSError>,
    ) {
        // If `n`, the number of multiplications, is not 0 or 2, then pad the circuit.
        let n = self.get_n();
        if !(n == 0 || n.is_power_of_two()) {
            let pad = n.next_power_of_two() - n;
            let zer_wire = Wire::with_secret(Scalar::zero());
            for _ in 0..pad {
                self.assign_a(zer_wire.clone(), zer_wire.clone(), zer_wire.clone());
            }
        }
        let m = self.get_m();
        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(rng)).collect();

        let circuit = self.create_circuit();
        let prover_input = self.create_prover_input(&v_blinding);
        let verifier_input = self.create_verifier_input(pedersen_gens, &v_blinding);

        (circuit, prover_input, verifier_input)
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
        prover_cs: ConstraintSystem,
        verifier_cs: ConstraintSystem,
        expected_result: Result<(), ()>,
    ) -> Result<(), R1CSError> {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let generators = Generators::new(pedersen_gens, prover_cs.get_n(), 1);

        let (prover_circuit, prover_input, verifier_input) =
            prover_cs.create_proof_input(&pedersen_gens, &mut rng);

        let mut prover_transcript = ProofTranscript::new(b"CircuitProofTest");
        let circuit_proof = CircuitProof::prove(
            &generators,
            &mut prover_transcript,
            &mut rng,
            &prover_circuit,
            &prover_input?,
        );

        let (verifier_circuit, _, _) = verifier_cs.create_proof_input(&pedersen_gens, &mut rng);

        assert_eq!(prover_circuit, verifier_circuit);

        let mut verifier_transcript = ProofTranscript::new(b"CircuitProofTest");
        let actual_result = circuit_proof.unwrap().verify(
            &generators,
            &mut verifier_transcript,
            &mut rng,
            &verifier_circuit,
            &verifier_input?,
        );

        println!("expected result: {:?}", expected_result);
        println!("actual result: {:?}", actual_result);
        match expected_result {
            Ok(_) => assert!(actual_result.is_ok()),
            Err(_) => assert!(actual_result.is_err()),
        }

        Ok(())
    }

    // a * b =? c
    // The purpose of this test is to see how a multiplication gate with no
    // variables (no corresponding v commitments) and no linear constraints behaves.
    fn mul_circuit_basic_helper(a: u64, b: u64, c: u64, expected_result: Result<(), ()>) {
        let mut prover_cs = ConstraintSystem::new();
        prover_cs.assign_a(
            Wire::with_secret(Scalar::from(a)),
            Wire::with_secret(Scalar::from(b)),
            Wire::with_secret(Scalar::from(c)),
        );

        let mut verifier_cs = ConstraintSystem::new();
        verifier_cs.assign_a(
            Wire::without_secret(),
            Wire::without_secret(),
            Wire::without_secret(),
        );

        assert!(create_and_verify_helper(prover_cs, verifier_cs, expected_result).is_ok());
    }

    #[test]
    fn mul_circuit_basic() {
        mul_circuit_basic_helper(3, 4, 12, Ok(())); // 3 * 4 = 12
        mul_circuit_basic_helper(3, 4, 10, Err(())); // 3 * 4 != 10
    }

    // (a * a_coeff) * (b * b_coeff) =? c * c_coeff
    // Where a, b, c are committed as v_a, v_b, v_c
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

        let mut prover_cs = ConstraintSystem::new();
        let (aL, aR, aO) = prover_cs.assign_a(
            Wire::with_secret(Scalar::from(a) * Scalar::from(a_coeff)),
            Wire::with_secret(Scalar::from(b) * Scalar::from(b_coeff)),
            Wire::with_secret(Scalar::from(c) * Scalar::from(c_coeff)),
        );
        let v_a = prover_cs.assign_v(Wire::with_secret(Scalar::from(a)));
        let v_b = prover_cs.assign_v(Wire::with_secret(Scalar::from(b)));
        let v_c = prover_cs.assign_v(Wire::with_secret(Scalar::from(c)));

        prover_cs.constrain(LinearCombination::new(
            vec![(aL, -one), (v_a, Scalar::from(a_coeff))],
            zer,
        ));
        prover_cs.constrain(LinearCombination::new(
            vec![(aR, -one), (v_b, Scalar::from(b_coeff))],
            zer,
        ));
        prover_cs.constrain(LinearCombination::new(
            vec![(aO, -one), (v_c, Scalar::from(c_coeff))],
            zer,
        ));

        let mut verifier_cs = ConstraintSystem::new();
        let (aL, aR, aO) = verifier_cs.assign_a(
            Wire::without_secret(),
            Wire::without_secret(),
            Wire::without_secret(),
        );
        let v_a = verifier_cs.assign_v(Wire::without_secret());
        let v_b = verifier_cs.assign_v(Wire::without_secret());
        let v_c = verifier_cs.assign_v(Wire::without_secret());

        verifier_cs.constrain(LinearCombination::new(
            vec![(aL, -one), (v_a, Scalar::from(a_coeff))],
            zer,
        ));
        verifier_cs.constrain(LinearCombination::new(
            vec![(aR, -one), (v_b, Scalar::from(b_coeff))],
            zer,
        ));
        verifier_cs.constrain(LinearCombination::new(
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

        let mut prover_cs = ConstraintSystem::new();
        let v_a = prover_cs.assign_v(Wire::with_secret(Scalar::from(a)));
        let v_b = prover_cs.assign_v(Wire::with_secret(Scalar::from(b)));
        let v_c = prover_cs.assign_v(Wire::with_secret(Scalar::from(c)));
        prover_cs.constrain(LinearCombination::new(
            vec![(v_a, one), (v_b, one), (v_c, -one)],
            zer,
        ));

        let mut verifier_cs = ConstraintSystem::new();
        let v_a = verifier_cs.assign_v(Wire::without_secret());
        let v_b = verifier_cs.assign_v(Wire::without_secret());
        let v_c = verifier_cs.assign_v(Wire::without_secret());
        verifier_cs.constrain(LinearCombination::new(
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

}

/*
    fn eval_lc(&self, lc: &LinearCombination) -> Result<Scalar, R1CSError> {
        let sum_vars = lc
            .variables
            .iter()
            .map(|(var, scalar)| Ok(scalar * self.witness_assignment[var.0].clone()?))
            .sum::<Result<Scalar, R1CSError>>()?;
        Ok(sum_vars + lc.constant)
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
*/
