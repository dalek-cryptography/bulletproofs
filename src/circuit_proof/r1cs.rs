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
    aL_assignment: Vec<Result<Scalar, R1CSError>>,
    aR_assignment: Vec<Result<Scalar, R1CSError>>,
    aO_assignment: Vec<Result<Scalar, R1CSError>>,
    v_assignment: Vec<Result<Scalar, R1CSError>>,
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

    // Allocate and do value assignment for aL, aR, aO.
    // Prover uses this function.
    pub fn assign_a(
        &mut self,
        aL_val: Scalar,
        aR_val: Scalar,
        aO_val: Scalar,
    ) -> (Variable, Variable, Variable) {
        let aL_var = self.make_variable(VariableType::aL, Ok(aL_val));
        let aR_var = self.make_variable(VariableType::aR, Ok(aR_val));
        let aO_var = self.make_variable(VariableType::aO, Ok(aO_val));
        (aL_var, aR_var, aO_var)
    }

    // Allocate and do value assignment for v.
    // Prover uses this function.
    pub fn assign_v(&mut self, v_val: Scalar) -> Variable {
        self.make_variable(VariableType::v, Ok(v_val))
    }

    // Allocate a variable with an Err value for aL, aR, aO.
    // Verifier uses this function.
    pub fn allocate_a(&mut self) -> (Variable, Variable, Variable) {
        let aL = self.make_variable(VariableType::aL, Err(R1CSError::InvalidVariableAssignment));
        let aR = self.make_variable(VariableType::aR, Err(R1CSError::InvalidVariableAssignment));
        let aO = self.make_variable(VariableType::aO, Err(R1CSError::InvalidVariableAssignment));
        (aL, aR, aO)
    }

    // Allocate a variable with an Err value for v.
    // Verifier uses this function.
    pub fn allocate_v(&mut self) -> Variable {
        self.make_variable(VariableType::v, Err(R1CSError::InvalidVariableAssignment))
    }

    fn make_variable(
        &mut self,
        var_type: VariableType,
        value: Result<Scalar, R1CSError>,
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
        if v_blinding.len() != self.v_assignment.len() {
            return Err(R1CSError::IncorrectInputSize);
        }
        self.v_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| Ok(pedersen_gens.commit((v_i.clone())?, *v_blinding_i)))
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
            .cloned()
            .collect::<Result<Vec<_>, _>>()?;
        let aR = self
            .aR_assignment
            .iter()
            .cloned()
            .collect::<Result<Vec<_>, _>>()?;
        let aO = self
            .aO_assignment
            .iter()
            .cloned()
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
                    VariableType::aL => W_L[index][var.index] = coeff,
                    VariableType::aR => W_R[index][var.index] = coeff,
                    VariableType::aO => W_O[index][var.index] = coeff,
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
    ) -> (Circuit, Result<ProverInput, R1CSError>, Result<VerifierInput, R1CSError>) {
        // If `n`, the number of multiplications, is not 0 or 2, then pad the circuit.
        let n = self.get_n();
        if !(n == 0 || n.is_power_of_two()) {
            let pad = n.next_power_of_two() - n;
            for _ in 0..pad {
                self.assign_a(Scalar::zero(), Scalar::zero(), Scalar::zero());
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
    ) {
        let mut rng = OsRng::new().unwrap();
        let pedersen_gens = PedersenGenerators::default();
        let generators = Generators::new(pedersen_gens, prover_cs.get_n(), 1);

        let (prover_circuit, prover_input, _) =
            prover_cs.create_proof_input(&pedersen_gens, &mut rng);

        let mut prover_transcript = ProofTranscript::new(b"CircuitProofTest");
        let circuit_proof = CircuitProof::prove(
            &generators,
            &mut prover_transcript,
            &mut rng,
            &prover_circuit,
            &prover_input.unwrap(),
        ).unwrap();

        let (verifier_circuit, _, verifier_input) =
            verifier_cs.create_proof_input(&pedersen_gens, &mut rng);

        assert_eq!(prover_circuit, verifier_circuit);

        let mut verifier_transcript = ProofTranscript::new(b"CircuitProofTest");
        let actual_result = circuit_proof.verify(
            &generators,
            &mut verifier_transcript,
            &mut rng,
            &verifier_circuit,
            &verifier_input.unwrap(),
        );

        match expected_result {
            Ok(_) => assert!(actual_result.is_ok()),
            Err(_) => assert!(actual_result.is_err()),
        }
    }

    fn mul_circuit_helper(a: u64, b: u64, c: u64, expected_result: Result<(), ()>) {
        let mut prover_cs = ConstraintSystem::new();
        prover_cs.assign_a(Scalar::from(a), Scalar::from(b), Scalar::from(c));

        let mut verifier_cs = ConstraintSystem::new();
        verifier_cs.allocate_a();

        create_and_verify_helper(prover_cs, verifier_cs, expected_result);
    }

    #[test]
    fn mul_circuit() {
        // 3 * 4 = 12
        mul_circuit_helper(3, 4, 12, Ok(()));
        // 3 * 4 != 10
        mul_circuit_helper(3, 4, 10, Err(()));
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
