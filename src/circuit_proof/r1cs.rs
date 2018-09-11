#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use rand::{CryptoRng, Rng};

use super::assignment::Assignment;
use super::circuit::{Circuit, CircuitProof, ProverInput, VerifierInput};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use generators::{Generators, PedersenGenerators};
use merlin::Transcript;
use std::ops::Try;
use transcript::TranscriptProtocol;

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
}

impl<'a> ConstraintSystem<'a> {
    pub fn prover_new(
        transcript: &'a mut Transcript,
        v: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
        pedersen_gens: PedersenGenerators,
    ) -> (Self, Vec<Variable>, Vec<RistrettoPoint>) {
        let mut v_assignments = vec![];
        let mut variables = vec![];
        let mut commitments = vec![];

        for (i, (v_i, v_i_blinding)) in v.iter().zip(v_blinding).enumerate() {
            // Generate pedersen commitment and commit it to the transcript
            let V = pedersen_gens.commit(*v_i, v_i_blinding);
            transcript.commit_point(b"Initializing ConstraintSystem", &V.compress());
            commitments.push(V);

            // Allocate and assign and return a variable for v_i
            v_assignments.push(Assignment::from(*v_i));
            variables.push(Variable::Committed(i));
        }

        let cs = ConstraintSystem {
            transcript,
            constraints: vec![],
            aL_assignments: vec![],
            aR_assignments: vec![],
            aO_assignments: vec![],
            v_assignments,
        };

        (cs, variables, commitments)
    }

    pub fn verifier_new(
        transcript: &'a mut Transcript,
        commitments: Vec<RistrettoPoint>,
    ) -> (Self, Vec<Variable>) {
        let mut variables = vec![];
        for (i, commitment) in commitments.iter().enumerate() {
            // Commit the commitment to the transcript
            transcript.commit_point(b"Initializing ConstraintSystem", &commitment.compress());

            // Allocate and return a variable for the commitment
            variables.push(Variable::Committed(i));
        }

        let cs = ConstraintSystem {
            transcript,
            constraints: vec![],
            aL_assignments: vec![],
            aR_assignments: vec![],
            aO_assignments: vec![],
            v_assignments: vec![Assignment::Missing(); commitments.len()],
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

    fn create_prover_input(&self, v_blinding: &Vec<Scalar>) -> Result<ProverInput, R1CSError> {
        let aL = self
            .aL_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;
        let aR = self
            .aR_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;
        let aO = self
            .aO_assignments
            .iter()
            .cloned()
            .map(Try::into_result)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(ProverInput::new(aL, aR, aO, v_blinding.to_vec()))
    }

    fn create_verifier_input(
        &self,
        pedersen_gens: &PedersenGenerators,
        v_blinding: &Vec<Scalar>,
    ) -> Result<VerifierInput, R1CSError> {
        if v_blinding.len() != self.commitments_count() {
            return Err(R1CSError::IncorrectInputSize);
        }
        let V = self
            .v_assignments
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| Ok(pedersen_gens.commit(v_i.clone()?, *v_blinding_i)))
            .collect::<Result<Vec<RistrettoPoint>, R1CSError>>()?;

        Ok(VerifierInput::new(V))
    }

    fn create_circuit(&mut self) -> Circuit {
        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let temp_n = self.aL_assignments.len();
        if !(temp_n == 0 || temp_n.is_power_of_two()) {
            let pad = temp_n.next_power_of_two() - temp_n;
            for _ in 0..pad {
                self.assign_multiplier(Assignment::zero(), Assignment::zero(), Assignment::zero());
            }
        }

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

        Circuit::new(n, m, q, c, W_L, W_R, W_O, W_V)
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn prove<R: Rng + CryptoRng>(
        mut self,
        v_blinding: &Vec<Scalar>,
        gen: &Generators,
        rng: &mut R,
    ) -> Result<(CircuitProof, VerifierInput), R1CSError> {
        if v_blinding.len() != self.commitments_count() {
            return Err(R1CSError::IncorrectInputSize);
        }
        // create circuit params
        let circuit = self.create_circuit();
        let prover_input = self.create_prover_input(&v_blinding)?;
        let verifier_input = self.create_verifier_input(&gen.pedersen_gens, &v_blinding)?;

        let circuit_proof =
            CircuitProof::prove(&gen, &mut self.transcript, rng, &circuit, &prover_input)?;

        Ok((circuit_proof, verifier_input))
    }

    // This function can only be called once per ConstraintSystem instance.
    pub fn verify<R: Rng + CryptoRng>(
        mut self,
        proof: &CircuitProof,
        verifier_input: &VerifierInput,
        gen: &Generators,
        rng: &mut R,
    ) -> Result<(), &'static str> {
        let circuit = self.create_circuit();
        proof.verify(&gen, &mut self.transcript, rng, &circuit, verifier_input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        prover_cs: ConstraintSystem,
        verifier_cs: ConstraintSystem,
        expected_result: Result<(), ()>,
        v_blinding: Vec<Scalar>,
    ) -> Result<(), R1CSError> {
        let mut rng = OsRng::new().unwrap();
        let gen = Generators::new(
            PedersenGenerators::default(),
            prover_cs.multiplications_count(),
            1,
        );

        let (proof, verifier_input) = prover_cs.prove(&v_blinding, &gen, &mut rng)?;
        let actual_result = verifier_cs.verify(&proof, &verifier_input, &gen, &mut rng);

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
        let mut prover_transcript = Transcript::new(b"CircuitProofTest");
        // empty commitments vec because there are no commitments in this test
        let v = vec![];
        let v_blinding = vec![];
        let (mut prover_cs, _prover_committed_variables, commitments) =
            ConstraintSystem::prover_new(
                &mut prover_transcript,
                v,
                v_blinding.clone(),
                PedersenGenerators::default(),
            );
        prover_cs.assign_multiplier(
            Assignment::from(a),
            Assignment::from(b),
            Assignment::from(c),
        );

        let mut verifier_transcript = Transcript::new(b"CircuitProofTest");
        let (mut verifier_cs, _verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        verifier_cs.assign_multiplier(
            Assignment::Missing(),
            Assignment::Missing(),
            Assignment::Missing(),
        );

        assert!(
            create_and_verify_helper(prover_cs, verifier_cs, expected_result, v_blinding).is_ok()
        );
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

        let mut prover_transcript = Transcript::new(b"CircuitProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding.clone(),
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

        let mut verifier_transcript = Transcript::new(b"CircuitProofTest");
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

        assert!(
            create_and_verify_helper(prover_cs, verifier_cs, expected_result, v_blinding).is_ok()
        );
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

        let mut prover_transcript = Transcript::new(b"CircuitProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding.clone(),
            PedersenGenerators::default(),
        );

        let v_a = prover_committed_variables[0];
        let v_b = prover_committed_variables[1];
        let v_c = prover_committed_variables[2];
        prover_cs.add_constraint(LinearCombination::new(
            vec![(v_a, one), (v_b, one), (v_c, -one)],
            zer,
        ));

        let mut verifier_transcript = Transcript::new(b"CircuitProofTest");
        let (mut verifier_cs, verifier_committed_variables) =
            ConstraintSystem::verifier_new(&mut verifier_transcript, commitments);
        let v_a = verifier_committed_variables[0];
        let v_b = verifier_committed_variables[1];
        let v_c = verifier_committed_variables[2];
        verifier_cs.add_constraint(LinearCombination::new(
            vec![(v_a, one), (v_b, one), (v_c, -one)],
            zer,
        ));

        assert!(
            create_and_verify_helper(prover_cs, verifier_cs, expected_result, v_blinding).is_ok()
        );
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

        let mut prover_transcript = Transcript::new(b"CircuitProofTest");
        let v = vec![Scalar::from(a), Scalar::from(b), Scalar::from(c)];
        let v_blinding = blinding_helper(v.len());
        let (mut prover_cs, prover_committed_variables, commitments) = ConstraintSystem::prover_new(
            &mut prover_transcript,
            v,
            v_blinding.clone(),
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

        let mut verifier_transcript = Transcript::new(b"CircuitProofTest");
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

        assert!(
            create_and_verify_helper(prover_cs, verifier_cs, expected_result, v_blinding).is_ok()
        );
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

        let mut prover_transcript = Transcript::new(b"CircuitProofTest");
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
            v_blinding.clone(),
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

        let mut verifier_transcript = Transcript::new(b"CircuitProofTest");
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

        assert!(
            create_and_verify_helper(prover_cs, verifier_cs, expected_result, v_blinding).is_ok()
        );
    }

    #[test]
    fn mixed_circuit() {
        mixed_circuit_helper(3, 4, 6, 1, 40, 9, Ok(())); // (3 + 4) * (6 + 1) = (40 + 9)
        mixed_circuit_helper(3, 4, 6, 1, 40, 10, Err(())); // (3 + 4) * (6 + 1) != (40 + 10)
    }
}
