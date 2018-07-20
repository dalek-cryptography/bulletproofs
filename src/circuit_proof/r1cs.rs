use rand::{CryptoRng, Rng};

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use generators::PedersenGenerators;
use std::iter::FromIterator;

use circuit_proof::{Circuit, ProverInput, VerifierInput};

// This is a stripped-down version of the Bellman r1cs representation, for the purposes of
// learning / understanding. The eventual goal is to write this as a BulletproofsConstraintSystem 
// that implements the Bellman ConstraintSystem trait, so we can use that code/logic.
// (That would require the bellman code to be decoupled from the underlying pairings.)

/// Represents a variable in our constraint system, where the value represents the index.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Variable(usize);

/// Represents a linear combination of some variables multiplied with their scalar coefficients,
/// plus a scalar. E.g. LC = variable[0]*scalar[0] + variable[1]*scalar[1] + scalar
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
        let sum_vars: Scalar = 
            lc.variables
            .iter()
            .map(|(var, scalar)| scalar * self.var_assignment[var.0])
            .sum();
        sum_vars + lc.constant        
    }

    fn create_verifier_input (
    	&self,
    	v_blinding: &Vec<Scalar>,
    	pedersen_generators: &PedersenGenerators,
    ) -> VerifierInput {
        let V: Vec<RistrettoPoint> = self
            .var_assignment
            .iter()
            .zip(v_blinding)
            .map(|(v_i, v_blinding_i)| pedersen_generators.commit(*v_i, *v_blinding_i))
            .collect();
        VerifierInput { V }	
    }

    fn create_prover_input(
    	&self,
    	v_blinding: &Vec<Scalar>
    ) -> ProverInput {
        // eval a, b, c and assign results to a_L, a_R, a_O respectively
        let a_L: Vec<Scalar> = self
            .a
            .iter()
            .map(|lc| self.eval_lc(&lc))
            .collect();
        let a_R: Vec<Scalar> = self
            .b
            .iter()
            .map(|lc| self.eval_lc(&lc))
            .collect();
        let a_O: Vec<Scalar> = self
            .c
            .iter()
            .map(|lc| self.eval_lc(&lc))
            .collect();
        ProverInput {
        	a_L,
        	a_R, 
        	a_O,
        	v_blinding: v_blinding.to_vec(),
        }
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

        Circuit {
            n,
            m,
            q,
            c,
            W_L,
            W_R,
            W_O,
            W_V,
        }
    }

    pub fn create_proof_input<R: Rng + CryptoRng>(
        &self,
        pedersen_generators: &PedersenGenerators,
        rng: &mut R,
    ) -> (Circuit, ProverInput, VerifierInput) {
    	let m = self.var_assignment.len();
        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(rng)).collect();

    	let circuit = self.create_circuit();
        let prover_input = self.create_prover_input(&v_blinding);
        let verifier_input = self.create_verifier_input(&v_blinding, pedersen_generators);

        (circuit, prover_input, verifier_input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_proof::CircuitProof;
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
            prover_input.a_L,
            prover_input.a_R,
            prover_input.a_O,
            prover_input.v_blinding,
        ).unwrap();

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest");

        circuit_proof.verify(
            &generators,
            &mut verify_transcript,
            &mut rng,
            &circuit,
            verifier_input.V,
        )
    }

    #[test]
    // 3 (const) * 4 (const) = 12 (const)
    fn mul_circuit_constants_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let lc_a = LinearCombination::new(vec![], Scalar::from_u64(3));
        let lc_b = LinearCombination::new(vec![], Scalar::from_u64(4));
        let lc_c = LinearCombination::new(vec![], Scalar::from_u64(12));
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (const) * 4 (const) != 10 (const)
    fn mul_circuit_constants_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let lc_a = LinearCombination::new(vec![], Scalar::from_u64(3));
        let lc_b = LinearCombination::new(vec![], Scalar::from_u64(4));
        let lc_c = LinearCombination::new(vec![], Scalar::from_u64(10));
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) * 4 (var) = 12 (var)
    fn mul_circuit_variables_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(12));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) * 4 (var) != 10 (var)
    fn mul_circuit_variables_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(10));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::one())], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::one())], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) = 120 (var)
    fn mul_circuit_mixed_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(120));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from_u64(2))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from_u64(5))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // ( 3 (var) * 2 (const) ) * ( 4 (var) * 5 (const) ) != 121 (var)
    fn mul_circuit_mixed_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(121));

        let lc_a = LinearCombination::new(vec![(var_a, Scalar::from_u64(2))], Scalar::zero());
        let lc_b = LinearCombination::new(vec![(var_b, Scalar::from_u64(5))], Scalar::zero());
        let lc_c = LinearCombination::new(vec![(var_c, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) + 4 (var) = 7 (var)
    fn add_circuit_variables_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(7));

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
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) + 4 (var) != 10 (var)
    fn add_circuit_variables_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(10));

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
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // 3 (var) + 4 (var) + 8 (const) = 15 (var)
    fn add_circuit_mixed_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(15));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from_u64(8),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // 3 (var) + 4 (var) + 8 (const) != 16 (var)
    fn add_circuit_mixed_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(16));

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from_u64(8),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::one());
        let lc_c = LinearCombination::new(vec![], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    #[test]
    // ( 3 (var) + 4 (var) + 8 (const) - 13 (var) ) * 2 (const) = 1 (var) * 4 (const)
    fn add_and_multiply_circuit_succeed() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(13));
        let var_d = cs.alloc_variable(Scalar::one());

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from_u64(8),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::from_u64(2));
        let lc_c = LinearCombination::new(vec![(var_d, Scalar::from_u64(4))], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_ok());
    }

    #[test]
    // ( 3 (var) + 4 (var) + 8 (const) - 13 (var) ) * 2 (const) = 1 (var) * 3 (const)
    fn add_and_multiply_circuit_fail() {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
        let mut cs = ConstraintSystem::new();

        let var_a = cs.alloc_variable(Scalar::from_u64(3));
        let var_b = cs.alloc_variable(Scalar::from_u64(4));
        let var_c = cs.alloc_variable(Scalar::from_u64(13));
        let var_d = cs.alloc_variable(Scalar::one());

        let lc_a = LinearCombination::new(
            vec![
                (var_a, Scalar::one()),
                (var_b, Scalar::one()),
                (var_c, -Scalar::one()),
            ],
            Scalar::from_u64(8),
        );
        let lc_b = LinearCombination::new(vec![], Scalar::from_u64(2));
        let lc_c = LinearCombination::new(vec![(var_d, Scalar::from_u64(3))], Scalar::zero());
        assert!(cs.constrain(lc_a, lc_b, lc_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        assert!(create_and_verify_helper(circuit, prover_input, verifier_input).is_err());
    }

    // Creates a 2 in 2 out shuffle circuit.
    fn shuffle_circuit_helper(
        in_0: Scalar,
        in_1: Scalar,
        out_0: Scalar,
        out_1: Scalar,
    ) -> Result<(), &'static str> {
        let mut rng = OsRng::new().unwrap();
        let pedersen_generators = PedersenGenerators::default();
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
        let lc_0_c =
            LinearCombination::new(vec![(var_mul.clone(), Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_0_a, lc_0_b, lc_0_c).is_ok());

        // lc_1: (var_out_0 - z) * (var_out_1 - z) = var_mul
        let lc_1_a = LinearCombination::new(vec![(var_out_0, Scalar::one())], -z);
        let lc_1_b = LinearCombination::new(vec![(var_out_1, Scalar::one())], -z);
        let lc_1_c = LinearCombination::new(vec![(var_mul, Scalar::one())], Scalar::zero());
        assert!(cs.constrain(lc_1_a, lc_1_b, lc_1_c).is_ok());

        let (circuit, prover_input, verifier_input) =
            cs.create_proof_input(&pedersen_generators, &mut rng);
        create_and_verify_helper(circuit, prover_input, verifier_input)
    }

    #[test]
    // Test that a 2 in 2 out shuffle circuit behaves as expected
    fn shuffle_circuit() {
        let three = Scalar::from_u64(3);
        let seven = Scalar::from_u64(7);
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
        let pedersen_generators = PedersenGenerators::default();
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
            cs.create_proof_input(&pedersen_generators, &mut rng);
        create_and_verify_helper(circuit, prover_input, verifier_input)
    }

    #[test]
    fn merge_circuit() {
        let buck = Scalar::from_u64(32);
        let yuan = Scalar::from_u64(86);
        let a = Scalar::from_u64(24);
        let b = Scalar::from_u64(76);
        let a_plus_b = Scalar::from_u64(100);
        let zero = Scalar::zero();

        assert!(merge_circuit_helper(buck, buck, a, a, a, a).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, a_plus_b).is_ok());
        assert!(merge_circuit_helper(buck, yuan, a, b, a, b).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, a, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, yuan, a, b, zero, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, zero).is_err());
    }
}
