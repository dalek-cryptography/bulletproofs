use rand::{CryptoRng, Rng};

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::RistrettoPoint;
use std::iter::FromIterator;
use generators::PedersenGenerators;

use circuit_proof::{Circuit, ProverInput, VerifierInput};

// This is a stripped-down version of the Bellman r1cs representation, for the purposes of
// learning / understanding. The goal is to write this as a BulletproofsConstraintSystem that 
// implements the Bellman ConstraintSystem trait, so we can use that code/logic.
// (That would require the bellman code to be decoupled from the underlying pairings.)

/// Represents a variable in our constraint system, where the value represents the index.
#[derive(Clone, Debug)]
pub struct Variable(usize);

impl Variable {
	pub fn get_index(&self) -> usize {
		self.0
	}
}

/// Represents a linear combination of some variables multiplied with their scalar coefficients, 
/// plus a scalar. E.g. LC = variable[0]*scalar[0] + variable[1]*scalar[1] + scalar
pub struct LinearCombination {
	variables: Vec<(Variable, Scalar)>,
	constant: Scalar, 
}

impl LinearCombination {
	// TODO: make constructor with iterators
	// see FromIterator trait - [(a1, v1), (a2, v2)].iter().collect() (pass in the iterator, collect to get LC)
	pub fn construct(variables: Vec<(Variable, Scalar)>, constant: Scalar) -> Self {
		LinearCombination {
			variables,
			constant,
		}
	}

	// Used to check that variables in the linear combination are valid
	pub fn check_variables(&self, var_count: usize) -> Result<(), &'static str> {
		for (var, _) in &self.variables {
			let index = var.get_index();
			if index > var_count - 1 {
				return Err("Invalid variable index");
			}
		}
		Ok(())
	}

	pub fn get_variables(&self) -> Vec<(Variable, Scalar)> {
		self.variables.clone()
	}

	pub fn get_constant(&self) -> Scalar {
		self.constant.clone()
	}

	// evaluate the linear combination, given the variable values in var_assignment
	pub fn eval(&self, var_assignment: &Vec<Scalar>) -> Scalar {
		let sum_vars: Scalar = self.variables.iter()
					.map(|(var, scalar)|
						scalar * var_assignment[var.get_index()]
					).sum();
		sum_vars + self.constant
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
		Variable(self.var_assignment.len()-1)
	}

	// Push one set of linear constraints (a, b, c) to the constraint system.
	// Pushing a, b, c together prevents mismatched constraints.
	pub fn push_lc(&mut self, lc_a: LinearCombination, lc_b: LinearCombination, lc_c: LinearCombination)
	-> Result<(), &'static str> {
		let num_vars = self.var_assignment.len();
		lc_a.check_variables(num_vars)?;
		lc_b.check_variables(num_vars)?;
		lc_c.check_variables(num_vars)?;
		self.a.push(lc_a);
		self.b.push(lc_b);
		self.c.push(lc_c);
		Ok(())
	}

	pub fn create_proof_input<R: Rng + CryptoRng>(
		&self,
		pedersen_generators: &PedersenGenerators,
		rng: &mut R,
	) -> (Circuit, ProverInput, VerifierInput) {
		// naive conversion that doesn't do any multiplication elimination
		let n = self.a.len();
		let m = self.var_assignment.len();
		let q = self.a.len() * 3;

		// eval a, b, c and assign results to a_L, a_R, a_O respectively
		let a_L: Vec<Scalar> = 
			self.a.iter().map(|lc| lc.eval(&self.var_assignment)).collect();
		let a_R: Vec<Scalar> = 
			self.b.iter().map(|lc| lc.eval(&self.var_assignment)).collect();
		let a_O: Vec<Scalar> = 
			self.c.iter().map(|lc| lc.eval(&self.var_assignment)).collect();

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
			W_O[i + 2*n][i] = one;
		}

		// TODO: create / append to c on the fly instead
		let mut c = vec![zer; q]; // length q vector of constants.
		let mut W_V = vec![vec![zer; m]; q]; // qxm matrix of commitments.
		for (i, lc) in self.a.iter().chain(self.b.iter()).chain(self.c.iter()).enumerate() {
			for (var, scalar) in lc.get_variables() {
				W_V[i][var.get_index()] = scalar;
			}
			c[i] = lc.get_constant();
		};

        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(rng)).collect();

        let V: Vec<RistrettoPoint> = self
            .var_assignment
            .iter()
            .zip(v_blinding.clone())
            .map(|(v_i, v_blinding_i)| pedersen_generators.commit(*v_i, v_blinding_i))
            .collect();

        let circuit = Circuit {
            n,
            m,
            q,
            c,
            W_L,
            W_R,
            W_O,
            W_V,
        };
        let prover_input = ProverInput { a_L, a_R, a_O, v_blinding };
        let verifier_input = VerifierInput { V };
        (circuit, prover_input, verifier_input)
	}
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_proof::CircuitProof;
    use proof_transcript::ProofTranscript;
    use rand::rngs::OsRng;
    use generators::Generators;

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
	// trivial case using constant multiplication
    fn mul_circuit_constants_succeed() {
    	let mut rng = OsRng::new().unwrap();
    	let pedersen_generators = PedersenGenerators::default();
    	let mut cs = ConstraintSystem::new();

    	let lc_a = LinearCombination::construct(vec![], Scalar::from_u64(3));
    	let lc_b = LinearCombination::construct(vec![], Scalar::from_u64(4));
    	let lc_c = LinearCombination::construct(vec![], Scalar::from_u64(12));
    	cs.push_lc(lc_a, lc_b, lc_c);

    	let (circuit, prover_input, verifier_input) = cs.create_proof_input(&pedersen_generators, &mut rng);
    	assert!(
    		create_and_verify_helper(circuit, prover_input, verifier_input)
    			.is_ok()
    	);
    }

	#[test]
    fn mul_circuit_constants_fail() {
    	let mut rng = OsRng::new().unwrap();
    	let pedersen_generators = PedersenGenerators::default();
    	let mut cs = ConstraintSystem::new();

    	let lc_a = LinearCombination::construct(vec![], Scalar::from_u64(3));
    	let lc_b = LinearCombination::construct(vec![], Scalar::from_u64(4));
    	let lc_c = LinearCombination::construct(vec![], Scalar::from_u64(10));
    	cs.push_lc(lc_a, lc_b, lc_c);

    	let (circuit, prover_input, verifier_input) = cs.create_proof_input(&pedersen_generators, &mut rng);
    	assert!(
    		create_and_verify_helper(circuit, prover_input, verifier_input)
    			.is_err()
    	);
    }

    #[test]
    // multiplication circuit where a, b, c are all variables
    fn mul_circuit_variables_succeed() {
    	let mut rng = OsRng::new().unwrap();
    	let pedersen_generators = PedersenGenerators::default();
    	let mut cs = ConstraintSystem::new();

    	let var_a = cs.alloc_variable(Scalar::from_u64(3));
    	let var_b = cs.alloc_variable(Scalar::from_u64(4));
    	let var_c = cs.alloc_variable(Scalar::from_u64(12));

    	let lc_a = LinearCombination::construct(vec![(var_a, Scalar::one())], Scalar::zero());
    	let lc_b = LinearCombination::construct(vec![(var_b, Scalar::one())], Scalar::zero());
    	let lc_c = LinearCombination::construct(vec![(var_c, Scalar::one())], Scalar::zero());
		cs.push_lc(lc_a, lc_b, lc_c);
		
    	let (circuit, prover_input, verifier_input) = cs.create_proof_input(&pedersen_generators, &mut rng);
    	assert!(
    		create_and_verify_helper(circuit, prover_input, verifier_input)
    			.is_ok()
    	);
    }

    #[test]
    // multiplication circuit where a, b, c are all variables
    fn mul_circuit_variables_fail() {
    	let mut rng = OsRng::new().unwrap();
    	let pedersen_generators = PedersenGenerators::default();
    	let mut cs = ConstraintSystem::new();

    	let var_a = cs.alloc_variable(Scalar::from_u64(3));
    	let var_b = cs.alloc_variable(Scalar::from_u64(4));
    	let var_c = cs.alloc_variable(Scalar::from_u64(10));

    	let lc_a = LinearCombination::construct(vec![(var_a, Scalar::one())], Scalar::zero());
    	let lc_b = LinearCombination::construct(vec![(var_b, Scalar::one())], Scalar::zero());
    	let lc_c = LinearCombination::construct(vec![(var_c, Scalar::one())], Scalar::zero());
		cs.push_lc(lc_a, lc_b, lc_c);
		
    	let (circuit, prover_input, verifier_input) = cs.create_proof_input(&pedersen_generators, &mut rng);
    	assert!(
    		create_and_verify_helper(circuit, prover_input, verifier_input)
    			.is_err()
    	);
    }
}