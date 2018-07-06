use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::RistrettoPoint;

use circuit_proof::{Circuit, CircuitInput};

// This is a stripped-down version of the Bellman r1cs representation, for the purposes of
// learning / understanding. The goal is to write this as a BulletproofsConstraintSystem that 
// implements the Bellman ConstraintSystem trait, so we can use that code/logic.
// (That would require the bellman code to be decoupled from the underlying pairings.)

/// Represents a variable in our constraint system, where the value represents the index.
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
	pub fn construct(variables: Vec<(Variable, Scalar)>, constant: Scalar) -> Self {
		LinearCombination {
			variables,
			constant,
		}
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
// (?) We also need to keep track of the evals of a, b, c (to know what values to assign to variables?)

impl ConstraintSystem {
	// TODO: make it so you have to request variables from the constraint system,
	// so it does variable allocation and assignment at the same time
	pub fn alloc_variable(&self, val: Scalar) -> Variable {
		unimplemented!();
	}

	pub fn create_proof_input(&self) -> (Circuit, CircuitInput) {
		unimplemented!();
	}
}

#[cfg(test)]
	mod tests {
    use super::*; 

	#[test]
	// trivial case using constant multiplication
    fn mul_circuit_constants() {
    	let lc_a = LinearCombination::construct(vec![], Scalar::from_u64(3));
    	let lc_b = LinearCombination::construct(vec![], Scalar::from_u64(4));
    	let lc_c = LinearCombination::construct(vec![], Scalar::from_u64(12));
    	
    	let cs = ConstraintSystem {
    		a: vec![lc_a], 
    		b: vec![lc_b], 
    		c: vec![lc_c],
    		var_assignment: vec![],
    	};

    	let (circuit, circuit_input) = cs.create_proof_input();
    	assert_eq!(circuit.q, 3);
    }

    #[test]
    // multiplication circuit where a, b, c are all (private?) variables
    fn mul_circuit_variables() {
    	// TODO: use alloc_variable to create the variables instead
    	let var_a = Variable(0);
    	let var_b = Variable(1);
    	let var_c = Variable(2);

    	let lc_a = LinearCombination {
    		variables: vec![(var_a, Scalar::one())],
    		constant: Scalar::zero(),
    	};
    	let lc_b = LinearCombination {
    		variables: vec![(var_b, Scalar::one())],
    		constant: Scalar::zero(),
    	};
    	let lc_c = LinearCombination {
    		variables: vec![(var_c, Scalar::one())],
    		constant: Scalar::zero(),
    	};

    	let cs = ConstraintSystem {
    		a: vec![lc_a], 
    		b: vec![lc_b], 
    		c: vec![lc_c],
    		var_assignment: vec![Scalar::from_u64(3), Scalar::from_u64(4), Scalar::from_u64(12)],
    	};

    	let proof_input = cs.create_proof_input();
    }
}