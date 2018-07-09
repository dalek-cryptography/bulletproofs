use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::RistrettoPoint;
use std::iter::FromIterator;

use circuit_proof::{Circuit, CircuitInput};

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
	pub fn get_variables(&self) -> Vec<Variable> {
		self.variables.iter().map(|(var, _)| var.clone()).collect()
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
		self.check_lc(&lc_a)?;
		self.check_lc(&lc_b)?;
		self.check_lc(&lc_c)?;
		self.a.push(lc_a);
		self.b.push(lc_b);
		self.c.push(lc_c);
		Ok(())
	}

	fn check_lc(&self, lc: &LinearCombination) -> Result<(), &'static str> {
		let vars = lc.get_variables();
		for var in vars {
			let index = var.get_index();
			if index > self.var_assignment.len() - 1 {
				return Err("Invalid variable index");
			}
		}
		Ok(())
	}

	pub fn create_proof_input(&self) -> (Circuit, CircuitInput) {
		// eval a, b, c - to know what values to assign to variables
		
		unimplemented!();
	}
}

#[cfg(test)]
	mod tests {
    use super::*; 

	#[test]
	// trivial case using constant multiplication
    fn mul_circuit_constants() {
    	let mut cs = ConstraintSystem::new();

    	let lc_a = LinearCombination::construct(vec![], Scalar::from_u64(3));
    	let lc_b = LinearCombination::construct(vec![], Scalar::from_u64(4));
    	let lc_c = LinearCombination::construct(vec![], Scalar::from_u64(12));
    	cs.push_lc(lc_a, lc_b, lc_c);

    	let (circuit, circuit_input) = cs.create_proof_input();
    	assert_eq!(circuit.q, 3);
    }

    #[test]
    // multiplication circuit where a, b, c are all (private?) variables
    fn mul_circuit_variables() {
    	let mut cs = ConstraintSystem::new();

    	let var_a = cs.alloc_variable(Scalar::from_u64(3));
    	let var_b = cs.alloc_variable(Scalar::from_u64(4));
    	let var_c = cs.alloc_variable(Scalar::from_u64(12));

    	let lc_a = LinearCombination::construct(vec![(var_a, Scalar::one())], Scalar::zero());
    	let lc_b = LinearCombination::construct(vec![(var_b, Scalar::one())], Scalar::zero());
    	let lc_c = LinearCombination::construct(vec![(var_c, Scalar::one())], Scalar::zero());
		cs.push_lc(lc_a, lc_b, lc_c);

    	let (circuit, circuit_input) = cs.create_proof_input();
    	assert_eq!(circuit.q, 3);
    }
}