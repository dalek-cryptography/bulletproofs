#![allow(non_snake_case)]

use curve25519_dalek::scalar::Scalar;

use super::assignment::Assignment;

use errors::R1CSError;

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
    // XXX fix privacy
    pub variables: Vec<(Variable, Scalar)>,
    pub constant: Scalar,
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
}

pub trait ConstraintSystem {
    // Allocate variables for left, right, and output wires of multiplication,
    // and assign them the Assignments that are passed in.
    // Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier(
        &mut self,
        left: Assignment,
        right: Assignment,
        out: Assignment,
    ) -> Result<(Variable, Variable, Variable), R1CSError>;

    // Allocate two uncommitted variables, and assign them the Assignments passed in.
    // Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_uncommitted(
        &mut self,
        val_1: Assignment,
        val_2: Assignment,
    ) -> Result<(Variable, Variable), R1CSError>;

    fn add_constraint(&mut self, lc: LinearCombination);

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}
