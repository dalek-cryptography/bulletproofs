use curve25519_dalek::scalar::Scalar;

use errors::R1CSError;

use super::assignment::{Assignment, AssignmentValue};
use super::linear_combination as lc;
use super::linear_combination::LinearCombination;
use super::opaque_scalar::OpaqueScalar;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub enum VariableIndex {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
}

/// Represents a variable in the constraint system.
/// Each variable is identified by its index (`VariableIndex`) and
/// has an assignment which can be present of missing.
#[derive(Copy,Clone,Debug)]
pub struct Variable<S: AssignmentValue> {
    pub index: VariableIndex,
    pub assignment: Assignment<S>,
}

/// Constraint is a linear combination over variable indices with opaque scalars to accomodate
/// both opaque and non-opaque combinations
pub type Constraint = LinearCombination<VariableIndex>;

/// `ConstraintSystem` trait represents the API for the gadgets.
/// Gadgets receive a mutable instance of the constraint system and use it
/// to allocate variables and create constraints between them.
pub trait ConstraintSystem {
    /// Type of the constraint system in the committed state.
    type CommittedCS: CommittedConstraintSystem;

    /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier<S: AssignmentValue + Into<OpaqueScalar>>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError>;

    /// Allocate two uncommitted variables, and assign them the Assignments passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_uncommitted<S: AssignmentValue + Into<OpaqueScalar>>(
        &mut self,
        a: Assignment<S>,
        b: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>), R1CSError> {
        let (left, right, _) = self.assign_multiplier(a, b, a * b)?;
        Ok((left, right))
    }

    /// Enforce that the given linear combination in the constraint is zero.
    fn add_constraint(&mut self, constraint: Constraint);

    /// Adds a callback for when the constraint system’s free variables are committed.
    /// If the CS is not yet committed, the call returns `Ok()`. 
    /// If the CS is already committed, the callback is invoked immediately
    /// with the result forwarded to the caller.
    fn after_commitment<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        for<'t> F: 'static + Fn(&'t mut Self::CommittedCS) -> Result<(), R1CSError>;
}

pub trait CommittedConstraintSystem: ConstraintSystem {
    /// Obtain a challenge scalar bound to the assignments of all of
    /// the externally committed wires.
    ///
    /// This allows the prover to select a challenge circuit from a
    /// family of circuits parameterized by challenge scalars.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> OpaqueScalar;
}



// Trait implementations for concrete types used in the constraint system
// ----------------------------------------------------------------------


impl AssignmentValue for OpaqueScalar {
    fn invert(&self) -> Self {
        Scalar::invert(&self.internal_scalar).into()
    }
}

impl AssignmentValue for Scalar {
    fn invert(&self) -> Self {
        Scalar::invert(self)
    }
}

/// Variable can be made opaque.
impl From<Variable<Scalar>> for Variable<OpaqueScalar> {
    fn from(v: Variable<Scalar>) -> Self {
        Variable {
            index: v.index,
            assignment: v.assignment.into(),
        }
    }
}

/// Assignment can be made opaque.
impl From<Assignment<Scalar>> for Assignment<OpaqueScalar> {
    fn from(a: Assignment<Scalar>) -> Self {
        match a {
            Assignment::Value(a) => Assignment::Value(a.into()),
            Assignment::Missing() => Assignment::Missing(),
        }
    }
}

// Any linear combination of variables with opaque or non-opaque scalars can be converted to a Constraint
// (which does not hold the assignments and contains only the opaque scalars for uniform representation inside CS)
impl<T> From<LinearCombination<Variable<T>>> for Constraint
where
    T: lc::Value + Into<OpaqueScalar>,
{
    fn from(lc: LinearCombination<Variable<T>>) -> Constraint {
        Constraint {
            precomputed: match lc.eval() {
                Assignment::Value(v) => Assignment::Value(v.into()),
                Assignment::Missing() => Assignment::Missing(),
            },
            terms: lc
                .terms
                .into_iter()
                .map(|(v, s)| (v.index, s.into()))
                .collect(),
        }
    }
}

// Linear combinations can be made over `(VariableIndex | Assignment | Variable)`
// with `Scalar` or `OpaqueScalar` as valid weights.
impl lc::Value for OpaqueScalar {
    fn one() -> Self {
        Scalar::one().into()
    }
    fn zero() -> Self {
        Scalar::zero().into()
    }
}

impl lc::Value for Scalar {
    fn one() -> Self {
        Scalar::one()
    }
    fn zero() -> Self {
        Scalar::zero()
    }
}

impl lc::Variable for VariableIndex {
    // Using OpaqueScalar for the Constraint to have opaque weights
    type ValueType = OpaqueScalar;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        Assignment::Missing()
    }

    fn constant_one() -> Self {
        VariableIndex::One()
    }
}

impl<S: lc::Value> lc::Variable for Assignment<S> {
    type ValueType = S;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        self.clone()
    }

    fn constant_one() -> Self {
        Assignment::Value(S::one())
    }
}

impl<S: lc::Value> lc::Variable for Variable<S> {
    type ValueType = S;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        self.assignment
    }

    fn constant_one() -> Self {
        Variable {
            index: VariableIndex::One(),
            assignment: Assignment::Value(S::one()),
        }
    }
}
