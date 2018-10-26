use curve25519_dalek::scalar::Scalar;

use errors::R1CSError;

use super::assignment::{Assignment,AssignmentValue};
use super::linear_combination::{LinearCombination};
use super::linear_combination as lc;
use super::opaque_scalar::{OpaqueScalar};


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
#[derive(Clone,Debug)]
pub struct Variable<S: AssignmentValue> {
    pub index: VariableIndex,
    pub assignment: Assignment<S>,
}

/// Constraint is a linear combination over variable indices with opaque scalars to accomodate
/// both opaque and non-opaque combinations
pub type Constraint = LinearCombination<VariableIndex>;

pub trait ConstraintSystem {
    type CommittedCS: CommittedConstraintSystem;

    /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier<S: AssignmentValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError>;

    /// Allocate two uncommitted variables, and assign them the Assignments passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_uncommitted<S: AssignmentValue>(
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
    fn after_commitment<F>(&mut self, callback: F) where F: Fn(&mut Self::CommittedCS)->Result<(), R1CSError>;
}

pub trait CommittedConstraintSystem: ConstraintSystem {

    /// Obtain a challenge scalar bound to the assignments of all of
    /// the externally committed wires.
    ///
    /// This allows the prover to select a challenge circuit from a
    /// family of circuits parameterized by challenge scalars.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> OpaqueScalar;
}


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
            assignment: v.assignment.into()
        }
    }
}

/// Assignment can be made opaque.
impl From<Assignment<Scalar>> for Assignment<OpaqueScalar> {
    fn from(a: Assignment<Scalar>) -> Self {
        match a {
            Assignment::Value(a) => Assignment::Value(a.into()),
            Assignment::Missing() => Assignment::Missing()
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
            terms: lc.terms.into_iter().map(|(v,s)| (v.index, s.into()) ).collect(),
            precomputed: match lc.eval() {
                Assignment::Value(v) => Assignment::Value(v.into()),
                Assignment::Missing() => Assignment::Missing()
            }
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


// pub(crate) trait ConstraintSystemDelegate {
//     /// This is called when the assignments are made.
//     /// The prover can add the scalars to the array used to form the vector commitments.
//     fn did_assign_multiplier(
//         &mut self,
//         left: Assignment<Scalar>,
//         right: Assignment<Scalar>,
//         out: Assignment<Scalar>,
//     ) -> Result<(), R1CSError>;
// }

// pub(crate) struct CS<'a, 'b, T> where T: ConstraintSystemDelegate {
//     bp_gens: &'b BulletproofGens,
//     pc_gens: &'b PedersenGens,
//     transcript: &'a mut Transcript,
//     constraints: Vec<Constraint>,
//     variables_count: usize,
//     delegate: T,
//     callbacks: Vec<Box<Fn(&mut CommittedCS<T>)->Result<(), R1CSError>>>
// }

// pub(crate) struct CommittedCS<'a, 'b, T> where T: ConstraintSystemDelegate {
//     cs: CS<'a, 'b, T>,
//     committed_variables_count: usize,
// }

// impl<'a,'b, T> ConstraintSystem for CS<'a,'b, T> {
//     type CommittedCSType = CommittedCS<'a, 'b, T>;

//     fn assign_multiplier<S>(
//         &mut self,
//         left: Assignment<S>,
//         right: Assignment<S>,
//         out: Assignment<S>,
//     ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {

//         // Convert potentially opaque assignments into non-opaque so that the prover can
//         // use raw scalars for the proof computation.
//         let (l,r,o) = match (left,right,out) {
//             (Assignment::Value(l), Assignment::Value(r), Assignment::Value(o)) => {
//                 (
//                     l.into::<OpaqueScalar>().internal_scalar,
//                     r.into::<OpaqueScalar>().internal_scalar,
//                     o.into::<OpaqueScalar>().internal_scalar
//                 )
//             },
//             (_, _, _) => (Assignment::Missing(), Assignment::Missing(), Assignment::Missing()),
//         };
//         self.delegate.did_assign_multiplier(l,r,o);

//         let index = self.variables_count;
//         self.variables_count += 1;

//         Ok((
//             Variable{index: VariableIndex::MultiplierLeft(index), assignment:left},
//             Variable{index: VariableIndex::MultiplierRight(index), assignment:right},
//             Variable{index: VariableIndex::MultiplierOutput(index), assignment:out},
//         ))
//     }

//     /// Enforce that the given `LinearCombination` is zero.
//     fn add_constraint(&mut self, constraint: Constraint) {
//         // TODO: check that the linear combinations are valid
//         // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
//         self.constraints.push(constraint);
//     }

//     /// Adds a callback for when the constraint system’s free variables are committed.
//     fn after_commitment<F: Fn(&mut Self::CommittedCSType)->Result<(), R1CSError>>(&mut self, callback: F) {
//         self.callbacks.push(Box::new(callback));
//     }
// }

// impl<'a,'b, T> CS<'a,'b, T> {
//     fn to_committed(self) -> CommittedCS<'a,'b,T> {
//         CommittedCS {
//             cs: self,
//             committed_variables_count: self.variables_count
//         }
//     }
// }

// impl<'a,'b, T> CommittedCS<'a,'b, T> {
//     fn process_callbacks(&mut self) -> Result<(), R1CSError> {
//         for closure in self.callbacks.drain(..) {
//             closure(self)?
//         }
//     }
// }

// // Implementation of constraint system in the committed state forwards
// // all calls to the underlying storage.
// impl<'a,'b, T> ConstraintSystem for CommittedCS<'a,'b, T> where T: ConstraintSystemDelegate {
//     type CommittedCSType = CommittedCS<'a, 'b, T>;

//     fn assign_multiplier<S>(
//         &mut self,
//         left: Assignment<S>,
//         right: Assignment<S>,
//         out: Assignment<S>,
//     ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {
//         self.cs.assign_multiplier(left, right, out)
//     }

//     /// Enforce that the given `LinearCombination` is zero.
//     fn add_constraint(&mut self, constraint: Constraint) {
//         self.cs.add_constraint(constraint);
//     }

//     /// Adds a callback for when the constraint system’s free variables are committed.
//     fn after_commitment<F: Fn(&mut Self::CommittedCSType)>(&mut self, callback: F) {
//         callback(self)
//     }
// }

// impl<'a,'b, T> CommittedConstraintSystem for CommittedCS<'a,'b, T> where T: ConstraintSystemDelegate {
//     fn challenge_scalar(&mut self, label: &'static [u8]) -> OpaqueScalar {
//         self.cs.transcript.challenge_scalar(label).into()
//     }
// }
