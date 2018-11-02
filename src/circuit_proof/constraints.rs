use core::ops::{Add, Sub, Mul};

use super::scalar_value::ScalarValue;
use super::assignment::Assignment;
use super::linear_combination as lc;
use super::linear_combination::{LinearCombination,IntoLC};
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
pub struct Variable<S: ScalarValue> {
    /// Index of the variable within the constraint system
    pub index: VariableIndex,

    /// Assignment of the variable within the constraint system.
    /// Assignment is present as a plain or opaque scalar for the prover,
    /// but missing for the verifier.
    pub assignment: Assignment<S>,
}

/// `Constraint` is a `LinearCombination` over variable indices with opaque scalars
/// that is required to equal zero.
/// Create constraints using `equals` method on `LinearCombination`s and `Variable`s.
pub struct Constraint(pub LinearCombination<VariableIndex>);


// Creating linear combinations from variables

/// Adding a linear combination `lc` to a variable `v` creates a combination `v*1 + lc`. 
impl<S,T> Add<T> for Variable<S> where S: ScalarValue, T: IntoLC<Variable<S>> {
    type Output = LinearCombination<Self>;

    fn add(self, lc: T) -> Self::Output {
        let mut lc = lc.into_lc();
        lc.precomputed += self.assignment;
        lc.terms.push((self, S::one()));
        lc
    }
}

/// Subtracting a linear combination `lc` from a variable `v` creates a combination `v*1 - lc`. 
impl<S,T> Sub<T> for Variable<S> where S: ScalarValue, T: IntoLC<Variable<S>> {
    type Output = LinearCombination<Self>;

    fn sub(self, lc: T) -> Self::Output {
        let mut lc = lc.into_lc();
        lc.precomputed = self.assignment - lc.precomputed;
        for (_, ref mut s) in lc.terms.iter_mut() {
            *s = -*s;
        }
        lc.terms.push((self, S::one()));
        lc
    }
}

/// Multiplying a variable `v` by a scalar `a` creates a combination `v*a`.
impl<T,S> Mul<T> for Variable<S> where T: Into<S>, S: ScalarValue {
    type Output = LinearCombination<Self>;

    fn mul(self, scalar: T) -> Self::Output {
        let scalar = scalar.into();
        LinearCombination {
            precomputed: self.assignment * Assignment::Value(scalar),
            terms: vec![(self, scalar)]
        }
    }
}


// Trait implementations for concrete types used in the constraint system
// ----------------------------------------------------------------------

impl<S> Variable<S> where S: ScalarValue {

    /// Creates a `Constraint` that this variable equals the given linear combination.
    pub fn equals<T>(self, lc: T) -> Constraint where T: IntoLC<Variable<S>> {
        (self - lc).into_constraint()
    }

    /// Converts the variable into an opaque one.
    pub fn into_opaque(self) -> Variable<OpaqueScalar> {
        Variable {
            index: self.index,
            assignment: self.assignment.into_opaque()
        }
    }
}

impl<S> LinearCombination<Variable<S>> where S: ScalarValue {

    /// Creates a `Constraint` that this linear combination equals the other linear combination.
    pub fn equals<T>(self, lc: T) -> Constraint where T: IntoLC<Variable<S>> {
        (self - lc.into_lc()).into_constraint()
    }

    // Any linear combination of variables with opaque or non-opaque scalars can be converted to a Constraint
    // (which does not hold the assignments and contains only the opaque scalars for uniform representation inside CS)
    fn into_constraint(self) -> Constraint {
        Constraint(LinearCombination{
            precomputed: match self.eval() {
                Assignment::Value(v) => Assignment::Value(v.into_opaque()),
                Assignment::Missing() => Assignment::Missing(),
            },
            terms: self
                .terms
                .into_iter()
                .map(|(v, s)| (v.index, s.into_opaque()))
                .collect(),
        })
    }
}

impl lc::Variable for VariableIndex {
    // Using OpaqueScalar for the Constraint to have opaque weights
    type ValueType = OpaqueScalar;
    type OpaqueType = VariableIndex;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        Assignment::Missing()
    }

    fn constant_one() -> Self {
        VariableIndex::One()
    }

    fn into_opaque(self) -> Self::OpaqueType {
        self
    }
}

impl<S: ScalarValue> lc::Variable for Variable<S> {
    type ValueType = S;
    type OpaqueType = Variable<OpaqueScalar>;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        self.assignment
    }

    fn constant_one() -> Self {
        Variable {
            index: VariableIndex::One(),
            assignment: Assignment::Value(S::one()),
        }
    }

    fn into_opaque(self) -> Self::OpaqueType {
        Variable::into_opaque(self)
    }
}


