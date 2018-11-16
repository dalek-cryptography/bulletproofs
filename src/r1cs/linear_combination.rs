//! Definition of linear combinations.

use curve25519_dalek::scalar::Scalar;
use std::iter::{self, FromIterator};
use std::ops::{Add, Mul, Sub};

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub enum Variable {
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

impl Add<Variable> for Variable {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> LinearCombination {
        LinearCombination {
            terms: vec![(self, Scalar::one()), (other, Scalar::one())],
        }
    }
}

impl Sub<Variable> for Variable {
    type Output = LinearCombination;

    fn sub(self, other: Variable) -> LinearCombination {
        LinearCombination {
            terms: vec![(self, Scalar::one()), (other, -Scalar::one())],
        }
    }
}

impl Add<Variable> for Scalar {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> LinearCombination {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, Scalar::one())],
        }
    }
}

impl Sub<Variable> for Scalar {
    type Output = LinearCombination;

    fn sub(self, other: Variable) -> LinearCombination {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, -Scalar::one())],
        }
    }
}

impl Mul<Variable> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: Variable) -> LinearCombination {
        LinearCombination {
            terms: vec![(other, self)],
        }
    }
}

impl Add<Scalar> for Variable {
    type Output = LinearCombination;

    fn add(self, other: Scalar) -> LinearCombination {
        LinearCombination {
            terms: vec![(self, Scalar::one()), (Variable::One(), other)],
        }
    }
}

impl Sub<Scalar> for Variable {
    type Output = LinearCombination;

    fn sub(self, other: Scalar) -> LinearCombination {
        LinearCombination {
            terms: vec![(self, Scalar::one()), (Variable::One(), -other)],
        }
    }
}

impl Mul<Scalar> for Variable {
    type Output = LinearCombination;

    fn mul(self, other: Scalar) -> LinearCombination {
        LinearCombination {
            terms: vec![(self, other)],
        }
    }
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug)]
pub struct LinearCombination {
    pub(super) terms: Vec<(Variable, Scalar)>,
}

impl Default for LinearCombination {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl From<Scalar> for LinearCombination {
    fn from(s: Scalar) -> Self {
        iter::once((Variable::One(), s)).collect()
    }
}

impl From<Variable> for LinearCombination {
    fn from(v: Variable) -> Self {
        iter::once((v, Scalar::one())).collect()
    }
}

impl FromIterator<(Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a> FromIterator<&'a (Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

impl Add<LinearCombination> for LinearCombination {
    type Output = Self;

    fn add(mut self, rhs: LinearCombination) -> Self {
        self.terms.extend(rhs.terms.iter().cloned());
        LinearCombination { terms: self.terms }
    }
}

impl Sub<LinearCombination> for LinearCombination {
    type Output = Self;

    fn sub(mut self, rhs: LinearCombination) -> Self {
        self.terms
            .extend(rhs.terms.iter().map(|(var, coeff)| (*var, -coeff)));
        LinearCombination { terms: self.terms }
    }
}

impl Mul<LinearCombination> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: LinearCombination) -> LinearCombination {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        LinearCombination { terms: out_terms }
    }
}

impl Mul<Scalar> for LinearCombination {
    type Output = Self;

    fn mul(self, other: Scalar) -> Self {
        let out_terms = self
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * other))
            .collect();
        LinearCombination { terms: out_terms }
    }
}
