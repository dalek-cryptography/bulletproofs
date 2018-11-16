//! Definition of linear combinations.

use curve25519_dalek::scalar::Scalar;
use std::iter::{self, FromIterator};
use std::ops::{Add, Mul, Neg, Sub};

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

/// Trait for types that can be unambiguously converted to a linear combination.
/// Variable is converted to `(var, 1)`, scalar is converted as `(One, scalar)`,
/// tuple `(v,w)` is converted to a single term.
pub trait IntoLinearCombination {
    /// Converts the type into a linear combination
    fn into_lc(self) -> LinearCombination;
}

// Implementation of IntoLinearCombination trait for various types
impl IntoLinearCombination for LinearCombination {
    fn into_lc(self) -> LinearCombination {
        self
    }
}

impl IntoLinearCombination for u64 {
    fn into_lc(self) -> LinearCombination {
        (Variable::One(), self).into_lc()
    }
}

impl IntoLinearCombination for Scalar {
    fn into_lc(self) -> LinearCombination {
        (Variable::One(), self).into_lc()
    }
}

impl IntoLinearCombination for Variable {
    fn into_lc(self) -> LinearCombination {
        (self, 1u64).into_lc()
    }
}

impl<S: Into<Scalar>> IntoLinearCombination for (Variable, S) {
    fn into_lc(self) -> LinearCombination {
        iter::once((self.0, self.1.into())).collect()
    }
}

// Arithmetic on variables produces linear combinations

impl Neg for Variable {
    type Output = LinearCombination;

    fn neg(self) -> Self::Output {
        -self.into_lc()
    }
}

impl<L: IntoLinearCombination> Add<L> for Variable {
    type Output = LinearCombination;

    fn add(self, other: L) -> Self::Output {
        self.into_lc() + other.into_lc()
    }
}

impl<L: IntoLinearCombination> Sub<L> for Variable {
    type Output = LinearCombination;

    fn sub(self, other: L) -> Self::Output {
        self.into_lc() - other.into_lc()
    }
}

impl<S: Into<Scalar>> Mul<S> for Variable {
    type Output = LinearCombination;

    fn mul(self, other: S) -> Self::Output {
        LinearCombination {
            terms: vec![(self, other.into())],
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations

impl Add<Variable> for Scalar {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, Scalar::one())],
        }
    }
}

impl Sub<Variable> for Scalar {
    type Output = LinearCombination;

    fn sub(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, -Scalar::one())],
        }
    }
}

impl Mul<Variable> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: vec![(other, self)],
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

// Arithmetic on linear combinations

impl<L: IntoLinearCombination> Add<L> for LinearCombination {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into_lc().terms.iter().cloned());
        LinearCombination { terms: self.terms }
    }
}

impl<L: IntoLinearCombination> Sub<L> for LinearCombination {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms.extend(
            rhs.into_lc()
                .terms
                .iter()
                .map(|(var, coeff)| (*var, -coeff)),
        );
        LinearCombination { terms: self.terms }
    }
}

impl Mul<LinearCombination> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: LinearCombination) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        LinearCombination { terms: out_terms }
    }
}

impl Neg for LinearCombination {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (v, s) in self.terms.iter_mut() {
            *s = -*s
        }
        self
    }
}

impl<S: Into<Scalar>> Mul<S> for LinearCombination {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (v, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}
