use core::iter::FromIterator;
use core::ops::{Add, Mul, Sub};

use curve25519_dalek::scalar::Scalar;

use super::assignment::{Assignment};
use super::scalar_value::{ScalarValue};
use super::opaque_scalar::OpaqueScalar;

/// Trait representing a variable in the linear combination
pub trait Variable: Clone {
    type ValueType: ScalarValue;
    type OpaqueType: Variable<ValueType=OpaqueScalar>;

    /// Returns the assignment
    fn assignment(&self) -> Assignment<Self::ValueType>;

    /// Returns the representation of "1" using which the constant terms can be stored
    fn constant_one() -> Self;

    /// Converts the variable to an opaque version
    fn into_opaque(self) -> Self::OpaqueType;
}

/// Trait for types that can be unambiguously converted to a linear combination.
/// Variable is converted to `(var, 1)`, scalar is converted as `(One, scalar)`,
/// tuple `(v,w)` is converted to a single term.
pub trait IntoLC<V> where V: Variable {
    /// Converts the type into a linear combination
    fn into_linear_combination(self) -> LinearCombination<V>;
}

/// Linear combination of variables `V` and scalars `S` allows
/// building a sum of V_i*S_i.
/// The assignment of the variable must have the same type as the weights to simplify the constraints.
/// If one needs to make an LC of a clear assignment with opaque weight,
/// the variable needs to be converted to opaque assignment first using `into_opaque`.
pub struct LinearCombination<V: Variable> {
    /// Terms of the linear combination.
    pub(crate) terms: Vec<(V, V::ValueType)>,

    /// Precomputed evaluation of the linear combination.
    pub(crate) precomputed: Assignment<V::ValueType>,
}


// Implementation of IntoLC trait for various types

impl<V: Variable> IntoLC<V> for LinearCombination<V> {
    fn into_linear_combination(self) -> LinearCombination<V> {
        self
    }
}

impl<V: Variable> IntoLC<V> for Scalar {
    fn into_linear_combination(self) -> LinearCombination<V> {
        LinearCombination {
            terms: vec![(V::constant_one(), self.into())],
            precomputed: Assignment::Value(self.into())
        }
    }
}

impl<V> IntoLC<V> for OpaqueScalar where V: Variable<ValueType=OpaqueScalar> {
    fn into_linear_combination(self) -> LinearCombination<V> {
        LinearCombination {
            terms: vec![(V::constant_one(), self)],
            precomputed: Assignment::Value(self)
        }
    }
}

impl<V> IntoLC<V> for (V, Scalar) where V: Variable, Assignment<V::ValueType>: From<Scalar> {
    fn into_linear_combination(self) -> LinearCombination<V> {
        LinearCombination {
            terms: vec![(self.0, self.1.into())],
            precomputed: self.0.assignment() * self.1
        }
    }
}

impl<V> IntoLC<V> for (V, OpaqueScalar) where V: Variable<ValueType=OpaqueScalar> {
    fn into_linear_combination(self) -> LinearCombination<V> {
        LinearCombination {
            terms: vec![(self.0, self.1)],
            precomputed: self.0.assignment() * self.1
        }
    }
}

impl<V: Variable> LinearCombination<V> {
    /// Evaluates the linear combination expression.
    pub fn eval(&self) -> Assignment<V::ValueType> {
        self.precomputed
    }

    pub fn into_opaque(&self) -> LinearCombination<V::OpaqueType> {
        LinearCombination {
            precomputed: self.precomputed.into_opaque(),
            // XXX: use mem::forget + mem::transmute + Vec::from_raw_parts + packed repr for OpaqueScalar
            // in order to avoid additional allocation here
            terms: self.terms.into_iter()
            .map(|(v, s)| (v.into_opaque(), s.into_opaque()))
            .collect(),
        }
    }
}

/// Empty linear combination
impl<V: Variable> Default for LinearCombination<V> {
    fn default() -> Self {
        LinearCombination {
            terms: Vec::new(),
            precomputed: Assignment::Value(V::ValueType::zero()),
        }
    }
}

/// Arithmetic on linear combinations

impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Add<(V, T)> for LinearCombination<V> {
    type Output = Self;

    fn add(mut self, rhs: (V, T)) -> Self {
        self.precomputed += rhs.0.assignment() * rhs.1.into();
        self.terms.push((rhs.0, rhs.1.into()));
        self
    }
}


// Adding a pair to a linear combination
impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Add<(V, T)> for LinearCombination<V> {
    type Output = Self;

    fn add(mut self, rhs: (V, T)) -> Self {
        self.precomputed += rhs.0.assignment() * rhs.1.into();
        self.terms.push((rhs.0, rhs.1.into()));
        self
    }
}

// Subtracting a pair from a linear combination
impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Sub<(V, T)> for LinearCombination<V> {
    type Output = Self;

    fn sub(mut self, rhs: (V, T)) -> Self {
        self.precomputed -= rhs.0.assignment() * rhs.1.into();
        self.terms.push((rhs.0, -rhs.1.into()));
        self
    }
}

// Adding a constant to a linear combination
impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Add<T> for LinearCombination<V> {
    type Output = Self;

    fn add(mut self, rhs: T) -> Self {
        self.precomputed += rhs.into();
        self.terms.push((V::constant_one(), rhs.into()));
        self
    }
}

// Subtracting a constant from a linear combination
impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Sub<T> for LinearCombination<V> {
    type Output = Self;

    fn sub(mut self, rhs: T) -> Self {
        self.precomputed -= rhs.into();
        self.terms.push((V::constant_one(), -rhs.into()));
        self
    }
}

// Multiplying a linear combination by a constant
impl<V: Variable, T: ScalarValue + Into<V::ValueType>> Mul<T> for LinearCombination<V> {
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self {
        self.precomputed = self.precomputed * rhs.into();
        for (_, ref mut s) in self.terms.iter_mut() {
            *s = *s * rhs.into();
        }
        self
    }
}

impl<V: Variable, T: ScalarValue + Into<V::ValueType>> FromIterator<(V, T)> for LinearCombination<V> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (V, T)>,
    {
        iter.into_iter()
            .fold(LinearCombination::default(), |t, (v, s)| t + (v, s))
    }
}

impl<'a, V: Variable, T: ScalarValue + Into<V::ValueType>> FromIterator<&'a (V, T)>
    for LinearCombination<V>
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a (V, T)>,
    {
        iter.into_iter()
            .fold(LinearCombination::default(), |t, (v, s)| {
                t + (v.clone(), s.clone().into())
            })
    }
}
