use super::assignment::{Assignment, AssignmentValue};
use core::iter::FromIterator;
use core::ops::{Add, Mul, Sub};

/// Trait for the weights and variable assignments
pub trait Value: AssignmentValue {
    /// Value of 1, neutral element in multiplication
    fn one() -> Self;

    /// Value of 0, neutral element in addition
    fn zero() -> Self;
}

pub trait Variable {
    type ValueType: Value;

    /// Returns the assignment
    fn assignment(&self) -> Assignment<Self::ValueType>;

    /// Returns the representation of "1" using which the constant terms can be stored
    fn constant_one() -> Self;
}

/// Linear combination of variables `V` and scalars `S` allows
/// building a sum of V_i*S_i.
/// The assignment of the variable must have the same type as the weights to simplify the constraints.
/// If one needs to make an LC of a clear assignment with opaque weight,
/// the variable needs to be converted to opaque assignment first.
pub struct LinearCombination<V: Variable> {
    pub terms: Vec<(V, V::ValueType)>,
    precomputed: Assignment<V::ValueType>,
}

impl<V: Variable> LinearCombination<V> {
    /// Evaluates the linear combination
    pub fn eval(&self) -> Assignment<V::ValueType> {
        self.precomputed
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

/// Converting a pair (var,value) into a linear combination
impl<V: Variable> From<(V, V::ValueType)> for LinearCombination<V> {
    fn from(pair: (V, V::ValueType)) -> Self {
        LinearCombination {
            terms: vec![(pair.0, pair.1)],
            precomputed: pair.0.assignment() * pair.1,
        }
    }
}

// Adding a pair to a linear combination
impl<V: Variable, T: Value + Into<V::ValueType>> Add<(V, T)> for LinearCombination<V> {
    type Output = Self;

    fn add(mut self, rhs: (V, T)) -> Self {
        self.terms.push((rhs.0, rhs.1.into()));
        self.precomputed += rhs.0.assignment() * rhs.1.into();
        self
    }
}

// Subtracting a pair from a linear combination
impl<V: Variable, T: Value + Into<V::ValueType>> Sub<(V, T)> for LinearCombination<V> {
    type Output = Self;

    fn sub(mut self, rhs: (V, T)) -> Self {
        self.terms.push((rhs.0, -rhs.1.into()));
        self.precomputed -= rhs.0.assignment() * rhs.1.into();
        self
    }
}

// Adding a constant to a linear combination
impl<V: Variable, T: Value + Into<V::ValueType>> Add<T> for LinearCombination<V> {
    type Output = Self;

    fn add(mut self, rhs: T) -> Self {
        self.terms.push((V::constant_one(), rhs.into()));
        self.precomputed += rhs.into();
        self
    }
}

// Subtracting a constant from a linear combination
impl<V: Variable, T: Value + Into<V::ValueType>> Sub<T> for LinearCombination<V> {
    type Output = Self;

    fn sub(mut self, rhs: T) -> Self {
        self.terms.push((V::constant_one(), -rhs.into()));
        self.precomputed -= rhs.into();
        self
    }
}

// Multiplying a linear combination by a constant
impl<V: Variable, T: Value + Into<V::ValueType>> Mul<T> for LinearCombination<V> {
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self {
        for (_, ref mut s) in self.terms.iter_mut() {
            *s = *s * rhs.into();
        }
        self.precomputed = self.precomputed * rhs.into();
        self
    }
}

impl<V: Variable, T: Value + Into<V::ValueType>> FromIterator<(V, T)> for LinearCombination<V> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (V, T)>,
    {
        iter.into_iter()
            .fold(LinearCombination::default(), |t, (v, s)| t + (v, s))
    }
}

impl<'a, V: Variable, T: Value + Into<V::ValueType>> FromIterator<&'a (V, T)>
    for LinearCombination<V>
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a (V, T)>,
    {
        iter.into_iter()
            .fold(LinearCombination::default(), |t, (v, s)| {
                t + (*v.clone(), s.clone())
            })
    }
}
