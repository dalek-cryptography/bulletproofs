use std::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign, Try};
use subtle::{Choice, ConditionallyAssignable, ConditionallySelectable, ConstantTimeEq};

use errors::R1CSError;

use super::scalar_value::ScalarValue;
use super::opaque_scalar::OpaqueScalar;

/// Represents an optional assignment to a [`Variable`](::r1cs::Variable).
///
/// This type is like an `Option<Scalar>`, but implements the
/// `std::ops` traits to perform arithmetic operations.
///
/// Proving code creates `Value` assignments, while verification code
/// creates `Missing` assignments.
#[derive(Copy,Clone,Debug)]
pub enum Assignment<S>
where
    S: ScalarValue,
{
    /// A known assignment to a variable in a [`ConstraintSystem`](::r1cs::ConstraintSystem).
    Value(S),
    /// An unknown assignment to a variable in a [`ConstraintSystem`](::r1cs::ConstraintSystem).
    Missing(),
}

impl<S: ScalarValue> Assignment<S> {
    /// Converts the assignment to an opaque scalar.
    pub fn into_opaque(self) -> Assignment<OpaqueScalar> {
        match self {
            Assignment::Value(x) => Assignment::Value(x.into()),
            Assignment::Missing() => Assignment::Missing(),
        }
    }

    /// Converts the assignment to a transparent scalar.
    /// This method is for internal use by ConstraintSystem only.
    pub(crate) fn into_transparent(self) -> Assignment<Scalar> {
        match self {
            Assignment::Value(x) => Assignment::Value(x.into_opaque().internal_scalar),
            Assignment::Missing() => Assignment::Missing(),
        }
    }
}

// Default implementation is used for zeroing secrets from allocated memory via `clear_on_drop`.
impl<S> Default for Assignment<S>
where
    S: ScalarValue,
{
    fn default() -> Assignment<S> {
        Assignment::Missing()
    }
}

impl<S> From<Option<S>> for Assignment<S>
where
    S: ScalarValue,
{
    fn from(o: Option<S>) -> Self {
        match o {
            Some(v) => Assignment::Value(v),
            None => Assignment::Missing(),
        }
    }
}

impl<S> From<S> for Assignment<S>
where
    S: ScalarValue,
{
    fn from(scalar: S) -> Self {
        Assignment::Value(scalar)
    }
}

impl<S> From<u64> for Assignment<S>
where
    S: ScalarValue,
{
    fn from(int: u64) -> Self {
        Assignment::Value(S::from(int))
    }
}

impl<A, B> Add<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    type Output = Self;

    fn add(self, rhs: B) -> Self {
        match (self, rhs.into()) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left + right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl<A, B> AddAssign<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    fn add_assign(&mut self, rhs: B) {
        match (self, rhs.into()) {
            (Assignment::Value(ref mut left), Assignment::Value(right)) => *left = *left + right,
            (_, _) => (),
        }
    }
}

impl<A, B> Sub<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    type Output = Self;

    fn sub(self, rhs: B) -> Self {
        match (self, rhs.into()) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left - right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl<A, B> SubAssign<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    fn sub_assign(&mut self, rhs: B) {
        match (self, rhs.into()) {
            (Assignment::Value(ref mut left), Assignment::Value(right)) => *left = *left - right,
            (_, _) => (),
        }
    }
}

impl<A, B> Mul<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    type Output = Self;

    fn mul(self, rhs: B) -> Self::Output {
        match (self, rhs.into()) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left * right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl<A, B> Div<B> for Assignment<A>
where
    A: ScalarValue,
    B: Into<Assignment<A>>,
{
    type Output = Self;

    fn div(self, rhs: B) -> Self {
        match (self, rhs.into()) {
            (Assignment::Value(left), Assignment::Value(right)) => {
                Assignment::Value(left * right.invert())
            }
            (_, _) => Assignment::Missing(),
        }
    }
}

impl<S> Try for Assignment<S>
where
    S: ScalarValue,
{
    type Ok = S;
    type Error = R1CSError;

    fn into_result(self) -> Result<Self::Ok, Self::Error> {
        match self {
            Assignment::Value(val) => Ok(val),
            Assignment::Missing() => Err(R1CSError::MissingAssignment),
        }
    }

    fn from_error(_v: Self::Error) -> Self {
        Assignment::Missing()
    }

    fn from_ok(v: Self::Ok) -> Self {
        Assignment::Value(v)
    }
}

impl<S> ConditionallySelectable for Assignment<S>
where
    S: ScalarValue + ConditionallyAssignable,
{
    // This function should execute in constant time for a and b of the same type.
    // So, if a and b are both of type Assignment::Value(), then the comparison will
    // execute in constant time regardless of their value assignments.
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        match (a, b) {
            (Assignment::Value(a_val), Assignment::Value(b_val)) => {
                // FIXME: use `Scalar::conditional_select(&a_val, &b_val, choice)` instead
                // Currently that trait is not available because of a bug in `curve25519-dalek`.
                // Filed issue: https://github.com/dalek-cryptography/curve25519-dalek/issues/200
                let mut out_val = a_val.clone();
                out_val.conditional_assign(&b_val, choice);
                Assignment::from(out_val)
            }
            (_, _) => Assignment::Missing(),
        }
    }
}

impl<S> ConstantTimeEq for Assignment<S>
where
    S: ScalarValue + ConstantTimeEq,
{
    // This function should execute in constant time for self and other of the same type.
    fn ct_eq(&self, other: &Self) -> Choice {
        match (self, other) {
            (Assignment::Value(self_value), Assignment::Value(other_value)) => {
                self_value.ct_eq(other_value)
            }
            (Assignment::Missing(), Assignment::Missing()) => Choice::from(1),
            _ => Choice::from(0),
        }
    }
}
