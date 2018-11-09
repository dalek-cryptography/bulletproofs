use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use std::ops::{Add, Div, Mul, Sub, Try};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

/// Represents an optional assignment to a [`Variable`](::r1cs::Variable).
///
/// This type is like an `Option<Scalar>`, but implements the
/// `std::ops` traits to perform arithmetic operations.
///
/// Proving code creates `Value` assignments, while verification code
/// creates `Missing` assignments.
///
/// This allows the prover and verifier to use the same code for
/// defining gadgets, eliminating the possibility of a constraint
/// system mismatch.
#[derive(Copy, Clone, Debug)]
pub enum Assignment {
    /// A known assignment to a variable in a [`ConstraintSystem`](::r1cs::ConstraintSystem).
    Value(Scalar),
    /// An unknown assignment to a variable in a [`ConstraintSystem`](::r1cs::ConstraintSystem).
    Missing(),
}

// Implementing `Default` means that the generic impl of
// `clear_on_drop::clear::InitializableFromZeroed` applies, which
// makes the generic impl of `clear_on_drop::clear::Clear` applies,
// which makes `Assignment`s erasable.
//
// This is somewhat baroque.
impl Default for Assignment {
    fn default() -> Assignment {
        Assignment::Missing()
    }
}

impl From<Option<Scalar>> for Assignment {
    fn from(o: Option<Scalar>) -> Self {
        match o {
            Some(v) => Assignment::Value(v),
            None => Assignment::Missing(),
        }
    }
}

impl From<Scalar> for Assignment {
    fn from(scalar: Scalar) -> Self {
        Assignment::Value(scalar)
    }
}

impl From<u64> for Assignment {
    fn from(int: u64) -> Self {
        Assignment::Value(Scalar::from(int))
    }
}

impl Add for Assignment {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left + right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl Add<Scalar> for Assignment {
    type Output = Self;

    fn add(self, rhs: Scalar) -> Self {
        match self {
            Assignment::Value(lhs) => Assignment::Value(lhs + rhs),
            _ => Assignment::Missing(),
        }
    }
}

impl Sub for Assignment {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left - right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl Sub<Scalar> for Assignment {
    type Output = Self;

    fn sub(self, rhs: Scalar) -> Self {
        match self {
            Assignment::Value(lhs) => Assignment::Value(lhs - rhs),
            _ => Assignment::Missing(),
        }
    }
}

impl Mul for Assignment {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Assignment::Value(left), Assignment::Value(right)) => Assignment::Value(left * right),
            (_, _) => Assignment::Missing(),
        }
    }
}

impl Mul<Scalar> for Assignment {
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self {
        match self {
            Assignment::Value(lhs) => Assignment::Value(lhs * rhs),
            _ => Assignment::Missing(),
        }
    }
}

impl Div for Assignment {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Assignment::Value(left), Assignment::Value(right)) => {
                Assignment::Value(left * right.invert())
            }
            (_, _) => Assignment::Missing(),
        }
    }
}

impl Div<Scalar> for Assignment {
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self {
        match self {
            Assignment::Value(lhs) => Assignment::Value(lhs * rhs.invert()),
            _ => Assignment::Missing(),
        }
    }
}

impl Try for Assignment {
    type Ok = Scalar;
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

impl ConditionallySelectable for Assignment {
    // This function should execute in constant time for a and b of the same type.
    // So, if a and b are both of type Assignment::Value(), then the comparison will
    // execute in constant time regardless of their value assignments.
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        match (a, b) {
            (Assignment::Value(a_val), Assignment::Value(b_val)) => {
                Assignment::Value(Scalar::conditional_select(&a_val, &b_val, choice))
            }
            (_, _) => Assignment::Missing(),
        }
    }
}

impl ConstantTimeEq for Assignment {
    // This function should execute in constant time for self and other of the same type.
    fn ct_eq(&self, other: &Self) -> Choice {
        match (self, other) {
            (Assignment::Value(self_value), Assignment::Value(other_value)) => {
                self_value.ct_eq(other_value)
            }
            // For all other combinations of Value/Missing, define the
            // comparison as "not equal"
            (_,_) => Choice::from(0),
        }
    }
}
