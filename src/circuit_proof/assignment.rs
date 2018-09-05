use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use std::ops::{Add, Div, Mul, Sub, Try};

// The assignment value to a variable, as stored in `ConstraintSystem`.
// Provers create a `Scalar` assignment, while verifiers create an `R1CSError` assignment.
#[derive(Copy, Clone, Debug)]
pub enum Assignment {
    Value(Scalar),
    Missing(),
}

impl Assignment {
    pub fn new(scalar: Scalar) -> Self {
        Assignment::Value(scalar)
    }

    pub fn zero() -> Self {
        Assignment::Value(Scalar::zero())
    }

    pub fn from_u64(v: u64) -> Self {
        Assignment::Value(Scalar::from(v))
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
