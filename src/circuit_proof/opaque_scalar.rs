use curve25519_dalek::scalar::Scalar;
use std::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallyAssignable, ConstantTimeEq};

/// A scalar that does not expose its value to the constraint system.
/// When CS samples a random challenge scalar, it is wrapped in `OpaqueScalar`
/// to prevent accidental use of it for making decisions on the prover side.
/// As a consequence, all the derived assignments are opaque as well.
#[derive(Copy, Clone, Debug)]
pub struct OpaqueScalar {
    /// The actual scalar value is only available to the constraint system implementation.
    pub(crate) internal_scalar: Scalar,
}

impl OpaqueScalar {
    fn one() -> Self {
        Scalar::one().into()
    }
    fn zero() -> Self {
        Scalar::zero().into()
    }
}

impl From<Scalar> for OpaqueScalar {
    fn from(scalar: Scalar) -> Self {
        OpaqueScalar {
            internal_scalar: scalar,
        }
    }
}

impl From<u64> for OpaqueScalar {
    fn from(scalar: u64) -> Self {
        OpaqueScalar {
            internal_scalar: Scalar::from(scalar),
        }
    }
}

impl Default for OpaqueScalar {
    fn default() -> Self {
        OpaqueScalar::zero()
    }
}

impl Neg for OpaqueScalar {
    type Output = OpaqueScalar;

    fn neg(mut self) -> OpaqueScalar {
        self.internal_scalar = -self.internal_scalar;
        self
    }
}

impl Add for OpaqueScalar {
    type Output = Self;
    fn add(mut self, rhs: OpaqueScalar) -> Self {
        self.internal_scalar += rhs.internal_scalar;
        self
    }
}

impl Add<Scalar> for OpaqueScalar {
    type Output = Self;
    fn add(mut self, rhs: Scalar) -> Self {
        self.internal_scalar += rhs;
        self
    }
}

impl AddAssign for OpaqueScalar {
    fn add_assign(&mut self, rhs: OpaqueScalar) {
        self.internal_scalar += rhs.internal_scalar;
    }
}

impl Sub for OpaqueScalar {
    type Output = Self;
    fn sub(mut self, rhs: OpaqueScalar) -> Self {
        self.internal_scalar -= rhs.internal_scalar;
        self
    }
}

impl Sub<Scalar> for OpaqueScalar {
    type Output = Self;
    fn sub(mut self, rhs: Scalar) -> Self {
        self.internal_scalar -= rhs;
        self
    }
}

impl SubAssign for OpaqueScalar {
    fn sub_assign(&mut self, rhs: OpaqueScalar) {
        self.internal_scalar -= rhs.internal_scalar;
    }
}

impl Mul for OpaqueScalar {
    type Output = Self;
    fn mul(mut self, rhs: OpaqueScalar) -> Self {
        self.internal_scalar *= rhs.internal_scalar;
        self
    }
}

impl Mul<Scalar> for OpaqueScalar {
    type Output = Self;
    fn mul(mut self, rhs: Scalar) -> Self {
        self.internal_scalar *= rhs;
        self
    }
}

impl ConditionallyAssignable for OpaqueScalar {
    fn conditional_assign(&mut self, other: &Self, choice: Choice) {
        self.internal_scalar
            .conditional_assign(&other.internal_scalar, choice)
    }
}

impl ConstantTimeEq for OpaqueScalar {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.internal_scalar.ct_eq(&other.internal_scalar)
    }
}
