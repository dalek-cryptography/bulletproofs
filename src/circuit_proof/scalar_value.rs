use curve25519_dalek::scalar::Scalar;
use std::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};

use super::opaque_scalar::OpaqueScalar;

/// Trait for the weights in linear constraints and variable assignments
/// that is implemented by `Scalar` and `OpaqueScalar`.
pub trait ScalarValue:
    Copy
    + Clone
    + From<Scalar>
    + Into<OpaqueScalar>
    + From<u64>
    + Neg<Output = Self>
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
{
	/// Value of 1, neutral element in multiplication
    fn one() -> Self;

    /// Value of 0, neutral element in addition
    fn zero() -> Self;

    /// Returns `x` such that `self*x mod l == 1`.
    fn invert(&self) -> Self;

    /// Converts the value into `OpaqueScalar`.
    fn into_opaque(self) -> OpaqueScalar;
}


impl ScalarValue for OpaqueScalar {
	fn one() -> Self {
        Scalar::one().into()
    }
    fn zero() -> Self {
        Scalar::zero().into()
    }
    fn invert(&self) -> Self {
        Scalar::invert(&self.internal_scalar).into()
    }
    fn into_opaque(self) -> OpaqueScalar {
    	self
    }
}

impl ScalarValue for Scalar {
	fn one() -> Self {
        Scalar::one()
    }
    fn zero() -> Self {
        Scalar::zero()
    }
    fn invert(&self) -> Self {
        Scalar::invert(self)
    }
    fn into_opaque(self) -> OpaqueScalar {
    	self.into()
    }
}
