use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::RistrettoPoint;

/// Represents a variable in our constraint system.
#[derive(Copy, Clone, Debug)]
pub struct Variable(Index);

/// Represents the index of either a public or private variable.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Index {
    Public(usize),
    Private(usize)
}

/// This represents a linear combination of some variables, with scalar coefficients.
#[derive(Clone)]
pub struct LinearCombination(Vec<Variable, Scalar>);