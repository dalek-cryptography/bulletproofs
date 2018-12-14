//! Definition of the constraint system trait.

use super::{LinearCombination, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

/// The interface for a constraint system, abstracting over the prover
/// and verifier's roles.
///
/// Statements to be proved by an [`R1CSProof`](::r1cs::R1CSProof) are specified by
/// programmatically constructing constraints.  These constraints need
/// to be identical between the prover and verifier, since the prover
/// and verifier need to construct the same statement.
///
/// To prevent code duplication or mismatches between the prover and
/// verifier, gadgets for the constraint system should be written
/// using the `ConstraintSystem` trait, so that the prover and
/// verifier share the logic for specifying constraints.
pub trait ConstraintSystem {
    /// Allocate and constrain multiplication variables.
    ///
    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    /// and add the explicit constraints that
    /// ```text
    /// left = left_constraint
    /// right = right_constraint
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable);

    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>;

    /// Enforce the explicit constraint that
    /// ```text
    /// lc = 0
    /// ```
    fn constrain(&mut self, lc: LinearCombination);

    /// Randomize the constraints using a randomly sampled challenge scalar
    /// bound to the assignments of the non-randomized variables.
    ///
    /// If the CS is not yet committed, the call returns `Ok()` and saves a callback
    /// for later, when the constraint system’s low-level variables are committed.
    /// If the CS is already committed, the callback is invoked immediately.
    fn randomized_constraints<F>(
        &mut self,
        label: &'static [u8],
        callback: F,
    ) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self, Scalar) -> Result<(), R1CSError>;
}
