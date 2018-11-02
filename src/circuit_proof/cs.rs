use core::mem;
use merlin::Transcript;

use errors::R1CSError;
use transcript::TranscriptProtocol;

use super::assignment::Assignment;
use super::constraints::{Constraint, Variable};
use super::opaque_scalar::OpaqueScalar;
use super::scalar_value::ScalarValue;

/// `ConstraintSystem` trait represents the API for the gadgets.
/// Gadgets receive a mutable instance of the constraint system and use it
/// to allocate variables and create constraints between them.
pub trait ConstraintSystem {
    /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier<S: ScalarValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError>;

    /// Allocate two uncommitted variables, and assign them the Assignments passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    ///
    /// XXX: replace this with a method that allocates a single variable and keeps another one
    /// in a pair in a stash for the next call.
    fn assign_uncommitted<S: ScalarValue>(
        &mut self,
        a: Assignment<S>,
        b: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>), R1CSError> {
        let (left, right, _) = self.assign_multiplier(a, b, a * b)?;
        Ok((left, right))
    }

    /// Enforce that the given linear combination in the constraint is zero.
    fn add_constraint(&mut self, constraint: Constraint);

    /// Obtain a challenge scalar bound to the assignments of all of
    /// the externally committed wires.
    ///
    /// If the CS is not yet committed, the call returns `Ok()` and saves a callback
    /// for later, when the constraint system’s free variables are committed.
    /// If the CS is already committed, the callback is invoked immediately
    ///
    /// This allows the prover to select a challenge circuit from a
    /// family of circuits parameterized by challenge scalars.
    fn challenge_scalar<F>(&mut self, label: &'static [u8], callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self, OpaqueScalar) -> Result<(), R1CSError>;
}

pub(crate) trait ConstraintSystemInternal: ConstraintSystem + Sized {
    /// Returns the transcript used by the constraint system.
    fn transcript(&mut self) -> &mut Transcript;

    /// Returns the deferred challenges used by the constraint system.
    fn deferred_challenges(&mut self) -> &mut DeferredChallenges<Self>;
}

/// Deferred challenge represents a callback that receives the challenge after the CS is committed.
pub(crate) struct DeferredChallenges<CS>
where
    CS: ConstraintSystem + ConstraintSystemInternal,
{
    list: Option<
        Vec<(
            &'static [u8],
            Box<Fn(&mut CS, OpaqueScalar) -> Result<(), R1CSError>>,
        )>,
    >,
}

impl<CS> DeferredChallenges<CS>
where
    CS: ConstraintSystem + ConstraintSystemInternal,
{
    /// Creates an empty set of deferred challenges
    pub(crate) fn new() -> Self {
        DeferredChallenges {
            list: Some(Vec::new()),
        }
    }

    /// Adds a new callback if the CS is not committed yet (== callbacks are not drained),
    /// or invokes it immediately if it is.
    pub(crate) fn push<F>(cs: &mut CS, label: &'static [u8], callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut CS, OpaqueScalar) -> Result<(), R1CSError>,
    {
        match cs.deferred_challenges().list {
            Some(ref mut list) => {
                list.push((label, Box::new(callback)));
                return Ok(());
            }
            None => {}
        }

        let challenge = cs.transcript().challenge_scalar(label);
        callback(cs, challenge.into())
    }

    /// Processes all stored callbacks, switching to a "committed" state.
    pub(crate) fn drain(cs: &mut CS) -> Result<(), R1CSError> {
        let dc = cs.deferred_challenges();
        let list = mem::replace(&mut dc.list, None).unwrap_or(Vec::new());

        for (label, callback) in list.into_iter() {
            let challenge = cs.transcript().challenge_scalar(label);
            callback(cs, challenge.into())?;
        }
        Ok(())
    }
}
