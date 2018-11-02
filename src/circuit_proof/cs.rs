#![allow(non_snake_case)]

use core::mem;

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;

use errors::R1CSError;
use transcript::TranscriptProtocol;

use super::scalar_value::ScalarValue;
use super::assignment::Assignment;
use super::opaque_scalar::OpaqueScalar;
use super::constraints::{Variable,VariableIndex,Constraint};


/// `ConstraintSystem` trait represents the API for the gadgets.
/// Gadgets receive a mutable instance of the constraint system and use it
/// to allocate variables and create constraints between them.
pub trait ConstraintSystem {
    type CommittedCS: ConstraintSystem;

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
        F: 'static + Fn(&mut Self::CommittedCS, OpaqueScalar)-> Result<(), R1CSError>;
}


/// Internal state of the constraint system
pub(crate) struct ConstraintSystemState<'a, CS: ConstraintSystem> {
    pub(crate) transcript: &'a mut Transcript,
    constraints: Vec<Constraint>,
    external_variables_count: usize,
    variables_count: usize,
    phase: Phase<CS>,
}

/// Represents the current phase of a constraint system
enum Phase<CS: ConstraintSystem> {
    /// First phase collects the callbacks that produce challenges
    DeferredCS(Vec<(&'static [u8], Box<Fn(&mut CS, OpaqueScalar) -> Result<(), R1CSError>>)>),
    CommittedCS
}

impl<'a, CS> ConstraintSystemState<'a, CS> where CS: ConstraintSystem {
    /// Creates an internal state for the constraint system.
    pub(crate) fn new(
        transcript: &'a mut Transcript,
        external_commitments: &[CompressedRistretto],
    ) -> Self {

        transcript.r1cs_domain_sep(external_commitments.len() as u64);

        for V in external_commitments.iter() {
            transcript.commit_point(b"V", V);
        }

        Self {
            transcript, 
            constraints: Vec::new(),
            external_variables_count: external_commitments.len(),
            variables_count: 0,
            phase: Phase::DeferredCS(Vec::new())
        }
    }

    /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    pub(crate) fn assign_multiplier<S: ScalarValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {

        let i = self.variables_count;
        self.variables_count += 1;

        Ok((
            Variable {
                index: VariableIndex::MultiplierLeft(i),
                assignment: left,
            },
            Variable {
                index: VariableIndex::MultiplierRight(i),
                assignment: right,
            },
            Variable {
                index: VariableIndex::MultiplierOutput(i),
                assignment: out,
            },
        ))
    }

    /// Enforce that the given linear combination in the constraint is zero.
    pub(crate) fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint)
    }

    /// Obtain a challenge scalar bound to the assignments of all of
    /// the externally committed wires.
    /// 
    /// If the CS is not yet committed, the call returns `Ok()` and saves a callback
    /// for later, when the constraint system’s free variables are committed.
    /// If the CS is already committed, the callback is invoked immediately
    ///
    /// This allows the prover to select a challenge circuit from a
    /// family of circuits parameterized by challenge scalars.
    pub(crate) fn delegated_challenge_scalar<F>(
        &mut self,
        cs: &mut CS,
        label: &'static [u8],
        callback: F
    ) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut CS, OpaqueScalar)-> Result<(), R1CSError>
    {
        match &mut self.phase {
            Phase::DeferredCS(ref mut callbacks) => {
                callbacks.push((label, Box::new(callback)));
                Ok(())
            },
            Phase::CommittedCS => {
                let challenge: OpaqueScalar = self.transcript.challenge_scalar(label).into();
                callback(cs, challenge)
            }
        }
    }


    /// Builds the second phase of the constraint system and generates deferred challenges.
    /// If the constraint system is already committed, this call has no effect.
    pub(crate) fn complete_constraints(&mut self, cs: &mut CS) -> Result<(), R1CSError> {
        let mut callbacks = match &mut self.phase {
            Phase::DeferredCS(ref mut callbacks) => mem::replace(callbacks, Vec::new()),
            _ => {
                return Ok(());
            }
        };

        // Switch the phase before we call any callbacks as those can trigger additional queries
        self.phase = Phase::CommittedCS;

        for (label, callback) in callbacks.drain(..) {
            let challenge = self.transcript.challenge_scalar(label).into();
            // Note: nested calls for challenges are going to yield immediately as we switched
            // to the second phase already. This means, the order of challenge generation is
            // depth-first: `A(B(C), D(E)), F(G)` -> `[A, B, C, D, E, F, G]`.
            callback(cs, challenge)?;
        }

        Ok(())
    }


    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    pub(crate) fn flattened_constraints<T: ZeroCostOptionalScalar>(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, T) {
        let n = self.variables_count;
        let m = self.external_variables_count;

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];
        let mut wc:T = Scalar::zero().into();

        let mut exp_z = *z;
        for c in self.constraints.iter() {
            for (var, coeff) in &c.0.terms {
                match var {
                    VariableIndex::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::Committed(i) => {
                        wV[*i] -= exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::One() => {
                        // Note: this is no-op for the prover because it'll use T = NoScalar.
                        wc -= T::from(exp_z) * coeff.internal_scalar;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wc)
    }
}

use std::ops::{Mul, SubAssign};
/// Trait representing either a `Scalar` or `NoScalar` (for which arithmetic is no-op).
pub(crate) trait ZeroCostOptionalScalar: Mul<Scalar, Output=Self>
                                       + SubAssign
                                       + Sized
                                       + From<Scalar>
{}

impl ZeroCostOptionalScalar for Scalar {}
impl ZeroCostOptionalScalar for NoScalar {}

/// Replacement for a scalar with zero-cost arithmetic operations
pub(crate) struct NoScalar {}

impl From<Scalar> for NoScalar {
    fn from(_: Scalar) -> Self {
        NoScalar{}
    }
}

impl SubAssign for NoScalar {
    fn sub_assign(&mut self, _rhs: NoScalar) {}
}

impl Mul<Scalar> for NoScalar {
    type Output = Self;
    fn mul(self, _rhs: Scalar) -> Self {
        self
    }
}

