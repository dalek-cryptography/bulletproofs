use core::ops::{Add, Sub, Mul};
use core::mem;

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use transcript::TranscriptProtocol;

use super::scalar_value::ScalarValue;
use super::assignment::Assignment;
use super::linear_combination as lc;
use super::linear_combination::{LinearCombination,IntoLC};
use super::opaque_scalar::OpaqueScalar;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub enum VariableIndex {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
}

/// Represents a variable in the constraint system.
/// Each variable is identified by its index (`VariableIndex`) and
/// has an assignment which can be present of missing.
#[derive(Copy,Clone,Debug)]
pub struct Variable<S: ScalarValue> {
    /// Index of the variable within the constraint system
    pub index: VariableIndex,

    /// Assignment of the variable within the constraint system.
    /// Assignment is present as a plain or opaque scalar for the prover,
    /// but missing for the verifier.
    pub assignment: Assignment<S>,
}

/// `Constraint` is a `LinearCombination` over variable indices with opaque scalars
/// that is required to equal zero.
/// Create constraints using `equals` method on `LinearCombination`s and `Variable`s.
pub struct Constraint(pub LinearCombination<VariableIndex>);

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
    /// TODO: replace this with a method that allocates a single variable and keeps another one
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
        F: 'static + Fn(OpaqueScalar)-> Result<(), R1CSError>;
}

/// State of the constraint system
pub(crate) struct InternalState<'a, 'b> {
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    constraints: Vec<Constraint>,
    variables_count: usize,
    phase: Phase,
}

/// Represents the current phase of a constraint system
enum Phase {
    /// First phase collects the callbacks that produce challenges
    First {
        callbacks: Vec<(&'static [u8], Box<Fn(OpaqueScalar) -> Result<(), R1CSError>>)>
    },

    /// Second phase contains the number of variables committed after the first phase
    Second {
        /// Number of committed variables
        committed_variables: usize
    }
}

impl<'a,'b> InternalState<'a, 'b> {
    /// Creates an internal state for the constraint system.
    pub(crate) fn new(
        transcript: &'a mut Transcript,
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
    ) -> InternalState<'a, 'b> {
        InternalState {
            transcript, 
            bp_gens,
            pc_gens,
            constraints: Vec::new(),
            phase: Phase::First{callbacks: Vec::new()}
        }
    }
}

pub(crate) trait ConstraintSystemInternal {
    /// Returns the mutable reference to the internal state of the constraint system.
    fn internal_state(&mut self) -> &mut InternalState;

    /// Processes the transparent assignments to the variables.
    /// Prover forms commitments, verifier does nothing.
    fn handle_assignments(
        &mut self,
        left: Assignment<Scalar>,
        right: Assignment<Scalar>,
        out: Assignment<Scalar>
    )-> Result<(), R1CSError>;

    /// Returns Pedersen commitments `A_I`, `A_O`, `S`.
    fn intermediate_commitments(&mut self) -> (&CompressedRistretto, &CompressedRistretto, &CompressedRistretto);

    /// Commits the constraint system and generates deferred challenges.
    /// If the constraint system is already committed, this call has no effect.
    fn commit(&mut self) -> Result<(), R1CSError> {

        let phase2 = Phase::Second { committed_variables: self.internal_state().variables_count };
        let current_phase = mem::replace(self.internal_state().phase, phase2);

        let callbacks = match current_phase {
            Phase::First{callbacks: callbacks} => callbacks,
            second => {
                // Repeated commit calls should have no effect, so we need to put this phase back in.
                let _ = mem::replace(self.internal_state().phase, second);
                return Ok(());
            }
        };

        let (A_I, A_O, S) = self.intermediate_commitments();
        self.internal_state().transcript.commit_point(b"A_I'", A_I);
        self.internal_state().transcript.commit_point(b"A_O'", A_O);
        self.internal_state().transcript.commit_point(b"S'", S);

        for (label, callback) in callbacks.drain(..) {
            let challenge = self.internal_state().transcript.challenge_scalar(label).into();
             callback(challenge)?;
        }

        Ok(())
    }
}

impl<C> ConstraintSystem for C where C: ConstraintSystemInternal {
     /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier<S: ScalarValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {

        // Pass the transparent assignments to the implementation of the CS
        self.handle_assignments(
            left.into_transparent(),
            right.into_transparent(),
            out.into_transparent()
        )?;

        let i = self.internal_state().variables_count;
        self.internal_state().variables_count += 1;

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
    fn add_constraint(&mut self, constraint: Constraint) {
        self.internal_state().constraints.push(constraint)
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
    fn challenge_scalar<F>(&mut self, label: &'static [u8], callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(OpaqueScalar) -> Result<(), R1CSError>
    {
        match &mut self.internal_state().phase {
            Phase::First{ callbacks: ref mut callbacks } => {
                callbacks.push((label, Box::new(callback)));
                Ok(())
            },
            Phase::Second{ committed_variables: _ } => {
                let challenge = self.internal_state().transcript.challenge_scalar(label).into();
                callback(challenge)
            }
        }
    }
}



// Creating linear combinations from variables

/// Adding a linear combination `lc` to a variable `v` creates a combination `v*1 + lc`. 
impl<S,T> Add<T> for Variable<S> where S: ScalarValue, T: IntoLC<Variable<S>> {
    type Output = LinearCombination<Self>;

    fn add(self, lc: T) -> Self::Output {
        let mut lc = lc.into_lc();
        lc.precomputed += self.assignment;
        lc.terms.push((self, S::one()));
        lc
    }
}

/// Subtracting a linear combination `lc` from a variable `v` creates a combination `v*1 - lc`. 
impl<S,T> Sub<T> for Variable<S> where S: ScalarValue, T: IntoLC<Variable<S>> {
    type Output = LinearCombination<Self>;

    fn sub(self, lc: T) -> Self::Output {
        let mut lc = lc.into_lc();
        lc.precomputed = self.assignment - lc.precomputed;
        for (_, ref mut s) in lc.terms.iter_mut() {
            *s = -*s;
        }
        lc.terms.push((self, S::one()));
        lc
    }
}

/// Multiplying a variable `v` by a scalar `a` creates a combination `v*a`.
impl<T,S> Mul<T> for Variable<S> where T: Into<S>, S: ScalarValue {
    type Output = LinearCombination<Self>;

    fn mul(self, scalar: T) -> Self::Output {
        let scalar = scalar.into();
        LinearCombination {
            precomputed: self.assignment * Assignment::Value(scalar),
            terms: vec![(self, scalar)]
        }
    }
}


// Trait implementations for concrete types used in the constraint system
// ----------------------------------------------------------------------

impl<S> Variable<S> where S: ScalarValue {

    /// Creates a `Constraint` that this variable equals the given linear combination.
    pub fn equals<T>(self, lc: T) -> Constraint where T: IntoLC<Variable<S>> {
        (self - lc).into_constraint()
    }

    /// Converts the variable into an opaque one.
    pub fn into_opaque(self) -> Variable<OpaqueScalar> {
        Variable {
            index: self.index,
            assignment: self.assignment.into_opaque()
        }
    }
}

impl<S> LinearCombination<Variable<S>> where S: ScalarValue {

    /// Creates a `Constraint` that this linear combination equals the other linear combination.
    pub fn equals<T>(self, lc: T) -> Constraint where T: IntoLC<Variable<S>> {
        (self - lc.into_lc()).into_constraint()
    }

    // Any linear combination of variables with opaque or non-opaque scalars can be converted to a Constraint
    // (which does not hold the assignments and contains only the opaque scalars for uniform representation inside CS)
    fn into_constraint(self) -> Constraint {
        Constraint(LinearCombination{
            precomputed: match self.eval() {
                Assignment::Value(v) => Assignment::Value(v.into_opaque()),
                Assignment::Missing() => Assignment::Missing(),
            },
            terms: self
                .terms
                .into_iter()
                .map(|(v, s)| (v.index, s.into_opaque()))
                .collect(),
        })
    }
}

impl lc::Variable for VariableIndex {
    // Using OpaqueScalar for the Constraint to have opaque weights
    type ValueType = OpaqueScalar;
    type OpaqueType = VariableIndex;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        Assignment::Missing()
    }

    fn constant_one() -> Self {
        VariableIndex::One()
    }

    fn into_opaque(self) -> Self::OpaqueType {
        self
    }
}

impl<S: ScalarValue> lc::Variable for Variable<S> {
    type ValueType = S;
    type OpaqueType = Variable<OpaqueScalar>;

    fn assignment(&self) -> Assignment<Self::ValueType> {
        self.assignment
    }

    fn constant_one() -> Self {
        Variable {
            index: VariableIndex::One(),
            assignment: Assignment::Value(S::one()),
        }
    }

    fn into_opaque(self) -> Self::OpaqueType {
        Variable::into_opaque(self)
    }
}


