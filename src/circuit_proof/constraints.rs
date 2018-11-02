#![allow(non_snake_case)]

use core::borrow::Borrow;
use core::ops::{Add, Mul, Neg, Sub, SubAssign};

use curve25519_dalek::scalar::Scalar;

use super::assignment::Assignment;
use super::opaque_scalar::OpaqueScalar;
use super::scalar_value::ScalarValue;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub(crate) enum VariableIndex {
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
#[derive(Copy, Clone, Debug)]
pub struct Variable<S: ScalarValue> {
    /// Index of the variable within the constraint system
    pub(crate) index: VariableIndex,

    /// Assignment of the variable within the constraint system.
    /// Assignment is present as a plain or opaque scalar for the prover,
    /// but missing for the verifier.
    pub assignment: Assignment<S>,
}

/// `Constraint` is a `LinearCombination` over variable indices with opaque scalars
/// that is required to equal zero.
/// Create constraints using `equals` method on `LinearCombination`s and `Variable`s.
pub struct Constraint(pub(crate) Vec<(VariableIndex, OpaqueScalar)>);

/// Trait for types that can be unambiguously converted to a linear combination.
/// Variable is converted to `(var, 1)`, scalar is converted as `(One, scalar)`,
/// tuple `(v,w)` is converted to a single term.
pub trait IntoLinearCombination<T>
where
    T: ScalarValue,
{
    /// Converts the type into a linear combination
    fn into_lc(self) -> LinearCombination<T>;
}

/// Linear combination of variables `V` and scalars `S` allows
/// building a sum of V_i*S_i.
/// The assignment of the variable must have the same type as the weights to simplify the constraints.
/// If one needs to make an LC of a clear assignment with opaque weight,
/// the variable needs to be converted to opaque assignment first using `into_opaque`.
pub struct LinearCombination<T: ScalarValue> {
    /// Terms of the linear combination.
    pub(crate) terms: Vec<(Variable<T>, T)>,
}

impl<T: ScalarValue> Variable<T> {
    /// Returns the representation of "1" using which the constant terms can be stored.
    pub fn constant_one() -> Self {
        Variable {
            index: VariableIndex::One(),
            assignment: Assignment::Value(T::one()),
        }
    }

    /// Creates a `Constraint` that this variable equals the given linear combination.
    pub fn equals<L>(self, lc: L) -> Constraint
    where
        L: IntoLinearCombination<T>,
    {
        (self - lc).into_constraint()
    }

    /// Converts the variable into an opaque one.
    pub fn into_opaque(self) -> Variable<OpaqueScalar> {
        Variable {
            index: self.index,
            assignment: self.assignment.into_opaque(),
        }
    }

    /// Creates a variable representing a committed
    pub(crate) fn committed(index: usize, assignment: Assignment<T>) -> Variable<T> {
        Self {
            index: VariableIndex::Committed(index),
            assignment,
        }
    }

    pub(crate) fn from_multiplier(
        index: usize,
        left: Assignment<T>,
        right: Assignment<T>,
        out: Assignment<T>,
    ) -> (Variable<T>, Variable<T>, Variable<T>) {
        (
            Variable {
                index: VariableIndex::MultiplierLeft(index),
                assignment: left,
            },
            Variable {
                index: VariableIndex::MultiplierRight(index),
                assignment: right,
            },
            Variable {
                index: VariableIndex::MultiplierOutput(index),
                assignment: out,
            },
        )
    }
}

impl Constraint {
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
    pub(crate) fn flatten<T, I>(
        constraints: I,
        z: &Scalar,
        external_variables_count: usize,
        internal_variables_count: usize,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, T)
    where
        T: ZeroCostOptionalScalar,
        I: Iterator,
        I::Item: Borrow<Constraint>,
    {
        let m = external_variables_count;
        let n = internal_variables_count;

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];
        let mut wc: T = Scalar::zero().into();

        let mut exp_z = *z;
        for c in constraints {
            for (var, coeff) in c.borrow().0.iter() {
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

impl<T: ScalarValue> LinearCombination<T> {
    /// Evaluates the linear combination expression.
    pub fn eval(&self) -> Assignment<T> {
        self.terms
            .iter()
            .fold(Assignment::Value(T::zero()), |t, (v, w)| {
                t + v.assignment * Assignment::Value(*w)
            })
    }

    /// Converts variables in the linear combination into opaque variables
    pub fn into_opaque(self) -> LinearCombination<OpaqueScalar> {
        LinearCombination {
            // XXX: use mem::forget + mem::transmute + Vec::from_raw_parts + packed repr for OpaqueScalar
            // in order to avoid additional allocation here
            terms: self
                .terms
                .into_iter()
                .map(|(v, s)| (v.into_opaque(), s.into_opaque()))
                .collect(),
        }
    }

    /// Creates a `Constraint` that this linear combination equals the other linear combination.
    pub fn equals<L>(self, lc: L) -> Constraint
    where
        L: IntoLinearCombination<T>,
    {
        (self - lc.into_lc()).into_constraint()
    }

    // Any linear combination of variables with opaque or non-opaque scalars can be converted to a Constraint
    // (which does not hold the assignments and contains only the opaque scalars for uniform representation inside CS)
    fn into_constraint(self) -> Constraint {
        Constraint(
            self.terms
                .into_iter()
                .map(|(v, s)| (v.index, s.into_opaque()))
                .collect(),
        )
    }
}

impl<T: ScalarValue> Default for LinearCombination<T> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

// Implementation of IntoLinearCombination trait for various types

impl<T: ScalarValue> IntoLinearCombination<T> for LinearCombination<T> {
    fn into_lc(self) -> LinearCombination<T> {
        self
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for u64 {
    fn into_lc(self) -> LinearCombination<T> {
        LinearCombination {
            terms: vec![(Variable::constant_one(), T::from(self))],
        }
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for Scalar {
    fn into_lc(self) -> LinearCombination<T> {
        LinearCombination {
            terms: vec![(Variable::constant_one(), T::from(self))],
        }
    }
}

impl IntoLinearCombination<OpaqueScalar> for OpaqueScalar {
    fn into_lc(self) -> LinearCombination<OpaqueScalar> {
        LinearCombination {
            terms: vec![(Variable::constant_one(), self)],
        }
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for Variable<T> {
    fn into_lc(self) -> LinearCombination<T> {
        LinearCombination {
            terms: vec![(self, T::one())],
        }
    }
}

impl<T1, T2> IntoLinearCombination<T1> for (Variable<T1>, T2)
where
    T1: ScalarValue,
    T2: ScalarValue,
    T2: Into<T1>,
{
    fn into_lc(self) -> LinearCombination<T1> {
        LinearCombination {
            terms: vec![(self.0, self.1.into())],
        }
    }
}

/// Arithmetic on linear combinations

impl<T: ScalarValue> Neg for LinearCombination<T> {
    type Output = Self;

    fn neg(mut self) -> Self {
        for (_, ref mut s) in self.terms.iter_mut() {
            *s = -*s;
        }
        self
    }
}

impl<T, B> Add<B> for LinearCombination<T>
where
    B: IntoLinearCombination<T>,
    T: ScalarValue,
{
    type Output = Self;

    fn add(mut self, other: B) -> Self {
        let other = other.into_lc();
        self.terms.extend(other.terms.into_iter());
        self
    }
}

impl<T, B> Sub<B> for LinearCombination<T>
where
    B: IntoLinearCombination<T>,
    T: ScalarValue,
{
    type Output = Self;

    fn sub(mut self, other: B) -> Self {
        self.terms
            .extend(other.into_lc().terms.into_iter().map(|(v, w)| (v, -w)));
        self
    }
}

// Multiplying a linear combination by a constant
impl<T1, T2> Mul<T2> for LinearCombination<T1>
where
    T1: ScalarValue,
    T2: ScalarValue,
    T2: Into<T1>,
{
    type Output = Self;

    fn mul(mut self, scalar: T2) -> Self {
        for (_, ref mut s) in self.terms.iter_mut() {
            *s = *s * scalar.into();
        }
        self
    }
}

// Creating linear combinations from variables

/// Adding a linear combination `lc` to a variable `v` creates a combination `v*1 + lc`.
impl<T, L> Add<L> for Variable<T>
where
    T: ScalarValue,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T>;

    fn add(self, lc: L) -> Self::Output {
        let mut lc = lc.into_lc();
        lc.terms.push((self, T::one()));
        lc
    }
}

/// Subtracting a linear combination `lc` from a variable `v` creates a combination `v*1 - lc`.
impl<T, L> Sub<L> for Variable<T>
where
    T: ScalarValue,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T>;

    fn sub(self, lc: L) -> Self::Output {
        let mut lc = lc.into_lc();
        for (_, ref mut s) in lc.terms.iter_mut() {
            *s = -*s;
        }
        lc.terms.push((self, T::one()));
        lc
    }
}

/// Multiplying a variable `v` by a scalar `a` creates a combination `v*a`.
impl<T1, T2> Mul<T2> for Variable<T1>
where
    T1: ScalarValue,
    T2: Into<T1>,
{
    type Output = LinearCombination<T1>;

    fn mul(self, scalar: T2) -> Self::Output {
        let scalar = scalar.into();
        LinearCombination {
            terms: vec![(self, scalar)],
        }
    }
}

/// Trait representing either a `Scalar` or `NoScalar` (for which arithmetic is no-op).
pub(crate) trait ZeroCostOptionalScalar:
    Mul<Scalar, Output = Self> + SubAssign + Sized + From<Scalar>
{
}

impl ZeroCostOptionalScalar for Scalar {}
impl ZeroCostOptionalScalar for NoScalar {}

/// Replacement for a scalar with zero-cost arithmetic operations
pub(crate) struct NoScalar {}

impl From<Scalar> for NoScalar {
    fn from(_: Scalar) -> Self {
        NoScalar {}
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
