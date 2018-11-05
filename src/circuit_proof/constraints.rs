#![allow(non_snake_case)]

use core::borrow::Borrow;
use core::iter;
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
    type Terms: Iterator<Item = (Variable<T>, T)> + Clone;

    /// Converts the type into a linear combination
    fn into_lc(self) -> LinearCombination<T, Self::Terms>;
}

/// Linear combination of variables `V` and scalars `S` allows
/// building a sum of V_i*S_i.
/// The assignment of the variable must have the same type as the weights to simplify the constraints.
/// If one needs to make an LC of a clear assignment with opaque weight,
/// the variable needs to be converted to opaque assignment first using `into_opaque`.
#[derive(Clone)]
pub struct LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    /// Iterator of terms (variable, weight)
    pub(crate) terms: I,
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

    pub(crate) fn make_multiplier(
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

impl<T, I> LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    /// Evaluates the linear combination expression.
    pub fn eval(&self) -> Assignment<T> {
        self.terms
            .clone()
            .fold(Assignment::Value(T::zero()), |t, (v, w)| {
                t + v.assignment * Assignment::Value(w)
            })
    }

    /// Converts variables in the linear combination into opaque variables
    pub fn into_opaque(
        self,
    ) -> LinearCombination<
        OpaqueScalar,
        impl Iterator<Item = (Variable<OpaqueScalar>, OpaqueScalar)> + Clone,
    > {
        LinearCombination {
            terms: IntoOpaque { iter: self.terms },
        }
    }

    /// Creates a `Constraint` that this linear combination equals the other linear combination.
    /// The left hand side linear combination is negated, as it is typically just one term
    /// (e.g. "variable X equals LC(A,B,C)"). This allows minimizing negations.
    pub fn equals<L>(self, lc: L) -> Constraint
    where
        L: IntoLinearCombination<T>,
    {
        (lc.into_lc() - self).into_constraint()
    }

    // Any linear combination of variables with opaque or non-opaque scalars can be converted to a Constraint
    // (which does not hold the assignments and contains only the opaque scalars for uniform representation inside CS)
    fn into_constraint(self) -> Constraint {
        Constraint(
            self.terms
                .map(|(v, s)| (v.index, s.into_opaque()))
                .collect(),
        )
    }
}

impl<T> Default for LinearCombination<T, iter::Empty<(Variable<T>, T)>>
where
    T: ScalarValue,
{
    fn default() -> Self {
        LinearCombination {
            terms: iter::empty(),
        }
    }
}

/// An iterator of terms can be wrapped into a LinearCombination type.
impl<T, I> From<I> for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    fn from(iter: I) -> Self {
        LinearCombination { terms: iter }
    }
}

// Implementation of IntoLinearCombination trait for various types

impl<T, I> IntoLinearCombination<T> for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    type Terms = I;

    fn into_lc(self) -> LinearCombination<T, I> {
        self
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for u64 {
    type Terms = iter::Once<(Variable<T>, T)>;

    fn into_lc(self) -> LinearCombination<T, Self::Terms> {
        LinearCombination {
            terms: iter::once((Variable::constant_one(), T::from(self))),
        }
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for Scalar {
    type Terms = iter::Once<(Variable<T>, T)>;

    fn into_lc(self) -> LinearCombination<T, Self::Terms> {
        LinearCombination {
            terms: iter::once((Variable::constant_one(), T::from(self))),
        }
    }
}

impl IntoLinearCombination<OpaqueScalar> for OpaqueScalar {
    type Terms = iter::Once<(Variable<OpaqueScalar>, OpaqueScalar)>;

    fn into_lc(self) -> LinearCombination<OpaqueScalar, Self::Terms> {
        LinearCombination {
            terms: iter::once((Variable::constant_one(), self)),
        }
    }
}

impl<T: ScalarValue> IntoLinearCombination<T> for Variable<T> {
    type Terms = iter::Once<(Variable<T>, T)>;

    fn into_lc(self) -> LinearCombination<T, Self::Terms> {
        LinearCombination {
            terms: iter::once((self, T::one())),
        }
    }
}

impl<T, S> IntoLinearCombination<T> for (Variable<T>, S)
where
    T: ScalarValue,
    T: ScalarValue,
    S: Into<T>,
{
    type Terms = iter::Once<(Variable<T>, T)>;

    fn into_lc(self) -> LinearCombination<T, Self::Terms> {
        LinearCombination {
            terms: iter::once((self.0, self.1.into())),
        }
    }
}

/// Arithmetic on linear combinations

impl<T, I> Neg for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    type Output = LinearCombination<T, Negate<I>>;

    fn neg(self) -> Self::Output {
        LinearCombination {
            terms: Negate { iter: self.terms },
        }
    }
}

impl<T, I, L> Add<L> for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T, iter::Chain<I, L::Terms>>;

    fn add(self, other: L) -> Self::Output {
        LinearCombination {
            terms: self.terms.chain(other.into_lc().terms),
        }
    }
}

impl<T, I, L> Sub<L> for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T, iter::Chain<I, Negate<L::Terms>>>;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination {
            terms: self.terms.chain(Negate {
                iter: other.into_lc().terms,
            }),
        }
    }
}

// Multiplying a linear combination by a constant
impl<T, I, T2> Mul<T2> for LinearCombination<T, I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
    T2: ScalarValue,
    T2: Into<T>,
{
    type Output = LinearCombination<T, MulByConstant<I, T>>;

    fn mul(self, scalar: T2) -> Self::Output {
        let scalar = scalar.into();
        LinearCombination {
            terms: MulByConstant {
                scalar,
                iter: self.terms,
            },
        }
    }
}

// Combinators for LC operations

#[derive(Clone)]
pub struct IntoOpaque<I> {
    iter: I,
}

impl<T, I> Iterator for IntoOpaque<I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    type Item = (Variable<OpaqueScalar>, OpaqueScalar);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(v, w)| (v.into_opaque(), w.into_opaque()))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Clone)]
pub struct Negate<I> {
    iter: I,
}

impl<T, I> Iterator for Negate<I>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(v, w)| (v, -w))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Clone)]
pub struct MulByConstant<I, T> {
    iter: I,
    scalar: T,
}

impl<T, I> Iterator for MulByConstant<I, T>
where
    T: ScalarValue,
    I: Iterator<Item = (Variable<T>, T)> + Clone,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(v, w)| (v, w * self.scalar))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// Creating linear combinations from variables

/// Adding a linear combination `lc` to a variable `v` creates a combination `v*1 + lc`.
impl<T, L> Add<L> for Variable<T>
where
    T: ScalarValue,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T, iter::Chain<iter::Once<(Variable<T>, T)>, L::Terms>>;

    fn add(self, lc: L) -> Self::Output {
        self.into_lc() + lc
    }
}

/// Subtracting a linear combination `lc` from a variable `v` creates a combination `v*1 - lc`.
impl<T, L> Sub<L> for Variable<T>
where
    T: ScalarValue,
    L: IntoLinearCombination<T>,
{
    type Output = LinearCombination<T, iter::Chain<iter::Once<(Variable<T>, T)>, Negate<L::Terms>>>;

    fn sub(self, lc: L) -> Self::Output {
        self.into_lc() - lc
    }
}

/// Multiplying a variable `v` by a scalar `a` creates a combination `v*a`.
impl<T, T2> Mul<T2> for Variable<T>
where
    T: ScalarValue,
    T2: Into<T>,
{
    type Output = LinearCombination<T, MulByConstant<iter::Once<(Variable<T>, T)>, T>>;

    fn mul(self, scalar: T2) -> Self::Output {
        self.into_lc() * scalar.into()
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
