// use core::ops;

// use curve25519_dalek::scalar::Scalar;

// use super::assignment::{Assignment};
// use super::constraints::Variable;
// use super::linear_combination::Variable as LCVar; // temp here until we move constant_one() to Variable
// use super::scalar_value::{ScalarValue};
// use super::opaque_scalar::OpaqueScalar;

// /// Trait representing a linear combination of variables
// pub trait LinearCombination {
//     /// Type of the scalar used in the assignment for this variable.
//     type ScalarType: ScalarValue;

//     /// Evaluates the linear combination expression.
//     fn eval(&self) -> Assignment<Self::ScalarType>;

//     /// Number of terms in this linear combination.
//     fn terms_count(&self) -> usize;

//     /// Populates the array of terms.
//     /// The slice is guaranteed to be big enough to fit `terms_count` items.
//     fn add_terms(&self, terms: &mut [(Variable<Self::ScalarType>, Self::ScalarType)]);
// }

// /// Trait for types that can be unambiguously converted to a linear combination.
// /// Variable is converted to `(var, 1)`, scalar is converted as `(One, scalar)`,
// /// tuple `(v,w)` is converted to a single term.
// pub trait IntoLinearCombination<LC: LinearCombination> {
//     /// Converts the type into a linear combination
//     fn into_lc(self) -> LC;
// }


// impl IntoLinearCombination<Constant<Scalar>> for u64 {
//     fn into_lc(self) -> Constant<Scalar> {
//         Constant(Scalar::from(self))
//     }
// }

// impl IntoLinearCombination<Constant<Scalar>> for Scalar {
//     fn into_lc(self) -> Constant<Scalar> {
//         Constant(self)
//     }
// }

// impl IntoLinearCombination<Constant<OpaqueScalar>> for OpaqueScalar {
//     fn into_lc(self) -> Constant<OpaqueScalar> {
//         Constant(self)
//     }
// }

// impl<LC,T> IntoLinearCombination<LC> for LC
// where T: ScalarValue, LC: LinearCombination<ScalarType=T>
// {
//     fn into_lc(self) -> LC {
//         self
//     }
// }

// pub struct Constant<T: ScalarValue>(T);

// impl<T> LinearCombination for Constant<T> where T: ScalarValue {
//     type ScalarType = T;

//     fn eval(&self) -> Assignment<T> {
//         Assignment::Value(self.0)
//     }

//     fn terms_count(&self) -> usize { 1 }

//     fn add_terms(&self, terms: &mut [(Variable<Self::ScalarType>, Self::ScalarType)]) {
//         terms[0] = (Variable::constant_one(), self.0)
//     }
// }

// pub struct WeightedVariable<T: ScalarValue> {
//     v: Variable<T>,
//     w: T
// }

// impl<T> LinearCombination for WeightedVariable<T> where T: ScalarValue {
//     type ScalarType = T;

//     fn eval(&self) -> Assignment<T> {
//         self.v.assignment * Assignment::Value(self.w)
//     }

//     fn terms_count(&self) -> usize { 1 }

//     fn add_terms(&self, terms: &mut [(Variable<Self::ScalarType>, Self::ScalarType)]) {
//         terms[0] = (self.v, self.w)
//     }
// }

// pub struct Add<A,B>
// where 
// A: LinearCombination,
// B: LinearCombination<ScalarType=A::ScalarType>
// {
//     a: A,
//     b: B
// }

// impl<A,B> LinearCombination for Add<A,B>
// where
// A: LinearCombination,
// B: LinearCombination<ScalarType=A::ScalarType>
// {
//     type ScalarType = A::ScalarType;

//     fn eval(&self) -> Assignment<Self::ScalarType> {
//        self.a.eval() + self.b.eval()
//     }

//     fn terms_count(&self) -> usize {
//         self.a.terms_count() + self.b.terms_count()
//     }

//     fn add_terms(&self, terms: &mut [(Variable<Self::ScalarType>, Self::ScalarType)]) {
//         self.a.add_terms(terms);
//         self.b.add_terms(&mut terms[self.a.terms_count()..]);
//     }
// }

// impl<T,B,LC> ops::Add<B> for Constant<T> where T:ScalarValue, B:IntoLinearCombination<LC>, LC:LinearCombination<ScalarType=T> {
//     type Output = Add<Constant<T>, LC>;

//     fn add(self, other: B) -> Self::Output {
//         Add { a: self, b: other.into_lc() }
//     }
// }


// // impl<A,B> ops::Add<B> for A
// // where
// // A: LinearCombination,
// // B: LinearCombination<ScalarType=A::ScalarType>
// // {
// //     type Output = Add<A,B>;

// //     fn add(self, other: B) -> Self::Output {
// //         Add { a: self, b: other }
// //     }
// // }


// // /// Linear combination of variables `V` and scalars `S` allows
// // /// building a sum of V_i*S_i.
// // /// The assignment of the variable must have the same type as the weights to simplify the constraints.
// // /// If one needs to make an LC of a clear assignment with opaque weight,
// // /// the variable needs to be converted to opaque assignment first using `into_opaque`.
// // pub struct LinearCombination<V: Variable> {
// //     /// Terms of the linear combination.
// //     pub(crate) terms: Vec<(V, V::ValueType)>,

// //     /// Precomputed evaluation of the linear combination.
// //     pub(crate) precomputed: Assignment<V::ValueType>,
// // }


// // // Implementation of IntoLC trait for various types

// // impl<V: Variable> IntoLC<V> for LinearCombination<V> {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         self
// //     }
// // }

// // impl<V: Variable> IntoLC<V> for Scalar {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         LinearCombination {
// //             terms: vec![(V::constant_one(), self.into())],
// //             precomputed: Assignment::Value(self.into())
// //         }
// //     }
// // }

// // impl<V> IntoLC<V> for OpaqueScalar where V: Variable<ValueType=OpaqueScalar> {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         LinearCombination {
// //             terms: vec![(V::constant_one(), self)],
// //             precomputed: Assignment::Value(self)
// //         }
// //     }
// // }

// // impl<V> IntoLC<V> for V where V: Variable {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         LinearCombination {
// //             precomputed: self.assignment(),
// //             terms: vec![(self, V::ValueType::one())],
// //         }
// //     }
// // }

// // impl<V> IntoLC<V> for (V, Scalar) where V: Variable, Assignment<V::ValueType>: From<Scalar> {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         LinearCombination {
// //             precomputed: self.0.assignment() * self.1,
// //             terms: vec![(self.0, self.1.into())],
// //         }
// //     }
// // }

// // impl<V> IntoLC<V> for (V, OpaqueScalar) where V: Variable<ValueType=OpaqueScalar> {
// //     fn into_lc(self) -> LinearCombination<V> {
// //         LinearCombination {
// //             precomputed: self.0.assignment() * self.1,
// //             terms: vec![(self.0, self.1)],
// //         }
// //     }
// // }

// // impl<V: Variable> LinearCombination<V> {
// //     /// Evaluates the linear combination expression.
// //     pub fn eval(&self) -> Assignment<V::ValueType> {
// //         self.precomputed
// //     }

// //     /// Converts variables in the linear combination into opaque variables
// //     pub fn into_opaque(self) -> LinearCombination<V::OpaqueType> {
// //         LinearCombination {
// //             precomputed: self.precomputed.into_opaque(),
// //             // XXX: use mem::forget + mem::transmute + Vec::from_raw_parts + packed repr for OpaqueScalar
// //             // in order to avoid additional allocation here
// //             terms: self.terms.into_iter()
// //             .map(|(v, s)| (v.into_opaque(), s.into_opaque()))
// //             .collect(),
// //         }
// //     }
// // }

// // /// Empty linear combination
// // impl<V: Variable> Default for LinearCombination<V> {
// //     fn default() -> Self {
// //         LinearCombination {
// //             terms: Vec::new(),
// //             precomputed: Assignment::Value(V::ValueType::zero()),
// //         }
// //     }
// // }

// // /// Arithmetic on linear combinations

// // impl<T, V> Add<T> for LinearCombination<V> where T: IntoLC<V>, V: Variable {
// //     type Output = Self;

// //     fn add(mut self, other: T) -> Self {
// //         let other = other.into_lc();
// //         self.precomputed += other.precomputed;
// //         self.terms.extend(other.terms.into_iter());
// //         self
// //     }
// // }

// // impl<T, V> Sub<T> for LinearCombination<V> where T: IntoLC<V>, V: Variable {
// //     type Output = Self;

// //     fn sub(mut self, other: T) -> Self {
// //         let other = other.into_lc();
// //         self.precomputed -= other.precomputed;
// //         self.terms.extend(other.terms.into_iter().map(|(v,w)| (v,-w)));
// //         self
// //     }
// // }

// // // Multiplying a linear combination by a constant
// // impl<V> Mul<V::ValueType> for LinearCombination<V> where V: Variable {
// //     type Output = Self;

// //     fn mul(mut self, scalar: V::ValueType) -> Self {
// //         self.precomputed = self.precomputed * Assignment::Value(scalar);
// //         for (_, ref mut s) in self.terms.iter_mut() {
// //             *s = *s * scalar;
// //         }
// //         self
// //     }
// // }
