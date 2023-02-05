#![deny(missing_docs)]
#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use clear_on_drop::clear::Clear;
use curve25519_dalek::scalar::Scalar;

use crate::inner_product_proof::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<Scalar>, pub Vec<Scalar>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "yoloproofs")]
pub struct VecPoly3(
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2(pub Scalar, pub Scalar, pub Scalar);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[cfg(feature = "yoloproofs")]
pub struct Poly6 {
    pub t1: Scalar,
    pub t2: Scalar,
    pub t3: Scalar,
    pub t4: Scalar,
    pub t5: Scalar,
    pub t6: Scalar,
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.len() != b.len() {
        // throw some error
        //println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![Scalar::zero(); b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![Scalar::zero(); n], vec![Scalar::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1) -> Poly2 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

#[cfg(feature = "yoloproofs")]
impl VecPoly3 {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![Scalar::zero(); n],
            vec![Scalar::zero(); n],
            vec![Scalar::zero(); n],
            vec![Scalar::zero(); n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6 {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}

impl Poly2 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        self.0 + x * (self.1 + x * self.2)
    }
}

#[cfg(feature = "yoloproofs")]
impl Poly6 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

impl Drop for VecPoly1 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.clear();
        }
        for e in self.1.iter_mut() {
            e.clear();
        }
    }
}

impl Drop for Poly2 {
    fn drop(&mut self) {
        self.0.clear();
        self.1.clear();
        self.2.clear();
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for VecPoly3 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.clear();
        }
        for e in self.1.iter_mut() {
            e.clear();
        }
        for e in self.2.iter_mut() {
            e.clear();
        }
        for e in self.3.iter_mut() {
            e.clear();
        }
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for Poly6 {
    fn drop(&mut self) {
        self.t1.clear();
        self.t2.clear();
        self.t3.clear();
        self.t4.clear();
        self.t5.clear();
        self.t6.clear();
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with `(1 to 2)*lg(n)` scalar multiplications.
/// TODO: a consttime version of this would be similar to a Montgomery ladder.
pub fn scalar_exp_vartime(x: &Scalar, mut n: u64) -> Scalar {
    let mut result = Scalar::one();
    let mut aux = *x; // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result = result * aux;
        }
        n = n >> 1;
        if n > 0 {
            aux = aux * aux;
        }
    }
    result
}

/// Computes the sum of all the powers of \\(x\\) \\(S(n) = (x^0 + \dots + x^{n-1})\\)
/// using \\(O(\lg n)\\) multiplications. Length \\(n\\) is not considered secret
/// and algorithm is fastest when \\(n\\) is the power of two (\\(2\lg n + 1\\) multiplications).
///
/// ### Algorithm description
///
/// First, let \\(n\\) be a power of two.
/// Then, we can divide the polynomial in two halves like so:
/// \\[
/// \begin{aligned}
/// S(n) &= (1+\dots+x^{n-1})                                 \\\\
///      &= (1+\dots+x^{n/2-1}) + x^{n/2} (1+\dots+x^{n/2-1}) \\\\
///      &= s + x^{n/2} s.
/// \end{aligned}
/// \\]
/// We can divide each \\(s\\) in half until we arrive to a degree-1 polynomial \\((1+x\cdot 1)\\).
/// Recursively, the total sum can be defined as:
/// \\[
/// \begin{aligned}
/// S(0)    &= 0 \\\\
/// S(n)    &= s_{\lg n} \\\\
/// s_0     &= 1 \\\\
/// s_i     &= s_{i-1} + x^{2^{i-1}} s_{i-1}
/// \end{aligned}
/// \\]
/// This representation allows us to do only \\(2 \cdot \lg n\\) multiplications:
/// squaring \\(x\\) and multiplying it by \\(s_{i-1}\\) at each iteration.
///
/// Lets apply this to \\(n\\) which is not a power of two. The intuition behind the generalized
/// algorithm is to combine all intermediate power-of-two-degree polynomials corresponding to the
/// bits of \\(n\\) that are equal to 1.
///
/// 1. Represent \\(n\\) in binary.
/// 2. For each bit which is set (from the lowest to the highest):
///    1. Compute a corresponding power-of-two-degree polynomial using the above algorithm.
///       Since we can reuse all intermediate polynomials, this adds no overhead to computing
///       a polynomial for the highest bit.
///    2. Multiply the polynomial by the next power of \\(x\\), relative to the degree of the
///       already computed result. This effectively _offsets_ the polynomial to a correct range of
///       powers, so it can be added directly with the rest.
///       The next power of \\(x\\) is computed along all the intermediate polynomials,
///       by multiplying it by power-of-two power of \\(x\\) computed in step 2.1.
///    3. Add to the result.
///
/// (\\(2^{k-1} < n < 2^k\\)) which can be represented in binary using
/// bits \\(b_i\\) in \\(\\{0,1\\}\\):
/// \\[
/// n = b_0 2^0 + \dots + b_{k-1} 2^{k-1}
/// \\]
/// If we scan the bits of \\(n\\) from low to high (\\(i \in [0,k)\\)),
/// we can conditionally (if \\(b_i = 1\\)) add to a resulting scalar
/// an intermediate polynomial with \\(2^i\\) terms using the above algorithm,
/// provided we offset the polynomial by \\(x^{n_i}\\), the next power of \\(x\\)
/// for the existing sum, where \\(n_i = \sum_{j=0}^{i-1} b_j 2^j\\).
///
/// The full algorithm becomes:
/// \\[
/// \begin{aligned}
/// S(0)    &= 0 \\\\
/// S(1)    &= 1 \\\\
/// S(i)    &= S(i-1) + x^{n_i} s_i b_i\\\\
///         &= S(i-1) + x^{n_{i-1}} (x^{2^{i-1}})^{b_{i-1}} s_i b_i
/// \end{aligned}
/// \\]
pub fn sum_of_powers(x: &Scalar, mut n: usize) -> Scalar {
    let mut result = Scalar::zero();
    let mut f = Scalar::one(); // next-power-of-x to offset subsequent polynomials based on preceding bits of n.
    let mut s = Scalar::one(); // power-of-two polynomials: (1, 1+x, 1+x+x^2+x^3, 1+...+x^7, , 1+...+x^15, ...)
    let mut p = *x; // power-of-two powers of x: (x, x^2, x^4, ..., x^{2^i})
    while n > 0 {
        // take a bit from n
        let bit = n & 1;
        n = n >> 1;

        if bit == 1 {
            // `n` is not secret, so it's okay to be vartime on bits of `n`.
            result += f * s;
            if n > 0 {
                // avoid multiplication if no bits left
                f = f * p;
            }
        }
        if n > 0 {
            // avoid multiplication if no bits left
            s = s + p * s;
            p = p * p;
        }
    }
    result
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from(1u64));
        assert_eq!(exp_2[1], Scalar::from(2u64));
        assert_eq!(exp_2[2], Scalar::from(4u64));
        assert_eq!(exp_2[3], Scalar::from(8u64));
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }

    /// Raises `x` to the power `n`.
    fn scalar_exp_vartime_slow(x: &Scalar, n: u64) -> Scalar {
        let mut result = Scalar::one();
        for _ in 0..n {
            result = result * x;
        }
        result
    }

    #[test]
    fn test_scalar_exp() {
        let x = Scalar::from_bits(
            *b"\x84\xfc\xbcOx\x12\xa0\x06\xd7\x91\xd9z:'\xdd\x1e!CE\xf7\xb1\xb9Vz\x810sD\x96\x85\xb5\x07",
        );
        assert_eq!(scalar_exp_vartime(&x, 0), Scalar::one());
        assert_eq!(scalar_exp_vartime(&x, 1), x);
        assert_eq!(scalar_exp_vartime(&x, 2), x * x);
        assert_eq!(scalar_exp_vartime(&x, 3), x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 4), x * x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 5), x * x * x * x * x);
        assert_eq!(scalar_exp_vartime(&x, 64), scalar_exp_vartime_slow(&x, 64));
        assert_eq!(
            scalar_exp_vartime(&x, 0b11001010),
            scalar_exp_vartime_slow(&x, 0b11001010)
        );
    }

    // takes the sum of all of the powers of x, up to n
    fn sum_of_powers_slow(x: &Scalar, n: usize) -> Scalar {
        exp_iter(*x).take(n).fold(Scalar::zero(), |acc, x| acc + x)
    }

    #[test]
    fn test_sum_of_powers_pow2() {
        let x = Scalar::from(1337133713371337u64);
        assert_eq!(sum_of_powers_slow(&x, 0), sum_of_powers(&x, 0));
        assert_eq!(sum_of_powers_slow(&x, 1), sum_of_powers(&x, 1));
        assert_eq!(sum_of_powers_slow(&x, 2), sum_of_powers(&x, 2));
        assert_eq!(sum_of_powers_slow(&x, 4), sum_of_powers(&x, 4));
        assert_eq!(sum_of_powers_slow(&x, 8), sum_of_powers(&x, 8));
        assert_eq!(sum_of_powers_slow(&x, 16), sum_of_powers(&x, 16));
        assert_eq!(sum_of_powers_slow(&x, 32), sum_of_powers(&x, 32));
        assert_eq!(sum_of_powers_slow(&x, 64), sum_of_powers(&x, 64));
    }

    #[test]
    fn test_sum_of_powers_non_pow2() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers(&x, 0), Scalar::zero());
        assert_eq!(sum_of_powers(&x, 1), Scalar::one());
        assert_eq!(sum_of_powers(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers(&x, 6), Scalar::from(111111u64));
        assert_eq!(sum_of_powers(&x, 7), Scalar::from(1111111u64));
        assert_eq!(sum_of_powers(&x, 8), Scalar::from(11111111u64));
    }

    #[test]
    fn vec_of_scalars_clear_on_drop() {
        let mut v = vec![Scalar::from(24u64), Scalar::from(42u64)];

        for e in v.iter_mut() {
            e.clear();
        }

        fn flat_slice<T>(x: &[T]) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x.as_ptr() as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(flat_slice(&v.as_slice()), &[0u8; 64][..]);
        assert_eq!(v[0], Scalar::zero());
        assert_eq!(v[1], Scalar::zero());
    }

    #[test]
    fn tuple_of_scalars_clear_on_drop() {
        let mut v = Poly2(
            Scalar::from(24u64),
            Scalar::from(42u64),
            Scalar::from(255u64),
        );

        v.0.clear();
        v.1.clear();
        v.2.clear();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(as_bytes(&v), &[0u8; 96][..]);
        assert_eq!(v.0, Scalar::zero());
        assert_eq!(v.1, Scalar::zero());
        assert_eq!(v.2, Scalar::zero());
    }
}
