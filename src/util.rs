#![deny(missing_docs)]
#![allow(non_snake_case)]

extern crate alloc;

use alloc::{vec, vec::Vec};
use std::cmp::{max, min};

use curve25519_dalek::scalar::Scalar;
use zeroize::Zeroize;

use crate::inner_product_proof::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<Scalar>, pub Vec<Scalar>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "yoloproofs")]
pub struct VecPoly3(pub Vec<Scalar>, pub Vec<Scalar>, pub Vec<Scalar>, pub Vec<Scalar>);

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
    let next_exp_x = Scalar::ONE;
    ScalarExp { x, next_exp_x }
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.len() != b.len() {
        // throw some error
        // println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![Scalar::ZERO; b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![Scalar::ZERO; n], vec![Scalar::ZERO; n])
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
        let mut out = vec![Scalar::ZERO; n];
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
            vec![Scalar::ZERO; n],
            vec![Scalar::ZERO; n],
            vec![Scalar::ZERO; n],
            vec![Scalar::ZERO; n],
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

        Poly6 { t1, t2, t3, t4, t5, t6 }
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::ZERO; n];
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
            e.zeroize();
        }
        for e in self.1.iter_mut() {
            e.zeroize();
        }
    }
}

impl Drop for Poly2 {
    fn drop(&mut self) {
        self.0.zeroize();
        self.1.zeroize();
        self.2.zeroize();
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for VecPoly3 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.zeroize();
        }
        for e in self.1.iter_mut() {
            e.zeroize();
        }
        for e in self.2.iter_mut() {
            e.zeroize();
        }
        for e in self.3.iter_mut() {
            e.zeroize();
        }
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for Poly6 {
    fn drop(&mut self) {
        self.t1.zeroize();
        self.t2.zeroize();
        self.t3.zeroize();
        self.t4.zeroize();
        self.t5.zeroize();
        self.t6.zeroize();
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a consttime version of this would be awfully similar to a Montgomery ladder.
pub fn scalar_exp_vartime(x: &Scalar, mut n: u64) -> Scalar {
    let mut result = Scalar::ONE;
    let mut aux = *x; // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result = result * aux;
        }
        n = n >> 1;
        aux = aux * aux; // FIXME: one unnecessary mult at the last step here!
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers(x: &Scalar, n: usize) -> Scalar {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return Scalar::from(n as u64);
    }
    let mut m = n;
    let mut result = Scalar::ONE + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m = m / 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow(x: &Scalar, n: usize) -> Scalar {
    exp_iter(*x).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

/// Converts Vec<u8> of bytes to Vec<u8> representing its bits.
pub fn bytes_to_bits(bytes: &[u8]) -> Vec<u8> {
    let mut bits = vec![0u8; bytes.len() * 8];
    for i in 0..(bytes.len() * 8) {
        // As i runs from 0..(bytes.len() * 8), the bottom 3 bits index the bit,
        // while the upper bits index the byte.
        bits[i] = ((bytes[i >> 3] >> (i & 7) as u8) & 1u8) as u8;
    }
    bits
}

/// Converts up to 64 bits of a little endian bit vector, represented
/// by Vec<u8>, to usize.
pub fn bits_to_usize(bits: &[u8]) -> usize {
    let end_bit = min(bits.len(), 64);
    let mut result = bits[0] as usize;
    for (i, bit) in bits.iter().enumerate().take(end_bit).skip(1) {
        if *bit != 0 {
            result += (2u64 << (i - 1) as u64) as usize;
        }
    }
    result
}

/// Converts up to 16 bytes of a little endian byte vector to usize,
/// from start byte to end byte inclusive.
pub fn bytes_to_usize(bytes: &[u8], start_byte: usize, end_byte: usize) -> usize {
    // bytes to bits to vector
    let bits = bytes_to_bits(&bytes);
    // Apply usize limits
    let start_byte = max(start_byte, 1);
    let end_byte = min(bytes.len(), end_byte);
    let end_byte = start_byte + min(end_byte - start_byte + 1, 16) - 1;
    let start_bit_index = (start_byte - 1) * 8;
    let end_bit_index = end_byte * 8;
    // bits to usize using bit vector
    let bits = bits[start_bit_index..end_bit_index].to_vec();
    bits_to_usize(&bits)
}

/// XOR two 32 byte sized vectors of u8.
pub fn xor_32_bytes(vec1: &[u8; 32], vec2: &[u8; 32]) -> [u8; 32] {
    let xor_vec: Vec<u8> = vec1
        .iter()
        .zip(vec2.iter())
        .map(|(&x1, &x2)| {
            let byte1_bits = bytes_to_bits(&[x1]);
            let byte2_bits = bytes_to_bits(&[x2]);
            let bits: Vec<u8> = byte1_bits
                .iter()
                .zip(byte2_bits.iter())
                .map(|(&x1, &x2)| match (&x1, &x2) {
                    (1, 0) | (0, 1) => 1,
                    _ => 0,
                })
                .collect();
            bits_to_usize(&bits) as u8
        })
        .collect();
    add_bytes_to_word([0u8; 32], &xor_vec, 0)
}

/// Add bytes to a 32 byte word (overwrite contents) from a specified array position
pub fn add_bytes_to_word(mut word: [u8; 32], bytes: &[u8], array_position: usize) -> [u8; 32] {
    for (place, element) in word.iter_mut().skip(array_position).zip(bytes.iter()) {
        *place = *element;
    }
    word
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
        let mut result = Scalar::ONE;
        for _ in 0..n {
            result = result * x;
        }
        result
    }

    #[test]
    fn test_scalar_exp() {
        let x = Scalar::from_bytes_mod_order(
            *b"\x84\xfc\xbcOx\x12\xa0\x06\xd7\x91\xd9z:'\xdd\x1e!CE\xf7\xb1\xb9Vz\x810sD\x96\x85\xb5\x07",
        );
        assert_eq!(scalar_exp_vartime(&x, 0), Scalar::ONE);
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

    #[test]
    fn test_sum_of_powers() {
        let x = Scalar::from(10u64);
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
    fn test_sum_of_powers_slow() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), Scalar::ZERO);
        assert_eq!(sum_of_powers_slow(&x, 1), Scalar::ONE);
        assert_eq!(sum_of_powers_slow(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow(&x, 6), Scalar::from(111111u64));
    }

    #[test]
    fn vec_of_scalars_zeroize() {
        let mut v = vec![Scalar::from(24u64), Scalar::from(42u64)];

        for e in v.iter_mut() {
            e.zeroize();
        }

        fn flat_slice<T>(x: &[T]) -> &[u8] {
            use core::{mem, slice};

            unsafe { slice::from_raw_parts(x.as_ptr() as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(flat_slice(&v.as_slice()), &[0u8; 64][..]);
        assert_eq!(v[0], Scalar::ZERO);
        assert_eq!(v[1], Scalar::ZERO);
    }

    #[test]
    fn tuple_of_scalars_zeroize() {
        let mut v = Poly2(Scalar::from(24u64), Scalar::from(42u64), Scalar::from(255u64));

        v.0.zeroize();
        v.1.zeroize();
        v.2.zeroize();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use core::{mem, slice};

            unsafe { slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(as_bytes(&v), &[0u8; 96][..]);
        assert_eq!(v.0, Scalar::ZERO);
        assert_eq!(v.1, Scalar::ZERO);
        assert_eq!(v.2, Scalar::ZERO);
    }

    #[test]
    fn test_bytes_to_bits() {
        let byte_vec: Vec<u8> = [
            21, 205, 91, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();

        let bit_vec = bytes_to_bits(&[byte_vec[0]]);
        assert_eq!(bit_vec, [1, 0, 1, 0, 1, 0, 0, 0].to_vec());

        let bit_vec = bytes_to_bits(&byte_vec[0..2]);
        assert_eq!(bit_vec, [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1].to_vec());

        let bit_vec = bytes_to_bits(&byte_vec[2..4]);
        assert_eq!(bit_vec, [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0].to_vec());

        let bit_vec = bytes_to_bits(&byte_vec[3..6]);
        assert_eq!(
            bit_vec,
            [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec()
        );
    }

    #[test]
    fn test_bits_to_usize() {
        // Test lower bounds
        let bit_vec: Vec<u8> = [0].to_vec();
        assert_eq!(bits_to_usize(&bit_vec), 0);

        let bit_vec: Vec<u8> = [1, 0, 1].to_vec();
        assert_eq!(bits_to_usize(&bit_vec), 5);

        let bit_vec: Vec<u8> = [
            1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1,
        ]
        .to_vec();
        assert_eq!(bits_to_usize(&bit_vec), 123456789);

        let bit_vec: Vec<u8> = [
            1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bits_to_usize(&bit_vec), 123456789);

        // Test upper bounds
        let bit_vec: Vec<u8> = [
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        ]
        .to_vec();
        assert_eq!(bits_to_usize(&bit_vec), std::usize::MAX);

        let bit_vec: Vec<u8> = [
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        ]
        .to_vec();
        assert_eq!(bits_to_usize(&bit_vec), std::usize::MAX);
    }

    #[test]
    fn test_bytes_to_usize() {
        // Test lower bounds
        let byte_vec: Vec<u8> = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, 1), 0);

        let byte_vec: Vec<u8> = [
            255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, 1), 255);

        let byte_vec: Vec<u8> = [
            21, 205, 91, 7, 22, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, 4), 123456789);

        let byte_vec: Vec<u8> = [
            21, 205, 91, 7, 22, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 5, 6), 8470);

        let byte_vec: Vec<u8> = [
            21, 205, 91, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, 4), 123456789);

        // Test upper bounds
        let byte_vec: Vec<u8> = [
            255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, 8), std::usize::MAX);

        let byte_vec: Vec<u8> = [
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        ]
        .to_vec();
        assert_eq!(bytes_to_usize(&byte_vec, 1, byte_vec.len()), std::usize::MAX);
    }

    #[test]
    fn test_xor_32_bytes() {
        let vec1: [u8; 32] = [
            88, 38, 63, 128, 120, 246, 179, 65, 172, 254, 213, 32, 26, 126, 42, 168, 25, 172, 68, 174, 13, 24, 30, 83,
            187, 187, 147, 104, 226, 85, 95, 15,
        ];
        let vec2: [u8; 32] = [
            21, 205, 91, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];

        let vec3 = xor_32_bytes(&vec1, &vec2);
        assert_ne!(vec1, vec2);
        assert_ne!(vec1, vec3);
        assert_ne!(vec2, vec3);

        let vec3_xor_vec1 = xor_32_bytes(&vec3, &vec1);
        assert_eq!(vec3_xor_vec1, vec2);

        let vec3_xor_vec2 = xor_32_bytes(&vec3, &vec2);
        assert_eq!(vec3_xor_vec2, vec1);
    }

    #[test]
    fn test_add_bytes_to_word() {
        let vec1: [u8; 32] = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
            30, 31, 32,
        ];
        let vec2: [u8; 4] = [101, 102, 103, 104];

        let mut word = add_bytes_to_word(vec1, &vec2.to_vec(), 0);
        assert_eq!(word, [
            101, 102, 103, 104, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
            28, 29, 30, 31, 32
        ]);
        word = add_bytes_to_word(word, &vec2.to_vec(), 8);
        assert_eq!(word, [
            101, 102, 103, 104, 5, 6, 7, 8, 101, 102, 103, 104, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
            27, 28, 29, 30, 31, 32
        ]);
        word = add_bytes_to_word(word, &vec2.to_vec(), 16);
        assert_eq!(word, [
            101, 102, 103, 104, 5, 6, 7, 8, 101, 102, 103, 104, 13, 14, 15, 16, 101, 102, 103, 104, 21, 22, 23, 24, 25,
            26, 27, 28, 29, 30, 31, 32
        ]);
        word = add_bytes_to_word(word, &vec2.to_vec(), 24);
        assert_eq!(word, [
            101, 102, 103, 104, 5, 6, 7, 8, 101, 102, 103, 104, 13, 14, 15, 16, 101, 102, 103, 104, 21, 22, 23, 24,
            101, 102, 103, 104, 29, 30, 31, 32
        ]);
    }
}
