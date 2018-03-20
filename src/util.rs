#![deny(missing_docs)]
#![allow(non_snake_case)]

use curve25519_dalek::scalar::Scalar;

pub struct PolyDeg3(pub Scalar, pub Scalar, pub Scalar);

impl PolyDeg3 {
    pub fn eval(&self, x: &Scalar) -> Scalar {
        self.0 + x * (self.1 + x * self.2)
    }
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
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

pub struct VecPoly2(pub Vec<Scalar>, pub Vec<Scalar>);

impl VecPoly2 {
    pub fn zero(n: usize) -> VecPoly2 {
        VecPoly2(vec![Scalar::zero(); n], vec![Scalar::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly2) -> PolyDeg3 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        PolyDeg3(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::zero(); n];
        for i in 0..n {
            out[i] += self.0[i] + self.1[i] * x;
        }
        out
    }
}

pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        // throw some error
        println!("lengths of vectors don't match for inner product multiplication");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut out = Vec::new();
    if a.len() != b.len() {
        // throw some error
        println!("lengths of vectors don't match for vector addition");
    }
    for i in 0..a.len() {
        out.push(a[i] + b[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from_u64(2)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from_u64(1));
        assert_eq!(exp_2[1], Scalar::from_u64(2));
        assert_eq!(exp_2[2], Scalar::from_u64(4));
        assert_eq!(exp_2[3], Scalar::from_u64(8));
    }

    #[test]
    fn test_inner_product() {
    let a = vec![
        Scalar::from_u64(1),
        Scalar::from_u64(2),
        Scalar::from_u64(3),
        Scalar::from_u64(4),
    ];
    let b = vec![
        Scalar::from_u64(2),
        Scalar::from_u64(3),
        Scalar::from_u64(4),
        Scalar::from_u64(5),
    ];
    assert_eq!(Scalar::from_u64(40), inner_product(&a, &b));
}
}
