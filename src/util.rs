#![deny(missing_docs)]
#![allow(non_snake_case)]

use curve25519_dalek::scalar::Scalar;

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
}
