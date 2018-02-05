#![feature(test)]

extern crate curve25519_dalek;
extern crate sha2;
extern crate test;
extern crate rand;
use std::iter;
use std::ops::Add;
use std::ops::Mul;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha256, Sha512};
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;

struct Degree3Poly {
    pub d0: Scalar,
    pub d1: Scalar,
    pub d2: Scalar,
}

struct RangeProof {}

impl RangeProof {
    pub fn generate_proof(
        v: u64,
        len: usize,
        a: &RistrettoPoint,
        b: &RistrettoPoint,
    ) -> RangeProof {
        let mut rng: OsRng = OsRng::new().unwrap();

        // Generate groups a, b (in the paper: groups g, h)
        let b_vec = make_generators(b, len);
        let a_vec = make_generators(a, len);

        // Compute big_a (in the paper: A; line 36-39)
        let alpha = RistrettoPoint::random(&mut rng);
        let mut big_a = alpha.clone();
        for i in 0..len {
            let v_i = (v >> i) & 1;
            if v_i == 0 {
                big_a -= a_vec[i];
            } else {
                big_a += b_vec[i];
            }
        }

        // Compute big_s (in the paper: S; line 40-42)
        let points_iter = iter::once(a).chain(b_vec.iter()).chain(a_vec.iter());
        let randomness: Vec<_> = (0..2 * len + 1).map(|_| Scalar::random(&mut rng)).collect();
        let big_s = ristretto::multiscalar_mult(&randomness, points_iter);

        // Save/label randomness (rho, s_L, s_R) to be used later
        let _rho = &randomness[0];
        let s_l = &randomness[1..len + 1];
        let s_r = &randomness[len + 1..2 * len + 1];

        // Generate y, z by committing to A, S (line 43-45)
        let (y, z) = commit(&big_a, &big_s);

        // Calculate t1, t2 (line 46)
        let mut t = Degree3Poly::new();
        let mut v_temp = v.clone();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let z2 = z * z;

        for i in 0..len {
            t.d1 += s_l[i] * exp_y * z + s_l[i] * z2 * exp_2 + s_r[i] * exp_y * (-z);
            t.d2 += s_l[i] * exp_y * s_r[i];
            // check if a_l is 0 or 1
            if v_temp & 1 == 0 {
                t.d1 -= s_l[i] * exp_y;
            } else {
                t.d1 += s_r[i] * exp_y;
            }
            v_temp = v_temp >> 1; // bit-shift v by one
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        // Generate x by committing to T_1, T_2 (line 47-51)
        let tau_1 = Scalar::random(&mut rng);
        let tau_2 = Scalar::random(&mut rng);
        let big_t_1 = b * t.d1 + a * tau_1;
        let big_t_2 = b * t.d2 + a * tau_2;
        let (x, _) = commit(&big_t_1, &big_t_2);

        unimplemented!()
    }

    pub fn verify_proof() -> Result<(), ()> {
        unimplemented!()
    }
}

impl Degree3Poly {
    pub fn new() -> Self {
        Self {
            d0: Scalar::zero(),
            d1: Scalar::zero(),
            d2: Scalar::zero(),
        }
    }
}

pub fn hadamard_product(a: Vec<Scalar>, b: Vec<Scalar>) -> Vec<Scalar> {
    let mut result = Vec::new();
    if a.len() != b.len() {
        // throw some error
    }
    for i in 0..a.len() {
        result[i] = a[i] * b[i];
    }
    result
}

pub fn inner_product(a: Vec<Scalar>, b: Vec<Scalar>) -> Scalar {
    let mut result = Scalar::zero();
    if a.len() != b.len() {
        // throw some error
    }
    for i in 0..a.len() {
        result += a[i] * b[i];
    }
    result
}

pub fn make_generators(point: &RistrettoPoint, len: usize) -> Vec<RistrettoPoint> {
    let mut generators = vec![RistrettoPoint::identity(); len];

    generators[0] = RistrettoPoint::hash_from_bytes::<Sha256>(point.compress().as_bytes());
    for i in 1..len {
        let prev = generators[i - 1].compress();
        generators[i] = RistrettoPoint::hash_from_bytes::<Sha256>(prev.as_bytes());
    }
    generators
}

pub fn commit(a: &RistrettoPoint, b: &RistrettoPoint) -> (Scalar, Scalar) {
    let mut y_digest = Sha512::new();
    y_digest.input(a.compress().as_bytes());
    y_digest.input(b.compress().as_bytes());
    let y = Scalar::from_hash(y_digest);

    let mut z_digest = Sha512::new();
    z_digest.input(a.compress().as_bytes());
    z_digest.input(b.compress().as_bytes());
    z_digest.input(y.as_bytes());
    let z = Scalar::from_hash(z_digest);

    (y, z)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_make_generators() {
        use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
        println!("{:?}", make_generators(&RISTRETTO_BASEPOINT_POINT, 20));
    }
}

mod bench {
    use super::*;
    use test::Bencher;

    #[bench]
    fn benchmark_make_generators(b: &mut Bencher) {
        use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
        b.iter(|| make_generators(&RISTRETTO_BASEPOINT_POINT, 100));
    }
}
