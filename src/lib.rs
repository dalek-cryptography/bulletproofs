#![feature(test)]

extern crate curve25519_dalek;
extern crate sha2;
extern crate test;
extern crate rand;
use std::iter;
use curve25519_dalek::ristretto::{RistrettoPoint};
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha256};
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;


struct RangeProof {

}

impl RangeProof {
	pub fn generate_proof(v: u64, len: usize, a: &RistrettoPoint, b: &RistrettoPoint) -> RangeProof {
		let mut rng: OsRng = OsRng::new().unwrap();

		let b_vec = make_generators(b, len);
		let a_vec = make_generators(a, len);

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

		let points_iter = iter::once(a).chain(b_vec.iter()).chain(a_vec.iter());
		let randomness: Vec<_> = (0..2*len+1).map(|_| Scalar::random(&mut rng)).collect();
		let big_s = ristretto::multiscalar_mult(&randomness, points_iter);

		let _rho = &randomness[0];
		let _s_l = &randomness[1..len+1];
		let _s_r = &randomness[len+1..2*len+1];

		let (_y, _z) = commit(&big_a, &big_s);

		unimplemented!()
	}

	pub fn verify_proof() -> Result<(), ()> {
		unimplemented!()
	}
}

pub fn make_generators(point: &RistrettoPoint, len: usize) 
	-> Vec<RistrettoPoint> 
{
	let mut generators = vec![RistrettoPoint::identity(); len];

	generators[0] = RistrettoPoint::hash_from_bytes::<Sha256>(point.compress().as_bytes());
	for i in 1..len {
		let prev = generators[i-1].compress();
		generators[i] = RistrettoPoint::hash_from_bytes::<Sha256>(prev.as_bytes());
	}
	generators
}

pub fn commit(a: &RistrettoPoint, s: &RistrettoPoint) -> (RistrettoPoint, RistrettoPoint) {
	let mut y_digest = Sha256::new();
	y_digest.input(a.compress().as_bytes());
	y_digest.input(s.compress().as_bytes());
	let y = RistrettoPoint::hash_from_bytes::<Sha256>(&y_digest.result());

	let mut z_digest = Sha256::new();
	z_digest.input(a.compress().as_bytes());
	z_digest.input(s.compress().as_bytes());
	z_digest.input(y.compress().as_bytes());
	let z = RistrettoPoint::hash_from_bytes::<Sha256>(&z_digest.result());	

	(y, z)
}

#[cfg(test)]
mod tests {
	use super::*;
    #[test]
    fn test_make_generators() {
    	use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    	println!("{:?}", make_generators(RISTRETTO_BASEPOINT_POINT, 20));
    }
}

mod bench {
	use super::*;
	use test::Bencher;

	#[bench]
    fn benchmark_make_generators(b: &mut Bencher) {
    	use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    	b.iter(|| make_generators(RISTRETTO_BASEPOINT_POINT, 100));
    }
}
