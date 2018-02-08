#![feature(test)]

extern crate curve25519_dalek;
extern crate sha2;
extern crate test;
extern crate rand;
use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha256, Sha512};
use curve25519_dalek::scalar::Scalar;
// use rand::OsRng;
use rand::SeedableRng;
use rand::StdRng;

struct Polynomial(Scalar, Scalar, Scalar);

struct RangeProof {
    tau_x: Scalar,
    mu: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>, 
    r: Vec<Scalar>,

    // committed values
    big_v: RistrettoPoint,
    big_a: RistrettoPoint,
    big_s: RistrettoPoint,
    big_t_1: RistrettoPoint,
    big_t_2: RistrettoPoint,

    // public knowledge
    n: usize,
    g: RistrettoPoint,
    h: RistrettoPoint,
}

impl RangeProof {

    pub fn generate_proof(
        v: u64,
        n: usize,
    ) -> RangeProof {
        // let mut rng: OsRng = OsRng::new().unwrap();
        let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);


        // Setup: generate groups g & h, commit to v
        let g = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let h = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let g_vec = make_generators(g, n);
        let h_vec = make_generators(h, n);
        let gamma = Scalar::random(&mut rng);
        let big_v = h * gamma + g * Scalar::from_u64(v);

        // Compute big_a (in the paper: A; line 36-39)
        let alpha = Scalar::random(&mut rng);
        let mut big_a = h * alpha;
        for i in 0..n {
            let v_i = (v >> i) & 1;
            if v_i == 0 {
                big_a -= h_vec[i];
            } else {
                big_a += g_vec[i];
            }
        }

        // Compute big_s (in the paper: S; line 40-42)
        let points_iter = iter::once(h).chain(g_vec.iter()).chain(h_vec.iter());
        let randomness: Vec<_> = (0..(1 + 2 * n)).map(|_| Scalar::random(&mut rng)).collect();
        let big_s = ristretto::multiscalar_mult(&randomness, points_iter);

        // Save/label randomness (rho, s_L, s_R) to be used later
        let rho = &randomness[0];
        let s_l = &randomness[1..(n + 1)];
        let s_r = &randomness[(n + 1)..(1 + 2 * n)];

        // Generate y, z by committing to A, S (line 43-45)
        let (y, z) = commit(&big_a, &big_s);

        // Calculate t (line 46)

        // APPROACH 1 TO CALCULATING T:
        // calculate vectors l0, l1, r0, r1 and multiply
        let mut l0 = vec![Scalar::zero(); n];
        let mut l1 = vec![Scalar::zero(); n];
        let mut r0 = vec![Scalar::zero(); n];
        let mut r1 = vec![Scalar::zero(); n];
        let mut t = Polynomial::new();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1

        for i in 0..n {
        	let v_i = (v >> i) & 1;
        	let a_l = Scalar::from_u64(v_i);
        	let a_r = a_l - Scalar::one();

            l0[i] += a_l - z;
            l1[i] += s_l[i];
            r0[i] += exp_y * (a_r + z) + z * z * exp_2;
            r1[i] += exp_y * s_r[i];
            println!("v_i at position {:?}: {:?}", i, v_i);
            // if v_i == 0 {
            //     r0[i] -= exp_y;
            // } else {
            // 	   l0[i] += Scalar::one();
            // }
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        t.0 = inner_product(&l0, &r0);
        t.1 = inner_product(&l0, &r1) + inner_product(&l1, &r0);
        t.2 = inner_product(&l1, &r1);
        println!("t0: {:?}", t.0);
        println!("t1: {:?}", t.1);
        println!("t2: {:?}", t.2);

        // let mut t2 = Polynomial::new();
        // for i in 0..n {
        // 	t2.0 += l0[i] * r0[i];
        // 	t2.1 += l0[i] * r1[i] + l1[i] * r0[i];
        // 	t2.2 += l1[i] * r1[i];
        // }

        // println!("t2_0: {:?}", t2.0);
        // println!("t2_1: {:?}", t2.1);
        // println!("t2_2: {:?}", t2.2);

		/*
        // APPROACH 2 TO CALCULATING T:
        // calculate scalars t0, t1, t2 seperately
        let mut t = Polynomial::new();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let z2 = z * z;
        let z3 = z2 * z;

        for i in 0..n {
        	let v_i = (v >> i) & 1;
            t.0 += exp_y * (z - z2) - z3 * exp_2;
            t.1 += s_l[i] * exp_y * z + s_l[i] * z2 * exp_2 + s_r[i] * exp_y * (-z);
            t.2 += s_l[i] * exp_y * s_r[i];
            // check if a_l is 0 or 1
            if v_i == 0 {
                t.1 -= s_l[i] * exp_y;
            } else {
                t.0 += z2 * exp_2;
                t.1 += s_r[i] * exp_y;
            }
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        println!("t0: {:?}", t.0);
        println!("t1: {:?}", t.1);
        println!("t2: {:?}", t.2);
        */

        // Generate x by committing to big_t_1, big_t_2 (in the paper: T1, T2; line 47-51)
        let tau_1 = Scalar::random(&mut rng);
        let tau_2 = Scalar::random(&mut rng);
        let big_t_1 = g * t.1 + h * tau_1;
        let big_t_2 = g * t.2 + h * tau_2;
        let (x, _) = commit(&big_t_1, &big_t_2); // TODO: use a different commit?

        // Generate final values for proof (line 52-54)
        let tau_x = tau_1 * x + tau_2 * x * x + z * z * gamma;
        let mu = alpha + rho * x;
        let t_total = t.0 + t.1 * x + t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later

        let mut l = vec![Scalar::zero(); n];
        let mut r = vec![Scalar::zero(); n];

        /* 
        // APPROACH 1 TO CALCULATING l, r
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..n {
        	let a_l = (v >> i) & 1;

            // is it ok to convert a_l to scalar?
            l += Scalar::from_u64(a_l) - z + s_l[i] * x;
            r += exp_y * (z + s_r[i] * x) + z * z * exp_2;
            if a_l == 0 {
                r -= exp_y
            }
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        } 
        */
        
        // APPROACH 2 TO CALCULATING l, r
        for i in 0..n {
        	l[i] += l0[i] + l1[i] * x;
        	r[i] += r0[i] + r1[i] * x;
        }

        // Generate proof! (line 58)
        RangeProof {
            tau_x: tau_x,
            mu: mu,
            t: t_total,
            l: l,
            r: r,

			big_v: big_v,
            big_a: big_a,
            big_s: big_s,
            big_t_1: big_t_1,
            big_t_2: big_t_2,

            n: n,
            g: *g,
            h: *h,
        }
    }

    pub fn verify_proof(&self) -> bool {
    	let (y, z) = commit(&self.big_a, &self.big_s);
    	let (x, _) = commit(&self.big_t_1, &self.big_t_2);

        // line 60
        if self.t != inner_product(&self.l, &self.r) {
        	println!("fails check on line 60: t != l * r");
            return false
        }

        // line 61
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
		let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1

        for _ in 0..self.n {
        	power_g += -z2 * exp_y - z3 * exp_2 + z * exp_y;

       	    exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1) 	
        }


        let t_check = self.g * power_g + self.big_v * z2 + self.big_t_1 * x + self.big_t_2 * x * x;
        let t_commit = self.g * self.t + self.h * self.tau_x;
        if t_commit != t_check {
        	println!("fails check on line 61");
        	return false
        }

        return true
    }
}

impl Polynomial {
    pub fn new() -> Polynomial {
        Polynomial(Scalar::zero(), Scalar::zero(), Scalar::zero())
    }
}

pub fn make_generators(point: &RistrettoPoint, n: usize) -> Vec<RistrettoPoint> {
    let mut generators = vec![RistrettoPoint::identity(); n];

    generators[0] = RistrettoPoint::hash_from_bytes::<Sha256>(point.compress().as_bytes());
    for i in 1..n {
        let prev = generators[i - 1].compress();
        generators[i] = RistrettoPoint::hash_from_bytes::<Sha256>(prev.as_bytes());
    }
    generators
}

pub fn commit(v1: &RistrettoPoint, v2: &RistrettoPoint) -> (Scalar, Scalar) {
    let mut c1_digest = Sha512::new();
    c1_digest.input(v1.compress().as_bytes());
    c1_digest.input(v2.compress().as_bytes());
    let c1 = Scalar::from_hash(c1_digest);

    let mut c2_digest = Sha512::new();
    c2_digest.input(v1.compress().as_bytes());
    c2_digest.input(v2.compress().as_bytes());
    c2_digest.input(c1.as_bytes());
    let c2 = Scalar::from_hash(c2_digest);

    (c1, c2)
}

pub fn inner_product(a: &Vec<Scalar>, b: &Vec<Scalar>) -> Scalar {
	let mut result = Scalar::zero();
	if a.len() != b.len() {
		// throw some error
	}
	for i in 0..a.len() {
		result += a[i] * b[i];
	}
	result
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_inner_product() {
    	let a = vec![Scalar::from_u64(1), Scalar::from_u64(2), Scalar::from_u64(3), Scalar::from_u64(4)];
    	let b = vec![Scalar::from_u64(2), Scalar::from_u64(3), Scalar::from_u64(4), Scalar::from_u64(5)];
    	assert_eq!(Scalar::from_u64(40), inner_product(&a, &b));
    }
    #[test]
    fn test_t() {
        let rp = RangeProof::generate_proof(1, 1);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
        let rp = RangeProof::generate_proof(1, 2);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
    }
    #[test]
    fn test_verify_one() {
        let rp = RangeProof::generate_proof(0, 1);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(1, 1);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(2, 1);
        assert_eq!(rp.verify_proof(), false);
        let rp = RangeProof::generate_proof(3, 1);
        assert_eq!(rp.verify_proof(), false);
    }
    #[test]
    fn test_verify_two() {
        let rp = RangeProof::generate_proof(0, 2);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(1, 2);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(3, 2);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(4, 2);
        assert_eq!(rp.verify_proof(), false);
        let rp = RangeProof::generate_proof(8, 2);
        assert_eq!(rp.verify_proof(), false);
    }
    #[test]
    fn test_verify_large() {
        let rp = RangeProof::generate_proof(250, 8);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(300, 8);
        assert_eq!(rp.verify_proof(), false);
        let rp = RangeProof::generate_proof(1000000, 20);
        assert_eq!(rp.verify_proof(), true);
        let rp = RangeProof::generate_proof(1050000, 20);
        assert_eq!(rp.verify_proof(), false);    	
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
