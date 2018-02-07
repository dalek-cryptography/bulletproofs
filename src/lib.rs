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
    l: Scalar, 
    r: Scalar,

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
        g: &RistrettoPoint,
        h: &RistrettoPoint,
    ) -> RangeProof {
        // let mut rng: OsRng = OsRng::new().unwrap();
        let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);

        // Setup: generate groups g & h, commit to v
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
        let randomness: Vec<_> = (0..2 * n + 1).map(|_| Scalar::random(&mut rng)).collect();
        let big_s = ristretto::multiscalar_mult(&randomness, points_iter);

        // Save/label randomness (rho, s_L, s_R) to be used later
        let rho = &randomness[0];
        let s_l = &randomness[1..n + 1];
        let s_r = &randomness[n + 1..2 * n + 1];

        // Generate y, z by committing to A, S (line 43-45)
        let (y, z) = commit(&big_a, &big_s);

        // Calculate t (line 46)
        let mut t = Polynomial::new();
        let mut l = Polynomial::new();
        let mut r = Polynomial::new();

        let mut v_temp = v.clone();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let z2 = z * z;

        for i in 0..n {
            let a_l = v_temp & 1;
            l.0 += -z;
            l.1 += s_l[i];
            r.0 += exp_y * z + z2 * exp_2;
            r.1 += exp_y * s_r[i];
            if a_l == 0 {
                r.0 -= exp_y;
            } else {
            	l.0 += Scalar::one();
            }
            v_temp = v_temp >> 1; // bit-shift v by one
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        t.0 = l.0 * r.0;
        t.1 = l.1 * r.0 + l.0 * r.1;
        t.2 = l.1 * r.1;

        // Generate x by committing to big_t_1, big_t_2 (in the paper: T1, T2; line 47-51)
        let tau_1 = Scalar::random(&mut rng);
        let tau_2 = Scalar::random(&mut rng);
        let big_t_1 = g * t.1 + h * tau_1;
        let big_t_2 = g * t.2 + h * tau_2;
        let (x, _) = commit(&big_t_1, &big_t_2); // TODO: use a different commit

        // Generate final values for proof (line 52-54)
        let tau_x = tau_1 * x + tau_2 * x * x + z2 * gamma;
        let mu = alpha + rho * x;
        let t_total = t.0 + t.1 * x + t.2 * x * x;

        // Generate proof! (line 55-58)
        RangeProof {
            tau_x: tau_x,
            mu: mu,
            t: t_total,
            l: l.0 + l.1 * x,
            r: r.0 + r.1 * x,

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
        if self.t != self.l * self.r {
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

        // line 62

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

pub fn commit(g: &RistrettoPoint, h: &RistrettoPoint) -> (Scalar, Scalar) {
    let mut y_digest = Sha512::new();
    y_digest.input(g.compress().as_bytes());
    y_digest.input(h.compress().as_bytes());
    let c1 = Scalar::from_hash(y_digest);

    let mut z_digest = Sha512::new();
    z_digest.input(g.compress().as_bytes());
    z_digest.input(h.compress().as_bytes());
    z_digest.input(c1.as_bytes());
    let c2 = Scalar::from_hash(z_digest);

    (c1, c2)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_t() {
        let g = RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let h = RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());

        let rp = RangeProof::generate_proof(153, 10, &g, &h);
        assert_eq!(rp.t, rp.l * rp.r);
    }
    #[test]
    fn test_verify() {
        let g = RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let h = RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());

        let rp = RangeProof::generate_proof(153, 10, &b, &a);
        assert_eq!(rp.verify_proof(), true);
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
