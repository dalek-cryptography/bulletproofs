#![allow(non_snake_case)]

use std::iter;
use sha2::{Digest, Sha256, Sha512};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);


pub struct RangeProof {
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
    pub fn generate_proof(v: u64, n: usize) -> RangeProof {
        let mut rng: OsRng = OsRng::new().unwrap();
        // useful for debugging:
        // let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);

        // Setup: generate groups g & h, commit to v (line 34)
        let g = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let h = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let g_vec = make_generators(g, n);
        let h_vec = make_generators(h, n);
        let gamma = Scalar::random(&mut rng);
        let big_v = h * gamma + g * Scalar::from_u64(v);

        // Compute big_a (line 39-42)
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

        // Compute big_s (in the paper: S; line 43-45)
        let points_iter = iter::once(h).chain(g_vec.iter()).chain(h_vec.iter());
        let randomness: Vec<_> = (0..(1 + 2 * n)).map(|_| Scalar::random(&mut rng)).collect();
        let big_s = ristretto::multiscalar_mult(&randomness, points_iter);

        // Save/label randomness (rho, s_L, s_R) to be used later
        let rho = &randomness[0];
        let s_l = &randomness[1..(n + 1)];
        let s_r = &randomness[(n + 1)..(1 + 2 * n)];

        // Generate y, z by committing to A, S (line 46-48)
        let (y, z) = commit(&big_a, &big_s);

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l = VecPoly2::new(n);
        let mut r = VecPoly2::new(n);
        let z2 = z * z;
        let mut t = PolyDeg3::new();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..n {
            let v_i = (v >> i) & 1;
            l.0[i] -= z;
            l.1[i] += s_l[i];
            r.0[i] += exp_y * z + z2 * exp_2;
            r.1[i] += exp_y * s_r[i];
            if v_i == 0 {
                r.0[i] -= exp_y;
            } else {
                l.0[i] += Scalar::one();
            }
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        t.0 = inner_product(&l.0, &r.0);
        t.2 = inner_product(&l.1, &r.1);
        // use Karatsuba algorithm to find t.1 = l.0*r.1 + l.1*r.0
        let l_add = add_vec(&l.0, &l.1);
        let r_add = add_vec(&r.0, &r.1);
        let l_r_mul = inner_product(&l_add, &r_add);
        t.1 = l_r_mul - t.0 - t.2;

        // Generate x by committing to big_t_1, big_t_2 (line 49-54)
        let tau_1 = Scalar::random(&mut rng);
        let tau_2 = Scalar::random(&mut rng);
        let big_t_1 = g * t.1 + h * tau_1;
        let big_t_2 = g * t.2 + h * tau_2;
        let (x, _) = commit(&big_t_1, &big_t_2); // TODO: use a different commit?

        // Generate final values for proof (line 55-60)
        let tau_x = tau_1 * x + tau_2 * x * x + z2 * gamma;
        let mu = alpha + rho * x;
        let t_hat = t.0 + t.1 * x + t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = l.eval(x);
        let r_total = r.eval(x);

        // Generate proof! (line 61)
        RangeProof {
            tau_x: tau_x,
            mu: mu,
            t: t_hat,
            l: l_total,
            r: r_total,

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
        let g_vec = make_generators(&self.g, self.n);
        let mut hprime_vec = make_generators(&self.h, self.n);

        // line 63: check that t = t0 + t1 * x + t2 * x * x
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..self.n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        let t_check = self.g * power_g + self.big_v * z2 + self.big_t_1 * x + self.big_t_2 * x * x;
        let t_commit = self.g * self.t + self.h * self.tau_x;
        if t_commit != t_check {
            //println!("fails check on line 63");
            return false;
        }

        // line 62: calculate hprime
        // line 64: compute commitment to l, r
        let mut sum_g_vec = RistrettoPoint::identity();
        for i in 0..self.n {
            sum_g_vec += g_vec[i];
        }
        let mut big_p = self.big_a + self.big_s * x;
        big_p -= sum_g_vec * z;

        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let inverse_y = Scalar::invert(&y);
        let mut inv_exp_y = Scalar::one(); // start at y^-0 = 1
        for i in 0..self.n {
            hprime_vec[i] = hprime_vec[i] * inv_exp_y;
            big_p += hprime_vec[i] * (z * exp_y + z2 * exp_2);
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
            inv_exp_y = inv_exp_y * inverse_y; // y^(-i) * y^(-1) -> y^(-(i+1))
        }

        // line 65: check that l, r are correct
        let mut big_p_check = self.h * self.mu;
        let points_iter = g_vec.iter().chain(hprime_vec.iter());
        let scalars_iter = self.l.iter().chain(self.r.iter());
        big_p_check += ristretto::multiscalar_mult(scalars_iter, points_iter);
        if big_p != big_p_check {
            //println!("fails check on line 65: big_p != g * l + hprime * r");
            return false;
        }

        // line 66: check that t is correct
        if self.t != inner_product(&self.l, &self.r) {
            //println!("fails check on line 66: t != l * r");
            return false;
        }

        return true;
    }
}

impl PolyDeg3 {
    pub fn new() -> PolyDeg3 {
        PolyDeg3(Scalar::zero(), Scalar::zero(), Scalar::zero())
    }
}

impl VecPoly2 {
    pub fn new(n: usize) -> VecPoly2 {
        VecPoly2(vec![Scalar::zero(); n], vec![Scalar::zero(); n])
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
    use rand::Rng;

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
    #[test]
    fn test_rp_t() {
        let rp = RangeProof::generate_proof(1, 1);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
        let rp = RangeProof::generate_proof(1, 2);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
    }
    #[test]
    fn verify_rp_simple() {
        for n in &[1, 2, 4, 8, 16, 32] {
            //println!("n: {:?}", n);
            let rp = RangeProof::generate_proof(0, *n);
            assert_eq!(rp.verify_proof(), true);
            let rp = RangeProof::generate_proof(2u64.pow(*n as u32) - 1, *n);
            assert_eq!(rp.verify_proof(), true);
            let rp = RangeProof::generate_proof(2u64.pow(*n as u32), *n);
            assert_eq!(rp.verify_proof(), false);
            let rp = RangeProof::generate_proof(2u64.pow(*n as u32) + 1, *n);
            assert_eq!(rp.verify_proof(), false);
            let rp = RangeProof::generate_proof(u64::max_value(), *n);
            assert_eq!(rp.verify_proof(), false);
        }
    }
    #[test]
    fn verify_rp_rand_big() {
        for _ in 0..50 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u64 = rng.next_u64();
            //println!("v: {:?}", v);
            let rp = RangeProof::generate_proof(v, 32);
            let expected = v <= 2u64.pow(32);
            assert_eq!(rp.verify_proof(), expected);
        }
    }
    #[test]
    fn verify_rp_rand_small() {
        for _ in 0..50 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u32 = rng.next_u32();
            //println!("v: {:?}", v);
            let rp = RangeProof::generate_proof(v as u64, 32);
            assert_eq!(rp.verify_proof(), true);
        }
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    use rand::Rng;
    use test::Bencher;

    #[bench]
    fn generators(b: &mut Bencher) {
        use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
        b.iter(|| make_generators(&RISTRETTO_BASEPOINT_POINT, 100));
    }
    #[bench]
    fn make_rp_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| RangeProof::generate_proof(rng.next_u64(), 64));
    }
    #[bench]
    fn make_rp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| RangeProof::generate_proof(rng.next_u32() as u64, 32));
    }
    #[bench]
    fn verify_rp_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = RangeProof::generate_proof(rng.next_u64(), 64);
        b.iter(|| rp.verify_proof());
    }
    #[bench]
    fn verify_rp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = RangeProof::generate_proof(rng.next_u32() as u64, 32);
        b.iter(|| rp.verify_proof());
    }
}
