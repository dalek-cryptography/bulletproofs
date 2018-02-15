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
    t_x_blinding: Scalar,
    e_blinding: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>,
    r: Vec<Scalar>,

    // committed values
    V: RistrettoPoint,
    A: RistrettoPoint,
    S: RistrettoPoint,
    T_1: RistrettoPoint,
    T_2: RistrettoPoint,

    // public knowledge
    n: usize,
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,
}

impl RangeProof {
    pub fn generate_proof(v: u64, n: usize) -> RangeProof {
        let mut rng: OsRng = OsRng::new().unwrap();
        // useful for debugging:
        // let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);

        // Setup: generate points, commit to v (in the paper: g, h, bold(g), bolg(h); line 34)
        let B = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let B_blinding = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G = make_generators(B, n);
        let H = make_generators(B_blinding, n);
        let v_blinding = Scalar::random(&mut rng);
        let V = B_blinding * v_blinding + B * Scalar::from_u64(v);

        // Compute A (line 39-42)
        let a_blinding = Scalar::random(&mut rng);
        let mut A = B_blinding * a_blinding;
        for i in 0..n {
            let v_i = (v >> i) & 1;
            if v_i == 0 {
                A -= H[i];
            } else {
                A += G[i];
            }
        }

        // Compute S (line 43-45)
        let points_iter = iter::once(B_blinding).chain(G.iter()).chain(H.iter());
        let randomness: Vec<_> = (0..(1 + 2 * n)).map(|_| Scalar::random(&mut rng)).collect();
        let S = ristretto::multiscalar_mult(&randomness, points_iter);

        // Save/label randomness to be used later (in the paper: rho, s_L, s_R)
        let s_blinding = &randomness[0];
        let s_a = &randomness[1..(n + 1)];
        let s_b = &randomness[(n + 1)..(1 + 2 * n)];

        // Generate y, z by committing to A, S (line 46-48)
        let (y, z) = commit(&A, &S);

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
            l.1[i] += s_a[i];
            r.0[i] += exp_y * z + z2 * exp_2;
            r.1[i] += exp_y * s_b[i];
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

        // Generate x by committing to T_1, T_2 (line 49-54)
        let t_1_blinding = Scalar::random(&mut rng);
        let t_2_blinding = Scalar::random(&mut rng);
        let T_1 = B * t.1 + B_blinding * t_1_blinding;
        let T_2 = B * t.2 + B_blinding * t_2_blinding;
        let (x, _) = commit(&T_1, &T_2); // TODO: use a different commit?

        // Generate final values for proof (line 55-60)
        let t_x_blinding = t_1_blinding * x + t_2_blinding * x * x + z2 * v_blinding;
        let e_blinding = a_blinding + s_blinding * x;
        let t_hat = t.0 + t.1 * x + t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = l.eval(x);
        let r_total = r.eval(x);

        // Generate proof! (line 61)
        RangeProof {
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,

            V: V,
            A: A,
            S: S,
            T_1: T_1,
            T_2: T_2,

            n: n,
            B: *B,
            B_blinding: *B_blinding,
        }
    }

    pub fn verify_proof(&self) -> bool {
        let (y, z) = commit(&self.A, &self.S);
        let (x, _) = commit(&self.T_1, &self.T_2);
        let G = make_generators(&self.B, self.n);
        let mut hprime_vec = make_generators(&self.B_blinding, self.n);

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
        let t_check = self.B * power_g + self.V * z2 + self.T_1 * x + self.T_2 * x * x;
        let t_commit = self.B * self.t + self.B_blinding * self.t_x_blinding;
        if t_commit != t_check {
            //println!("fails check on line 63");
            return false;
        }

        // line 62: calculate hprime
        // line 64: compute commitment to l, r
        let mut sum_G = RistrettoPoint::identity();
        for i in 0..self.n {
            sum_G += G[i];
        }
        let mut big_p = self.A + self.S * x;
        big_p -= sum_G * z;

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
        let mut big_p_check = self.B_blinding * self.e_blinding;
        let points_iter = G.iter().chain(hprime_vec.iter());
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

pub fn inner_product(a: &Vec<Scalar>, b: &Vec<Scalar>) -> Scalar {
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

pub fn add_vec(a: &Vec<Scalar>, b: &Vec<Scalar>) -> Vec<Scalar> {
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
    fn test_t() {
        let rp = RangeProof::generate_proof(1, 1);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
        let rp = RangeProof::generate_proof(1, 2);
        assert_eq!(rp.t, inner_product(&rp.l, &rp.r));
    }
    #[test]
    fn test_verify_simple() {
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
    fn test_verify_rand_big() {
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
    fn test_verify_rand_small() {
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
    fn benchmark_make_generators(b: &mut Bencher) {
        use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
        b.iter(|| make_generators(&RISTRETTO_BASEPOINT_POINT, 100));
    }
    #[bench]
    fn benchmark_make_proof_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| RangeProof::generate_proof(rng.next_u64(), 64));
    }
    #[bench]
    fn benchmark_make_proof_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| RangeProof::generate_proof(rng.next_u32() as u64, 32));
    }
    #[bench]
    fn benchmark_verify_proof_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = RangeProof::generate_proof(rng.next_u64(), 64);
        b.iter(|| rp.verify_proof());
    }
    #[bench]
    fn benchmark_verify_proof_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = RangeProof::generate_proof(rng.next_u32() as u64, 32);
        b.iter(|| rp.verify_proof());
    }
}
