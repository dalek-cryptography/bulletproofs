#![allow(non_snake_case)]

use std::iter;
use sha2::{Digest, Sha256, Sha512};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;
use range_proof::{make_generators, inner_product, add_vec};

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

pub struct Generators {
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,
    G: Vec<RistrettoPoint>,
    H: Vec<RistrettoPoint>,
    n: usize,
}

pub struct State1 {
    // committed values (public)
    pub V: RistrettoPoint,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,

    // intermediate values (private)
    v_blinding: Scalar,
    a_blinding: Scalar,
    randomness: Vec<Scalar>,
    v: u64,

    // public knowledge
    n: usize,
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,   
}

pub struct State2 {
    // committed values (public)
    V: RistrettoPoint, // TBD: do we still need to save V, A, S? The've been committed/sent already...
    A: RistrettoPoint,
    S: RistrettoPoint,
    pub T_1: RistrettoPoint,
    pub T_2: RistrettoPoint,

    // intermediate values (private)
    y: Scalar,
    z: Scalar,
    l: VecPoly2,
    r: VecPoly2,
    t: PolyDeg3,
    v_blinding: Scalar,
    a_blinding: Scalar,
    s_blinding: Scalar,
    t_1_blinding: Scalar,
    t_2_blinding: Scalar,

    // public knowledge
    n: usize,
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,     
}

pub struct State3 {
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


impl Generators {
    pub fn make(n: usize) -> Generators {
        let B = RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let B_blinding = RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        Generators {
            B: B,
            B_blinding: B_blinding,
            G: make_generators(&B, n),
            H: make_generators(&B_blinding, n),
            n: n,
        }
    }

    pub fn prove(&self, v: u64) -> State1 {
        let mut rng: OsRng = OsRng::new().unwrap();
        // useful for debugging:
        // let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]); 

        // Compute V
        let v_blinding = Scalar::random(&mut rng);
        let V = self.B_blinding * v_blinding + self.B * Scalar::from_u64(v);

        // Compute A
        let a_blinding = Scalar::random(&mut rng);
        let mut A = self.B_blinding * a_blinding;
        for i in 0..self.n {
            let v_i = (v >> i) & 1;
            if v_i == 0 {
                A -= self.H[i];
            } else {
                A += self.G[i];
            }
        }

        // Compute S
        let points_iter = iter::once(&self.B_blinding).chain((&self.G).iter()).chain((&self.H).iter());
        let randomness: Vec<_> = (0..(1 + 2 * self.n)).map(|_| Scalar::random(&mut rng)).collect();
        let S = ristretto::multiscalar_mult(&randomness, points_iter);

        State1 {
            V: V,
            A: A,
            S: S,

            v_blinding: v_blinding,
            a_blinding: a_blinding,
            randomness: randomness,
            v: v,

            n: self.n,
            B: self.B,
            B_blinding: self.B_blinding,
        }
    }
}

impl State1 {
    pub fn prove(&self, y: Scalar, z: Scalar) -> State2 {
        let mut rng: OsRng = OsRng::new().unwrap();
        // useful for debugging:
        // let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);

        // Save/label randomness to be used later (in the paper: rho, s_L, s_R)
        let s_blinding = self.randomness[0];
        let s_a = &self.randomness[1..(self.n + 1)];
        let s_b = &self.randomness[(self.n + 1)..(1 + 2 * self.n)];

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l = VecPoly2::new(self.n);
        let mut r = VecPoly2::new(self.n);
        let z2 = z * z;
        let mut t = PolyDeg3::new();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..self.n {
            let v_i = (self.v >> i) & 1;
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
        let T_1 = self.B * t.1 + self.B_blinding * t_1_blinding;
        let T_2 = self.B * t.2 + self.B_blinding * t_2_blinding;

        State2 {
            V: self.V,
            A: self.A,
            S: self.S,
            T_1: T_1,
            T_2: T_2,
            y: y,
            z: z,
            l: l,
            r: r,
            t: t,
            v_blinding: self.v_blinding,
            a_blinding: self.a_blinding,
            s_blinding: s_blinding,
            t_1_blinding: t_1_blinding,
            t_2_blinding: t_2_blinding,
            n: self.n,
            B: self.B,
            B_blinding: self.B_blinding,
        }
    }
}

impl State2 {
    pub fn prove(&self, x: Scalar) -> State3 {
        // Generate final values for proof (line 55-60)
        let t_x_blinding = self.t_1_blinding * x + self.t_2_blinding * x * x + self.z * self.z * self.v_blinding;
        let e_blinding = self.a_blinding + self.s_blinding * x;
        let t_hat = self.t.0 + self.t.1 * x + self.t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = self.l.eval(x);
        let r_total = self.r.eval(x);

        State3 {
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,

            V: self.V,
            A: self.A,
            S: self.S,
            T_1: self.T_1,
            T_2: self.T_2,

            n: self.n,
            B: self.B,
            B_blinding: self.B_blinding,
        }
    }
}

impl State3 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

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
*/