#![allow(non_snake_case)]

use std::iter;
use sha2::Sha256;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;
use range_proof::{make_generators, inner_product, add_vec, commit};

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

pub struct Generators {
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,
    G: Vec<RistrettoPoint>,
    H: Vec<RistrettoPoint>,
    n: usize,
}

pub struct InputCommitment {
    pub V: RistrettoPoint,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,    
}

pub struct Input {
    pub gen: Generators,
    pub inp_comm: InputCommitment,

    v_blinding: Scalar,
    a_blinding: Scalar,
    randomness: Vec<Scalar>,
    v: u64,  
}

pub struct StatementCommitment {
    pub T_1: RistrettoPoint,
    pub T_2: RistrettoPoint, 
}

pub struct Statement {
    pub gen: Generators,
    pub inp_comm: InputCommitment,
    pub st_comm: StatementCommitment,

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
}

pub struct Proof {
    pub gen: Generators,
    pub inp_comm: InputCommitment,
    pub st_comm: StatementCommitment,

    t_x_blinding: Scalar,
    e_blinding: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>,
    r: Vec<Scalar>,
}


impl Generators {
    pub fn new(n: usize) -> Generators {
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

    pub fn make_input(&self, v: u64) -> Input {
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
        let inp_comm = InputCommitment {
            V: V,
            A: A,
            S: S,            
        };

        Input {
            gen: *self,
            inp_comm: inp_comm,
            v_blinding: v_blinding,
            a_blinding: a_blinding,
            randomness: randomness,
            v: v,
        }
    }
}

impl Input {
    pub fn make_statement(&self, y: Scalar, z: Scalar) -> Statement {
        let mut rng: OsRng = OsRng::new().unwrap();
        // useful for debugging:
        // let mut rng: StdRng = StdRng::from_seed(&[1, 2, 3, 4]);
        let n = self.gen.n;

        // Save/label randomness to be used later (in the paper: rho, s_L, s_R)
        let s_blinding = self.randomness[0];
        let s_a = &self.randomness[1..(n + 1)];
        let s_b = &self.randomness[(n + 1)..(1 + 2 * n)];

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l = VecPoly2::new(n);
        let mut r = VecPoly2::new(n);
        let z2 = z * z;
        let mut t = PolyDeg3::new();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..n {
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
        let T_1 = self.gen.B * t.1 + self.gen.B_blinding * t_1_blinding;
        let T_2 = self.gen.B * t.2 + self.gen.B_blinding * t_2_blinding;
        let st_comm = StatementCommitment {
            T_1: T_1,
            T_2: T_2,            
        };

        Statement {
            gen: self.gen,
            inp_comm: self.inp_comm,
            st_comm: st_comm,
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
        }
    }
}

impl Statement {
    pub fn make_proof(&self, x: Scalar) -> Proof {
        // Generate final values for proof (line 55-60)
        let t_x_blinding = self.t_1_blinding * x + self.t_2_blinding * x * x + self.z * self.z * self.v_blinding;
        let e_blinding = self.a_blinding + self.s_blinding * x;
        let t_hat = self.t.0 + self.t.1 * x + self.t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = self.l.eval(x);
        let r_total = self.r.eval(x);

        Proof {
            gen: self.gen,
            inp_comm: self.inp_comm,
            st_comm: self.st_comm,
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,
        }
    }
}

impl Proof {
    pub fn prove_single(v: u64, n: usize) -> Proof {
        let input = Generators::new(n).make_input(v);
        // TODO: swap out this commitment with use of RO
        let (y, z) = commit(&input.inp_comm.A, &input.inp_comm.S);
        let statement = input.make_statement(y, z);
        // TODO: swap out this commitment with use of RO
        let (x, _) = commit(&statement.st_comm.T_1, &statement.st_comm.T_2);
        statement.make_proof(x)
    }

    pub fn combine(proofs: Vec<Proof>) -> Proof {
        unimplemented!()
    }

    pub fn verify_proof(&self) -> bool {
        let V = &self.inp_comm.V;
        let A = &self.inp_comm.A;
        let S = &self.inp_comm.S;
        let T_1 = &self.st_comm.T_1;
        let T_2 = &self.st_comm.T_2;
        let n = self.gen.n;
        let B = &self.gen.B;
        let B_blinding = &self.gen.B_blinding;

        let (y, z) = commit(A, S);
        let (x, _) = commit(T_1, T_2);
        let G = make_generators(B, n);
        let mut hprime_vec = make_generators(B_blinding, n);

        // line 63: check that t = t0 + t1 * x + t2 * x * x
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        let t_check = B * power_g + V * z2 + T_1 * x + T_2 * x * x;
        let t_commit = B * self.t + B_blinding * self.t_x_blinding;
        if t_commit != t_check {
            //println!("fails check on line 63");
            return false;
        }

        // line 62: calculate hprime
        // line 64: compute commitment to l, r
        let mut sum_G = RistrettoPoint::identity();
        for i in 0..n {
            sum_G += G[i];
        }
        let mut big_p = A + S * x;
        big_p -= sum_G * z;

        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        let inverse_y = Scalar::invert(&y);
        let mut inv_exp_y = Scalar::one(); // start at y^-0 = 1
        for i in 0..n {
            hprime_vec[i] = hprime_vec[i] * inv_exp_y;
            big_p += hprime_vec[i] * (z * exp_y + z2 * exp_2);
            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
            inv_exp_y = inv_exp_y * inverse_y; // y^(-i) * y^(-1) -> y^(-(i+1))
        }

        // line 65: check that l, r are correct
        let mut big_p_check = B_blinding * self.e_blinding;
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn verify_multirp_simple() {
        for n in &[1, 2, 4, 8, 16, 32] {
            //println!("n: {:?}", n);
            let rp = State3::prove_single(0, *n);
            assert_eq!(rp.verify_proof(), true);
            let rp = State3::prove_single(2u64.pow(*n as u32) - 1, *n);
            assert_eq!(rp.verify_proof(), true);
            let rp = State3::prove_single(2u64.pow(*n as u32), *n);
            assert_eq!(rp.verify_proof(), false);
            let rp = State3::prove_single(2u64.pow(*n as u32) + 1, *n);
            assert_eq!(rp.verify_proof(), false);
            let rp = State3::prove_single(u64::max_value(), *n);
            assert_eq!(rp.verify_proof(), false);
        }
    }
    #[test]
    fn verify_multirp_rand_big() {
        for _ in 0..50 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u64 = rng.next_u64();
            let rp = State3::prove_single(v, 32);
            let expected = v <= 2u64.pow(32);
            assert_eq!(rp.verify_proof(), expected);
        }
    }
    #[test]
    fn verify_multirp_rand_small() {
        for _ in 0..50 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u32 = rng.next_u32();
            let rp = State3::prove_single(v as u64, 32);
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
    fn make_multirp_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| State3::prove_single(rng.next_u64(), 64));
    }
    #[bench]
    fn make_multirp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| State3::prove_single(rng.next_u32() as u64, 32));
    }
    #[bench]
    fn verify_multirp_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = State3::prove_single(rng.next_u64(), 64);
        b.iter(|| rp.verify_proof());
    }
    #[bench]
    fn verify_multirp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = State3::prove_single(rng.next_u32() as u64, 32);
        b.iter(|| rp.verify_proof());
    }
}