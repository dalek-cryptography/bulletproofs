#![allow(non_snake_case)]

use std::iter;
use sha2::Sha256;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use rand::OsRng;
use std::clone::Clone;
use range_proof::{make_generators, inner_product, add_vec, commit};

struct PolyDeg3(Scalar, Scalar, Scalar);

struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

#[derive(Clone)]
pub struct Generators {
    B: RistrettoPoint,
    B_blinding: RistrettoPoint,
    G: Vec<RistrettoPoint>,
    H: Vec<RistrettoPoint>,
    n: usize,
    m: usize,
}

#[derive(Clone)]
pub struct InputCommitment {
    V: Vec<RistrettoPoint>,
    A: RistrettoPoint,
    S: RistrettoPoint,
}

pub struct Input {
    gen: Generators,
    pub inp_comm: InputCommitment,

    j: usize,  // index of the party, 1..m as in original paper
    v_blinding: Scalar,
    a_blinding: Scalar,
    randomness: Vec<Scalar>, // s_blinding (aka s_tilde), {s_a},  {s_b}
    v: u64,  
}

#[derive(Clone)]
pub struct StatementCommitment {
    T_1: RistrettoPoint,
    T_2: RistrettoPoint, 
}

pub struct Statement {
    gen: Generators,
    inp_comm: InputCommitment,
    pub st_comm: StatementCommitment,

    // intermediate values (private)
    y: Scalar,
    z: Scalar,
    offset_z: Scalar,
    l: VecPoly2,
    r: VecPoly2,
    t: PolyDeg3,
    v_blinding: Scalar,
    a_blinding: Scalar,
    s_blinding: Scalar,
    t_1_blinding: Scalar,
    t_2_blinding: Scalar,
}

#[derive(Clone)]
pub struct Proof {
    gen: Generators,
    inp_comm: InputCommitment,
    st_comm: StatementCommitment,

    t_x_blinding: Scalar,
    e_blinding: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>,
    r: Vec<Scalar>,
}


impl Generators {
    pub fn new(n: usize, m: usize) -> Generators {
        let B = RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let B_blinding = RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        Generators {
            B: B,
            B_blinding: B_blinding,
            G: make_generators(&B, n*m),
            H: make_generators(&B_blinding, n*m),
            n: n,
            m: m,
        }
    }

    pub fn make_input(&self, j: usize, v: u64) -> Input {
        let mut rng: OsRng = OsRng::new().unwrap();
        let n = self.n;

        // Compute V
        let v_blinding = Scalar::random(&mut rng);
        let V = self.B_blinding * v_blinding + self.B * Scalar::from_u64(v);

        // Compute A
        let a_blinding = Scalar::random(&mut rng);
        let mut A = self.B_blinding * a_blinding;
        for i in 0..n {
            let bit = (v >> i) & 1;
            if bit == 1 {
                // a_L = bit, bit = 1, so a_L=1, a_R=0
                A += self.G[(j-1)*n + i];
            } else {
                // a_R = bit - 1, bit = 0, so a_L=0, a_R=-1
                A -= self.H[(j-1)*n + i];
            }
        }

        // Compute S
        let points_iter = iter::once(&self.B_blinding).
            chain((&self.G[(j-1)*n..j*n]).iter()).
            chain((&self.H[(j-1)*n..j*n]).iter());
        let randomness: Vec<_> = (0..(1 + 2 * self.n)).map(|_| Scalar::random(&mut rng)).collect();
        let S = ristretto::multiscalar_mult(&randomness, points_iter);
        let inp_comm = InputCommitment {
            V: vec![V],
            A: A,
            S: S,            
        };
        
        let gen = self.clone();

        Input {
            gen,
            j,
            inp_comm,
            v_blinding,
            a_blinding,
            randomness,
            v,
        }
    }
}

impl Input {
    pub fn make_statement(&self, y: Scalar, z: Scalar) -> Statement {
        let mut rng: OsRng = OsRng::new().unwrap();
        let n = self.gen.n;

        // needed for multi-range-proof only: generate y, z offsets
        let mut offset_y = Scalar::one(); // offset_y = y^((j-1)*n);
        for _ in 0..((self.j-1)*n) {
            offset_y = offset_y*y;
        }
        let mut offset_z = Scalar::one(); // offset_z = z^(j-1); 
        for _ in 0..(self.j-1) {
            offset_z = offset_z*z;
        }

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
            let a_l = Scalar::from_u64((self.v >> i) & 1);
            let a_r = a_l - Scalar::one();
            
            l.0[i] = a_l - z;
            l.1[i] = s_a[i];

            r.0[i] = exp_y * offset_y * (a_r + z) + z2 * offset_z * exp_2;
            r.1[i] = exp_y * offset_y * s_b[i];

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
            gen: self.gen.clone(),
            inp_comm: self.inp_comm.clone(),
            st_comm: st_comm,
            y: y,
            z: z,
            offset_z: offset_z,
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
        let t_x_blinding = self.t_1_blinding * x + self.t_2_blinding * x * x + self.z * self.z * self.offset_z * self.v_blinding;
        let e_blinding = self.a_blinding + self.s_blinding * x;
        let t_hat = self.t.0 + self.t.1 * x + self.t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = self.l.eval(x);
        let r_total = self.r.eval(x);

        Proof {
            gen: self.gen.clone(),
            inp_comm: self.inp_comm.clone(),
            st_comm: self.st_comm.clone(),
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,
        }
    }
}

impl Proof {
    pub fn create_one(v: u64, n: usize) -> Proof {
        let input = Generators::new(n, 1).make_input(1, v);
        // TODO: swap out this commitment with use of RO
        let (y, z) = commit(&input.inp_comm.A, &input.inp_comm.S);
        let statement = input.make_statement(y, z);
        // TODO: swap out this commitment with use of RO
        let (x, _) = commit(&statement.st_comm.T_1, &statement.st_comm.T_2);
        statement.make_proof(x)
    }

    pub fn create_multi(values: Vec<u64>, n: usize) -> Proof {
        let m = values.len();
        let gen = Generators::new(n, m);
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();
        let mut inputs = Vec::new();
        for j in 0..m {
            let input = gen.make_input(j+1, values[j]);
            A += input.inp_comm.A;
            S += input.inp_comm.S;
            inputs.push(input);
        }
        let (y, z) = commit(&A, &S);

        let mut T_1 = RistrettoPoint::identity();
        let mut T_2 = RistrettoPoint::identity();
        let mut statements = Vec::new();
        for j in 0..m {
            let statement = inputs[j].make_statement(y,z);
            T_1 += statement.st_comm.T_1;
            T_2 += statement.st_comm.T_2;
            statements.push(statement);
        }
        let (x, _) = commit(&T_1, &T_2);

        let mut proofs = Vec::new();
        for j in 0..m {
            let proof = statements[j].make_proof(x);
            proofs.push(proof);
        }
        Proof::combine(proofs)
    }

    pub fn combine(proofs: Vec<Proof>) -> Proof {
        let mut V = Vec::new();
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();
        let mut T_1 = RistrettoPoint::identity();
        let mut T_2 = RistrettoPoint::identity();
        let mut t_x_blinding = Scalar::zero();
        let mut e_blinding = Scalar::zero();
        let mut t = Scalar::zero();
        let mut l:Vec<Scalar> = Vec::new();
        let mut r:Vec<Scalar> = Vec::new();

        for proof in &proofs {
            V.push(proof.inp_comm.V[0]);
            A += proof.inp_comm.A;
            S += proof.inp_comm.S;
            T_1 += proof.st_comm.T_1;
            T_2 += proof.st_comm.T_2;
            t_x_blinding += proof.t_x_blinding;
            e_blinding += proof.e_blinding;
            t += proof.t;
            l.extend(&proof.l);
            r.extend(&proof.r);
        }

        Proof {
            gen: proofs[0].gen.clone(),
            inp_comm: InputCommitment {
                V: V,
                A: A,
                S: S,
            },
            st_comm: StatementCommitment {
                T_1: T_1,
                T_2: T_2,
            },
            t_x_blinding: t_x_blinding,
            e_blinding,
            t: t,
            l: l,
            r: r,
        }
    }

    pub fn verify(&self, m: usize) -> bool {
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
        let G = make_generators(B, n*m);
        let mut hprime_vec = make_generators(B_blinding, n*m);

        // line 63: check that t = t0 + t1 * x + t2 * x * x
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero(); // delta(y,z)

        // calculate power_g += (z - z^2) * <1^(n*m), y^(n*m)>
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n*m {
            power_g += (z - z2) * exp_y;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        // calculate power_g += sum_(j=1)^(m)(z^(j+2) * (2^n - 1))
        let mut exp_z = z3;
        for _ in 1..(m+1) {
            power_g -= exp_z * Scalar::from_u64(((1u128<<n) - 1) as u64);
            exp_z = exp_z * z;
        }

        let mut t_check = B * power_g + T_1 * x + T_2 * x * x;
        let mut exp_z = Scalar::one();
        for j in 0..m {
            t_check += V[j] * z2 * exp_z;
            exp_z = exp_z * z;
        }
        let t_commit = B * self.t + B_blinding * self.t_x_blinding;
        if t_commit != t_check {
            println!("fails check on line 63");
            return false;
        }
        
        // line 64: compute commitment to l, r
        // calculate P: add A + S*x - G*z
        let mut sum_G = RistrettoPoint::identity();
        for i in 0..n*m {
            sum_G += G[i];
        }
        let mut P = A + S * x;
        P -= sum_G * z;

        // line 62: calculate hprime
        // calculate P: add < vec(h'), z * vec(y)^n*m >
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let inverse_y = Scalar::invert(&y); // inverse_y = 1/y
        let mut inv_exp_y = Scalar::one(); // start at y^-0 = 1
        for i in 0..n*m {
            hprime_vec[i] = hprime_vec[i] * inv_exp_y;
            P += hprime_vec[i] * z * exp_y;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
            inv_exp_y = inv_exp_y * inverse_y; // y^(-i) * y^(-1) -> y^(-(i+1))
        }

        // calculate P: add sum(j_1^m)(<H[(j-1)*n:j*n-1], z^(j+1)*vec(2)^n>)
        let mut exp_z = z * z;
        for j in 1..(m+1) {
            exp_2 = Scalar::one();
            for index in 0..n {
                // index into hprime, from [(j-1)*n : j*n-1]
                P += hprime_vec[index + (j-1)*n] * exp_z * exp_2;
                exp_2 = exp_2 + exp_2;
            }
            exp_z = exp_z * z;
        }

        // line 65: check that l, r are correct
        let mut P_check = B_blinding * self.e_blinding;
        let points_iter = G.iter().chain(hprime_vec.iter());
        let scalars_iter = self.l.iter().chain(self.r.iter());
        P_check += ristretto::multiscalar_mult(scalars_iter, points_iter);
        if P != P_check {
            println!("fails check on line 65: P != g * l + hprime * r");
            return false;
        }

        // line 66: check that t is correct
        if self.t != inner_product(&self.l, &self.r) {
            println!("fails check on line 66: t != l * r");
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
    fn one_party_small() {
        for n in vec![1, 16, 32] {
            let rp = Proof::create_one(0, n);
            assert_eq!(rp.verify(1), true);
            let rp = Proof::create_one(2u64.pow(n as u32) - 1, n);
            assert_eq!(rp.verify(1), true);
            let rp = Proof::create_one(2u64.pow(n as u32), n);
            assert_eq!(rp.verify(1), false);
            let rp = Proof::create_one(2u64.pow(n as u32) + 1, n);
            assert_eq!(rp.verify(1), false);
            let rp = Proof::create_one(u64::max_value(), n);
            assert_eq!(rp.verify(1), false);
        }
    }
    #[test]
    fn one_party_u64() {
        let n = 64;
        let rp = Proof::create_one(0, n);
        assert_eq!(rp.verify(1), true);
        let rp = Proof::create_one(1, n);
        assert_eq!(rp.verify(1), true);
        let rp = Proof::create_one(u64::max_value(), n);
        assert_eq!(rp.verify(1), true);    
    }
    #[test]
    fn two_party_small() {
        for n in vec![1, 16, 32] {
            let rp = Proof::create_multi(vec![1, 1], n);
            assert_eq!(rp.verify(2), true);
            let rp = Proof::create_multi(vec![0, 1], n);
            assert_eq!(rp.verify(2), true);
            let rp = Proof::create_multi(vec![1, 0], n);
            assert_eq!(rp.verify(2), true);
            let rp = Proof::create_multi(vec![0, 0], n);
            assert_eq!(rp.verify(2), true);
            let rp = Proof::create_multi(vec![2u64.pow(n as u32) - 1, 1], n);
            assert_eq!(rp.verify(2), true);
            let rp = Proof::create_multi(vec![2u64.pow(n as u32) + 1, 0], n);
            assert_eq!(rp.verify(2), false);
            let rp = Proof::create_multi(vec![0, u64::max_value()], n);
            assert_eq!(rp.verify(2), false);
        }
    }
    #[test]
    fn two_party_u64() {
        let n = 64;
        let rp = Proof::create_multi(vec![u64::max_value(), 1], n);
        assert_eq!(rp.verify(2), true);
        let rp = Proof::create_multi(vec![0, u64::max_value()-1], n);
        assert_eq!(rp.verify(2), true);
    }
    #[test]
    fn ten_party_small() {
        let m = 10;
        for n in vec![1, 16, 32] {
            let rp = Proof::create_multi(vec![1, 1, 0, 0, 1, 1, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), true);
            let rp = Proof::create_multi(vec![2u64.pow(n as u32) - 1, 2u64.pow(n as u32) - 1, 0, 0, 0, 0, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), true);
            let rp = Proof::create_multi(vec![2u64.pow(n as u32) + 1, 0, 0, 0, 0, 0, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), false);
            let rp = Proof::create_multi(vec![0, u64::max_value(), 0, 0, 0, 0, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), false);
        }
    }
    #[test]
    fn ten_party_u64() {
        let m = 10;
        let n = 64;
        let rp = Proof::create_multi(vec![u64::max_value(), u64::max_value(), 0, 0, 1, 1, 0, 0, 1, 1], n);
        assert_eq!(rp.verify(m), true);
        let rp = Proof::create_multi(vec![u64::max_value() - 1, 1, 0, 0, 0, 0, 0, 0, 1, u64::max_value()/2], n);
        assert_eq!(rp.verify(m), true);
    }
    #[test]
    fn rand_small() {
        for _ in 0..10 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u32 = rng.next_u32();
            let rp = Proof::create_one(v as u64, 32);
            assert_eq!(rp.verify(1), true);
        }
    }
    #[test]
    fn rand_u32() {
        for _ in 0..10 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u64 = rng.next_u64();
            let rp = Proof::create_one(v, 32);
            let expected = v <= 2u64.pow(32);
            assert_eq!(rp.verify(1), expected);
        }
    }
    #[test]
    fn rand_u64() {
        for _ in 0..10 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v: u64 = rng.next_u64();
            let rp = Proof::create_one(v, 32);
            let expected = v <= 2u64.pow(32);
            assert_eq!(rp.verify(1), expected);
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
        b.iter(|| Proof::create_one(rng.next_u64(), 64));
    }
    #[bench]
    fn make_multirp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| Proof::create_one(rng.next_u32() as u64, 32));
    }
    #[bench]
    fn verify_multirp_64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = Proof::create_one(rng.next_u64(), 64);
        b.iter(|| rp.verify(1));
    }
    #[bench]
    fn verify_multirp_32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = Proof::create_one(rng.next_u32() as u64, 32);
        b.iter(|| rp.verify(1));
    }
}