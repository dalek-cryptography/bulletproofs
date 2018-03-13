#![allow(non_snake_case)]
//#![deny(missing_docs)]

use std::iter;
use rand::Rng;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use std::clone::Clone;
use scalar::{scalar_pow_vartime_slow,scalar_pow_vartime_fast};
use proof_transcript::ProofTranscript;
use self::generators::Generators;
use self::rangeproof_generators::RangeproofGenerators;

/// Party is an entry-point API for setting up a party.
pub struct Party {}

/// Dealer is an entry-point API for setting up a dealer
pub struct Dealer {}

/// As party awaits its position, they only know their value and desired bit-size of the proof.
pub struct PartyAwaitingPosition {
    n: usize,
    v: u64,
    v_blinding: Scalar
}

/// When party knows its position (`j`), it can produce commitments
/// to all bits of the value and necessary blinding factors.
pub struct PartyAwaitingValueChallenge {
    n: usize, // bitsize of the range
    v: u64,
    v_blinding: Scalar,

    j: usize, // index of the party, 1..m as in original paper
    generators: RangeproofGenerators,
    val_comm: ValueCommitment,
    a_blinding: Scalar,
    s_blinding: Scalar,
    s_l: Vec<Scalar>,
    s_r: Vec<Scalar>,
}

pub struct PartyAwaitingPolyChallenge {
    generators: RangeproofGenerators,

    val_comm:  ValueCommitment,
    poly_comm: PolyCommitment,

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

/// When the dealer is initialized, it only knows the size of the set.
pub struct DealerAwaitingValues {
    pt: ProofTranscript,
    n: usize,
    m: usize,
}

pub struct DealerAwaitingPoly {
    pt: ProofTranscript,
    n: usize,
    m: usize,
}

pub struct DealerAwaitingShares {
    pt: ProofTranscript,
    n: usize,
    m: usize,
}

pub struct ValueCommitment {
    V: RistrettoPoint,
    A: RistrettoPoint,
    S: RistrettoPoint,
}

pub struct PolyCommitment {
    T_1: RistrettoPoint,
    T_2: RistrettoPoint,
}

pub struct ProofShare {
    generators: RangeproofGenerators,
    val_comm: ValueCommitment,
    poly_comm: PolyCommitment,

    t_x_blinding: Scalar,
    e_blinding: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>,
    r: Vec<Scalar>, 
}

pub struct AggregatedProof {
    generators: RangeproofGenerators,

    inp_comm: ValueCommitment,
    st_comm: PolyCommitment,

    t_x_blinding: Scalar,
    e_blinding: Scalar,
    t: Scalar,

    // don't need if doing inner product proof
    l: Vec<Scalar>,
    r: Vec<Scalar>,
}

/// Aggregator is a high-level API for creating proofs in one go.
pub struct Aggregator {
    n: usize,
    m: usize,
}

impl Party {
    pub fn new<R:Rng>(value: u64, n: usize, rng: &mut R) -> PartyAwaitingPosition {
        PartyAwaitingPosition {
            n: n,
            v: value,
            v_blinding: Scalar::random(&mut rng),
        }
    }
}

impl Dealer {
    /// Creates a new dealer with the given parties and a number of bits
    pub fn new(n: usize, parties: Vec<PartyAwaitingPosition>) -> Result<DealerAwaitingValues, &'static str> {
        if let Some(_) = parties.iter().find(|&x| x.n != n) {
            return Err("Inconsistent n among parties!")
        }
        let mut pt = ProofTranscript::new(b"MultiRangeProof");
        let m = parties.len();
        pt.commit_u64(n as u64);
        pt.commit_u64(m as u64);
        Ok(DealerAwaitingValues { pt, n, m })
    }
}

impl PartyAwaitingPosition {
    /// Assigns the position to a party, 
    /// at which point the party knows its generators.
    pub fn assign_position<R: Rng>(&self, j: usize, rng: &mut R) -> (PartyAwaitingValueChallenge, ValueCommitment) {
        let n = self.n;
        let gen = RangeproofGenerators::share(n, j);

        // Compute V
        let V = gen.B_b * self.v_blinding + gen.B * Scalar::from_u64(self.v);

        // Compute A
        let a_blinding = Scalar::random(&mut rng);
        let mut A = gen.B_b * a_blinding;
        for i in 0..n {
            let bit = (self.v >> i) & 1;
            if bit == 1 {
                // a_L = bit, bit = 1, so a_L=1, a_R=0
                A += gen.G[i];
            } else {
                // a_R = bit - 1, bit = 0, so a_L=0, a_R=-1
                A -= gen.H[i];
            }
        }

        // Compute S
        let s_blinding = Scalar::random(&mut rng);
        let s_l:Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let s_r:Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let S = ristretto::multiscalar_mult(
            iter::once(&s_blinding).chain(s_l.iter()).chain(s_r.iter()),
            iter::once(&gen.B_b).chain(gen.G.iter()).chain(gen.H.iter())
        );

        // Return next state and all commitments
        let val_comm = ValueCommitment { V, A, S };
        let next_state = PartyAwaitingValueChallenge {
            n: self.n,
            v: self.v,
            v_blinding: self.v_blinding,

            j,
            generators: gen,
            val_comm,
            a_blinding,
            s_blinding,
            s_l,
            s_r, 
        };
        (next_state, val_comm)
    }
}

impl DealerAwaitingValues {
    /// Combines commitments and computes challenge variables.
    pub fn present_values(mut self, vc: Vec<ValueCommitment>) -> (DealerAwaitingPoly, Scalar, Scalar) {
        // Commit each V individually
        for commitment in vc.iter() {
            self.pt.commit(commitment.V.compress().as_bytes());
        }
        
        // Commit sums of As and Ss.
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();
        for commitment in vc.iter() {
            A += commitment.A;
            S += commitment.S;
        }

        self.pt.commit(A.compress().as_bytes());
        self.pt.commit(S.compress().as_bytes());

        let y = self.pt.challenge_scalar();
        let z = self.pt.challenge_scalar();

        (DealerAwaitingPoly {
            pt: self.pt,
            n: self.n,
            m: self.m
        }, y,z)
    }
}


impl PartyAwaitingValueChallenge {
    pub fn apply_challenge(&self, y: Scalar, z: Scalar) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
        let n = self.n;

        // needed for multi-range-proof only: generate y, z offsets
        let mut offset_y = Scalar::one(); // offset_y = y^(j*n);
        for _ in 0..self.j*n {
            offset_y = offset_y * y;
        }
        let mut offset_z = Scalar::one(); // offset_z = z^j;
        for _ in 0..self.j {
            offset_z = offset_z * z;
        }

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
            l.1[i] = self.s_l[i];

            r.0[i] = exp_y * offset_y * (a_r + z) + z2 * offset_z * exp_2;
            r.1[i] = exp_y * offset_y * self.s_r[i];

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
        let t_1_blinding = Scalar::random(&mut self.rng);
        let t_2_blinding = Scalar::random(&mut self.rng);
        let T_1 = self.gen.B * t.1 + self.gen.B_blinding * t_1_blinding;
        let T_2 = self.gen.B * t.2 + self.gen.B_blinding * t_2_blinding;
        let poly_comm = PolyCommitment { T_1: T_1, T_2: T_2 };

        let papc = PartyAwaitingPolyChallenge {
            gen: self.gen,
            val_comm: self.val_comm,
            poly_comm,
            y,
            z,
            offset_z,
            l,
            r,
            t,
            v_blinding: self.v_blinding,
            a_blinding: self.a_blinding,
            s_blinding: self.s_blinding,
            t_1_blinding,
            t_2_blinding,
        };

        (papc, poly_comm)
    }
}

impl PartyAwaitingPolyChallenge {
    pub fn get_poly_challenge(&self, x: Scalar) -> ProofShare {
        // Generate final values for proof (line 55-60)
        let t_x_blinding = self.t_1_blinding * x + self.t_2_blinding * x * x +
            self.z * self.z * self.offset_z * self.v_blinding;
        let e_blinding = self.a_blinding + self.s_blinding * x;
        let t_hat = self.t.0 + self.t.1 * x + self.t.2 * x * x;

        // Calculate l, r - which is only necessary if not doing IPP (line 55-57)
        // Adding this in a seperate loop so we can remove it easily later
        let l_total = self.l.eval(x);
        let r_total = self.r.eval(x);

        ProofShare {
            gen: self.gen,
            val_comm: self.val_comm,
            poly_comm: self.poly_comm,
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,
        }
    }
}

impl DealerAwaitingPoly {
    pub fn get_poly(&self, pc: Vec<PolyCommitment>) -> (DealerAwaitingShares, Scalar) {
        unimplemented!()
    }
}

impl DealerAwaitingShares {
    pub fn get_shares(&self, ps: Vec<ProofShare>) -> AggregatedProof {
        unimplemented!()
    }
}

impl Aggregator {
    pub fn create_one<R: Rng>(v: u64, n: usize, rng: &mut R) -> AggregatedProof {
        Self::create_multi(vec![v], n, rng)
    }

    pub fn create_multi<R: Rng>(values: Vec<u64>, n: usize, rng: &mut R) -> AggregatedProof {
        let parties: Vec<_> = values.iter().map(|&v| Party::new(v, n, rng) ).collect();
        let mut dealer = Dealer::new(n, parties);
        let parties_commits: Vec<_> = parties.iter().zip(0..values.len()).map(|(&p,j)| p.assign_position(j,rng) ).collect();
        let parties: Vec<_> = parties_commits.iter().map(|&(p,c)| p ).collect();
        let commits: Vec<_> = parties_commits.iter().map(|&(p,c)| c ).collect();

        for party in parties {

        }

        /// TBD:

        let mut T_1 = RistrettoPoint::identity();
        let mut T_2 = RistrettoPoint::identity();
        let mut statements = Vec::new();
        for j in 0..m {
            let statement = inputs[j].make_statement(y, z);
            T_1 += statement.st_comm.T_1;
            T_2 += statement.st_comm.T_2;
            statements.push(statement);
        }

        ro.commit(&T_1.compress().as_bytes());
        ro.commit(&T_2.compress().as_bytes());
        let x = ro.challenge_scalar();

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
        let mut l: Vec<Scalar> = Vec::new();
        let mut r: Vec<Scalar> = Vec::new();

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
            inp_comm: InputCommitment { V: V, A: A, S: S },
            st_comm: StatementCommitment { T_1: T_1, T_2: T_2 },
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

        let mut ro = ProofTranscript::new(b"MultiRangeProof");
        ro.commit_u64(n as u64);
        ro.commit_u64(m as u64);
        for j in 0..m {
            ro.commit(V[j].compress().as_bytes());
        }
        ro.commit(&A.compress().as_bytes());
        ro.commit(&S.compress().as_bytes());
        let y = ro.challenge_scalar();
        let z = ro.challenge_scalar();
        ro.commit(&T_1.compress().as_bytes());
        ro.commit(&T_2.compress().as_bytes());
        let x = ro.challenge_scalar();

        let G = make_generators(B, n * m);
        let mut hprime_vec = make_generators(B_blinding, n * m);

        // line 63: check that t = t0 + t1 * x + t2 * x * x
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero(); // delta(y,z)

        // calculate power_g += (z - z^2) * <1^(n*m), y^(n*m)>
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n * m {
            power_g += (z - z2) * exp_y;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }
        // calculate power_g += sum_(j=1)^(m)(z^(j+2) * (2^n - 1))
        let mut exp_z = z3;
        for _ in 1..(m + 1) {
            power_g -= exp_z * Scalar::from_u64(((1u128 << n) - 1) as u64);
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
        for i in 0..n * m {
            sum_G += G[i];
        }
        let mut P = A + S * x;
        P -= sum_G * z;

        // line 62: calculate hprime
        // calculate P: add < vec(h'), z * vec(y)^n*m >
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let inverse_y = Scalar::invert(&y); // inverse_y = 1/y
        let mut inv_exp_y = Scalar::one(); // start at y^-0 = 1
        for i in 0..n * m {
            hprime_vec[i] = hprime_vec[i] * inv_exp_y;
            P += hprime_vec[i] * z * exp_y;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
            inv_exp_y = inv_exp_y * inverse_y; // y^(-i) * y^(-1) -> y^(-(i+1))
        }

        // calculate P: add sum(j_1^m)(<H[(j-1)*n:j*n-1], z^(j+1)*vec(2)^n>)
        let mut exp_z = z * z;
        for j in 1..(m + 1) {
            exp_2 = Scalar::one();
            for index in 0..n {
                // index into hprime, from [(j-1)*n : j*n-1]
                P += hprime_vec[(j - 1) * n + index] * exp_z * exp_2;
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

struct PolyDeg3(Scalar, Scalar, Scalar);
struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

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


///////////////////////////////////////////////////////
//            Copy-paste from a PR #15               //
///////////////////////////////////////////////////////
mod generators {
    use curve25519_dalek::ristretto::RistrettoPoint;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    use sha2::Sha256;

    /// The `Generators` represents an unbounded sequence
    /// of orthogonal points.
    pub struct Generators {
        next_point: RistrettoPoint
    }

    impl Generators {

        /// Instantiates a sequence starting with a standard Ristretto base point
        /// (inclusive).
        pub fn new() -> Self {
            Generators::at(&RISTRETTO_BASEPOINT_POINT)
        }

        /// Instantiates a sequence starting with a given generator.
        pub fn at(point: &RistrettoPoint) -> Self {
            Generators {
                next_point: point.clone()
            }
        }

        /// Emits the next generator and advances the internal state.
        pub fn next_point(&mut self) -> RistrettoPoint {
            let p2 = RistrettoPoint::hash_from_bytes::<Sha256>(self.next_point.compress().as_bytes());
            let result = self.next_point.clone();
            self.next_point = p2;
            result
        }

        /// Emits the next `n` generators and advances the internal state.
        pub fn next_points(&mut self, n: usize) -> Vec<RistrettoPoint> {
            let mut points = Vec::<RistrettoPoint>::with_capacity(n);
            for _ in 0..n {
                points.push(self.next_point())
            }
            points
        }
    }
    impl Iterator for Generators {
        type Item = RistrettoPoint;
        fn next(&mut self) -> Option<Self::Item> {
            Some(self.next_point())
        }
    }
}

mod rangeproof_generators {
    use curve25519_dalek::ristretto::RistrettoPoint;
        /// Each party has their own set of generators based on their position (`j`).
    pub struct RangeproofGenerators {
        /// Main base of the pedersen commitment
        pub B: RistrettoPoint,
        /// Base for the blinding factor in the pedersen commitment
        pub B_b: RistrettoPoint,
        /// Aux base for IPP
        pub Q: RistrettoPoint,
        /// Per-bit generators for the bit values
        pub G: Vec<RistrettoPoint>,
        /// Per-bit generators for the bit blinding factors
        pub H: Vec<RistrettoPoint>,
    }

    impl RangeproofGenerators {
        /// Creates a set of generators for an n-bit range proof.
        /// This can be used for an aggregated rangeproof from `m` parties using `new(n*m)`.
        pub fn new(n: usize) -> Self {
            let mut gen = super::generators::Generators::new();
            let B = gen.next_point();
            let B_b = gen.next_point();
            let Q = gen.next_point();

            // remaining points are: G0, H0, ..., G_(n-1), H_(n-1)
            let (G, H): (Vec<_>, Vec<_>) = gen.take(2 * n).enumerate().partition(|&(i, _)| i % 2 == 0);
            let G: Vec<_> = G.iter().map(|&(_, p)| p).collect();
            let H: Vec<_> = H.iter().map(|&(_, p)| p).collect();

            RangeproofGenerators { B, B_b, Q, G, H }
        }

        /// Creates a set of generators for an n-bit proof j-th party and n-bit proofs.
        pub fn share(n: usize, j: usize) -> Self {
            let mut gen = super::generators::Generators::new();
            let B = gen.next_point();
            let B_b = gen.next_point();
            let Q = gen.next_point();

            // remaining points are: G0, H0, ..., G_(n-1), H_(n-1)
            let (G, H): (Vec<_>, Vec<_>) = gen.skip(2 * n * j).take(2 * n).enumerate().partition(
                |&(i, _)| {
                    i % 2 == 0
                },
            );
            let G: Vec<_> = G.iter().map(|&(_, p)| p).collect();
            let H: Vec<_> = H.iter().map(|&(_, p)| p).collect();

            RangeproofGenerators { B, B_b, Q, G, H }
        }
    }
}
///////////////////////////////////////////////////////
//           End copy-paste from a PR #15            //
///////////////////////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use rand::OsRng;

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
        let rp = Proof::create_multi(vec![0, u64::max_value() - 1], n);
        assert_eq!(rp.verify(2), true);
    }
    #[test]
    fn ten_party_small() {
        let m = 10;
        for n in vec![1, 16, 32] {
            let rp = Proof::create_multi(vec![1, 1, 0, 0, 1, 1, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), true);
            let rp = Proof::create_multi(
                vec![
                    2u64.pow(n as u32) - 1,
                    2u64.pow(n as u32) - 1,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    1,
                    1,
                ],
                n,
            );
            assert_eq!(rp.verify(m), true);
            let rp =
                Proof::create_multi(vec![2u64.pow(n as u32) + 1, 0, 0, 0, 0, 0, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), false);
            let rp = Proof::create_multi(vec![0, u64::max_value(), 0, 0, 0, 0, 0, 0, 1, 1], n);
            assert_eq!(rp.verify(m), false);
        }
    }
    #[test]
    fn ten_party_u64() {
        let m = 10;
        let n = 64;
        let rp = Proof::create_multi(
            vec![u64::max_value(), u64::max_value(), 0, 0, 1, 1, 0, 0, 1, 1],
            n,
        );
        assert_eq!(rp.verify(m), true);
        let rp = Proof::create_multi(
            vec![
                u64::max_value() - 1,
                1,
                0,
                0,
                0,
                0,
                0,
                0,
                1,
                u64::max_value() / 2,
            ],
            n,
        );
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
            let v = rng.next_u32() as u64;
            let rp = Proof::create_one(v, 32);
            assert_eq!(rp.verify(1), true);
        }
    }
    #[test]
    fn rand_u64() {
        for _ in 0..10 {
            let mut rng: OsRng = OsRng::new().unwrap();
            let v = rng.next_u64();
            let rp = Proof::create_one(v, 64);
            assert_eq!(rp.verify(1), true);
        }
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    use rand::Rng;
    use test::Bencher;

    #[bench]
    fn make_u64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| Proof::create_one(rng.next_u64(), 64));
    }
    #[bench]
    fn make_u32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        b.iter(|| Proof::create_one(rng.next_u32() as u64, 32));
    }
    #[bench]
    fn verify_u64(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = Proof::create_one(rng.next_u64(), 64);
        b.iter(|| rp.verify(1));
    }
    #[bench]
    fn verify_u32(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let rp = Proof::create_one(rng.next_u32() as u64, 32);
        b.iter(|| rp.verify(1));
    }
}
