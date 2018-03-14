#![allow(non_snake_case)]
//#![deny(missing_docs)]

use std::iter;
use rand::Rng;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use std::clone::Clone;
use scalar::{scalar_pow_vartime,inner_product,add_vectors};
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
    v_blinding: Scalar,
    V: RistrettoPoint,
}

/// When party knows its position (`j`), it can produce commitments
/// to all bits of the value and necessary blinding factors.
pub struct PartyAwaitingValueChallenge {
    n: usize, // bitsize of the range
    v: u64,
    v_blinding: Scalar,

    j: usize, // index of the party, 1..m as in original paper
    generators: RangeproofGenerators,
    value_commitment: ValueCommitment,
    a_blinding: Scalar,
    s_blinding: Scalar,
    s_l: Vec<Scalar>,
    s_r: Vec<Scalar>,
}

pub struct PartyAwaitingPolyChallenge {
    generators: RangeproofGenerators,

    value_commitment:  ValueCommitment,
    poly_commitment: PolyCommitment,

    y: Scalar,
    z: Scalar,
    offset_z: Scalar,
    l: VecPoly2,
    r: VecPoly2,
    t: Poly3,
    v_blinding: Scalar,
    a_blinding: Scalar,
    s_blinding: Scalar,
    t1_blinding: Scalar,
    t2_blinding: Scalar,
}

/// When the dealer is initialized, it only knows the size of the set.
pub struct DealerAwaitingValues {
    transcript: ProofTranscript,
    n: usize,
    m: usize,
}

pub struct DealerAwaitingPoly {
    transcript: ProofTranscript,
    n: usize,
    m: usize,
}

pub struct DealerAwaitingShares {
    transcript: ProofTranscript,
    n: usize,
    m: usize,
}

#[derive(Clone)]
pub struct ValueCommitment {
    pub V: RistrettoPoint,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,
}

#[derive(Clone)]
pub struct PolyCommitment {
    pub T1: RistrettoPoint,
    pub T2: RistrettoPoint,
}

#[derive(Clone)]
pub struct ProofShare {
    pub generators: RangeproofGenerators,
    pub value_commitment: ValueCommitment,
    pub poly_commitment: PolyCommitment,

    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,
    pub t: Scalar,

    // don't need if doing inner product proof
    pub l: Vec<Scalar>,
    pub r: Vec<Scalar>, 
}


pub struct Proof {
    pub n: usize,
    pub value_commitments: Vec<RistrettoPoint>,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,
    pub T1: RistrettoPoint,
    pub T2: RistrettoPoint,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,
    pub t: Scalar,

    // FIXME: don't need if doing inner product proof
    pub l: Vec<Scalar>,
    pub r: Vec<Scalar>,
}

impl Party {
    pub fn new<R:Rng>(value: u64, n: usize, mut rng: &mut R) -> PartyAwaitingPosition {
        let gen = RangeproofGenerators::new(0);
        let (V,v_blinding) = gen.pedersen_commitment(&Scalar::from_u64(value), &mut rng);
        PartyAwaitingPosition { n, v: value, v_blinding, V }
    }
}

impl Dealer {
    /// Creates a new dealer with the given parties and a number of bits
    pub fn new(n: usize, parties: &Vec<PartyAwaitingPosition>) -> Result<DealerAwaitingValues, &'static str> {
        if let Some(_) = parties.iter().find(|&x| x.n != n) {
            return Err("Inconsistent n among parties!")
        }
        let mut transcript = ProofTranscript::new(b"MultiRangeProof");
        let m = parties.len();
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        Ok(DealerAwaitingValues { transcript, n, m })
    }
}

impl PartyAwaitingPosition {
    /// Assigns the position to a party, 
    /// at which point the party knows its generators.
    pub fn assign_position<R: Rng>(&self, j: usize, mut rng: &mut R) -> (PartyAwaitingValueChallenge, ValueCommitment) {
        let n = self.n;
        let gen = RangeproofGenerators::share(n, j);

        let one = Scalar::one();
        let bits: Vec<_> = (0..n).map(|i| Scalar::from_u64((self.v >> i) & 1)).collect(); // a_L
        let bits_minus_one: Vec<_> = bits.iter().map(|bit| bit - one).collect();  // a_R
        let s_l:Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let s_r:Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        
        let (A, a_blinding) = gen.vector_pedersen_commitment(bits.iter().chain(bits_minus_one.iter()), &mut rng);
        let (S, s_blinding) = gen.vector_pedersen_commitment(s_l.iter().chain(s_r.iter()), &mut rng);

        // Return next state and all commitments
        let value_commitment = ValueCommitment { V: self.V, A, S };
        let next_state = PartyAwaitingValueChallenge {
            n: self.n,
            v: self.v,
            v_blinding: self.v_blinding,

            j,
            generators: gen,
            value_commitment: value_commitment.clone(),
            a_blinding,
            s_blinding,
            s_l,
            s_r, 
        };
        (next_state, value_commitment)
    }
}

impl DealerAwaitingValues {
    /// Combines commitments and computes challenge variables.
    pub fn present_value_commitments(mut self, vc: &Vec<ValueCommitment>) -> (DealerAwaitingPoly, Scalar, Scalar) {
        let mut A = RistrettoPoint::identity();
        let mut S = RistrettoPoint::identity();

        for commitment in vc.iter() {
            // Commit each V individually
            self.transcript.commit(commitment.V.compress().as_bytes());

            // Commit sums of As and Ss.
            A += commitment.A;
            S += commitment.S;
        }

        self.transcript.commit(A.compress().as_bytes());
        self.transcript.commit(S.compress().as_bytes());

        let y = self.transcript.challenge_scalar();
        let z = self.transcript.challenge_scalar();

        (DealerAwaitingPoly {
            transcript: self.transcript,
            n: self.n,
            m: self.m
        }, y,z)
    }
}

impl PartyAwaitingValueChallenge {
    pub fn apply_challenge<R: Rng>(&self, y: &Scalar, z: &Scalar, mut rng: &mut R) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
        let n = self.n;
        let offset_y = scalar_pow_vartime(&y, (self.j*n) as u64);
        let offset_z = scalar_pow_vartime(&z, self.j as u64);

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l = VecPoly2::new(n);
        let mut r = VecPoly2::new(n);
        let z2 = z * z;
        let mut t = Poly3::new();
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
        let l_add = add_vectors(&l.0, &l.1);
        let r_add = add_vectors(&r.0, &r.1);
        let l_r_mul = inner_product(&l_add, &r_add);
        t.1 = l_r_mul - t.0 - t.2;

        // Generate x by committing to T_1, T_2 (line 49-54)
        let (T1, t1_blinding) = self.generators.pedersen_commitment(&t.1, &mut rng);
        let (T2, t2_blinding) = self.generators.pedersen_commitment(&t.2, &mut rng);

        let poly_commitment = PolyCommitment { T1, T2 };

        let papc = PartyAwaitingPolyChallenge {
            generators: self.generators.clone(),
            value_commitment: self.value_commitment.clone(),
            poly_commitment: poly_commitment.clone(),
            y: *y,
            z: *z,
            offset_z,
            l,
            r,
            t,
            v_blinding: self.v_blinding,
            a_blinding: self.a_blinding,
            s_blinding: self.s_blinding,
            t1_blinding,
            t2_blinding,
        };

        (papc, poly_commitment)
    }
}

impl PartyAwaitingPolyChallenge {
    pub fn apply_challenge(&self, x: &Scalar) -> ProofShare {
        // Generate final values for proof (line 55-60)
        let t_x_blinding = 
            self.t1_blinding * x + 
            self.t2_blinding * x * x +
            self.z * self.z * self.offset_z * self.v_blinding;

        let e_blinding = self.a_blinding + self.s_blinding * x;
        let t_hat = self.t.0 + self.t.1 * x + self.t.2 * x * x;

        let l_total = self.l.eval(x);
        let r_total = self.r.eval(x);

        ProofShare {
            generators: self.generators.clone(),
            value_commitment: self.value_commitment.clone(),
            poly_commitment: self.poly_commitment.clone(),
            t_x_blinding: t_x_blinding,
            e_blinding: e_blinding,
            t: t_hat,
            l: l_total,
            r: r_total,
        }
    }
}

impl DealerAwaitingPoly {
    pub fn present_poly_commitments(mut self, poly_commitments: &Vec<PolyCommitment>) -> (DealerAwaitingShares, Scalar) {
        // Commit sums of T1s and T2s.
        let mut T1 = RistrettoPoint::identity();
        let mut T2 = RistrettoPoint::identity();
        for commitment in poly_commitments.iter() {
            T1 += commitment.T1;
            T2 += commitment.T2;
        }

        self.transcript.commit(T1.compress().as_bytes());
        self.transcript.commit(T2.compress().as_bytes());

        let x = self.transcript.challenge_scalar();

        (DealerAwaitingShares {
            transcript: self.transcript,
            n: self.n,
            m: self.m
        }, x)
    }
}

impl DealerAwaitingShares {
    pub fn present_shares(&self, proof_shares: &Vec<ProofShare>) -> Proof {
        Proof {
            n: self.n,
            value_commitments: proof_shares.iter().map(|ps| ps.value_commitment.V.clone()).collect(),
            A: proof_shares.iter().fold(RistrettoPoint::identity(), |A, ps| A + ps.value_commitment.A),
            S: proof_shares.iter().fold(RistrettoPoint::identity(), |S, ps| S + ps.value_commitment.S),
            T1: proof_shares.iter().fold(RistrettoPoint::identity(), |T1, ps| T1 + ps.poly_commitment.T1),
            T2: proof_shares.iter().fold(RistrettoPoint::identity(), |T2, ps| T2 + ps.poly_commitment.T2),
            t_x_blinding: proof_shares.iter().fold(Scalar::zero(), |acc, ps| acc + ps.t_x_blinding),
            e_blinding: proof_shares.iter().fold(Scalar::zero(), |acc, ps| acc + ps.e_blinding),
            t: proof_shares.iter().fold(Scalar::zero(), |acc, ps| acc + ps.t),

            // FIXME: don't need if doing inner product proof
            l: proof_shares.iter().flat_map(|ps| ps.l.clone().into_iter()).collect(),
            r: proof_shares.iter().flat_map(|ps| ps.r.clone().into_iter()).collect(),
        }
    }
}

impl Proof {
    pub fn create_one<R: Rng>(v: u64, n: usize, rng: &mut R) -> Proof {
        Self::create_multi(vec![v], n, rng)
    }

    pub fn create_multi<R: Rng>(values: Vec<u64>, n: usize, rng: &mut R) -> Proof {
        let parties: Vec<_> = values.iter().map(|&v| Party::new(v, n, rng) ).collect();
        
        let dealer = Dealer::new(n, &parties).unwrap();

        let (parties, value_commitments): (Vec<_>,Vec<_>) =
            parties.iter().enumerate().map(|(j, p)| p.assign_position(j,rng) ).unzip();
        
        let (dealer, y, z) = dealer.present_value_commitments(&value_commitments);

        let (parties, poly_commitments): (Vec<_>,Vec<_>) =
            parties.iter().map(|p| p.apply_challenge( &y, &z, rng) ).unzip();

        let (dealer, x) = dealer.present_poly_commitments(&poly_commitments);

        let proof_shares: Vec<ProofShare> = parties.iter().map(|p| p.apply_challenge(&x) ).collect();

        dealer.present_shares(&proof_shares)
    }

    pub fn verify(&self) -> bool {
        let n = self.n;
        let m = self.value_commitments.len();

        let gen = RangeproofGenerators::new(n*m);

        let mut transcript = ProofTranscript::new(b"MultiRangeProof");
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        for V in self.value_commitments.iter() {
            transcript.commit(V.compress().as_bytes());
        }
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        unimplemented!();
        // ro.commit(&A.compress().as_bytes());
        // ro.commit(&S.compress().as_bytes());
        // let y = ro.challenge_scalar();
        // let z = ro.challenge_scalar();
        // ro.commit(&T_1.compress().as_bytes());
        // ro.commit(&T_2.compress().as_bytes());
        // let x = ro.challenge_scalar();

        // let G = make_generators(B, n * m);
        // let mut hprime_vec = make_generators(B_blinding, n * m);

        // // line 63: check that t = t0 + t1 * x + t2 * x * x
        // let z2 = z * z;
        // let z3 = z2 * z;
        // let mut power_g = Scalar::zero(); // delta(y,z)

        // // calculate power_g += (z - z^2) * <1^(n*m), y^(n*m)>
        // let mut exp_y = Scalar::one(); // start at y^0 = 1
        // let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        // for _ in 0..n * m {
        //     power_g += (z - z2) * exp_y;

        //     exp_y = exp_y * y; // y^i -> y^(i+1)
        //     exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        // }
        // // calculate power_g += sum_(j=1)^(m)(z^(j+2) * (2^n - 1))
        // let mut exp_z = z3;
        // for _ in 1..(m + 1) {
        //     power_g -= exp_z * Scalar::from_u64(((1u128 << n) - 1) as u64);
        //     exp_z = exp_z * z;
        // }

        // let mut t_check = B * power_g + T_1 * x + T_2 * x * x;
        // let mut exp_z = Scalar::one();
        // for j in 0..m {
        //     t_check += V[j] * z2 * exp_z;
        //     exp_z = exp_z * z;
        // }
        // let t_commit = B * self.t + B_blinding * self.t_x_blinding;
        // if t_commit != t_check {
        //     println!("fails check on line 63");
        //     return false;
        // }

        // // line 64: compute commitment to l, r
        // // calculate P: add A + S*x - G*z
        // let mut sum_G = RistrettoPoint::identity();
        // for i in 0..n * m {
        //     sum_G += G[i];
        // }
        // let mut P = A + S * x;
        // P -= sum_G * z;

        // // line 62: calculate hprime
        // // calculate P: add < vec(h'), z * vec(y)^n*m >
        // let mut exp_y = Scalar::one(); // start at y^0 = 1
        // let inverse_y = Scalar::invert(&y); // inverse_y = 1/y
        // let mut inv_exp_y = Scalar::one(); // start at y^-0 = 1
        // for i in 0..n * m {
        //     hprime_vec[i] = hprime_vec[i] * inv_exp_y;
        //     P += hprime_vec[i] * z * exp_y;

        //     exp_y = exp_y * y; // y^i -> y^(i+1)
        //     exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        //     inv_exp_y = inv_exp_y * inverse_y; // y^(-i) * y^(-1) -> y^(-(i+1))
        // }

        // // calculate P: add sum(j_1^m)(<H[(j-1)*n:j*n-1], z^(j+1)*vec(2)^n>)
        // let mut exp_z = z * z;
        // for j in 1..(m + 1) {
        //     exp_2 = Scalar::one();
        //     for index in 0..n {
        //         // index into hprime, from [(j-1)*n : j*n-1]
        //         P += hprime_vec[(j - 1) * n + index] * exp_z * exp_2;
        //         exp_2 = exp_2 + exp_2;
        //     }
        //     exp_z = exp_z * z;
        // }

        // // line 65: check that l, r are correct
        // let mut P_check = B_blinding * self.e_blinding;
        // let points_iter = G.iter().chain(hprime_vec.iter());
        // let scalars_iter = self.l.iter().chain(self.r.iter());
        // P_check += ristretto::multiscalar_mult(scalars_iter, points_iter);
        // if P != P_check {
        //     println!("fails check on line 65: P != g * l + hprime * r");
        //     return false;
        // }

        // // line 66: check that t is correct
        // if self.t != inner_product(&self.l, &self.r) {
        //     println!("fails check on line 66: t != l * r");
        //     return false;
        // }

        // return true;
    }
}


struct Poly3(Scalar, Scalar, Scalar);
struct VecPoly2(Vec<Scalar>, Vec<Scalar>);

impl Poly3 {
    pub fn new() -> Poly3 {
        Poly3(Scalar::zero(), Scalar::zero(), Scalar::zero())
    }
}

impl VecPoly2 {
    pub fn new(n: usize) -> VecPoly2 {
        VecPoly2(vec![Scalar::zero(); n], vec![Scalar::zero(); n])
    }
    pub fn eval(&self, x: &Scalar) -> Vec<Scalar> {
        self.0.iter().
            zip(self.1.iter()).
            map(|(a,b)| a + x*b ).
            collect()
        // let n = self.0.len();
        // let mut out = vec![Scalar::zero(); n];
        // for i in 0..n {
        //     out[i] += self.0[i] + self.1[i] * x;
        // }
        // out
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
    use rand::Rng;
    use std::iter;
    use curve25519_dalek::ristretto;
    use curve25519_dalek::ristretto::RistrettoPoint;
    use curve25519_dalek::scalar::Scalar;

    /// Each party has their own set of generators based on their position (`j`).
    #[derive(Clone)]
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

        /// Creates a new pedersen commitment
        pub fn pedersen_commitment<R: Rng>(&self, scalar: &Scalar, mut rng: &mut R) -> (RistrettoPoint, Scalar) {
            let blinding = Scalar::random(&mut rng);
            ((self.B * scalar + self.B_b * blinding), blinding)
        }

        /// Creates a new vector pedersen commitment
        pub fn vector_pedersen_commitment<'a, I, R>(&self, scalars: I, mut rng: &mut R) -> (RistrettoPoint, Scalar)
            where I: IntoIterator<Item = &'a Scalar>,
                  R: Rng
        {
            let blinding = Scalar::random(&mut rng);
            // FIXME: we do this because of lifetime mismatch of scalars and &blinding.
            let scalars: Vec<_> = scalars.into_iter().collect();
            let C = ristretto::multiscalar_mult(
                iter::once(&blinding).chain(scalars.into_iter()),
                iter::once(&self.B_b).chain(self.G.iter()).chain(self.H.iter())
            );

            (C, blinding)
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
        // for n in vec![1, 16, 32] {
        //     let rp = Proof::create_one(0, n);
        //     assert_eq!(rp.verify(1), true);
        //     let rp = Proof::create_one(2u64.pow(n as u32) - 1, n);
        //     assert_eq!(rp.verify(1), true);
        //     let rp = Proof::create_one(2u64.pow(n as u32), n);
        //     assert_eq!(rp.verify(1), false);
        //     let rp = Proof::create_one(2u64.pow(n as u32) + 1, n);
        //     assert_eq!(rp.verify(1), false);
        //     let rp = Proof::create_one(u64::max_value(), n);
        //     assert_eq!(rp.verify(1), false);
        // }
    }
    #[test]
    fn one_party_u64() {
        // let n = 64;
        // let rp = Proof::create_one(0, n);
        // assert_eq!(rp.verify(1), true);
        // let rp = Proof::create_one(1, n);
        // assert_eq!(rp.verify(1), true);
        // let rp = Proof::create_one(u64::max_value(), n);
        // assert_eq!(rp.verify(1), true);
    }
    #[test]
    fn two_party_small() {
        // for n in vec![1, 16, 32] {
        //     let rp = Proof::create_multi(vec![1, 1], n);
        //     assert_eq!(rp.verify(2), true);
        //     let rp = Proof::create_multi(vec![0, 1], n);
        //     assert_eq!(rp.verify(2), true);
        //     let rp = Proof::create_multi(vec![1, 0], n);
        //     assert_eq!(rp.verify(2), true);
        //     let rp = Proof::create_multi(vec![0, 0], n);
        //     assert_eq!(rp.verify(2), true);
        //     let rp = Proof::create_multi(vec![2u64.pow(n as u32) - 1, 1], n);
        //     assert_eq!(rp.verify(2), true);
        //     let rp = Proof::create_multi(vec![2u64.pow(n as u32) + 1, 0], n);
        //     assert_eq!(rp.verify(2), false);
        //     let rp = Proof::create_multi(vec![0, u64::max_value()], n);
        //     assert_eq!(rp.verify(2), false);
        // }
    }
    #[test]
    fn two_party_u64() {
        // let n = 64;
        // let rp = Proof::create_multi(vec![u64::max_value(), 1], n);
        // assert_eq!(rp.verify(2), true);
        // let rp = Proof::create_multi(vec![0, u64::max_value() - 1], n);
        // assert_eq!(rp.verify(2), true);
    }
    #[test]
    fn ten_party_small() {
        // let m = 10;
        // for n in vec![1, 16, 32] {
        //     let rp = Proof::create_multi(vec![1, 1, 0, 0, 1, 1, 0, 0, 1, 1], n);
        //     assert_eq!(rp.verify(m), true);
        //     let rp = Proof::create_multi(
        //         vec![
        //             2u64.pow(n as u32) - 1,
        //             2u64.pow(n as u32) - 1,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             1,
        //             1,
        //         ],
        //         n,
        //     );
        //     assert_eq!(rp.verify(m), true);
        //     let rp =
        //         Proof::create_multi(vec![2u64.pow(n as u32) + 1, 0, 0, 0, 0, 0, 0, 0, 1, 1], n);
        //     assert_eq!(rp.verify(m), false);
        //     let rp = Proof::create_multi(vec![0, u64::max_value(), 0, 0, 0, 0, 0, 0, 1, 1], n);
        //     assert_eq!(rp.verify(m), false);
        // }
    }
    #[test]
    fn ten_party_u64() {
        // let m = 10;
        // let n = 64;
        // let rp = Proof::create_multi(
        //     vec![u64::max_value(), u64::max_value(), 0, 0, 1, 1, 0, 0, 1, 1],
        //     n,
        // );
        // assert_eq!(rp.verify(m), true);
        // let rp = Proof::create_multi(
        //     vec![
        //         u64::max_value() - 1,
        //         1,
        //         0,
        //         0,
        //         0,
        //         0,
        //         0,
        //         0,
        //         1,
        //         u64::max_value() / 2,
        //     ],
        //     n,
        // );
        // assert_eq!(rp.verify(m), true);
    }
    #[test]
    fn rand_small() {
        // for _ in 0..10 {
        //     let mut rng: OsRng = OsRng::new().unwrap();
        //     let v: u32 = rng.next_u32();
        //     let rp = Proof::create_one(v as u64, 32);
        //     assert_eq!(rp.verify(1), true);
        // }
    }
    #[test]
    fn rand_u32() {
        // for _ in 0..10 {
        //     let mut rng: OsRng = OsRng::new().unwrap();
        //     let v = rng.next_u32() as u64;
        //     let rp = Proof::create_one(v, 32);
        //     assert_eq!(rp.verify(1), true);
        // }
    }
    #[test]
    fn rand_u64() {
        // for _ in 0..10 {
        //     let mut rng: OsRng = OsRng::new().unwrap();
        //     let v = rng.next_u64();
        //     let rp = Proof::create_one(v, 64);
        //     assert_eq!(rp.verify(1), true);
        // }
    }
}

// #[cfg(test)]
// mod bench {
//     use super::*;
//     use rand::Rng;
//     use test::Bencher;

//     #[bench]
//     fn make_u64(b: &mut Bencher) {
//         let mut rng: OsRng = OsRng::new().unwrap();
//         b.iter(|| Proof::create_one(rng.next_u64(), 64));
//     }
//     #[bench]
//     fn make_u32(b: &mut Bencher) {
//         let mut rng: OsRng = OsRng::new().unwrap();
//         b.iter(|| Proof::create_one(rng.next_u32() as u64, 32));
//     }
//     #[bench]
//     fn verify_u64(b: &mut Bencher) {
//         let mut rng: OsRng = OsRng::new().unwrap();
//         let rp = Proof::create_one(rng.next_u64(), 64);
//         b.iter(|| rp.verify(1));
//     }
//     #[bench]
//     fn verify_u32(b: &mut Bencher) {
//         let mut rng: OsRng = OsRng::new().unwrap();
//         let rp = Proof::create_one(rng.next_u32() as u64, 32);
//         b.iter(|| rp.verify(1));
//     }
// }
