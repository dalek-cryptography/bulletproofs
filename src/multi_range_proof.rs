#![allow(non_snake_case)]
//#![deny(missing_docs)]

use std::iter;
use rand::Rng;
use curve25519_dalek::ristretto;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::{Identity, IsIdentity};
use curve25519_dalek::scalar::Scalar;
use std::clone::Clone;
use scalar::scalar_pow_vartime;
use proof_transcript::ProofTranscript;
use generators::{Generators, GeneratorsView};
use util::{self, PolyDeg3, VecPoly2};
use inner_product_proof;

/// Party is an entry-point API for setting up a party.
pub struct Party {}

impl Party {
    pub fn new<'a, 'b, R: Rng>(
        value: u64,
        n: usize,
        gen: &'a Generators,
        mut rng: &'b mut R,
    ) -> PartyAwaitingPosition<'a> {
        let (V, v_blinding) = pedersen_commitment(&Scalar::from_u64(value), &gen.all(), &mut rng);
        PartyAwaitingPosition {
            generators: gen,
            n,
            v: value,
            v_blinding,
            V,
        }
    }
}

/// Dealer is an entry-point API for setting up a dealer
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer with the given parties and a number of bits
    pub fn new(
        n: usize,
        parties: &Vec<PartyAwaitingPosition>,
    ) -> Result<DealerAwaitingValues, &'static str> {
        if let Some(_) = parties.iter().find(|&x| x.n != n) {
            return Err("Inconsistent n among parties!");
        }
        let mut transcript = ProofTranscript::new(b"MultiRangeProof");
        let m = parties.len();
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        Ok(DealerAwaitingValues { transcript, n })
    }
}

/// As party awaits its position, they only know their value and desired bit-size of the proof.
pub struct PartyAwaitingPosition<'a> {
    generators: &'a Generators,
    n: usize,
    v: u64,
    v_blinding: Scalar,
    V: RistrettoPoint,
}

impl<'a> PartyAwaitingPosition<'a> {
    /// Assigns the position to a party,
    /// at which point the party knows its generators.
    pub fn assign_position<R: Rng>(
        &self,
        j: usize,
        mut rng: &mut R,
    ) -> (PartyAwaitingValueChallenge<'a>, ValueCommitment) {
        let gen_share = self.generators.share(j);

        let a_blinding = Scalar::random(&mut rng);
        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding
        let mut A = gen_share.B_blinding * a_blinding;
        for i in 0..self.n {
            let v_i = (self.v >> i) & 1;
            // XXX replace this with a conditional move
            if v_i == 1 {
                A += gen_share.G[i]; // + bit*G_i
            } else {
                A -= gen_share.H[i]; // + (bit-1)*H_i
            }
        }

        let s_blinding = Scalar::random(&mut rng);
        let s_L: Vec<Scalar> = (0..self.n).map(|_| Scalar::random(&mut rng)).collect();
        let s_R: Vec<Scalar> = (0..self.n).map(|_| Scalar::random(&mut rng)).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = ristretto::multiscalar_mult(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(gen_share.B_blinding)
                .chain(gen_share.G.iter())
                .chain(gen_share.H.iter()),
        );

        // Return next state and all commitments
        let value_commitment = ValueCommitment { V: self.V, A, S };
        let next_state = PartyAwaitingValueChallenge {
            n: self.n,
            v: self.v,
            v_blinding: self.v_blinding,

            j,
            generators: self.generators,
            value_commitment: value_commitment.clone(),
            a_blinding,
            s_blinding,
            s_L,
            s_R,
        };
        (next_state, value_commitment)
    }
}

/// When the dealer is initialized, it only knows the size of the set.
pub struct DealerAwaitingValues {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingValues {
    /// Combines commitments and computes challenge variables.
    pub fn present_value_commitments(
        mut self,
        vc: &Vec<ValueCommitment>,
    ) -> (DealerAwaitingPoly, Scalar, Scalar) {
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

        (
            DealerAwaitingPoly {
                transcript: self.transcript,
                n: self.n,
            },
            y,
            z,
        )
    }
}

#[derive(Clone)]
pub struct ValueCommitment {
    pub V: RistrettoPoint,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,
}

/// When party knows its position (`j`), it can produce commitments
/// to all bits of the value and necessary blinding factors.
pub struct PartyAwaitingValueChallenge<'a> {
    n: usize, // bitsize of the range
    v: u64,
    v_blinding: Scalar,

    j: usize, // index of the party, 1..m as in original paper
    generators: &'a Generators,
    value_commitment: ValueCommitment,
    a_blinding: Scalar,
    s_blinding: Scalar,
    s_L: Vec<Scalar>,
    s_R: Vec<Scalar>,
}

impl<'a> PartyAwaitingValueChallenge<'a> {
    pub fn apply_challenge<R: Rng>(
        &self,
        y: &Scalar,
        z: &Scalar,
        rng: &mut R,
    ) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
        let n = self.n;
        let offset_y = scalar_pow_vartime(&y, (self.j * n) as u64);
        let offset_z = scalar_pow_vartime(&z, self.j as u64);

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l_poly = VecPoly2::zero(n);
        let mut r_poly = VecPoly2::zero(n);

        let zz = z * z;
        let mut exp_y = offset_y; // start at y^j
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..n {
            let a_L_i = Scalar::from_u64((self.v >> i) & 1);
            let a_R_i = a_L_i - Scalar::one();

            l_poly.0[i] = a_L_i - z;
            l_poly.1[i] = self.s_L[i];
            r_poly.0[i] = exp_y * (a_R_i + z) + zz * offset_z * exp_2;
            r_poly.1[i] = exp_y * self.s_R[i];

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

        // Generate x by committing to T_1, T_2 (line 49-54)
        let (T_1, t_1_blinding) =
            pedersen_commitment(&t_poly.1, &self.generators.share(self.j), rng);
        let (T_2, t_2_blinding) =
            pedersen_commitment(&t_poly.2, &self.generators.share(self.j), rng);

        let poly_commitment = PolyCommitment { T_1, T_2 };

        let papc = PartyAwaitingPolyChallenge {
            value_commitment: self.value_commitment.clone(),
            poly_commitment: poly_commitment.clone(),
            z: *z,
            offset_z,
            l_poly,
            r_poly,
            t_poly,
            v_blinding: self.v_blinding,
            a_blinding: self.a_blinding,
            s_blinding: self.s_blinding,
            t_1_blinding,
            t_2_blinding,
        };

        (papc, poly_commitment)
    }
}

#[derive(Clone)]
pub struct PolyCommitment {
    pub T_1: RistrettoPoint,
    pub T_2: RistrettoPoint,
}

pub struct PartyAwaitingPolyChallenge {
    value_commitment: ValueCommitment,
    poly_commitment: PolyCommitment,

    z: Scalar,
    offset_z: Scalar,
    l_poly: VecPoly2,
    r_poly: VecPoly2,
    t_poly: PolyDeg3,
    v_blinding: Scalar,
    a_blinding: Scalar,
    s_blinding: Scalar,
    t_1_blinding: Scalar,
    t_2_blinding: Scalar,
}

impl PartyAwaitingPolyChallenge {
    pub fn apply_challenge(&self, x: &Scalar) -> ProofShare {
        // Generate final values for proof (line 55-60)
        let t_blinding_poly = PolyDeg3(
            self.z * self.z * self.offset_z * self.v_blinding,
            self.t_1_blinding,
            self.t_2_blinding,
        );

        let t_x = self.t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let e_blinding = self.a_blinding + self.s_blinding * x;
        let l_vec = self.l_poly.eval(*x);
        let r_vec = self.r_poly.eval(*x);

        ProofShare {
            value_commitment: self.value_commitment.clone(),
            poly_commitment: self.poly_commitment.clone(),
            t_x_blinding,
            t_x,
            e_blinding,
            l_vec,
            r_vec,
        }
    }
}

#[derive(Clone)]
pub struct ProofShare {
    pub value_commitment: ValueCommitment,
    pub poly_commitment: PolyCommitment,

    pub t_x: Scalar,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,

    pub l_vec: Vec<Scalar>,
    pub r_vec: Vec<Scalar>,
}

pub struct DealerAwaitingPoly {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingPoly {
    pub fn present_poly_commitments(
        mut self,
        poly_commitments: &Vec<PolyCommitment>,
    ) -> (DealerAwaitingShares, Scalar) {
        // Commit sums of T1s and T2s.
        let mut T1 = RistrettoPoint::identity();
        let mut T2 = RistrettoPoint::identity();
        for commitment in poly_commitments.iter() {
            T1 += commitment.T_1;
            T2 += commitment.T_2;
        }
        self.transcript.commit(T1.compress().as_bytes());
        self.transcript.commit(T2.compress().as_bytes());

        let x = self.transcript.challenge_scalar();

        (
            DealerAwaitingShares {
                transcript: self.transcript,
                n: self.n,
            },
            x,
        )
    }
}

pub struct DealerAwaitingShares {
    transcript: ProofTranscript,
    n: usize,
}

impl DealerAwaitingShares {
    pub fn present_shares(
        mut self,
        proof_shares: &Vec<ProofShare>,
        gen: &GeneratorsView,
        y: Scalar,
    ) -> Proof {
        let value_commitments = proof_shares
            .iter()
            .map(|ps| ps.value_commitment.V.clone())
            .collect();
        let A = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |A, ps| A + ps.value_commitment.A,
        );
        let S = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |S, ps| S + ps.value_commitment.S,
        );
        let T_1 = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |T_1, ps| T_1 + ps.poly_commitment.T_1,
        );
        let T_2 = proof_shares.iter().fold(
            RistrettoPoint::identity(),
            |T_2, ps| T_2 + ps.poly_commitment.T_2,
        );
        let t = proof_shares.iter().fold(
            Scalar::zero(),
            |acc, ps| acc + ps.t_x,
        );
        let t_x_blinding = proof_shares.iter().fold(Scalar::zero(), |acc, ps| {
            acc + ps.t_x_blinding
        });
        let e_blinding = proof_shares.iter().fold(Scalar::zero(), |acc, ps| {
            acc + ps.e_blinding
        });
        self.transcript.commit(t.as_bytes());
        self.transcript.commit(t_x_blinding.as_bytes());
        self.transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar();
        let Q = w * gen.B;

        let l_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();
        let ipp_proof = inner_product_proof::Proof::create(
            &mut self.transcript,
            &Q,
            util::exp_iter(y.invert()),
            gen.G.to_vec(),
            gen.H.to_vec(),
            l_vec.clone(),
            r_vec.clone(),
        );

        Proof {
            n: self.n,
            value_commitments,
            A,
            S,
            T_1,
            T_2,
            t_x: t,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            l: l_vec,
            r: r_vec,
        }
    }
}

pub struct Proof {
    pub n: usize,
    /// Commitment to the value
    // XXX this should not be included, so that we can prove about existing commitments
    // included for now so that it's easier to test
    pub value_commitments: Vec<RistrettoPoint>,
    /// Commitment to the bits of the value
    pub A: RistrettoPoint,
    /// Commitment to the blinding factors
    pub S: RistrettoPoint,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub T_1: RistrettoPoint,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    pub T_2: RistrettoPoint,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    pub t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    pub e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub ipp_proof: inner_product_proof::Proof,

    // FIXME: don't need if doing inner product proof
    pub l: Vec<Scalar>,
    pub r: Vec<Scalar>,
}

impl Proof {
    pub fn create_one<R: Rng>(v: u64, n: usize, rng: &mut R) -> Proof {
        Self::create_multi(vec![v], n, rng)
    }

    pub fn create_multi<R: Rng>(values: Vec<u64>, n: usize, rng: &mut R) -> Proof {
        let m = values.len();
        let generators = Generators::new(n, m);

        let parties: Vec<_> = values
            .iter()
            .map(|&v| Party::new(v, n, &generators, rng))
            .collect();

        let dealer = Dealer::new(n, &parties).unwrap();

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, y, z) = dealer.present_value_commitments(&value_commitments);

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .iter()
            .map(|p| p.apply_challenge(&y, &z, rng))
            .unzip();

        let (dealer, x) = dealer.present_poly_commitments(&poly_commitments);

        let proof_shares: Vec<ProofShare> = parties.iter().map(|p| p.apply_challenge(&x)).collect();

        dealer.present_shares(&proof_shares, &generators.all(), y)
    }

    pub fn verify<R: Rng>(&self, rng: &mut R) -> Result<(), ()> {
        let n = self.n;
        let m = self.value_commitments.len();

        let generators = Generators::new(n, m);
        let gen = generators.all();

        let mut transcript = ProofTranscript::new(b"MultiRangeProof");
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        for V in self.value_commitments.iter() {
            transcript.commit(V.compress().as_bytes());
        }
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();
        let zz = z * z;

/*
        // start copypasta
        let mut hprime_vec = gen.H.to_vec();
        let mut delta = Scalar::zero(); // delta(y,z)

        // // calculate delta += (z - z^2) * <1^(n*m), y^(n*m)>
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n * m {
            delta += (z - zz) * exp_y;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        // calculate delta += sum_(j=1)^(m)(z^(j+2) * (2^n - 1))
        let mut exp_z = zz * z;
        for _ in 1..(m + 1) {
            delta -= exp_z * Scalar::from_u64(((1u128 << n) - 1) as u64);
            exp_z = exp_z * z;
        }

        // TBD: put in a multiscalar mult
        let mut t_check = gen.B * delta + self.T_1 * x + self.T_2 * x * x;

        let mut exp_z = Scalar::one();
        for j in 0..m {
            t_check += self.value_commitments[j] * zz * exp_z;
            exp_z = exp_z * z;
        }
        let t_commit = gen.B * self.t_x + gen.B_blinding * self.t_x_blinding;
        if t_commit != t_check {
            println!("fails check on line 63");
            return Err(());
        }

        // line 64: compute commitment to l, r
        // calculate P: add A + S*x - G*z
        let mut sum_G = RistrettoPoint::identity();
        for i in 0..n * m {
            sum_G += gen.G[i];
        }
        let mut P = self.A + self.S * x;
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
        let mut P_check = gen.B_blinding * self.e_blinding;
        let points_iter = gen.G.iter().chain(hprime_vec.iter());
        let scalars_iter = self.l.iter().chain(self.r.iter());
        P_check += ristretto::multiscalar_mult(scalars_iter, points_iter);
        if P != P_check {
            println!("fails check on line 65: P != g * l + hprime * r");
            return Err(());
        }

        // line 66: check that t is correct
        if self.t_x != util::inner_product(&self.l, &self.r) {
            println!("fails check on line 66: t != l * r");
            return Err(());
        }

        return Ok(());
    }

*/
        let c = Scalar::random(rng);
        let t_check = ristretto::vartime::multiscalar_mult(
            util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp)
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(iter::once(- c * self.t_x_blinding))
                .chain(iter::once( c * (delta(n, m, &y, &z) - self.t_x))),
            self.value_commitments.iter()
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(iter::once(gen.B_blinding))
                .chain(iter::once(gen.B))
            );

        if t_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }
    }


/*
        let minus_z = -z;

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(&mut transcript);

        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        // (\vec(2) / \vec(y))^n
        let powers_of_2_over_y: Vec<Scalar> = util::exp_iter(Scalar::from_u64(2) * y.invert())
            .take(n)
            .collect();
        let powers_of_z = util::exp_iter(z).take(m);
        // z^0 (\vec(2) / \vec(y))^n || z^1 * (\vec(2) / \vec(y))^n || ... || z^(m-1)(\vec(2) / \vec(y))^n
        let z_2_over_y_concat = powers_of_z.flat_map(|exp_z| 
            powers_of_2_over_y.iter().map(move |exp_2_over_y| exp_2_over_y * exp_z)
            );

        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(z_2_over_y_concat)
            .map(|((s_i_inv, exp_y_inv), z_2_over_y)| {
                println!("z_2_over_y_concat {:?}", z_2_over_y);

                z - exp_y_inv * b * s_i_inv + zz * z_2_over_y
            });

        let mega_check = ristretto::vartime::multiscalar_mult(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(iter::once(
                    w * (self.t_x - a * b) +
                        c * (delta(n, m, &y, &z) - self.t_x),
                ))
                .chain(g)
                .chain(h)
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned()),
            iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(self.value_commitments.iter())
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(iter::once(gen.B_blinding))
                .chain(iter::once(gen.B))
                .chain(gen.G.iter())
                .chain(gen.H.iter())
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter()),
        );

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }
    }
*/
}

/// Compute
/// delta(y,z) = (z - z^2)<1^n*m, y^n*m> + z^3 <1, 2^n*m> * \sum_j=0^(m-1) z^j
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let two = Scalar::from_u64(2);

    // XXX this could be more efficient, esp for powers of 2
    let sum_of_powers_of_y = util::exp_iter(*y).take(n * m).fold(
        Scalar::zero(),
        |acc, x| acc + x,
    );

    // XXX TODO: just calculate (2^n - 1) instead
    let sum_of_powers_of_2 = util::exp_iter(two).take(n * m).fold(
        Scalar::zero(),
        |acc, x| acc + x,
    );

    let sum_of_powers_of_z = util::exp_iter(*z).take(m).fold(
        Scalar::zero(),
        |acc, x| acc + x,
    );

    let zz = z * z;

    (z - zz) * sum_of_powers_of_y - z * zz * sum_of_powers_of_2 * sum_of_powers_of_z
}

/// Creates a new pedersen commitment
fn pedersen_commitment<R: Rng>(
    scalar: &Scalar,
    generators: &GeneratorsView,
    mut rng: &mut R,
) -> (RistrettoPoint, Scalar) {
    let blinding = Scalar::random(&mut rng);

    let commitment = ristretto::multiscalar_mult(
        iter::once(scalar).chain(iter::once(&blinding)),
        iter::once(generators.B).chain(iter::once(generators.B_blinding)),
    );
    (commitment, blinding)
}

/// Creates a new vector pedersen commitment
pub fn vector_pedersen_commitment<'a, I, R>(
    scalars: I,
    generators: &GeneratorsView,
    mut rng: &mut R,
) -> (RistrettoPoint, Scalar)
where
    I: IntoIterator<Item = &'a Scalar>,
    R: Rng,
{
    let blinding = Scalar::random(&mut rng);
    // FIXME: we do this because of lifetime mismatch of scalars and &blinding.
    let scalars: Vec<_> = scalars.into_iter().collect();
    let C = ristretto::multiscalar_mult(
        iter::once(&blinding).chain(scalars.into_iter()),
        iter::once(generators.B_blinding)
            .chain(generators.G.iter())
            .chain(generators.H.iter()),
    );

    (C, blinding)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    fn construct_u32(m: usize) {
        let mut rng = OsRng::new().unwrap();

        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u32() as u64).take(m).collect();
        let rp = Proof::create_multi(v, 32, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
    }

    fn construct_u64(m: usize) {
        let mut rng = OsRng::new().unwrap();

        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u64()).take(m).collect();
        let rp = Proof::create_multi(v, 64, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
    }

    #[test]
    fn one_rangeproof() {
        let mut rng = OsRng::new().unwrap();
        let rp = Proof::create_one(0, 16, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
        let rp = Proof::create_one(12341, 16, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
    }

    #[test]
    fn two_rangeproofs() {
        construct_u32(2);
        construct_u64(2);
    }

    #[test]
    fn four_rangeproofs() {
        construct_u32(4);
        construct_u64(4);
    }

    #[test]
    fn eight_rangeproofs() {
        construct_u32(8);
        construct_u64(8);
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
