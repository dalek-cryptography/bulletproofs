//! The `party` module contains the API for the party state while the party is
//! engaging in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use generators::Generators;
use rand::{CryptoRng, Rng};
use std::iter;
use util;

use super::messages::*;

/// Party is an entry-point API for setting up a party.
pub struct Party {}

impl Party {
    pub fn new(
        v: u64,
        v_blinding: Scalar,
        n: usize,
        generators: &Generators,
    ) -> Result<PartyAwaitingPosition, &'static str> {
        if !n.is_power_of_two() || n > 64 {
            return Err("n is not valid: must be a power of 2, and less than or equal to 64");
        }
        let V = generators
            .share(0)
            .pedersen_generators
            .commit(Scalar::from_u64(v), v_blinding);

        Ok(PartyAwaitingPosition {
            generators,
            n,
            v,
            v_blinding,
            V,
        })
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
    pub fn assign_position<R: Rng + CryptoRng>(
        self,
        j: usize,
        rng: &mut R,
    ) -> (PartyAwaitingValueChallenge<'a>, ValueCommitment) {
        let gen_share = self.generators.share(j);

        let a_blinding = Scalar::random(rng);
        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding
        let mut A = gen_share.pedersen_generators.B_blinding * a_blinding;

        use subtle::{Choice, ConditionallyAssignable};
        for i in 0..self.n {
            // If v_i = 0, we add a_L[i] * G[i] + a_R[i] * H[i] = - H[i]
            // If v_i = 1, we add a_L[i] * G[i] + a_R[i] * H[i] =   G[i]
            let v_i = Choice::from(((self.v >> i) & 1) as u8);
            let mut point = -gen_share.H[i];
            point.conditional_assign(&gen_share.G[i], v_i);
            A += point;
        }

        let s_blinding = Scalar::random(rng);
        let s_L: Vec<Scalar> = (0..self.n).map(|_| Scalar::random(rng)).collect();
        let s_R: Vec<Scalar> = (0..self.n).map(|_| Scalar::random(rng)).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(&gen_share.pedersen_generators.B_blinding)
                .chain(gen_share.G.iter())
                .chain(gen_share.H.iter()),
        );

        // Return next state and all commitments
        let value_commitment = ValueCommitment {
            V_j: self.V,
            A_j: A,
            S_j: S,
        };
        let next_state = PartyAwaitingValueChallenge {
            n: self.n,
            v: self.v,
            v_blinding: self.v_blinding,
            generators: self.generators,
            j,
            a_blinding,
            s_blinding,
            s_L,
            s_R,
        };
        (next_state, value_commitment)
    }
}

/// When party knows its position (`j`), it can produce commitments
/// to all bits of the value and necessary blinding factors.
pub struct PartyAwaitingValueChallenge<'a> {
    n: usize, // bitsize of the range
    v: u64,
    v_blinding: Scalar,

    j: usize,
    generators: &'a Generators,
    a_blinding: Scalar,
    s_blinding: Scalar,
    s_L: Vec<Scalar>,
    s_R: Vec<Scalar>,
}

impl<'a> PartyAwaitingValueChallenge<'a> {
    pub fn apply_challenge<R: Rng + CryptoRng>(
        self,
        vc: &ValueChallenge,
        rng: &mut R,
    ) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
        let n = self.n;
        let offset_y = util::scalar_exp_vartime(&vc.y, (self.j * n) as u64);
        let offset_z = util::scalar_exp_vartime(&vc.z, self.j as u64);

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l_poly = util::VecPoly1::zero(n);
        let mut r_poly = util::VecPoly1::zero(n);

        let zz = vc.z * vc.z;
        let mut exp_y = offset_y; // start at y^j
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for i in 0..n {
            let a_L_i = Scalar::from_u64((self.v >> i) & 1);
            let a_R_i = a_L_i - Scalar::one();

            l_poly.0[i] = a_L_i - vc.z;
            l_poly.1[i] = self.s_L[i];
            r_poly.0[i] = exp_y * (a_R_i + vc.z) + zz * offset_z * exp_2;
            r_poly.1[i] = exp_y * self.s_R[i];

            exp_y *= vc.y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

        // Generate x by committing to T_1, T_2 (line 49-54)
        let t_1_blinding = Scalar::random(rng);
        let t_2_blinding = Scalar::random(rng);
        let T_1 = self
            .generators
            .share(self.j)
            .pedersen_generators
            .commit(t_poly.1, t_1_blinding);
        let T_2 = self
            .generators
            .share(self.j)
            .pedersen_generators
            .commit(t_poly.2, t_2_blinding);

        let poly_commitment = PolyCommitment {
            T_1_j: T_1,
            T_2_j: T_2,
        };

        let papc = PartyAwaitingPolyChallenge {
            z: vc.z,
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

pub struct PartyAwaitingPolyChallenge {
    z: Scalar,
    offset_z: Scalar,
    l_poly: util::VecPoly1,
    r_poly: util::VecPoly1,
    t_poly: util::Poly2,
    v_blinding: Scalar,
    a_blinding: Scalar,
    s_blinding: Scalar,
    t_1_blinding: Scalar,
    t_2_blinding: Scalar,
}

impl PartyAwaitingPolyChallenge {
    pub fn apply_challenge(self, pc: &PolyChallenge) -> Result<ProofShare, &'static str> {
        // Prevent a malicious dealer from annihilating the blinding factors:
        if pc.x == Scalar::zero() {
            return Err("Poly challenge was zero, which would leak secrets, bailing out");
        }

        let t_blinding_poly = util::Poly2(
            self.z * self.z * self.offset_z * self.v_blinding,
            self.t_1_blinding,
            self.t_2_blinding,
        );

        let t_x = self.t_poly.eval(pc.x);
        let t_x_blinding = t_blinding_poly.eval(pc.x);
        let e_blinding = self.a_blinding + self.s_blinding * &pc.x;
        let l_vec = self.l_poly.eval(pc.x);
        let r_vec = self.r_poly.eval(pc.x);

        Ok(ProofShare {
            t_x_blinding,
            t_x,
            e_blinding,
            l_vec,
            r_vec,
        })
    }
}
