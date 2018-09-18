//! The `messages` module contains the API for the messages passed between the parties and the dealer
//! in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

use generators::{BulletproofGens, PedersenGens};

/// XXX rename this to `BitCommitment`
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct ValueCommitment {
    pub V_j: RistrettoPoint,
    pub A_j: RistrettoPoint,
    pub S_j: RistrettoPoint,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct ValueChallenge {
    pub y: Scalar,
    pub z: Scalar,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyCommitment {
    pub T_1_j: RistrettoPoint,
    pub T_2_j: RistrettoPoint,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyChallenge {
    pub x: Scalar,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ProofShare {
    pub t_x: Scalar,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,

    pub l_vec: Vec<Scalar>,
    pub r_vec: Vec<Scalar>,
}

impl ProofShare {
    /// Audit an individual proof share to determine whether it is
    /// malformed.
    pub(crate) fn audit_share(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        j: usize,
        value_commitment: &ValueCommitment,
        value_challenge: &ValueChallenge,
        poly_commitment: &PolyCommitment,
        poly_challenge: &PolyChallenge,
    ) -> Result<(), ()> {
        use std::iter;

        use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

        use inner_product_proof::inner_product;
        use util;

        let n = self.l_vec.len();
        let (y, z) = (&value_challenge.y, &value_challenge.z);
        let x = &poly_challenge.x;

        // Precompute some variables
        let zz = z * z;
        let minus_z = -z;
        let z_j = util::scalar_exp_vartime(z, j as u64); // z^j
        let y_jn = util::scalar_exp_vartime(y, (j * n) as u64); // y^(j*n)
        let y_jn_inv = y_jn.invert(); // y^(-j*n)
        let y_inv = y.invert(); // y^(-1)

        if self.t_x != inner_product(&self.l_vec, &self.r_vec) {
            return Err(());
        }

        let g = self.l_vec.iter().map(|l_i| minus_z - l_i);
        let h = self
            .r_vec
            .iter()
            .zip(util::exp_iter(Scalar::from(2u64)))
            .zip(util::exp_iter(y_inv))
            .map(|((r_i, exp_2), exp_y_inv)| {
                z + exp_y_inv * y_jn_inv * (-r_i) + exp_y_inv * y_jn_inv * (zz * z_j * exp_2)
            });

        let P_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(*x))
                .chain(iter::once(-self.e_blinding))
                .chain(g)
                .chain(h),
            iter::once(&value_commitment.A_j)
                .chain(iter::once(&value_commitment.S_j))
                .chain(iter::once(&pc_gens.B_blinding))
                .chain(bp_gens.share(j).G(n))
                .chain(bp_gens.share(j).H(n)),
        );
        if !P_check.is_identity() {
            return Err(());
        }

        let sum_of_powers_y = util::sum_of_powers(&y, n);
        let sum_of_powers_2 = util::sum_of_powers(&Scalar::from(2u64), n);
        let delta = (z - zz) * sum_of_powers_y * y_jn - z * zz * sum_of_powers_2 * z_j;
        let t_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(zz * z_j)
                .chain(iter::once(*x))
                .chain(iter::once(x * x))
                .chain(iter::once(delta - self.t_x))
                .chain(iter::once(-self.t_x_blinding)),
            iter::once(&value_commitment.V_j)
                .chain(iter::once(&poly_commitment.T_1_j))
                .chain(iter::once(&poly_commitment.T_2_j))
                .chain(iter::once(&pc_gens.B))
                .chain(iter::once(&pc_gens.B_blinding)),
        );

        if t_check.is_identity() {
            Ok(())
        } else {
            Err(())
        }
    }
}
