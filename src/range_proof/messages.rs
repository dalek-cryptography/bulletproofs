//! The `messages` module contains the API for the messages passed between the parties and the dealer
//! in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

use generators::{BulletproofGens, PedersenGens};

/// A byte array that holds a Scalar
pub type CurvePoint = [u8; 32];
/// A byte array that holds a CompressedRistretto
pub type CurveScalar = [u8; 32];

/// A commitment to the bits of a party's value.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct BitCommitment {
    pub(super) V_j: CurvePoint,
    pub(super) A_j: CurvePoint,
    pub(super) S_j: CurvePoint,
}

/// Challenge values derived from all parties' [`BitCommitment`]s.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct BitChallenge {
    pub(super) y: CurveScalar,
    pub(super) z: CurveScalar,
}

/// A commitment to a party's polynomial coefficents.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyCommitment {
    pub(super) T_1_j: CurvePoint,
    pub(super) T_2_j: CurvePoint,
}

/// Challenge values derived from all parties' [`PolyCommitment`]s.
#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyChallenge {
    pub(super) x: CurveScalar,
}

/// A party's proof share, ready for aggregation into the final
/// [`RangeProof`](::RangeProof).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ProofShare {
    pub(super) t_x: CurveScalar,
    pub(super) t_x_blinding: CurveScalar,
    pub(super) e_blinding: CurveScalar,
    pub(super) l_vec: Vec<CurveScalar>,
    pub(super) r_vec: Vec<CurveScalar>,
}

impl ProofShare {
    /// Audit an individual proof share to determine whether it is
    /// malformed.
    pub(super) fn audit_share(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        j: usize,
        bit_commitment: &BitCommitment,
        bit_challenge: &BitChallenge,
        poly_commitment: &PolyCommitment,
        poly_challenge: &PolyChallenge,
    ) -> Result<(), ()> {
        use std::iter;

        use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

        use inner_product_proof::inner_product;
        use util;

        let n = self.l_vec.len();
        let (y, z) = (&Scalar::from_bytes_mod_order(bit_challenge.y), &Scalar::from_bytes_mod_order(bit_challenge.z));
        let x = &Scalar::from_bytes_mod_order(poly_challenge.x);
        let e_blinding = &Scalar::from_bytes_mod_order(self.e_blinding);

        // Precompute some variables
        let zz = z * z;
        let minus_z = -z;
        let z_j = util::scalar_exp_vartime(z, j as u64); // z^j
        let y_jn = util::scalar_exp_vartime(y, (j * n) as u64); // y^(j*n)
        let y_jn_inv = y_jn.invert(); // y^(-j*n)
        let y_inv = y.invert(); // y^(-1)
        let l_vec: Vec<Scalar> = self.l_vec.iter().map(|s| Scalar::from_bytes_mod_order(*s)).collect();
        let r_vec: Vec<Scalar> = self.r_vec.iter().map(|s| Scalar::from_bytes_mod_order(*s)).collect();
        let t_x: Scalar = Scalar::from_bytes_mod_order(self.t_x);
        
        if t_x != inner_product(&l_vec, &r_vec) {
            return Err(());
        }

        let g = l_vec.iter().map(|l_i| minus_z - l_i);
        let h = r_vec
            .iter()
            .zip(util::exp_iter(Scalar::from(2u64)))
            .zip(util::exp_iter(y_inv))
            .map(|((r_i, exp_2), exp_y_inv)| {
                z + exp_y_inv * y_jn_inv * (-r_i) + exp_y_inv * y_jn_inv * (zz * z_j * exp_2)
            });

        let P_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(*x))
                .chain(iter::once(-e_blinding))
                .chain(g)
                .chain(h),
            iter::once(&CompressedRistretto::from_slice(&bit_commitment.A_j).decompress().unwrap())
                .chain(iter::once(&CompressedRistretto::from_slice(&bit_commitment.S_j).decompress().unwrap()))
                .chain(iter::once(&pc_gens.B_blinding))
                .chain(bp_gens.share(j).G(n))
                .chain(bp_gens.share(j).H(n)),
        );
        if !P_check.is_identity() {
            return Err(());
        }

        let V_j = CompressedRistretto::from_slice(&bit_commitment.V_j).decompress().ok_or(())?;

        let sum_of_powers_y = util::sum_of_powers(&y, n);
        let sum_of_powers_2 = util::sum_of_powers(&Scalar::from(2u64), n);
        let delta = (z - zz) * sum_of_powers_y * y_jn - z * zz * sum_of_powers_2 * z_j;
        let t_x_blinding: Scalar = Scalar::from_bytes_mod_order(self.t_x_blinding);
        let T_1_j = CompressedRistretto::from_slice(&poly_commitment.T_1_j).decompress().ok_or(())?;
        let T_2_j = CompressedRistretto::from_slice(&poly_commitment.T_2_j).decompress().ok_or(())?;
        let t_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(zz * z_j)
                .chain(iter::once(*x))
                .chain(iter::once(x * x))
                .chain(iter::once(delta - t_x))
                .chain(iter::once(-t_x_blinding)),
            iter::once(&V_j)
                .chain(iter::once(&T_1_j))
                .chain(iter::once(&T_2_j))
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
