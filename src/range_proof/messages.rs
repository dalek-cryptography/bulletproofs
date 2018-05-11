//! The `messages` module contains the API for the messages passed between the parties and the dealer
//! in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use std::iter;

use curve25519_dalek::ristretto::{self, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use inner_product_proof;
use util;

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct ValueCommitment {
    pub V: RistrettoPoint,
    pub A: RistrettoPoint,
    pub S: RistrettoPoint,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct ValueChallenge {
    pub y: Scalar,
    pub z: Scalar,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyCommitment {
    pub T_1: RistrettoPoint,
    pub T_2: RistrettoPoint,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct PolyChallenge {
    pub x: Scalar,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ProofShare {
    pub value_commitment: ValueCommitment,
    pub poly_commitment: PolyCommitment,

    pub t_x: Scalar,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,

    pub l_vec: Vec<Scalar>,
    pub r_vec: Vec<Scalar>,
}

impl ProofShare {
    pub fn verify_share(
        &self,
        n: usize,
        j: usize,
        value_challenge: &ValueChallenge,
        poly_challenge: &PolyChallenge,
    ) -> Result<(), &'static str> {
        use generators::{Generators, PedersenGenerators};
        let generators = Generators::new(PedersenGenerators::default(), n, j + 1);
        let gen = generators.share(j);

        // renaming and precomputation
        let x = poly_challenge.x;
        let y = value_challenge.y;
        let z = value_challenge.z;
        let zz = z * z;
        let minus_z = -z;
        let z_j = util::exp_iter(z).take(j + 1).last().unwrap(); // z^j
        let y_jn = util::exp_iter(y).take(j * n + 1).last().unwrap(); // y^(j*n)
        let y_jn_inv = y_jn.invert(); // y^(-j*n)
        let y_inv = y.invert(); // y^(-1)

        if self.t_x != inner_product_proof::inner_product(&self.l_vec, &self.r_vec) {
            return Err("Inner product of l_vec and r_vec is not equal to t_x");
        }

        let g = self.l_vec.iter().map(|l_i| minus_z - l_i);
        let h = self.r_vec
            .iter()
            .zip(util::exp_iter(Scalar::from_u64(2)))
            .zip(util::exp_iter(y_inv))
            .map(|((r_i, exp_2), exp_y_inv)| {
                z + exp_y_inv * y_jn_inv * (-r_i) + exp_y_inv * y_jn_inv * (zz * z_j * exp_2)
            });
        let P_check = ristretto::vartime::multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(-self.e_blinding))
                .chain(g)
                .chain(h),
            iter::once(&self.value_commitment.A)
                .chain(iter::once(&self.value_commitment.S))
                .chain(iter::once(&gen.pedersen_generators.B_blinding))
                .chain(gen.G.iter())
                .chain(gen.H.iter()),
        );
        if !P_check.is_identity() {
            return Err("P check is not equal to zero");
        }

        let sum_of_powers_y = util::sum_of_powers(&y, n);
        let sum_of_powers_2 = util::sum_of_powers(&Scalar::from_u64(2), n);
        let delta = (z - zz) * sum_of_powers_y * y_jn - z * zz * sum_of_powers_2 * z_j;
        let t_check = ristretto::vartime::multiscalar_mul(
            iter::once(zz * z_j)
                .chain(iter::once(x))
                .chain(iter::once(x * x))
                .chain(iter::once(delta - self.t_x))
                .chain(iter::once(-self.t_x_blinding)),
            iter::once(&self.value_commitment.V)
                .chain(iter::once(&self.poly_commitment.T_1))
                .chain(iter::once(&self.poly_commitment.T_2))
                .chain(iter::once(&gen.pedersen_generators.B))
                .chain(iter::once(&gen.pedersen_generators.B_blinding)),
        );
        if !t_check.is_identity() {
            return Err("t check is not equal to zero");
        }

        Ok(())
    }
}
