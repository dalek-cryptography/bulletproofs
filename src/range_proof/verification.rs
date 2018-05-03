#![allow(non_snake_case)]

use rand::Rng;

use std::iter;
use std::borrow::Borrow;

use curve25519_dalek::ristretto;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use generators::GeneratorsView;
use proof_transcript::ProofTranscript;
use range_proof::RangeProof;
use util;

/// Represents a deferred computation to verify a single rangeproof. 
/// Multiple instances can be verified more efficient as a batch using
/// `RangeProof::verify_batch` function.
pub struct Verification {
	/// Number of commitments in the aggregated proof
	m: usize,

	/// Size of the range in bits
	n: usize,

	/// Pair of scalars multiplying pedersen bases `B`, `B_blinding`.
	pedersen_base_scalars: (Scalar, Scalar),

	/// List of scalars for `n*m` `G` bases. These are separated from `h_scalars`
	/// so we can easily pad them when verifying proofs with different `m`s.
	g_scalars: Vec<Scalar>,

	/// List of scalars for `n*m` `H` bases. These are separated from `g_scalars`
	/// so we can easily pad them when verifying proofs with different `m`s.
 	h_scalars: Vec<Scalar>,

 	/// List of scalars for any number of dynamic bases.
 	dynamic_base_scalars: Vec<Scalar>,

 	/// List of dynamic bases for the corresponding scalars.
 	dynamic_bases: Vec<RistrettoPoint>,
}

impl RangeProof {

    /// Prepares a `Verification` struct
    /// that can be combined with others in a batch.
    pub fn prepare_verification<R: Rng>(
        &self,
        value_commitments: &[RistrettoPoint],
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Verification {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        let m = value_commitments.as_ref().len();

        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        for V in value_commitments.as_ref().iter() {
            transcript.commit(V.borrow().compress().as_bytes());
        }
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;
        let minus_z = -z;

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from_u64(2)).take(n).collect();
        let powers_of_z = util::exp_iter(z).take(m);
        let concat_z_and_2 =
            powers_of_z.flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z));

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2)
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        Verification {
            m,
            n,
            pedersen_base_scalars: (basepoint_scalar, -self.e_blinding - c * self.t_x_blinding),
            g_scalars: g.collect(),
            h_scalars: h.collect(),
            dynamic_base_scalars:
                iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(value_commitment_scalars)
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .collect(),
            dynamic_bases:
                iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(value_commitments.iter())
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter())
                .cloned()
                .collect()
        }
    }

    /// Verifies multiple range proofs at once.
    /// If any range proof is invalid, the whole batch is invalid.
    /// Proofs may use different ranges (`n`) or different number of aggregated commitments (`m`).
    /// You must provide big enough view into generators (`gens`) that covers
    /// the biggest proof
    pub fn verify_batch<R: Rng, V: Borrow<Verification>>(
    	batch: &[V],
    	gens: GeneratorsView,
    	rng: &mut R
    ) -> Result<(), &'static str> {
    	// we will special-case the first item to avoid unnecessary multiplication,
    	// so lets check that we have at least one item.
		if batch.len() == 0 {
			return Ok(())
		}

        // Make sure we have enough static generators
        let n = batch.iter().map(|v| v.borrow().n).max().unwrap_or(0);
        let m = batch.iter().map(|v| v.borrow().m).max().unwrap_or(0);
        if gens.G.len() < (n * m) {
        	return Err("The generators view does not have enough generators for the largest proof")
        }

        // First statement is used without a random factor
        let mut pedersen_base_scalars: (Scalar, Scalar) = batch[0].borrow().pedersen_base_scalars;
        let mut g_scalars: Vec<Scalar> = batch[0].borrow().g_scalars.clone();
        let mut h_scalars: Vec<Scalar> = batch[0].borrow().h_scalars.clone();
        
        // pad static scalars to the largest proof
        g_scalars.resize(n*m, Scalar::zero());
        h_scalars.resize(n*m, Scalar::zero());

        let mut dynamic_base_scalars: Vec<Scalar> = batch[0].borrow().dynamic_base_scalars.clone();
        let mut dynamic_bases: Vec<RistrettoPoint> = batch[0].borrow().dynamic_bases.clone();
        
        // Other statements are added with a random factor per statement
        for borrowable_verification in &batch[1..] {
        	let verification = borrowable_verification.borrow();
            let batch_challenge = Scalar::random(rng);

            pedersen_base_scalars.0 += batch_challenge*verification.pedersen_base_scalars.0;
            pedersen_base_scalars.1 += batch_challenge*verification.pedersen_base_scalars.1;

            // Note: this loop may be shorter than the total amount of scalars if `m < max({m})`
            for (i, s) in verification.g_scalars.iter().enumerate() {
                g_scalars[i] += batch_challenge*s;
            }
            for (i, s) in verification.h_scalars.iter().enumerate() {
                h_scalars[i] += batch_challenge*s;
            }

            dynamic_base_scalars = dynamic_base_scalars.iter()
                .cloned()
                .chain(verification.dynamic_base_scalars.iter().map(|s| batch_challenge*s ))
                .collect();

            dynamic_bases = dynamic_bases.iter()
                .chain(verification.dynamic_bases.iter())
                .cloned()
                .collect();
        }

 		let mega_check = ristretto::vartime::multiscalar_mul(
 			iter::once(&pedersen_base_scalars.0)
 				.chain(iter::once(&pedersen_base_scalars.1))
 				.chain(g_scalars.iter())
 				.chain(h_scalars.iter())
 				.chain(dynamic_base_scalars.iter()),
 			iter::once(&gens.pedersen_generators.B)
 				.chain(iter::once(&gens.pedersen_generators.B_blinding))
 				.chain(gens.G.iter())
 				.chain(gens.H.iter())
 				.chain(dynamic_bases.iter())
 		);

 		if mega_check.is_identity() {
 			Ok(())
 		} else {
 			Err("Batch verification failed")
 		}
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle 1, {\mathbf{y}}^{nm} \rangle + z^{3} \langle \mathbf{1}, {\mathbf{2}}^{nm} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from_u64(2), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    #[test]
    fn test_delta() {
        let mut rng = OsRng::new().unwrap();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
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

        assert_eq!(power_g, delta(n, 1, &y, &z),);
    }
}