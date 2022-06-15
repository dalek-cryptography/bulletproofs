#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc = include_str!("../../docs/range-proof-protocol.md"))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "std")]
use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;
use blake2::{Blake2b, Digest};

use crate::util::{add_bytes_to_word, bytes_to_usize, xor_32_bytes};
use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_COMPRESSED, RISTRETTO_BASEPOINT_TABLE};
use rand_core::{CryptoRng, RngCore};
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Modules for MPC protocol

pub mod dealer;
pub mod messages;
pub mod party;

/// The `RangeProof` struct represents a proof that one or more values
/// are in a range.
///
/// The `RangeProof` struct contains functions for creating and
/// verifying aggregated range proofs.  The single-value case is
/// implemented as a special case of aggregated range proofs.
///
/// The bitsize of the range, as well as the list of commitments to
/// the values, are not included in the proof, and must be known to
/// the verifier.
///
/// This implementation requires that both the bitsize `n` and the
/// aggregation size `m` be powers of two, so that `n = 8, 16, 32, 64`
/// and `m = 1, 2, 4, 8, 16, ...`.  Note that the aggregation size is
/// not given as an explicit parameter, but is determined by the
/// number of values or commitments passed to the prover or verifier.
///
/// # Note
///
/// For proving, these functions run the multiparty aggregation
/// protocol locally.  That API is exposed in the [`aggregation`](::range_proof_mpc)
/// module and can be used to perform online aggregation between
/// parties without revealing secret values to each other.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    A: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate tari_bulletproofs;
    /// use tari_bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::new(64, 1);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let secret_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding = Scalar::random(&mut thread_rng());
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::prove_single(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     secret_value,
    ///     &blinding,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_single_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        let (p, Vs) = RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            &[v],
            &[*v_blinding],
            n,
            rng,
        )?;
        Ok((p, Vs[0]))
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`, passing in a rewind key to
    /// enable rangeproof rewinding with 23 bytes worth of extra
    /// data that can be embedded.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate tari_bulletproofs;
    /// use tari_bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    /// use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
    /// use tari_bulletproofs::range_proof::{get_rewind_nonce_from_pub_key, get_secret_nonce_from_pvt_key};
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::new(64, 1);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let confidential_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding_factor = Scalar::random(&mut thread_rng());
    ///
    /// // The private keys for range proof rewinding; these may be based on a wallet's private root key
    /// let pvt_rewind_key = Scalar::random(&mut thread_rng());
    /// let pvt_blinding_key = Scalar::random(&mut thread_rng());
    ///
    /// // Up to 23 bytes extra data may be embedded in the range proof meta data
    /// let proof_message: [u8; 23] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    ///         18, 19, 20, 21, 22, 23];
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::prove_single_with_rewind_key(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     confidential_value,
    ///     &blinding_factor,
    ///     32,
    ///     &pvt_rewind_key,
    ///     &pvt_blinding_key,
    ///     &proof_message,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    ///
    /// // A third party may have access to the public keys and extra data for range proof rewinding
    /// let pub_rewind_key_1 = RistrettoPoint::from(&pvt_rewind_key * &RISTRETTO_BASEPOINT_TABLE).compress();
    /// let pub_rewind_key_2 = RistrettoPoint::from(&pvt_blinding_key * &RISTRETTO_BASEPOINT_TABLE).compress();
    ///
    /// // The rewind nonce is necessary to rewind the range proof, which is uniquely bound to the commitment
    /// let rewind_nonce_1 = get_rewind_nonce_from_pub_key(&pub_rewind_key_1, &committed_value);
    /// let rewind_nonce_2 = get_rewind_nonce_from_pub_key(&pub_rewind_key_2, &committed_value);
    ///
    /// // A owner or third party can extract the value and extra data; if it is the wrong combination
    /// // garbage data will be extracted
    /// let mut rewind_transcript = Transcript::new(b"doctest example");
    /// assert_eq!(
    ///     proof.rewind_single_get_value_only(
    ///         &bp_gens,
    ///         &mut rewind_transcript,
    ///         &committed_value,
    ///         32,
    ///         &rewind_nonce_1,
    ///         &rewind_nonce_2,
    ///     ),
    ///     Ok((confidential_value, proof_message))
    /// );
    ///
    /// // The two blinding nonces are necessary to rewind the range proof fully, which are also
    /// // uniquely bound to the commitment
    /// let blinding_nonce_1 = get_secret_nonce_from_pvt_key(&pvt_rewind_key, &committed_value);
    /// let blinding_nonce_2 = get_secret_nonce_from_pvt_key(&pvt_blinding_key, &committed_value);
    ///
    /// // The owner or trusted party can extract the value, extra data and blinding factor; if it is the
    /// // wrong combination an error will be returned
    /// let mut rewind_transcript = Transcript::new(b"doctest example");
    /// assert_eq!(
    ///     proof.rewind_single_get_commitment_data(
    ///         &bp_gens,
    ///         &pc_gens,
    ///         &mut rewind_transcript,
    ///         &committed_value,
    ///         32,
    ///         &rewind_nonce_1,
    ///         &rewind_nonce_2,
    ///         &blinding_nonce_1,
    ///         &blinding_nonce_2,
    ///     ),
    ///     Ok((confidential_value, blinding_factor, proof_message))
    /// );
    ///
    /// # }
    /// ```
    pub fn prove_single_with_rng_and_rewind_key<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
        rng: &mut T,
        pvt_rewind_key: &Scalar,
        pvt_blinding_key: &Scalar,
        proof_message: &[u8; 23],
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        let values = &[v];
        let blindings = &[*v_blinding];
        // Temporarily borrow the blindings array to pass the additional parameters
        // into the next function
        let mut blindings = blindings.to_vec();
        blindings.push(RangeProof::get_rewind_key_separator());
        blindings.push(*pvt_rewind_key);
        blindings.push(*pvt_blinding_key);
        blindings.push(Scalar::from_bits(add_bytes_to_word(
            [0u8; 32],
            proof_message,
            8,
        )));

        let (p, Vs) = RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            &blindings[0..blindings.len()],
            n,
            rng,
        )?;
        Ok((p, Vs[0]))
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_single(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        RangeProof::prove_single_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
        )
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`, passing in a rewind key to
    /// enable rangeproof rewinding with 23 bytes worth of extra
    /// data that can be embedded.
    /// This is a convenience wrapper around
    /// [`RangeProof::prove_single_with_rng_and_rewind_key`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_single_with_rewind_key(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
        pvt_rewind_key: &Scalar,
        pvt_blinding_key: &Scalar,
        proof_message: &[u8; 23],
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        RangeProof::prove_single_with_rng_and_rewind_key(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
            pvt_rewind_key,
            pvt_blinding_key,
            proof_message,
        )
    }

    /// Create a rangeproof for a set of values.
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate tari_bulletproofs;
    /// use tari_bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 16.
    /// let bp_gens = BulletproofGens::new(64, 16);
    ///
    /// // Four secret values we want to prove lie in the range [0, 2^32)
    /// let secrets = [4242344947u64, 3718732727u64, 2255562556u64, 2526146994u64];
    ///
    /// // The API takes blinding factors for the commitments.
    /// let blindings: Vec<_> = (0..4).map(|_| Scalar::random(&mut thread_rng())).collect();
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create an aggregated 32-bit rangeproof and corresponding commitments.
    /// let (proof, commitments) = RangeProof::prove_multiple(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     &secrets,
    ///     &blindings,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_multiple(&bp_gens, &pc_gens, &mut verifier_transcript, &commitments, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_multiple_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        use self::dealer::*;
        use self::party::*;

        //Extract the rewind key and extra bytes from the blindings vector where it was temporarily assigned
        let (pvt_rewind_key, pvt_blinding_key, proof_message, blindings) =
            if values.len() + 4 == blindings.len() {
                if blindings[blindings.len() - 4] != RangeProof::get_rewind_key_separator() {
                    return Err(ProofError::InvalidRewindKeySeparator);
                }
                let rewind_key = blindings[blindings.len() - 3].to_owned();
                let blinding_key = blindings[blindings.len() - 2].to_owned();
                let data = blindings[blindings.len() - 1].to_owned();
                (
                    rewind_key,
                    blinding_key,
                    data,
                    &blindings[0..blindings.len() - 4],
                )
            } else {
                (
                    Scalar::default().to_owned(),
                    Scalar::default().to_owned(),
                    Scalar::default().to_owned(),
                    &blindings[0..blindings.len()],
                )
            };

        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| {
                Party::new(
                    bp_gens,
                    pc_gens,
                    v,
                    v_blinding,
                    n,
                    pvt_rewind_key,
                    pvt_blinding_key,
                    proof_message,
                )
            })
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position_with_rng(j, rng)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge_with_rng(&bit_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let proof = dealer.receive_trusted_shares(&proof_shares)?;

        Ok((proof, value_commitments))
    }

    /// Create a rangeproof for a set of values.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            blindings,
            n,
            &mut thread_rng(),
        )
    }

    /// Uniquely identify-able scalar used as a pvt_rewind_key separator
    fn get_rewind_key_separator() -> Scalar {
        Scalar::from_bits(*RISTRETTO_BASEPOINT_COMPRESSED.as_bytes())
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify_multiple` for the `m=1` case.
    pub fn verify_single_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(bp_gens, pc_gens, transcript, &[*V], n, rng)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around [`RangeProof::verify_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_single(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_single_with_rng(bp_gens, pc_gens, transcript, V, n, &mut thread_rng())
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    pub fn verify_multiple_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let zz = z * z;
        let minus_z = -z;

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<Scalar> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h)
                .chain(value_commitment_scalars),
            iter::once(self.A.decompress())
                .chain(iter::once(self.S.decompress()))
                .chain(iter::once(self.T_1.decompress()))
                .chain(iter::once(self.T_2.decompress()))
                .chain(self.ipp_proof.L_vec.iter().map(|L| L.decompress()))
                .chain(self.ipp_proof.R_vec.iter().map(|R| R.decompress()))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(bp_gens.G(n, m).map(|&x| Some(x)))
                .chain(bp_gens.H(n, m).map(|&x| Some(x)))
                .chain(value_commitments.iter().map(|V| V.decompress())),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    /// This is a convenience wrapper around [`RangeProof::verify_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            value_commitments,
            n,
            &mut thread_rng(),
        )
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * four compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        // 7 elements: points A, S, T1, T2, scalars tx, tx_bl, e_bl.
        let mut buf = Vec::with_capacity(7 * 32 + self.ipp_proof.serialized_size());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<RangeProof, ProofError> {
        if slice.len() % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 7 * 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        #[allow(clippy::erasing_op)]
        let A = CompressedRistretto(read32(&slice[0 * 32..]));
        let S = CompressedRistretto(read32(&slice[1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[2 * 32..]));
        let T_2 = CompressedRistretto(read32(&slice[3 * 32..]));

        let t_x = Scalar::from_canonical_bytes(read32(&slice[4 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Scalar::from_canonical_bytes(read32(&slice[5 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Scalar::from_canonical_bytes(read32(&slice[6 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[7 * 32..])?;

        Ok(RangeProof {
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }

    /// Rewinds a rangeproof for a given value commitment \\(V\\),
    /// returning the value, blinding factor and 23 bytes extra data
    /// upon success.
    pub fn rewind_single_get_commitment_data(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitment: &CompressedRistretto,
        n: usize,
        rewind_nonce_1: &Scalar,
        rewind_nonce_2: &Scalar,
        blinding_nonce_1: &Scalar,
        blinding_nonce_2: &Scalar,
    ) -> Result<(u64, Scalar, [u8; 23]), ProofError> {
        let result = self.rewind_single_get_commitment_value(
            bp_gens,
            transcript,
            value_commitment,
            n,
            &rewind_nonce_1,
            &rewind_nonce_2,
        )?;
        let value = result.0;
        let proof_message = result.1;
        let x = result.2;
        let z = result.3;

        // Extract the blinding factor:
        //   t_x_blinding = z^2 * v_blinding + x * t_1_blinding + x^2 * t_2_blinding
        //   v_blinding = (1 / z^2) * (t_x_blinding - x * t_1_blinding - x^2 * t_2_blinding)
        //   t_1_blinding: replaced by blinding_nonce_1
        //   t_2_blinding: replaced by blinding_nonce_2
        let v_blinding = z.invert()
            * z.invert()
            * (self.t_x_blinding - x * blinding_nonce_1 - x * x * blinding_nonce_2);

        //Verify if the correct value and blinding factor was extracted
        let value_commitment_calculated = pc_gens.commit(value.into(), v_blinding).compress();
        if value_commitment.as_bytes() != value_commitment_calculated.as_bytes() {
            return Err(ProofError::InvalidCommitmentExtracted);
        } else {
            Ok((value, v_blinding, proof_message))
        }
    }

    /// Rewinds a rangeproof for a given value commitment \\(V\\)
    /// to get the value and 23 bytes extra data only. If the wrong
    /// rewind_nonce is provided, garbage data will be returned.
    #[cfg(feature = "std")]
    pub fn rewind_single_get_value_only(
        &self,
        bp_gens: &BulletproofGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
        rewind_nonce_1: &Scalar,
        rewind_nonce_2: &Scalar,
    ) -> Result<(u64, [u8; 23]), ProofError> {
        let result = self.rewind_single_get_commitment_value(
            bp_gens,
            transcript,
            V,
            n,
            &rewind_nonce_1,
            &rewind_nonce_2,
        );
        let result: Result<(u64, [u8; 23]), ProofError> =
            Ok((result.clone().unwrap().0, result.clone().unwrap().1));
        result
    }

    /// Rewinds a rangeproof for a given value commitment \\(V\\)
    /// to retrieve the value, challenge scalars x and y and 23
    /// bytes extra data.
    fn rewind_single_get_commitment_value(
        &self,
        bp_gens: &BulletproofGens,
        transcript: &mut Transcript,
        value_commitment: &CompressedRistretto,
        n: usize,
        rewind_nonce_1: &Scalar,
        rewind_nonce_2: &Scalar,
    ) -> Result<(u64, [u8; 23], Scalar, Scalar), ProofError> {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < 1 {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, 1u64);
        transcript.append_point(b"V", value_commitment);
        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;
        transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;
        let x = transcript.challenge_scalar(b"x");

        // Extract s_blinding:
        //   e_blinding = a_blinding + x * s_blinding
        //   s_blinding = (e_blinding - a_blinding) * (1/x)
        //   a_blinding: replaced by rewind_nonce_1
        let s_blinding = (self.e_blinding - rewind_nonce_1) * x.invert();
        // Extract the value and extra data
        let xor_s_blinding = xor_32_bytes(&rewind_nonce_2.as_bytes(), &s_blinding.as_bytes());
        let value = bytes_to_usize(&xor_s_blinding, 1, 8) as u64;
        let mut proof_message = [0u8; 23];
        for (place, element) in proof_message.iter_mut().zip(xor_s_blinding.iter().skip(8)) {
            *place = *element;
        }

        Ok((value, proof_message, x, z))
    }
}

impl Serialize for RangeProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for RangeProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct RangeProofVisitor;

        impl<'de> Visitor<'de> for RangeProofVisitor {
            type Value = RangeProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("a valid RangeProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<RangeProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return RangeProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return RangeProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(RangeProofVisitor)
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

/// Calculate a rewind nonce from a private key and the value commitment.
pub fn get_rewind_nonce_from_pvt_key(pvt_key: &Scalar, commitment: &CompressedRistretto) -> Scalar {
    let pub_key = (pvt_key * &RISTRETTO_BASEPOINT_TABLE).compress();
    get_rewind_nonce_from_pub_key(&pub_key, commitment)
}

/// Calculate a rewind nonce from a public key and the value commitment.
pub fn get_rewind_nonce_from_pub_key(
    pub_key: &CompressedRistretto,
    commitment: &CompressedRistretto,
) -> Scalar {
    let rewind_nonce_initial =
        Blake2b::with_params(&pub_key.to_bytes().as_ref(), &[], "Rewind sep 1".as_bytes())
            .finalize();
    let rewind_nonce_data = [
        rewind_nonce_initial.to_vec().as_slice(),
        commitment.to_bytes().as_ref(),
    ]
    .concat();
    let rewind_nonce_final = Blake2b::with_params(
        &Blake2b::digest(&rewind_nonce_data),
        &[],
        "Rewind sep 2".as_bytes(),
    );
    Scalar::from_hash(rewind_nonce_final)
}

/// Calculate a secret nonce from a private key and the value commitment.
pub fn get_secret_nonce_from_pvt_key(pvt_key: &Scalar, commitment: &CompressedRistretto) -> Scalar {
    let secret_nonce_initial =
        Blake2b::with_params(&pvt_key.to_bytes().as_ref(), &[], "Secret sep 1".as_bytes())
            .finalize();
    let secret_nonce_data = [
        secret_nonce_initial.to_vec().as_slice(),
        commitment.to_bytes().as_ref(),
    ]
    .concat();
    let secret_nonce_final = Blake2b::with_params(
        &Blake2b::digest(&secret_nonce_data),
        &[],
        "Secret sep 2".as_bytes(),
    );
    Scalar::from_hash(secret_nonce_final)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::generators::PedersenGens;

    #[test]
    fn test_delta() {
        let mut rng = rand::thread_rng();
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

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        //use bincode; // already present in lib.rs

        // Both prover and verifier have access to the generators and the proof
        let max_bitsize = 64;
        let max_parties = 8;
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(max_bitsize, max_parties);

        // Prover's scope
        let (proof_bytes, value_commitments) = {
            use self::rand::Rng;
            let mut rng = rand::thread_rng();

            // 0. Create witness data
            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            // 1. Create the proof
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");
            let (proof, value_commitments) = RangeProof::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values,
                &blindings,
                n,
            )
            .unwrap();

            // 2. Return serialized proof and value commitments
            (bincode::serialize(&proof).unwrap(), value_commitments)
        };

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

            assert!(proof
                .verify_multiple(&bp_gens, &pc_gens, &mut transcript, &value_commitments, n)
                .is_ok());
        }
    }

    #[test]
    fn create_and_verify_n_32_m_1() {
        singleparty_create_and_verify_helper(32, 1);
    }

    #[test]
    fn create_and_verify_n_32_m_2() {
        singleparty_create_and_verify_helper(32, 2);
    }

    #[test]
    fn create_and_verify_n_32_m_4() {
        singleparty_create_and_verify_helper(32, 4);
    }

    #[test]
    fn create_and_verify_n_32_m_8() {
        singleparty_create_and_verify_helper(32, 8);
    }

    #[test]
    fn create_and_verify_n_64_m_1() {
        singleparty_create_and_verify_helper(64, 1);
    }

    #[test]
    fn create_and_verify_n_64_m_2() {
        singleparty_create_and_verify_helper(64, 2);
    }

    #[test]
    fn create_and_verify_n_64_m_4() {
        singleparty_create_and_verify_helper(64, 4);
    }

    #[test]
    fn create_and_verify_n_64_m_8() {
        singleparty_create_and_verify_helper(64, 8);
    }

    #[test]
    fn detect_dishonest_party_during_aggregation() {
        use self::dealer::*;
        use self::party::*;

        use crate::errors::MPCError;

        // Common data - rewind functionality not used
        let not_used = Scalar::default();

        // Simulate four parties, two of which will be dishonest and use a 64-bit value.
        let m = 4;
        let n = 32;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n, m);

        use self::rand::Rng;
        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        // Parties 0, 2 are honest and use a 32-bit value
        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(
            &bp_gens,
            &pc_gens,
            v0,
            v0_blinding,
            n,
            not_used,
            not_used,
            not_used,
        )
        .unwrap();

        let v2 = rng.gen::<u32>() as u64;
        let v2_blinding = Scalar::random(&mut rng);
        let party2 = Party::new(
            &bp_gens,
            &pc_gens,
            v2,
            v2_blinding,
            n,
            not_used,
            not_used,
            not_used,
        )
        .unwrap();

        // Parties 1, 3 are dishonest and use a 64-bit value
        let v1 = rng.gen::<u64>();
        let v1_blinding = Scalar::random(&mut rng);
        let party1 = Party::new(
            &bp_gens,
            &pc_gens,
            v1,
            v1_blinding,
            n,
            not_used,
            not_used,
            not_used,
        )
        .unwrap();

        let v3 = rng.gen::<u64>();
        let v3_blinding = Scalar::random(&mut rng);
        let party3 = Party::new(
            &bp_gens,
            &pc_gens,
            v3,
            v3_blinding,
            n,
            not_used,
            not_used,
            not_used,
        )
        .unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        let (party0, bit_com0) = party0.assign_position(0).unwrap();
        let (party1, bit_com1) = party1.assign_position(1).unwrap();
        let (party2, bit_com2) = party2.assign_position(2).unwrap();
        let (party3, bit_com3) = party3.assign_position(3).unwrap();

        let (dealer, bit_challenge) = dealer
            .receive_bit_commitments(vec![bit_com0, bit_com1, bit_com2, bit_com3])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);
        let (party1, poly_com1) = party1.apply_challenge(&bit_challenge);
        let (party2, poly_com2) = party2.apply_challenge(&bit_challenge);
        let (party3, poly_com3) = party3.apply_challenge(&bit_challenge);

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(vec![poly_com0, poly_com1, poly_com2, poly_com3])
            .unwrap();

        let share0 = party0.apply_challenge(&poly_challenge).unwrap();
        let share1 = party1.apply_challenge(&poly_challenge).unwrap();
        let share2 = party2.apply_challenge(&poly_challenge).unwrap();
        let share3 = party3.apply_challenge(&poly_challenge).unwrap();

        match dealer.receive_shares(&[share0, share1, share2, share3]) {
            Err(MPCError::MalformedProofShares { bad_shares }) => {
                assert_eq!(bad_shares, vec![1, 3]);
            }
            Err(_) => {
                panic!("Got wrong error type from malformed shares");
            }
            Ok(_) => {
                panic!("The proof was malformed, but it was not detected");
            }
        }
    }

    #[test]
    fn detect_dishonest_dealer_during_aggregation() {
        use self::dealer::*;
        use self::party::*;
        use crate::errors::MPCError;

        // Common data - rewind functionality not used
        let not_used = Scalar::default();

        // Simulate one party
        let m = 1;
        let n = 32;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n, m);

        use self::rand::Rng;
        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(
            &bp_gens,
            &pc_gens,
            v0,
            v0_blinding,
            n,
            not_used,
            not_used,
            not_used,
        )
        .unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        // Now do the protocol flow as normal....

        let (party0, bit_com0) = party0.assign_position(0).unwrap();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(vec![bit_com0]).unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);

        let (_dealer, mut poly_challenge) =
            dealer.receive_poly_commitments(vec![poly_com0]).unwrap();

        // But now simulate a malicious dealer choosing x = 0
        poly_challenge.x = Scalar::zero();

        let maybe_share0 = party0.apply_challenge(&poly_challenge);

        assert!(maybe_share0.unwrap_err() == MPCError::MaliciousDealer);
    }

    #[test]
    fn rewind_nonce_and_secret_nonce() {
        // Static data
        let pvt_rewind_key = Scalar::from_bits([
            52, 177, 175, 139, 230, 130, 194, 20, 235, 30, 175, 83, 36, 74, 152, 44, 159, 164, 58,
            224, 1, 145, 79, 3, 28, 84, 255, 124, 182, 63, 105, 2,
        ]);
        let pub_rewind_key =
            RistrettoPoint::from(&pvt_rewind_key * &RISTRETTO_BASEPOINT_TABLE).compress();
        let committed_value = CompressedRistretto::from_slice(
            [
                208, 101, 226, 203, 8, 161, 147, 169, 30, 0, 90, 57, 238, 214, 80, 108, 172, 123,
                34, 250, 205, 128, 227, 180, 0, 157, 217, 236, 238, 229, 180, 36,
            ]
            .to_vec()
            .as_slice(),
        );

        assert_eq!(
            get_rewind_nonce_from_pub_key(&pub_rewind_key, &committed_value),
            get_rewind_nonce_from_pvt_key(&pvt_rewind_key, &committed_value)
        );
        assert_eq!(
            get_rewind_nonce_from_pub_key(&pub_rewind_key, &committed_value)
                .as_bytes()
                .to_vec(),
            [
                96, 129, 189, 122, 3, 143, 202, 124, 159, 114, 5, 6, 215, 201, 79, 169, 222, 245,
                78, 216, 172, 107, 49, 168, 117, 193, 119, 138, 93, 83, 47, 8
            ]
            .to_vec()
        );
        assert_eq!(
            get_secret_nonce_from_pvt_key(&pvt_rewind_key, &committed_value)
                .as_bytes()
                .to_vec(),
            [
                85, 7, 115, 151, 38, 196, 12, 17, 39, 183, 224, 49, 161, 52, 38, 108, 106, 223,
                233, 81, 219, 109, 253, 129, 250, 223, 236, 228, 191, 172, 167, 14
            ]
            .to_vec()
        );

        // Dynamic data
        let pvt_rewind_key = Scalar::random(&mut thread_rng());
        let pub_rewind_key =
            RistrettoPoint::from(&pvt_rewind_key * &RISTRETTO_BASEPOINT_TABLE).compress();
        let committed_value = CompressedRistretto::from_slice(
            Scalar::random(&mut thread_rng())
                .as_bytes()
                .to_vec()
                .as_slice(),
        );

        assert_eq!(
            get_rewind_nonce_from_pub_key(&pub_rewind_key, &committed_value),
            get_rewind_nonce_from_pvt_key(&pvt_rewind_key, &committed_value)
        );
        assert_ne!(
            get_rewind_nonce_from_pvt_key(&pvt_rewind_key, &committed_value),
            get_secret_nonce_from_pvt_key(&pvt_rewind_key, &committed_value)
        );
    }
}
