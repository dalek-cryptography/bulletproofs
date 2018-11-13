#![feature(nll)]
#![feature(external_doc)]
#![feature(try_trait)]
#![deny(missing_docs)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

extern crate byteorder;
extern crate core;
extern crate digest;
extern crate rand;
extern crate sha3;

extern crate clear_on_drop;
extern crate curve25519_dalek;
extern crate merlin;
extern crate subtle;
#[macro_use]
extern crate serde_derive;
extern crate serde;

#[macro_use]
extern crate failure;

#[cfg(test)]
extern crate bincode;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}
mod constraint_system;
mod errors;
mod generators;
mod inner_product_proof;
mod range_proof;
mod transcript;

pub use errors::ProofError;
pub use generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use range_proof::RangeProof;

#[doc(include = "../docs/aggregation-api.md")]
pub mod range_proof_mpc {
    pub use errors::MPCError;
    pub use range_proof::dealer;
    pub use range_proof::messages;
    pub use range_proof::party;
}

/// The rank-1 constraint system API for programmatically defining constraint systems.
///
/// XXX explain how the parts fit together here
///
/// ```
/// extern crate bulletproofs;
/// use bulletproofs::r1cs::{Assignment, ConstraintSystem, Variable, ProverCS, VerifierCS, ConstraintSystemError};
/// use bulletproofs::{BulletproofGens, PedersenGens};
///
/// extern crate curve25519_dalek;
/// use curve25519_dalek::scalar::Scalar;
///
/// extern crate subtle;
/// use subtle::{ConditionallySelectable, ConstantTimeEq};
///
/// extern crate merlin;
/// use merlin::Transcript;
///
/// #[macro_use]
/// extern crate failure;
/// extern crate rand;
///
/// /*
/// K-SHUFFLE GADGET SPECIFICATION:
///
/// Represents a permutation of a list of `k` scalars `{x_i}` into a list of `k` scalars `{y_i}`.
///
/// Algebraically it can be expressed as a statement that for a free variable `z`,
/// the roots of the two polynomials in terms of `z` are the same up to a permutation:
///
///     ∏(x_i - z) == ∏(y_i - z)
///
/// Prover can commit to blinded scalars `x_i` and `y_i` then receive a random challenge `z`,
/// and build a proof that the above relation holds.
///
/// K-shuffle requires `2*(K-1)` multipliers.
///
/// For K > 1:
///
///         (x_0 - z)---⊗------⊗---(y_0 - z)        // mulx[0], muly[0]
///                     |      |
///         (x_1 - z)---⊗      ⊗---(y_1 - z)        // mulx[1], muly[1]
///                     |      |
///                    ...    ...
///                     |      |
///     (x_{k-2} - z)---⊗      ⊗---(y_{k-2} - z)    // mulx[k-2], muly[k-2]
///                    /        \
///     (x_{k-1} - z)_/          \_(y_{k-1} - z)
///
///     // Connect left and right sides of the shuffle statement
///     mulx_out[0] = muly_out[0]
///
///     // For i == [0, k-3]:
///     mulx_left[i]  = x_i - z
///     mulx_right[i] = mulx_out[i+1]
///     muly_left[i]  = y_i - z
///     muly_right[i] = muly_out[i+1]
///
///     // last multipliers connect two last variables (on each side)
///     mulx_left[k-2]  = x_{k-2} - z
///     mulx_right[k-2] = x_{k-1} - z
///     muly_left[k-2]  = y_{k-2} - z
///     muly_right[k-2] = y_{k-1} - z
///
/// For K = 1:
///
///     (x_0 - z)--------------(y_0 - z)
///
///     // Connect x to y directly, omitting the challenge entirely as it cancels out
///     x_0 = y_0
/// */
///
/// /// Enforces that the output variables `y` are a valid reordering of the inputs variables `x`.
/// /// The inputs and outputs are all tuples of the `Variable, Assignment`, where the `Assignment`
/// /// can be either assigned as `Value::Scalar` or unassigned as `Missing`.
///
/// pub fn fill_cs<CS: ConstraintSystem>(
///     cs: &mut CS,
///     x: Vec<(Variable, Assignment)>,
///     y: Vec<(Variable, Assignment)>,
/// ) -> Result<(), KShuffleError> {
///     let one = Scalar::one();
///     let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
///     let neg_z = -z;
///
///     if x.len() != y.len() {
///         return Err(KShuffleError::InvalidConstraintSystemConstruction);
///     }
///     let k = x.len();
///     if k == 1 {
///         cs.add_constraint([(x[0].0, -one), (y[0].0, one)].iter().collect());
///         return Ok(());
///     }
///
///     // Make last x multiplier for i = k-1 and k-2
///     let last_mulx_out = last_multiplier(cs, neg_z, x[k - 1], x[k - 2]);
///
///     // Make multipliers for x from i == [0, k-3]
///     let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
///         intermediate_multiplier(cs, neg_z, prev_out?, x[i])
///     })?;
///
///     // Make last y multiplier for i = k-1 and k-2
///     let last_muly_out = last_multiplier(cs, neg_z, y[k - 1], y[k - 2]);
///
///     // Make multipliers for y from i == [0, k-3]
///     let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
///         intermediate_multiplier(cs, neg_z, prev_out?, y[i])
///     })?;
///
///     // Check equality between last x mul output and last y mul output
///     cs.add_constraint(
///         [(first_muly_out.0, -one), (first_mulx_out.0, one)]
///             .iter()
///             .collect(),
///     );
///
///     Ok(())
/// }
///
/// fn last_multiplier<CS: ConstraintSystem>(
///     cs: &mut CS,
///     neg_z: Scalar,
///     left: (Variable, Assignment),
///     right: (Variable, Assignment),
/// ) -> Result<(Variable, Assignment), KShuffleError> {
///     let one = Scalar::one();
///     let var_one = Variable::One();
///
///     let mul_left = left.1 + neg_z;
///     let mul_right = right.1 + neg_z;
///     let mul_out = mul_left * mul_right;
///
///     // Make multiplier gate variables
///     let (mul_left_var, mul_right_var, mul_out_var) =
///         cs.assign_multiplier(mul_left, mul_right, mul_out)?;
///
///     // Make multipliers
///     cs.add_constraint(
///         [(mul_left_var, -one), (var_one, neg_z), (left.0, one)]
///             .iter()
///             .collect(),
///     );
///     cs.add_constraint(
///         [(mul_right_var, -one), (var_one, neg_z), (right.0, one)]
///             .iter()
///             .collect(),
///     );
///
///     Ok((mul_out_var, mul_out))
/// }
///
/// fn intermediate_multiplier<CS: ConstraintSystem>(
///     cs: &mut CS,
///     neg_z: Scalar,
///     left: (Variable, Assignment),
///     right: (Variable, Assignment),
/// ) -> Result<(Variable, Assignment), KShuffleError> {
///     let one = Scalar::one();
///     let var_one = Variable::One();
///
///     let mul_left = left.1;
///     let mul_right = right.1 + neg_z;
///     let mul_out = mul_left * mul_right;
///
///     // Make multiplier gate variables
///     let (mul_left_var, mul_right_var, mul_out_var) =
///         cs.assign_multiplier(mul_left, mul_right, mul_out)?;
///
///     // Make multipliers
///     cs.add_constraint([(mul_left_var, -one), (left.0, one)].iter().collect());
///     cs.add_constraint(
///         [(mul_right_var, -one), (var_one, neg_z), (right.0, one)]
///             .iter()
///             .collect(),
///     );
///
///     Ok((mul_out_var, mul_out))
/// }
///
/// /// Represents an error during the proof creation of verification for a KShuffle or KValueShuffle gadget.
/// #[derive(Fail, Copy, Clone, Debug, Eq, PartialEq)]
/// pub enum KShuffleError {
///     /// Error in the constraint system creation process
///     #[fail(display = "Invalid KShuffle constraint system construction")]
///     InvalidConstraintSystemConstruction,
///     /// Occurs when there are insufficient generators for the proof.
///     #[fail(display = "Invalid generators size, too few generators for proof")]
///     InvalidGeneratorsLength,
///     /// Occurs when verification of an [`R1CSProof`](::r1cs::R1CSProof) fails.
///     #[fail(display = "R1CSProof did not verify correctly.")]
///     VerificationError,
/// }
///
/// impl From<ConstraintSystemError> for KShuffleError {
///     fn from(e: ConstraintSystemError) -> KShuffleError {
///         match e {
///             ConstraintSystemError::InvalidGeneratorsLength => KShuffleError::InvalidGeneratorsLength,
///             ConstraintSystemError::MissingAssignment => KShuffleError::InvalidConstraintSystemConstruction,
///             ConstraintSystemError::VerificationError => KShuffleError::VerificationError,
///         }
///     }
/// }
///
/// // This test allocates variables for the high-level variables, to check that high-level
/// // variable allocation and commitment works.
/// fn shuffle_helper(input: Vec<u64>, output: Vec<u64>) -> Result<(), KShuffleError> {
///     // Common
///     let pc_gens = PedersenGens::default();
///     let bp_gens = BulletproofGens::new(128, 1);
///
///     let k = input.len();
///     if k != output.len() {
///         return Err(KShuffleError::InvalidConstraintSystemConstruction);
///     }
///
///     // Prover's scope
///     let (proof, commitments) = {
///         // Prover makes a `ConstraintSystem` instance representing a shuffle gadget
///         // Make v vector
///         let mut v = vec![];
///         for i in 0..k {
///             v.push(Scalar::from(input[i]));
///         }
///         for i in 0..k {
///             v.push(Scalar::from(output[i]));
///         }
///
///         // Make v_blinding vector using RNG from transcript
///         let mut prover_transcript = Transcript::new(b"ShuffleTest");
///         let mut rng = {
///             let mut builder = prover_transcript.build_rng();
///
///             // commit the secret values
///             for &v_i in &v {
///                 builder = builder.commit_witness_bytes(b"v_i", v_i.as_bytes());
///             }
///
///             use rand::thread_rng;
///             builder.finalize(&mut thread_rng())
///         };
///         let v_blinding: Vec<Scalar> = (0..2 * k).map(|_| Scalar::random(&mut rng)).collect();
///
///         let (mut prover_cs, variables, commitments) = ProverCS::new(
///             &bp_gens,
///             &pc_gens,
///             &mut prover_transcript,
///             v,
///             v_blinding.clone(),
///         );
///
///         // Prover allocates variables and adds constraints to the constraint system
///         let in_pairs = variables[0..k]
///             .iter()
///             .zip(input.iter())
///             .map(|(var_i, in_i)| (*var_i, Assignment::from(in_i.clone())))
///             .collect();
///         let out_pairs = variables[k..2 * k]
///             .iter()
///             .zip(output.iter())
///             .map(|(var_i, out_i)| (*var_i, Assignment::from(out_i.clone())))
///             .collect();
///
///         fill_cs(&mut prover_cs, in_pairs, out_pairs)?;
///         let proof = prover_cs.prove()?;
///
///         (proof, commitments)
///     };
///
///     // Verifier makes a `ConstraintSystem` instance representing a shuffle gadget
///     let mut verifier_transcript = Transcript::new(b"ShuffleTest");
///     let (mut verifier_cs, variables) =
///         VerifierCS::new(&bp_gens, &pc_gens, &mut verifier_transcript, commitments);
///
///     // Verifier allocates variables and adds constraints to the constraint system
///     let in_pairs = variables[0..k]
///         .iter()
///         .map(|var_i| (*var_i, Assignment::Missing()))
///         .collect();
///     let out_pairs = variables[k..2 * k]
///         .iter()
///         .map(|var_i| (*var_i, Assignment::Missing()))
///         .collect();
///     assert!(fill_cs(&mut verifier_cs, in_pairs, out_pairs).is_ok());
///
///     // Verifier verifies proof
///     Ok(verifier_cs.verify(&proof)?)
/// }
///
/// # fn main() {
///     // k=1
///     assert!(shuffle_helper(vec![3], vec![3]).is_ok());
///     assert!(shuffle_helper(vec![6], vec![6]).is_ok());
///     assert!(shuffle_helper(vec![3], vec![6]).is_err());
///     // k=2
///     assert!(shuffle_helper(vec![3, 6], vec![3, 6]).is_ok());
///     assert!(shuffle_helper(vec![3, 6], vec![6, 3]).is_ok());
///     assert!(shuffle_helper(vec![6, 6], vec![6, 6]).is_ok());
///     assert!(shuffle_helper(vec![3, 3], vec![6, 3]).is_err());
///     // k=3
///     assert!(shuffle_helper(vec![3, 6, 10], vec![3, 6, 10]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![3, 10, 6]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![6, 3, 10]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![6, 10, 3]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![10, 3, 6]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![10, 6, 3]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![30, 6, 10]).is_err());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![3, 60, 10]).is_err());
///     assert!(shuffle_helper(vec![3, 6, 10], vec![3, 6, 100]).is_err());
///     // k=4
///     assert!(shuffle_helper(vec![3, 6, 10, 15], vec![3, 6, 10, 15]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10, 15], vec![15, 6, 10, 3]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10, 15], vec![3, 6, 10, 3]).is_err());
///     // k=5
///     assert!(shuffle_helper(vec![3, 6, 10, 15, 17], vec![3, 6, 10, 15, 17]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10, 15, 17], vec![10, 17, 3, 15, 6]).is_ok());
///     assert!(shuffle_helper(vec![3, 6, 10, 15, 17], vec![3, 6, 10, 15, 3]).is_err());
/// # }
///
/// ```

pub mod r1cs {
    pub use constraint_system::assignment::Assignment;
    pub use constraint_system::prover::ProverCS;
    pub use constraint_system::verifier::VerifierCS;
    pub use constraint_system::ConstraintSystem;
    pub use constraint_system::ConstraintSystemProof;
    pub use constraint_system::LinearCombination;
    pub use constraint_system::Variable;
    pub use errors::ConstraintSystemError;
}
