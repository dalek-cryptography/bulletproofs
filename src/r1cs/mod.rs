//! The rank-1 constraint system API for programmatically defining constraint systems.
//!
//! XXX explain how the parts fit together here
//!
//! ```
//! extern crate bulletproofs;
//! use bulletproofs::r1cs::{ConstraintSystem, Variable, ProverCS, VerifierCS, R1CSError};
//! use bulletproofs::{BulletproofGens, PedersenGens};
//!
//! extern crate curve25519_dalek;
//! use curve25519_dalek::scalar::Scalar;
//! use curve25519_dalek::ristretto::CompressedRistretto;
//!
//! extern crate merlin;
//! use merlin::Transcript;
//!
//! extern crate rand;
//!
//! /*
//! K-SHUFFLE GADGET SPECIFICATION:
//!
//! Represents a permutation of a list of `k` scalars `{x_i}` into a list of `k` scalars `{y_i}`.
//!
//! Algebraically it can be expressed as a statement that for a free variable `z`,
//! the roots of the two polynomials in terms of `z` are the same up to a permutation:
//!
//!     ∏(x_i - z) == ∏(y_i - z)
//!
//! Prover can commit to blinded scalars `x_i` and `y_i` then receive a random challenge `z`,
//! and build a proof that the above relation holds.
//!
//! K-shuffle requires `2*(K-1)` multipliers.
//!
//! For K > 1:
//!
//!         (x_0 - z)---⊗------⊗---(y_0 - z)        // mulx[0], muly[0]
//!                     |      |
//!         (x_1 - z)---⊗      ⊗---(y_1 - z)        // mulx[1], muly[1]
//!                     |      |
//!                    ...    ...
//!                     |      |
//!     (x_{k-2} - z)---⊗      ⊗---(y_{k-2} - z)    // mulx[k-2], muly[k-2]
//!                    /        \
//!     (x_{k-1} - z)_/          \_(y_{k-1} - z)
//!
//!     // Connect left and right sides of the shuffle statement
//!     mulx_out[0] = muly_out[0]
//!
//!     // For i == [0, k-3]:
//!     mulx_left[i]  = x_i - z
//!     mulx_right[i] = mulx_out[i+1]
//!     muly_left[i]  = y_i - z
//!     muly_right[i] = muly_out[i+1]
//!
//!     // last multipliers connect two last variables (on each side)
//!     mulx_left[k-2]  = x_{k-2} - z
//!     mulx_right[k-2] = x_{k-1} - z
//!     muly_left[k-2]  = y_{k-2} - z
//!     muly_right[k-2] = y_{k-1} - z
//!
//! For K = 1:
//!
//!     (x_0 - z)--------------(y_0 - z)
//!
//!     // Connect x to y directly, omitting the challenge entirely as it cancels out
//!     x_0 = y_0
//! */
//!
//! /// Enforces that the output variables `y` are a valid reordering of the inputs variables `x`.
//! /// The inputs and outputs are all tuples of the `Variable, Assignment`, where the `Assignment`
//! /// can be either assigned as `Value::Scalar` or unassigned as `Missing`.
//! pub fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) {
//!     let one = Scalar::one();
//!     let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
//!
//!     assert_eq!(x.len(), y.len());
//!
//!     let k = x.len();
//!     if k == 1 {
//!         cs.add_auxiliary_constraint([(x[0], -one), (y[0], one)].iter().collect());
//!         return;
//!     }
//!
//!     // Make last x multiplier for i = k-1 and k-2
//!     let (_, _, last_mulx_out) = cs.add_intermediate_constraint(x[k - 1] - z, x[k - 2] - z);
//!
//!     // Make multipliers for x from i == [0, k-3]
//!     let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
//!         let (_, _, o) = cs.add_intermediate_constraint(prev_out.into(), x[i] - z);
//!         o
//!     });
//!
//!     // Make last y multiplier for i = k-1 and k-2
//!     let (_, _, last_muly_out) = cs.add_intermediate_constraint(y[k - 1] - z, y[k - 2] - z);
//!
//!     // Make multipliers for y from i == [0, k-3]
//!     let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
//!         let (_, _, o) = cs.add_intermediate_constraint(prev_out.into(), y[i] - z);
//!         o
//!     });
//!
//!     // Check equality between last x mul output and last y mul output
//!     cs.add_auxiliary_constraint(
//!         [(first_muly_out, -one), (first_mulx_out, one)]
//!             .iter()
//!             .collect(),
//!     );
//! }
//!
//! // Helper functions for proof creation
//! fn kshuffle_prover_cs<'a, 'b>(
//!     pc_gens: &'b PedersenGens,
//!     bp_gens: &'b BulletproofGens,
//!     transcript: &'a mut Transcript,
//!     input: &Vec<u64>,
//!     output: &Vec<u64>,
//! ) -> (ProverCS<'a, 'b>, Vec<CompressedRistretto>) {
//!     let k = input.len();
//!
//!     // Prover makes a `ConstraintSystem` instance representing a shuffle gadget
//!     // Make v vector
//!     let mut v = Vec::with_capacity(2 * k);
//!     for i in 0..k {
//!         v.push(Scalar::from(input[i]));
//!     }
//!     for i in 0..k {
//!         v.push(Scalar::from(output[i]));
//!     }
//!
//!     // Make v_blinding vector using RNG from transcript
//!     let mut rng = {
//!         let mut builder = transcript.build_rng();
//!         // commit the secret values
//!         for &v_i in &v {
//!             builder = builder.commit_witness_bytes(b"v_i", v_i.as_bytes());
//!         }
//!         use rand::thread_rng;
//!         builder.finalize(&mut thread_rng())
//!     };
//!     let v_blinding: Vec<Scalar> = (0..2 * k).map(|_| Scalar::random(&mut rng)).collect();
//!     let (mut prover_cs, variables, commitments) =
//!         ProverCS::new(&bp_gens, &pc_gens, transcript, v, v_blinding.clone());
//!
//!     // Prover allocates variables and adds constraints to the constraint system
//!     fill_cs(
//!         &mut prover_cs,
//!         variables[0..k].to_vec(),
//!         variables[k..2 * k].to_vec(),
//!     );
//!
//!     (prover_cs, commitments)
//! }
//!
//! // Helper functions for proof verification
//! fn kshuffle_verifier_cs<'a, 'b>(
//!     pc_gens: &'b PedersenGens,
//!     bp_gens: &'b BulletproofGens,
//!     transcript: &'a mut Transcript,
//!     commitments: &Vec<CompressedRistretto>,
//! ) -> VerifierCS<'a, 'b> {
//!     let k = commitments.len() / 2;
//!
//!     // Verifier makes a `ConstraintSystem` instance representing a shuffle gadget
//!     let (mut verifier_cs, variables) =
//!         VerifierCS::new(&bp_gens, &pc_gens, transcript, commitments.to_vec());
//!
//!     // Verifier allocates variables and adds constraints to the constraint system
//!     fill_cs(
//!         &mut verifier_cs,
//!         variables[0..k].to_vec(),
//!         variables[k..2 * k].to_vec(),
//!     );
//!
//!     verifier_cs
//! }
//!
//! fn kshuffle_helper(k: usize) {
//!     use rand::Rng;
//!
//!     let pc_gens = PedersenGens::default();
//!     let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);
//!
//!     let mut transcript = Transcript::new(b"ShuffleTest");
//!     transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());
//!
//!     let (proof, commitments) = {
//!         // Randomly generate inputs and outputs to kshuffle
//!         let mut rng = rand::thread_rng();
//!         let (min, max) = (0u64, std::u64::MAX);
//!         let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
//!         let mut output = input.clone();
//!         rand::thread_rng().shuffle(&mut output);
//!
//!         let mut prover_transcript = transcript.clone();
//!         let (prover_cs, commits) =
//!             kshuffle_prover_cs(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output);
//!         let proof = prover_cs.prove().unwrap();
//!         (proof, commits)
//!     };
//!
//!     {
//!         let mut verifier_transcript = transcript.clone();
//!
//!         let verifier_cs =
//!             kshuffle_verifier_cs(&pc_gens, &bp_gens, &mut verifier_transcript, &commitments);
//!         verifier_cs.verify(&proof).unwrap();
//!     }
//! }
//!
//! # fn main() {
//!     kshuffle_helper(1);
//!     kshuffle_helper(2);
//!     kshuffle_helper(3);
//!     kshuffle_helper(4);
//!     kshuffle_helper(5);
//!     kshuffle_helper(10);
//!     kshuffle_helper(25);
//! # }
//!
//! ```

#[doc(include = "../docs/cs-proof.md")]
mod notes {}

mod constraint_system;
mod linear_combination;
mod proof;
mod prover;
mod verifier;

#[cfg(test)]
mod tests;

pub use self::constraint_system::ConstraintSystem;
pub use self::linear_combination::{LinearCombination, Variable};
pub use self::proof::R1CSProof;
pub use self::prover::ProverCS;
pub use self::verifier::VerifierCS;

pub use errors::R1CSError;
