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
mod circuit_proof;
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
/// use bulletproofs::r1cs::{ConstraintSystem, CommittedConstraintSystem, R1CSError, R1CSProof, Variable, OpaqueScalar};
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
/// struct KShuffleGadget {}
/// 
/// impl KShuffleGadget {
/// 
///     fn fill_cs<CS: ConstraintSystem>(
///         cs: &mut CS,
///         x: Vec<Variable<OpaqueScalar>>,
///         y: Vec<Variable<OpaqueScalar>>,
///     ) -> Result<(), R1CSError> {
/// 
///         if x.len() != y.len() {
///             return Err(R1CSError::LayoutError{cause: "KShuffleGadget: inputs have different lengths"});
///         }
///         
///         let k = x.len();
/// 
///         if k == 1 {
///             cs.add_constraint(x[0].equals(y[0]));
///             return Ok(());
///         }
///         
///         cs.after_commitment(move |cs| {
/// 
///             let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
/// 
///             // Make last x multiplier for i = k-1 and k-2
///             let last_mulx_out = KShuffleGadget::last_multiplier(cs, z, x[k - 1], x[k - 2]);
/// 
///             // Make multipliers for x from i == [0, k-3]
///             let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
///                 KShuffleGadget::intermediate_multiplier(cs, z, prev_out?, x[i])
///             })?;
/// 
///             // Make last y multiplier for i = k-1 and k-2
///             let last_muly_out = KShuffleGadget::last_multiplier(cs, z, y[k - 1], y[k - 2]);
/// 
///             // Make multipliers for y from i == [0, k-3]
///             let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
///                 KShuffleGadget::intermediate_multiplier(cs, z, prev_out?, y[i])
///             })?;
/// 
///             // Check equality between last x mul output and last y mul output
///             cs.add_constraint(first_mulx_out.equals(first_muly_out));
/// 
///             Ok(())
///         })?;
/// 
///         Ok(())
///     }
/// 
///     fn last_multiplier<CS: ConstraintSystem>(
///         cs: &mut CS,
///         z: OpaqueScalar,
///         left: Variable<OpaqueScalar>,
///         right: Variable<OpaqueScalar>,
///     ) -> Result<Variable<OpaqueScalar>, R1CSError> {
///         let l = left - z;
///         let r = right - z;
/// 
///         let (al, ar, ao) =
///             cs.assign_multiplier(l.eval(), r.eval(), l.eval()*r.eval())?;
/// 
///         cs.add_constraint(al.equals(l));
///         cs.add_constraint(ar.equals(r));
/// 
///         Ok(ao)
///     }
/// 
///     fn intermediate_multiplier<CS: ConstraintSystem>(
///         cs: &mut CS,
///         z: OpaqueScalar,
///         left: Variable<OpaqueScalar>,
///         right: Variable<OpaqueScalar>,
///     ) -> Result<Variable<OpaqueScalar>, R1CSError> {
///         let r = right - z;
/// 
///         let (al, ar, ao) =
///             cs.assign_multiplier(left.assignment, r.eval(), left.assignment*r.eval())?;
/// 
///         cs.add_constraint(al.equals(left));
///         cs.add_constraint(ar.equals(r));
/// 
///         Ok(ao)
///     }
/// }
///
/// // This test allocates variables for the high-level variables, to check that high-level
/// // variable allocation and commitment works.
/// fn shuffle_helper(input: Vec<u64>, output: Vec<u64>) -> Result<(), R1CSError> {
///     let k = input.len();
///     let pc_gens = PedersenGens::default();
///     let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);
///     
///     let mut base_transcript = Transcript::new(b"ShuffleTest");
///     base_transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());
///     
///     // Prover's scope
///     let (proof, commitments) = {
///    
///         let mut v = Vec::with_capacity(2 * k);
///         v.extend_from_slice(&input);
///         v.extend_from_slice(&output);
///         let v_blinding = (0..2*k).map(|_| Scalar::random(&mut rand::thread_rng())).collect();
///         
///         R1CSProof::prove(
///             &bp_gens,
///             &pc_gens,
///             &mut base_transcript.clone(),
///             v.into_iter().map(Scalar::from).collect(),
///             v_blinding,
///             |cs, vars| {
///                 KShuffleGadget::fill_cs(
///                     cs, 
///                     (&vars[0..k]).into_iter().map(|v| v.into_opaque()).collect(),
///                     (&vars[k..2*k]).into_iter().map(|v| v.into_opaque()).collect()
///                 )
///             },
///         )?
///     };
///     
///     // Verifier's scope
///     
///     proof.verify(
///         &bp_gens,
///         &pc_gens,
///         &mut base_transcript.clone(),
///         commitments,
///         |cs, vars| {
///             KShuffleGadget::fill_cs(
///                 cs, 
///                 (&vars[0..k]).into_iter().map(|v| v.into_opaque()).collect(),
///                 (&vars[k..2*k]).into_iter().map(|v| v.into_opaque()).collect()
///             )
///         }
///     )
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
    pub use circuit_proof::{ScalarValue,OpaqueScalar,Assignment,Variable,VariableIndex};
    pub use circuit_proof::{Constraint, LinearCombination, IntoLC, LCVariable};
    pub use circuit_proof::{ConstraintSystem,ProverCS, VerifierCS};
    pub use circuit_proof::R1CSProof;
    pub use errors::R1CSError;
}
