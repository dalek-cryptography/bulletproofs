#![doc(include = "../docs/cs-proof.md")]

pub mod assignment;
pub mod cs;
pub mod linear_combination;
pub mod opaque_scalar;
pub mod prover;
pub mod verifier;

pub use self::assignment::{Assignment, AssignmentValue};
pub use self::cs::*;
pub use self::linear_combination::LinearCombination;
pub use self::opaque_scalar::OpaqueScalar;

// #[cfg(test)]
// mod tests;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::InnerProductProof;

use self::prover::ProverCS;

/// A proof of some statement specified by a [`ConstraintSystem`].
///
/// Statements are specified by writing gadget functions which add
/// constraints to a `ConstraintSystem` implementation.  To construct
/// an `R1CSProof`, a prover constructs a
/// [`Prover`](::r1cs::Prover), then passes it to gadget functions
/// to build the constraint system, then consumes the constraint
/// system using [`Prover::prove`](::r1cs::Prover::prove) to
/// produce an `R1CSProof`.  To verify an `R1CSProof`, a verifier
/// constructs a [`VerifierCS`](::r1cs::VerifierCS), then passes it to
/// the same gadget functions to (re)build the constraint system, then
/// consumes the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl R1CSProof {
	/// Creates a proof. The constraint system is built using the `builder` closure.
    pub fn prove<'a, 'b, F>(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        v: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
        builder: F,
    ) where
        F: FnOnce(&mut ProverCS) -> Result<(), R1CSError>,
    {
        // TBD: set up a prover

        // TBD: build constraint system

        // TBD:
        unimplemented!()
    }
}
