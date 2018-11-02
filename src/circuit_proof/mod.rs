#![doc(include = "../docs/cs-proof.md")]

mod opaque_scalar;
mod scalar_value;
mod assignment;
mod constraints;
mod linear_combination;
mod lc;
mod cs;
mod prover;
mod verifier;

pub use self::scalar_value::ScalarValue;
pub use self::opaque_scalar::OpaqueScalar;
pub use self::assignment::Assignment;
pub use self::constraints::{Variable,VariableIndex,Constraint};
pub use self::linear_combination::{IntoLC, Variable as LCVariable, LinearCombination};
pub use self::cs::ConstraintSystem;
pub use self::prover::ProverCS;
pub use self::verifier::VerifierCS;

#[cfg(test)]
mod tests;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::InnerProductProof;

/// A proof of some statement specified by a [`ConstraintSystem`].
///
/// XXX OBSOLETE:
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
    /// Commitment to the values of the first-phase input wires
    A_I1: CompressedRistretto,
    /// Commitment to the values of the first-phase output wires
    A_O1: CompressedRistretto,
    /// Commitment to the first-phase blinding factors
    S1: CompressedRistretto,
    /// Commitment to the values of the second-phase input wires
    A_I2: CompressedRistretto,
    /// Commitment to the values of the second-phase output wires
    A_O2: CompressedRistretto,
    /// Commitment to the second-phase blinding factors
    S2: CompressedRistretto,
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
	/// Creates and returns a proof, along with the Pedersen commitments for all provided secrets.
	/// The constraint system is specified using the `builder` closure.
    pub fn prove<'a, 'b, F>(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        v: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
        builder: F,
    ) -> Result<(Self, Vec<CompressedRistretto>), R1CSError>
    where
        F: FnOnce(&mut ProverCS, Vec<Variable<Scalar>>) -> Result<(), R1CSError>,
    {
    	// 1. Prepare a proving CS.
    	let (prover, commitments) = ProverCS::new(
        	bp_gens,
        	pc_gens,
        	transcript,
        	v,
        	v_blinding
        );
    	
    	// 2. Create a proof.
        let proof = prover.prove(builder)?;

        Ok((proof, commitments))
    }

	/// Verifies the proof for the given commitments.
	/// The constraint system is specified using the `builder` closure.
    pub fn verify<'a, 'b, F>(
    	&self,
    	bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        commitments: Vec<CompressedRistretto>,
        builder: F,
    ) -> Result<(), R1CSError> 
    where
        F: FnOnce(&mut VerifierCS, Vec<Variable<Scalar>>) -> Result<(), R1CSError>,
    {
    	// 1. Prepare a verifying CS.
    	let verifier = VerifierCS::new(
        	bp_gens,
        	pc_gens,
        	transcript,
        	commitments,
    	);

    	// 2. Verify the proof.
        verifier.verify(&self, builder)
    }
}
