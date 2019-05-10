//! Definition of the proof struct.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use inner_product_proof::InnerProductProof;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
///
/// Statements are specified by writing gadget functions which add
/// constraints to a [`ConstraintSystem`](::r1cs::ConstraintSystem)
/// implementation.  To construct an [`R1CSProof`], a prover constructs
/// a [`ProverCS`](::r1cs::ProverCS), then passes it to gadget
/// functions to build the constraint system, then consumes the
/// constraint system using
/// [`ProverCS::prove`](::r1cs::ProverCS::prove) to produce an
/// [`R1CSProof`].  To verify an [`R1CSProof`], a verifier constructs a
/// [`VerifierCS`](::r1cs::VerifierCS), then passes it to the same
/// gadget functions to (re)build the constraint system, then consumes
/// the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    pub(super) A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    pub(super) A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    pub(super) S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub(super) ipp_proof: InnerProductProof,
}
