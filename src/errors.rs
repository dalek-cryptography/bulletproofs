//! Errors related to proving and verifying proofs.

/// Represents an error in proof creation, verification, or parsing.
#[derive(Fail, Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    /// This error occurs when a proof failed to verify.
    #[fail(display = "Proof verification failed.")]
    VerificationError,
    /// This error occurs when the proof encoding is malformed.
    #[fail(display = "Proof data could not be parsed.")]
    FormatError,
    /// This error occurs during proving if the number of blinding
    /// factors does not match the number of values.
    #[fail(display = "Wrong number of blinding factors supplied.")]
    WrongNumBlindingFactors,
    /// This error occurs when attempting to create a proof with
    /// bitsize other than \\(8\\), \\(16\\), \\(32\\), or \\(64\\).
    #[fail(display = "Invalid bitsize, must have n = 8,16,32,64.")]
    InvalidBitsize,
    /// This error occurs when attempting to create an aggregated
    /// proof with non-power-of-two aggregation size.
    #[fail(display = "Invalid aggregation size, m must be a power of 2.")]
    InvalidAggregation,
    /// This error occurs when there are insufficient generators for the proof.
    #[fail(display = "Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    /// This error results from an internal error during proving.
    ///
    /// The single-party prover is implemented by performing
    /// multiparty computation with ourselves.  However, because the
    /// MPC protocol is not exposed by the single-party API, we
    /// consider its errors to be internal errors.
    #[fail(display = "Internal error during proof creation: {}", _0)]
    ProvingError(MPCError),
}

impl From<MPCError> for ProofError {
    fn from(e: MPCError) -> ProofError {
        match e {
            MPCError::InvalidBitsize => ProofError::InvalidBitsize,
            MPCError::InvalidAggregation => ProofError::InvalidAggregation,
            MPCError::InvalidGeneratorsLength => ProofError::InvalidGeneratorsLength,
            _ => ProofError::ProvingError(e),
        }
    }
}

/// Represents an error during the multiparty computation protocol for
/// proof aggregation.
///
/// This is a separate type from the `ProofError` to allow a layered
/// API: although the MPC protocol is used internally for single-party
/// proving, its API should not expose the complexity of the MPC
/// protocol.
#[derive(Fail, Clone, Debug, Eq, PartialEq)]
pub enum MPCError {
    /// This error occurs when the dealer gives a zero challenge,
    /// which would annihilate the blinding factors.
    #[fail(display = "Dealer gave a malicious challenge value.")]
    MaliciousDealer,
    /// This error occurs when attempting to create a proof with
    /// bitsize other than \\(8\\), \\(16\\), \\(32\\), or \\(64\\).
    #[fail(display = "Invalid bitsize, must have n = 8,16,32,64")]
    InvalidBitsize,
    /// This error occurs when attempting to create an aggregated
    /// proof with non-power-of-two aggregation size.
    #[fail(display = "Invalid aggregation size, m must be a power of 2")]
    InvalidAggregation,
    /// This error occurs when there are insufficient generators for the proof.
    #[fail(display = "Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    /// This error occurs when the dealer is given the wrong number of
    /// value commitments.
    #[fail(display = "Wrong number of value commitments")]
    WrongNumBitCommitments,
    /// This error occurs when the dealer is given the wrong number of
    /// polynomial commitments.
    #[fail(display = "Wrong number of value commitments")]
    WrongNumPolyCommitments,
    /// This error occurs when the dealer is given the wrong number of
    /// proof shares.
    #[fail(display = "Wrong number of proof shares")]
    WrongNumProofShares,
    /// This error occurs when one or more parties submit malformed
    /// proof shares.
    #[fail(display = "Malformed proof shares from parties {:?}", bad_shares)]
    MalformedProofShares {
        /// A vector with the indexes of the parties whose shares were malformed.
        bad_shares: Vec<usize>,
    },
}

/// Represents an error during the proving or verifying of a constraint system.
#[cfg(feature = "yoloproofs")]
#[derive(Fail, Clone, Debug, Eq, PartialEq)]
pub enum R1CSError {
    /// Occurs when there are insufficient generators for the proof.
    #[fail(display = "Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    /// This error occurs when the proof encoding is malformed.
    #[fail(display = "Proof data could not be parsed.")]
    FormatError,
    /// Occurs when verification of an
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[fail(display = "R1CSProof did not verify correctly.")]
    VerificationError,

    /// Occurs when trying to use a missing variable assignment.
    /// Used by gadgets that build the constraint system to signal that
    /// a variable assignment is not provided when the prover needs it.
    #[fail(display = "Variable does not have a value assignment.")]
    MissingAssignment,

    /// Occurs when a gadget receives an inconsistent input.
    #[fail(display = "Gadget error: {:?}", description)]
    GadgetError {
        /// The description of the reasons for the error.
        description: String,
    },
}
