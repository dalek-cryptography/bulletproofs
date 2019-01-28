//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

use byteorder::{ByteOrder, LittleEndian};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::ProofError;

pub trait TranscriptProtocol {
    /// Commit a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Commit a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Commit a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a 64-bit integer.
    fn commit_u64(&mut self, label: &'static [u8], n: u64);

    /// Commit a `scalar` with the given `label`.
    fn commit_scalar(&mut self, label: &'static [u8], scalar: &Scalar);

    /// Commit a `point` with the given `label`.
    fn commit_point(&mut self, label: &'static [u8], point: &CompressedRistretto);

    /// Check that a point is not the identity, then commit it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_commit_point(
        &mut self,
        label: &'static [u8],
        point: &CompressedRistretto,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}

fn le_u64(value: u64) -> [u8; 8] {
    let mut value_bytes = [0u8; 8];
    LittleEndian::write_u64(&mut value_bytes, value);
    value_bytes
}

impl TranscriptProtocol for Transcript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.commit_bytes(b"dom-sep", b"rangeproof v1");
        self.commit_bytes(b"n", &le_u64(n));
        self.commit_bytes(b"m", &le_u64(m));
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.commit_bytes(b"dom-sep", b"ipp v1");
        self.commit_bytes(b"n", &le_u64(n));
    }

    fn r1cs_domain_sep(&mut self) {
        self.commit_bytes(b"dom-sep", b"r1cs v1");
    }

    fn commit_u64(&mut self, label: &'static [u8], n: u64) {
        self.commit_bytes(label, &le_u64(n));
    }

    fn commit_scalar(&mut self, label: &'static [u8], scalar: &Scalar) {
        self.commit_bytes(label, scalar.as_bytes());
    }

    fn commit_point(&mut self, label: &'static [u8], point: &CompressedRistretto) {
        self.commit_bytes(label, point.as_bytes());
    }

    fn validate_and_commit_point(
        &mut self,
        label: &'static [u8],
        point: &CompressedRistretto,
    ) -> Result<(), ProofError> {
        use curve25519_dalek::traits::IsIdentity;

        if point.is_identity() {
            Err(ProofError::VerificationError)
        } else {
            Ok(self.commit_bytes(label, point.as_bytes()))
        }
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        Scalar::from_bytes_mod_order_wide(&buf)
    }
}
