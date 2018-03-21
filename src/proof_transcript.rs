#![deny(missing_docs)]

//! The `proof_transcript` module contains API designed to allow
//! implementation of non-interactive proofs as if they were
//! interactive, using the Fiat-Shamir transform.

use curve25519_dalek::scalar::Scalar;

// XXX This uses experiment fork of tiny_keccak with half-duplex
// support that we require in this implementation.
// Review this after this PR is merged or updated:
// https://github.com/debris/tiny-keccak/pull/24
use tiny_keccak::Keccak;

use byteorder::{ByteOrder, LittleEndian};

/// The `ProofTranscript` struct represents a transcript of messages
/// between a prover and verifier engaged in a public-coin argument.
///
/// The prover can send messages to the `ProofTranscript` object,
/// which absorbs them into a sponge, and can then request challenges,
/// which are derived from all previous messages.
///
/// The verifier can then construct its own `ProofTranscript`
/// object, send it (what should be) the same messages, and request
/// (what should be) the same challenge values.
///
/// To create a `ProofTranscript` object, use `ProofTranscript::new()`
/// at the outermost protocol layer.  A `&mut` reference to this
/// object can then be passed to any sub-protocols, making it easy to
/// ensure that their challenge values are bound to the *entire* proof
/// transcript, not just the sub-protocol.
///
/// Internally, the `ProofTranscript` uses the Keccak sponge to
/// absorb messages and squeeze challenges.
///
/// # Example
///
/// ```
/// # extern crate curve25519_dalek;
/// # extern crate ristretto_bulletproofs;
/// # use ristretto_bulletproofs::proof_transcript::ProofTranscript;
/// # fn main() {
///
/// use curve25519_dalek::constants;
/// let B = &constants::RISTRETTO_BASEPOINT_TABLE;
///
/// let mut transcript = ProofTranscript::new(b"MyProofName: Don't copypaste this");
///
/// // Send "some message" to the verifier
/// transcript.commit(b"some message");
///
/// // Extract a challenge scalar
/// let x = transcript.challenge_scalar();
///
/// // Send x * B to the verifier
/// let P = B * &x;
/// transcript.commit(P.compress().as_bytes());
/// # }
/// ```
#[derive(Clone)]
pub struct ProofTranscript {
    hash: Keccak,
}

impl ProofTranscript {
    /// Begin a new, empty proof transcript, using the given `label`
    /// for domain separation.
    pub fn new(label: &[u8]) -> Self {
        let mut ro = ProofTranscript { hash: Keccak::new_shake128() };
        ro.commit(label);
        // makes sure the label is disambiguated from the rest of the messages.
        ro.pad();
        ro
    }

    /// Commit a `message` to the proof transcript.
    ///
    /// # Note
    ///
    /// Each message must be shorter than 64Kb (65536 bytes).
    pub fn commit(&mut self, message: &[u8]) {
        let len = message.len();
        if len > (u16::max_value() as usize) {
            panic!("Committed message must be less than 64Kb!");
        }

        let mut len_prefix = [0u8; 2];
        LittleEndian::write_u16(&mut len_prefix, len as u16);

        // XXX we rely on tiny_keccak experimental support for half-duplex mode and
        // correct switching from absorbing to squeezing and back.
        // Review this after this PR is merged or updated:
        // https://github.com/debris/tiny-keccak/pull/24
        self.hash.absorb(&len_prefix);
        self.hash.absorb(message);
    }

    /// Commit a `u64` to the proof transcript.
    ///
    /// This is a convenience method that commits the little-endian
    /// bytes of `value`.
    pub fn commit_u64(&mut self, value: u64) {
        let mut value_bytes = [0u8; 8];
        LittleEndian::write_u64(&mut value_bytes, value);

        self.commit(&value_bytes);
    }

    /// Extracts an arbitrary-sized challenge byte slice.
    pub fn challenge_bytes(&mut self, mut output: &mut [u8]) {
        // XXX we rely on tiny_keccak experimental support for half-duplex mode and
        // correct switching from absorbing to squeezing and back.
        // Review this after this PR is merged or updated:
        // https://github.com/debris/tiny-keccak/pull/24
        self.hash.squeeze(&mut output);
    }

    /// Extracts a challenge scalar.
    ///
    /// This is a convenience method that extracts 64 bytes and
    /// reduces modulo the group order.
    pub fn challenge_scalar(&mut self) -> Scalar {
        let mut buf = [0u8; 64];
        self.challenge_bytes(&mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }

    /// Pad separates the prior operations by padding
    /// the rest of the block with zeroes and applying a permutation.
    /// Each incoming message is length-prefixed anyway, but padding
    /// enables pre-computing and re-using the oracle state.
    fn pad(&mut self) {
        self.hash.fill_block();
    }
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;

    #[test]
    fn challenges_must_be_random() {
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"test");
            {
                let mut ch = [0u8; 32];
                ro.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "9ba30a0e71e8632b55fbae92495440b6afb5d2646ba6b1bb419933d97e06b810"
                );
                ro.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "add523844517c2320fc23ca72423b0ee072c6d076b05a6a7b6f46d8d2e322f94"
                );
                ro.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "ac279a11cac0b1271d210592c552d719d82d67c82d7f86772ed7bc6618b0927c"
                );
            }

            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"test");
            {
                let mut ch = [0u8; 16];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "9ba30a0e71e8632b55fbae92495440b6");
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "afb5d2646ba6b1bb419933d97e06b810");
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "add523844517c2320fc23ca72423b0ee");
            }

            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"test");
            {
                let mut ch = [0u8; 16];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "9ba30a0e71e8632b55fbae92495440b6");
                ro.commit(b"extra commitment");
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "11536e09cedbb6b302d8c7cd96471be5");
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "058c383da5f2e193a381aaa420b505b2");
            }
        }
    }

    #[test]
    fn messages_are_disambiguated_by_length_prefix() {
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "1ad843ea2bf7f8b6");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1");
            ro.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "79abbe29d8c33bb0");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg");
            ro.commit(b"1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "f88d0f790cde50d5");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"ms");
            ro.commit(b"g1ms");
            ro.commit(b"g2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "90ca22b443fb78a1");
            }
        }
    }
}
