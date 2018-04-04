#![deny(missing_docs)]

//! The `proof_transcript` module contains API designed to allow
//! implementation of non-interactive proofs as if they were
//! interactive, using the Fiat-Shamir transform.

use curve25519_dalek::scalar::Scalar;
use sha2::{Sha512, Digest};

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
/// Internally, the `ProofTranscript` uses a chain of SHA2-512 calls,
/// one call per absorbing a message or squeezing a challenge:
///
/// ```ascii
///
///
/// commit(message):      state0  message
///                            ↓  ↓
///                           sha512
///                            ↓  ↓
///                       state1  (ignore)
///                            ↓
/// challenge_scalar():       sha512
///                            ↓  ↓
///                       state2  L (left half)
///                            ↓
///                           sha512
///                            ↓  ↓
///                       state3  R (right half)  // scalar ← L||R mod l
///
/// ```
///
/// # Example
///
/// ```
/// # #![allow(non_snake_case)]
/// # extern crate curve25519_dalek;
/// # extern crate ristretto_bulletproofs;
/// # use ristretto_bulletproofs::ProofTranscript;
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
    state: [u8; 32],
}

impl ProofTranscript {
    /// Begin a new, empty proof transcript, using the given `label`
    /// for domain separation.
    pub fn new(label: &[u8]) -> Self {
        let mut pt = ProofTranscript { state: [0u8; 32] };
        pt.commit(label);
        pt
    }

    /// Commit a `message` to the proof transcript.
    ///
    /// # Note
    ///
    /// Each message must be shorter than 64Kb (65536 bytes).
    pub fn commit(&mut self, message: &[u8]) {
        let mut hash = Sha512::default();
        hash.input(&self.state);
        hash.input(message);
        let result = hash.result();
        self.state.copy_from_slice(&result[..32]);
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
        while output.len() > 0 {
            let outlen = output.len();
            let size: usize = if outlen <= 32 { outlen } else { 32 };

            let mut hash = Sha512::default();
            let mut prefix = [0u8; 8];
            LittleEndian::write_u64(&mut prefix, outlen as u64);
            // length prefix for the output is necessary
            // to make sure requests of different lengths are unrelated
            hash.input(&prefix);
            hash.input(&self.state);
            let result = hash.result();
            self.state.copy_from_slice(&result[..32]);
            output[..size].copy_from_slice(&result[32..(32 + size)]);
            output = &mut output[size..];
        }
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
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;

    #[test]
    fn challenges_must_be_random() {
        {
            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"test");
            {
                let mut ch = [0u8; 32];
                pt.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "250342b47f8992bd22e72707d9a0736f9b0a736786669020668c11d791359c14"
                );
                pt.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "8622e6b7c4f11c5752f784efd0a3c837c2aab46688ec5193a2c35293b1ebdf89"
                );
                pt.challenge_bytes(&mut ch);
                assert_eq!(
                    hex::encode(ch),
                    "20f419642415493816336132119293409da947a81e2f2a3a41586c579c252866"
                );
            }

            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"test");
            {
                let mut ch = [0u8; 16];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "e485d35fb39cb3dcffdb85e69d9f6e41");
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "6843787badc2c814a907b96724268276");
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "efc93d2be979ca3978323d04ed23faa8");
            }

            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"test");
            {
                let mut ch = [0u8; 16];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "e485d35fb39cb3dcffdb85e69d9f6e41");
                pt.commit(b"extra commitment");
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "182d0f0483b101b87e8be8026a3f864b");
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "20ad36c1adbf07c864650925af0316ce");
            }
        }
    }

    #[test]
    fn messages_are_disambiguated_by_length_prefix() {
        {
            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"msg1msg2");
            {
                let mut ch = [0u8; 8];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "0b19216256fe74cb");
            }
        }
        {
            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"msg1");
            pt.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "172398c864df2231");
            }
        }
        {
            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"msg");
            pt.commit(b"1msg2");
            {
                let mut ch = [0u8; 8];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "efb49fc1c7625d94");
            }
        }
        {
            let mut pt = ProofTranscript::new(b"TestProtocol");
            pt.commit(b"ms");
            pt.commit(b"g1ms");
            pt.commit(b"g2");
            {
                let mut ch = [0u8; 8];
                pt.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "9c6de7aecda7ee40");
            }
        }
    }
}
