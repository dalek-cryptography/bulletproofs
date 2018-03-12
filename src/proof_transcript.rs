#![deny(missing_docs)]

//! The `proof_transcript` module contains API designed to allow
//! implementation of non-interactive proofs as if they were
//! interactive, using the Fiat-Shamir transform.

use curve25519_dalek::scalar::Scalar;

// XXX fix up deps (see comment below re: "api somewhat unclear")
use tiny_keccak::Keccak;

use byteorder::{ByteOrder, LittleEndian};

/// The `SpongeState` enum describes the state of the internal sponge
/// used by a `ProofTranscript`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SpongeState {
    Absorbing,
    Squeezing,
}

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
/// Internally, the `ProofTranscript` uses the Keccak sponge in half-duplex
/// mode with at most 128-bit collision resistance and 256-bit preimage
/// resistance security.
///
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
    state: SpongeState,
}

impl ProofTranscript {
    /// Begin an new, empty proof transcript, using the given `label`
    /// for domain separation.
    pub fn new(label: &[u8]) -> Self {
        let mut ro = ProofTranscript {
            // NIST currently does not define a half-duplex Keccak instance
            // (meaning, the one that allows switching between squeezing and absorbing
            // multiple times). So we use the delimiter from the
            // raw Keccak instances which is 0x01 (aka "no delimiter", where 1
            // is a the pre-computed padding bit of the 10*1 sequence).
            // Note that due to this padding, the empty delimiter is fully domain-separated
            // from all NIST delimiters, current or future ones.
            //
            // We use the same security level as SHAKE-128 which gives us 256-bit capacity
            // and 1344 bits (168 bytes) of absorbing/squeezing rate per permutation.
            hash: Keccak::new((1600 - 2*128)/8, 0x01),
            state: SpongeState::Absorbing,
        };
        ro.commit(label);
        // makes sure the label is disambiguated from the rest of the messages.
        ro.permute();
        ro
    }

    /// Commit a `message` to the proof transcript.
    ///
    /// # Note
    ///
    /// Each message must be shorter than 64Kb (65536 bytes).
    pub fn commit(&mut self, message: &[u8]) {
        self.set_state(SpongeState::Absorbing);

        let len = message.len();
        if len > (u16::max_value() as usize) {
            panic!("Committed message must be less than 64Kb!");
        }

        let mut len_prefix = [0u8; 2];
        LittleEndian::write_u16(&mut len_prefix, len as u16);

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
        self.set_state(SpongeState::Squeezing);
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

    /// Set the sponge state to `new_state`.
    ///
    /// Does necessary padding+permutation if needed to transition
    /// from one state to another.
    fn set_state(&mut self, new_state: SpongeState) {
        if self.state != new_state {
            self.permute();
            self.state = new_state;
        }
    }

    /// Permute separates the prior operations by a full permutation.
    /// Each incoming message is length-prefixed anyway, but padding
    /// enables pre-computing and re-using the oracle state.
    fn permute(&mut self) {
        // API of tiny_keccak is weird, so here's a documentation of its internals:
        // 1. Keccak.pad() adds padding 10*1.
        //    It does not advance internal offset or perform a permutation round.
        // 2. Keccak.fill_block() does not pad,
        //    but resets the internal offset to zero and applies Keccak-f permutation round.
        //
        // XXX(hdevalence) before this is "production-ready", we
        // should sort out what tiny_keccak is actually doing and
        // decide on something sensible. Maybe this overlaps with
        // Noise NXOF work?
        match self.state {
            SpongeState::Absorbing => {
                // Pad the message with 10*1, 
                // then permute and reset the offset to 0.
                self.hash.pad();
                self.hash.fill_block();
            }
            SpongeState::Squeezing => {
                // Permute and reset the offset to 0.
                // Note: in the squeezing state we are not feeding messages,
                // only reading portions of a state, so padding with 10*1 does not make sense.
                self.hash.fill_block();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;

    #[test]
    fn messages_are_disambiguated_by_length_prefix() {
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "0b0150d57ba6bd60");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1");
            ro.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "b31e295b180fee9f");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg");
            ro.commit(b"1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "286c139c1606518d");
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
                assert_eq!(hex::encode(ch), "9bc04ae9835d000b");
            }
        }
    }
}
