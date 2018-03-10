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
    state: SpongeState,
}

impl ProofTranscript {
    /// Begin an new, empty proof transcript, using the given `label`
    /// for domain separation.
    pub fn new(label: &[u8]) -> Self {
        let mut ro = ProofTranscript {
            hash: Keccak::new_shake128(),
            state: SpongeState::Absorbing,
        };
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
            self.pad();
            self.state = new_state;
        }
    }

    /// Pad separates the prior operations by a full permutation.
    /// Each incoming message is length-prefixed anyway, but padding
    /// enables pre-computing and re-using the oracle state.
    fn pad(&mut self) {
        // tiny_keccak's API is not very clear,
        // so we'd probably need to fork and either document it, or tweak to make it more sensible.
        // 1. pad() only adds keccak padding, but does not advance internal offset and
        //    does not perform a permutation round.
        // 2. fill_block() does not pad, but resets the internal offset
        //    and does a permutation round.
        //
        // XXX(hdevalence) before this is "production-ready", we
        // should sort out what tiny_keccak is actually doing and
        // decide on something sensible. Maybe this overlaps with
        // Noise NXOF work?
        match self.state {
            SpongeState::Absorbing => {
                self.hash.pad();
                self.hash.fill_block();
            }
            SpongeState::Squeezing => {
                // in the squeezing state we are not feeding messages,
                // only reading portions of a state, so padding does not make sense.
                // what we need is to perform computation and reset the internal offset to zero.
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
                assert_eq!(hex::encode(ch), "039f39a21e3cce4a");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1");
            ro.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "b4c47055cfcec1d2");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg");
            ro.commit(b"1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "325247ab6948b7a1");
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
                assert_eq!(hex::encode(ch), "04068112e4fa0f44");
            }
        }
    }
}
