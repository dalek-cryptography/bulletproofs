#![deny(missing_docs)]

//! The `proof_transcript` module contains API designed to allow
//! implementation of non-interactive proofs as if they were
//! interactive, using the Fiat-Shamir transform.

use curve25519_dalek::scalar::Scalar;

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
/// Internally, the `ProofTranscript` is supposed to use Keccak to
/// absorb incoming messages and to squeeze challenges.  The
/// construction currently used is ad-hoc, has no security analysis,
/// and is **only suitable for testing**.
///
/// # Example
///
/// ```
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
    hash: Keccak,
    rate: usize,
    write_offset: usize, // index within a block where the message must be absorbed
}

impl ProofTranscript {
    // Implementation notes
    //
    // The implementation has 3 layers:
    // 1. commit/challenge - take input/output buffers <64K, responsible for disambiguation (length prefixing)
    // 2. write/read       - take arbitrary buffers, responsible for splitting data over Keccak-f invocations and padding
    // 3. absorb/squeeze   - actual sponge operations, outer layers ensure that absorb/squeeze do not perform unnecessary permutation
    //

    /// Begin a new, empty proof transcript, using the given `label`
    /// for domain separation.
    pub fn new(label: &[u8]) -> Self {
        let mut ro = ProofTranscript {
            // NOTE: if you change the security parameter, also change the rate below
            hash: Keccak::new_shake128(),
            rate: 1600/8 - (2*128/8), // 168 bytes
            write_offset: 0,
        };
        // We will bump the version prefix each time we
        // make a breaking change in order to disambiguate
        // from the previous versions of this implementation.
        ro.commit(b"ProofTranscript v2");
        ro.commit(label);
        let mut empty = [0;0];
        ro.challenge_bytes(&mut empty[..]);
        ro
    }

    /// Commit a `input` to the proof transcript.
    ///
    /// # Note
    ///
    /// Each input must be ≤ than the number of bytes
    /// returned by `max_commit_size()`.
    pub fn commit(&mut self, input: &[u8]) {
        let len = input.len();
        if len > (u16::max_value() as usize) {
            panic!("Committed input must be less than 64Kb!");
        }
        self.write_u16(len as u16);
        self.write(input);
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
    pub fn challenge_bytes(&mut self, output: &mut [u8]) {
        let len = output.len();
        if output.len() > (u16::max_value() as usize) {
            panic!("Challenge output must be less than 64Kb!");
        }
        // Note: when reading, length prefix N is followed by keccak padding 10*1
        // as if empty message was written; when writing, length prefix N is followed
        // by N bytes followed by keccak padding 10*1.
        // This creates ambiguity only for case N=0 (empty write or empty read),
        // which is safe as no information is actually transmitted in either direction.
        self.write_u16(len as u16);
        self.read(output);
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

    /// Extracts a pair of challenge scalars.
    ///
    /// This is a convenience method that extracts 128 bytes and
    /// reduces each 64-byte half modulo the group order.
    pub fn challenge_scalars_pair(&mut self) -> (Scalar, Scalar) {
        let mut buf128 = [0u8; 128];
        let mut buf64 = [0u8; 64];
        self.challenge_bytes(&mut buf128);
        buf64.copy_from_slice(&buf128[..64]);
        let a = Scalar::from_bytes_mod_order_wide(&buf64);
        buf64.copy_from_slice(&buf128[64..]);
        let b = Scalar::from_bytes_mod_order_wide(&buf64);
        (a,b)
    }

    /// Internal API: writes 2-byte length prefix.
    fn write_u16(&mut self, integer: u16) {
        let mut intbuf = [0u8; 2];
        LittleEndian::write_u16(&mut intbuf, integer);
        self.write(&intbuf);
    }

    /// Internal API: writes arbitrary byte slice
    /// splitting it over multiple duplex calls if needed.
    fn write(&mut self, mut input: &[u8]) {
        // `write` can be called multiple times.
        // If we overflow the available room (`rate-1` at most)
        // we absorb what we can, add Keccak padding, permute and continue.
        let mut room = self.rate - 1 - self.write_offset; // 1 byte is reserved for keccak padding 10*1.
        while input.len() > room {
            self.hash.absorb(&input[..room]);
            self.hash.pad();
            self.hash.fill_block();
            self.write_offset = 0;
            room = self.rate - 1;
            input = &input[room..];
        }
        self.hash.absorb(input);
        self.write_offset += input.len(); // could end up == (rate-1)
    }

    /// Internal API: reads arbitrary byte slice
    /// splitting it over multiple duplex calls if needed.
    fn read(&mut self, output: &mut [u8]) {
        // Note 1: `read` is called only once after `write`, so we do
        //         not need to support multiple reads from some offset.
        //         We only need to complete the pending duplex call by padding and permuting.
        // Note 2: Since we hash in the total output buffer length,
        //         we can use default squeeze behaviour w/o simulating blank inputs:
        //         the resulting byte-stream will be disambiguated by that length prefix and keccak padding.
        self.hash.pad();
        self.hash.fill_block();
        self.write_offset = 0;
        self.hash.squeeze(output);
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
            let mut ch = [0u8; 32];
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "956ea2a6919ea9d83523fcf31e96b78d10070d25e2c74e9b9fbab6e39f75c587"
            );
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "86533e8e5dad89cbea10d4a6c05a126713d6672005ab3e6737665f25cbad37b7"
            );
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "25b9a2ef2ee8a8e5f2a2397c13cd2ddb28f88c7aef9860d0c9e405383fa0a072"
            );
        }

        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"test");
            let mut ch = [0u8; 32];
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "956ea2a6919ea9d83523fcf31e96b78d10070d25e2c74e9b9fbab6e39f75c587"
            );
            ro.commit(b"extra commitment");
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "9322b9a5b29adb4a2f50649a7827cfd8e6e385ec02b29c75375720d8dcb18e02"
            );
            ro.challenge_bytes(&mut ch);
            assert_eq!(
                hex::encode(ch),
                "ea6f00d4158902aff1e4336c8774f0ad753baec8e90df3485240dbc9e4244813"
            );
        }
    }

    #[test]
    fn inputs_are_disambiguated_by_length_prefix() {
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "b66f3c6296c4e048");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg1");
            ro.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "d4633732e4ab0ebb");
            }
        }
        {
            let mut ro = ProofTranscript::new(b"TestProtocol");
            ro.commit(b"msg");
            ro.commit(b"1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "3a8811dd01672b37");
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
                assert_eq!(hex::encode(ch), "49800ad89aedfd44");
            }
        }
    }


    #[test]
    fn outputs_are_disambiguated_by_length_prefix() {
        let mut ro = ProofTranscript::new(b"TestProtocol");
        {
            let mut ch = [0u8; 16];
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "2c56459cdec02be511b7f97a41a54eba");
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "dfa982f9ad6167f3eb5eea78815d062b");
        }

        let mut ro = ProofTranscript::new(b"TestProtocol");
        {
            let mut ch = [0u8; 8];
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "c5103a6cfa35c699");
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "d471afab3b0a2ff1");
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "4697bc53108977b2");
            ro.challenge_bytes(&mut ch);
            assert_eq!(hex::encode(ch), "67e8d3923df50dd0");
        }
    }

}
