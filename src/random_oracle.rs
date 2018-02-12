use curve25519_dalek::scalar::Scalar;
use tiny_keccak::Keccak;

#[derive(Clone)]
pub struct RandomOracle {
    hash: Keccak,
    state: SpongeState,
}

impl RandomOracle {
    /// Instantiates a new random oracle with a given label that
    /// will be committed as a first message with a padding.
    pub fn new(label: &[u8]) -> Self {
        let mut ro = RandomOracle {
            hash: Keccak::new_shake128(),
            state: SpongeState::Absorbing,
        };
        ro.commit(label);
        ro.pad(); // makes sure the label is disambiguated from the rest of the messages.
        ro
    }

    /// Sends a message to a random oracle.
    /// Each message must be less than 256 bytes long.
    pub fn commit(&mut self, message: &[u8]) {
        match self.state {
            SpongeState::Absorbing => {}
            SpongeState::Squeezing => {
                // no padding because squeeze phase does not insert data
                self.pad();
                self.state = SpongeState::Absorbing;
            }			
        }
        let len = message.len();
        if len > 255 {
            panic!("Committed message must be less than 256 bytes!");
        }
        // we use 1-byte length prefix, hence the limitation on the message size.
        let lenprefix = [len as u8; 1];
        self.hash.absorb(&lenprefix);
        self.hash.absorb(message);
    }

    /// Extracts an arbitrary-sized number of bytes as a challenge.
    pub fn challenge_bytes(&mut self, mut output: &mut [u8]) {
        match self.state {
            SpongeState::Absorbing => {
                self.pad();
                self.state = SpongeState::Squeezing;
            }
            SpongeState::Squeezing => {}
        }
        self.hash.squeeze(&mut output);
    }

    /// Gets a challenge in a form of a scalar by squeezing 
    /// 64 bytes and reducing them to a scalar.
    pub fn challenge_scalar(&mut self) -> Scalar {
        let mut buf = [0u8; 64];
        self.challenge_bytes(&mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }

    /// Pad separates the prior operations by a full permutation.
    /// Each incoming message is length-prefixed anyway, but padding
    /// enables pre-computing and re-using the oracle state.
    fn pad(&mut self) {
        // tiny_keccak's API is not very clear, 
        // so we'd probably need to fork and either document it, or tweak to make it more sensible.
        // 1. pad() only adds keccak padding, but does not advance internal offset and
        //    does not perform a permutation round.
        // 2. fill_block() does not pad, but resets the internal offset and does a permutation round.        

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

#[derive(Clone)]
enum SpongeState {
    Absorbing,
    Squeezing,
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;

    #[test]
    fn usage_example() {
        let mut ro = RandomOracle::new(b"TestProtocol");
        ro.commit(b"msg1");
        ro.commit(b"msg2");
        {
            let mut challenge1 = [0u8; 8];
            ro.challenge_bytes(&mut challenge1);
            assert_eq!(hex::encode(challenge1), "7f04fadac332ce45");
        }
        {
            let mut challenge2 = [0u8; 200];
            ro.challenge_bytes(&mut challenge2);
        }
        {
            let mut challenge3 = [0u8; 8];
            ro.challenge_bytes(&mut challenge3);
            assert_eq!(hex::encode(challenge3), "2cd86eb9913c0dc7");
        }
        ro.commit(b"msg3");
        {
            let mut challenge4 = [0u8; 8];
            ro.challenge_bytes(&mut challenge4);
            assert_eq!(hex::encode(challenge4), "383c7fc8d7bf8ad3");
        }
    }

    #[test]
    fn disambiguation() {
        {
            let mut ro = RandomOracle::new(b"TestProtocol");
            ro.commit(b"msg1msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "42023e04ad4f232c");
            }
        }
        {
            let mut ro = RandomOracle::new(b"TestProtocol");
            ro.commit(b"msg1");
            ro.commit(b"msg2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "7f04fadac332ce45");
            }
        }
        {
            let mut ro = RandomOracle::new(b"TestProtocol");
            ro.commit(b"ms");
            ro.commit(b"g1ms");
            ro.commit(b"g2");
            {
                let mut ch = [0u8; 8];
                ro.challenge_bytes(&mut ch);
                assert_eq!(hex::encode(ch), "18860c017b1d28ec");
            }
        }
    }
}
