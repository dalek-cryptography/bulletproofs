use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use tiny_keccak::Keccak;

pub trait Element {
    fn as_bytes(&self) -> &[u8];
}

pub trait FS {
    /// Commits the encoded element.
    /// Element is not length-prefixed or otherwise disambiguated in the input stream,
    /// so all protocol parameters must be pre-committed in a form of a label or prior commitments.
    fn commit<E: Element>(&mut self, element: &E);

    /// Returns another challenge scalar from the current state.
    fn challenge(&mut self) -> Scalar;
}

enum SpongeState {
    Absorbing,
    Squeezing,
}

pub struct ShakeFS {
    hash: Keccak,
    state: SpongeState,
}

impl ShakeFS {
    pub fn new<S: AsRef<[u8]>>(label: S) -> Self {
        let mut hash = Keccak::new_shake128();
        hash.update(label.as_ref());
        hash.pad();
        hash.fill_block();
        ShakeFS {
            hash: hash,
            state: SpongeState::Absorbing,
        }
    }
}

impl FS for ShakeFS {
    fn commit<E: Element>(&mut self, element: &E) {
        match self.state {
            SpongeState::Absorbing => {}
            SpongeState::Squeezing => {
                // no padding because squeeze phase does not insert data
                self.hash.fill_block();
                self.state = SpongeState::Absorbing;
            }			
        }
        self.hash.absorb(element.as_bytes());
    }
    fn challenge(&mut self) -> Scalar {
        match self.state {
            SpongeState::Absorbing => {
                self.hash.pad();
                self.hash.fill_block();
                self.state = SpongeState::Squeezing;
            }
            SpongeState::Squeezing => {}			
        }
        let mut buf = [0u8; 64];
        self.hash.squeeze(&mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }
}

impl Element for CompressedRistretto {
    fn as_bytes(&self) -> &[u8] {
        CompressedRistretto::as_bytes(self)
    }
}

impl Element for Scalar {
    fn as_bytes(&self) -> &[u8] {
        Scalar::as_bytes(self)
    }
}

impl Element for [u8; 1] {
    fn as_bytes(&self) -> &[u8] {
        &self[..]
    }
}

impl Element for [u8; 8] {
    fn as_bytes(&self) -> &[u8] {
        &self[..]
    }
}
