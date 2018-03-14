//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.
//!
//!
//! # Example
//!
//! ```
//! # extern crate ristretto_bulletproofs;
//! # use ristretto_bulletproofs::generators::Generators;
//! # fn main() {
//!
//! let generators = Generators::new(64,1);
//! let view = generators.all();
//! let G0 = view.G[0];
//! let H0 = view.H[0];
//!
//! # }
//! ```

#![allow(non_snake_case)]
#![deny(missing_docs)]

// XXX we should use Sha3 everywhere

use curve25519_dalek::ristretto::RistrettoPoint;
use sha2::{Digest, Sha256};

/// The `GeneratorsChain` creates an arbitrary-long sequence of orthogonal generators.
/// The sequence can be deterministically produced starting with an arbitrary point.
struct GeneratorsChain {
    next_point: RistrettoPoint,
}

impl GeneratorsChain {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut hash = Sha256::default();
        hash.input(b"GeneratorsChainInit");
        hash.input(label);
        let next_point = RistrettoPoint::from_hash(hash);
        GeneratorsChain { next_point }
    }
}

impl Default for GeneratorsChain {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl Iterator for GeneratorsChain {
    type Item = RistrettoPoint;
    fn next(&mut self) -> Option<Self::Item> {
        let current_point = self.next_point;
        let mut hash = Sha256::default();
        hash.input(b"GeneratorsChainNext");
        hash.input(current_point.compress().as_bytes());
        self.next_point = RistrettoPoint::from_hash(hash);
        Some(current_point)
    }
}

/// `Generators` contains all the generators needed for aggregating `m` range proofs of `n` bits each.
#[derive(Clone)]
pub struct Generators {
    /// Number of bits in a rangeproof
    pub n: usize,
    /// Number of values or parties
    pub m: usize,
    /// Main base of a Pedersen commitment
    B: RistrettoPoint,
    /// Base for the blinding factor in a Pedersen commitment
    B_blinding: RistrettoPoint,
    /// Per-bit generators for the bit values
    G: Vec<RistrettoPoint>,
    /// Per-bit generators for the bit blinding factors
    H: Vec<RistrettoPoint>,
}

/// Represents a view into `Generators` relevant to a specific range proof.
pub struct GeneratorsView<'a> {
    /// Main base of a Pedersen commitment
    pub B: &'a RistrettoPoint,
    /// Base for the blinding factor in a Pedersen commitment
    pub B_blinding: &'a RistrettoPoint,
    /// Per-bit generators for the bit values
    pub G: &'a [RistrettoPoint],
    /// Per-bit generators for the bit blinding factors
    pub H: &'a [RistrettoPoint],
}

impl Generators {
    /// Creates generators for `m` range proofs of `n` bits each.
    pub fn new(n: usize, m: usize) -> Self {
        // Using unwrap is safe here, because the iterator is unbounded.
        let B = GeneratorsChain::new(b"Bulletproofs.Generators.B")
            .next()
            .unwrap();
        let B_blinding = GeneratorsChain::new(b"Bulletproofs.Generators.B_blinding")
            .next()
            .unwrap();

        let G = GeneratorsChain::new(b"Bulletproofs.Generators.G")
            .take(n * m)
            .collect();
        let H = GeneratorsChain::new(b"Bulletproofs.Generators.H")
            .take(n * m)
            .collect();

        Generators {
            n,
            m,
            B,
            B_blinding,
            G,
            H,
        }
    }

    /// Returns a view into the entirety of the generators.
    pub fn all(&self) -> GeneratorsView {
        GeneratorsView {
            B: &self.B,
            B_blinding: &self.B_blinding,
            G: &self.G[..],
            H: &self.H[..],
        }
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> GeneratorsView {
        let lower = self.n * j;
        let upper = self.n * (j + 1);
        GeneratorsView {
            B: &self.B,
            B_blinding: &self.B_blinding,
            G: &self.G[lower..upper],
            H: &self.H[lower..upper],
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;

    #[test]
    fn rangeproof_generators() {
        let n = 2;
        let m = 3;
        let gens = Generators::new(n, m);

        // The concatenation of shares must be the full generator set
        assert_eq!(
            [gens.all().G[..n].to_vec(), gens.all().H[..n].to_vec()],
            [gens.share(0).G[..].to_vec(), gens.share(0).H[..].to_vec()]
        );
        assert_eq!(
            [
                gens.all().G[n..][..n].to_vec(),
                gens.all().H[n..][..n].to_vec(),
            ],
            [gens.share(1).G[..].to_vec(), gens.share(1).H[..].to_vec()]
        );
        assert_eq!(
            [
                gens.all().G[2 * n..][..n].to_vec(),
                gens.all().H[2 * n..][..n].to_vec(),
            ],
            [gens.share(2).G[..].to_vec(), gens.share(2).H[..].to_vec()]
        );
    }

    #[test]
    fn generator_orthogonality() {
        let n = 2;
        let m = 1;
        let gens = Generators::new(n, m);
        let view = gens.all();

        assert_eq!(
            hex::encode(RISTRETTO_BASEPOINT_POINT.compress().as_bytes()),
            "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76"
        );
        assert_eq!(
            hex::encode(view.B.compress().as_bytes()),
            "6abd9de445ed16637be32da51bbd3fa114f984c52081258a1f476c8493f09731"
        );
        assert_eq!(
            hex::encode(view.B_blinding.compress().as_bytes()),
            "5c97d2b3cd6994ae1a4d6bd7371b40800b6a28afb1db14b81b4b5107ed9c5478"
        );
        assert_eq!(
            hex::encode(view.G[0].compress().as_bytes()),
            "688bac289f5e4ed902648278b4e81a2b8a028365b0a7753fd0242e499bd6200e"
        );
        assert_eq!(
            hex::encode(view.G[1].compress().as_bytes()),
            "7e49425c91464e4b3aa4c4676e7deba7e91d1cfd1a19a0a39dfd73b0cecdb55c"
        );
        assert_eq!(
            hex::encode(view.H[0].compress().as_bytes()),
            "50140daade760912586d04be961dab5d723d1aba05b536b13b99f69225ea4002"
        );
        assert_eq!(
            hex::encode(view.H[1].compress().as_bytes()),
            "ac23f3c0964e8bb1b9c61869edbb39c4417a96d518715d2e3e60a03cd722d13d"
        );
    }
}
