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
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
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
}
