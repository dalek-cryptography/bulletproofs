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

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use sha2::Sha256;

/// The `GeneratorsChain` creates an arbitrary-long sequence of orthogonal generators.
/// The sequence can be deterministically produced starting with an arbitrary point.
struct GeneratorsChain {
    current_point: RistrettoPoint,
}

impl GeneratorsChain {
    /// Creates a chain of generators starting with a given point.
    /// Use `GeneratorsChain::default()` to start after the
    /// standard Ristretto base point.
    fn start_after(point: &RistrettoPoint) -> Self {
        GeneratorsChain {
            current_point: point.clone(),
        }
    }
}

impl Default for GeneratorsChain {
    fn default() -> Self {
        GeneratorsChain::start_after(&RISTRETTO_BASEPOINT_POINT)
    }
}

impl Iterator for GeneratorsChain {
    type Item = RistrettoPoint;
    fn next(&mut self) -> Option<Self::Item> {
        self.current_point = RistrettoPoint::hash_from_bytes::<Sha256>(
            self.current_point.compress().as_bytes()
        );
        Some(self.current_point.clone())
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
        let mut gen = GeneratorsChain::default();
        let B = gen.next().unwrap();
        let B_blinding = gen.next().unwrap();

        let G = GeneratorsChain::start_after(&B).take(n*m).collect();
        let H = GeneratorsChain::start_after(&B_blinding).take(n*m).collect();

        Generators { n, m, B, B_blinding, G, H }
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
        let range = j * self.n..(j + 1) * self.n;
        GeneratorsView {
            B: &self.B,
            B_blinding: &self.B_blinding,
            G: &self.G[range.clone()],
            H: &self.H[range],
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

    #[test]
    fn generator_chain() {
        let mut gens = GeneratorsChain::default();
        let G = gens.next().unwrap();
        let H = gens.next().unwrap();
        let J = gens.next().unwrap();

        let GHJ: Vec<_> = GeneratorsChain::default().take(3).collect();
        let HJ: Vec<_> = GeneratorsChain::start_after(&G).take(2).collect();
        let J_vec: Vec<_> = GeneratorsChain::start_after(&H).take(1).collect();

        assert_eq!(vec![G, H, J], GHJ);
        assert_eq!(vec![H, J], HJ);
        assert_eq!(vec![J], J_vec);
    }
}
