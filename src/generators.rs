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

/// Implements an infinite iterator of generators
struct GeneratorsChain {
    next_point: RistrettoPoint,
}

impl GeneratorsChain {
    pub fn new() -> Self {
        GeneratorsChain::at(&RISTRETTO_BASEPOINT_POINT)
    }
    pub fn at(point: &RistrettoPoint) -> Self {
        GeneratorsChain { next_point: point.clone() }
    }
}

impl Iterator for GeneratorsChain {
    type Item = RistrettoPoint;
    fn next(&mut self) -> Option<Self::Item> {
        let p2 = RistrettoPoint::hash_from_bytes::<Sha256>(self.next_point.compress().as_bytes());
        let result = self.next_point.clone();
        self.next_point = p2;
        Some(result)
    }
}

/// `RangeproofGenerators` contains all the generators for `n`-bit proofs and `m` values (parties).
#[derive(Clone)]
pub struct Generators {
    /// Number of bits in a rangeproof
    pub n: usize,
    /// Number of values or parties
    pub m: usize,
    /// Main base of the pedersen commitment
    B: RistrettoPoint,
    /// Base for the blinding factor in the pedersen commitment
    B_b: RistrettoPoint,
    /// Per-bit generators for the bit values
    G: Vec<RistrettoPoint>,
    /// Per-bit generators for the bit blinding factors
    H: Vec<RistrettoPoint>,
}

/// Represents a view into generators relevant to a specific actor.
pub struct GeneratorsView<'a> {
    /// Main base of the pedersen commitment
    pub B: &'a RistrettoPoint,
    /// Base for the blinding factor in the pedersen commitment
    pub B_b: &'a RistrettoPoint,
    /// Per-bit generators for the bit values
    pub G: &'a [RistrettoPoint],
    /// Per-bit generators for the bit blinding factors
    pub H: &'a [RistrettoPoint],
}

impl Generators {
    /// Creates a set of generators for an `n`-bit range proof and `m` values (parties).
    pub fn new(n: usize, m: usize) -> Self {
        let mut gen = GeneratorsChain::new();
        let B = gen.next().unwrap();
        let B_b = gen.next().unwrap();

        // remaining points are: G0, H0, ..., G_(n*m-1), H_(n*m-1)
        let (G, H): (Vec<_>, Vec<_>) = gen.take(2 * n * m).enumerate().partition(|&(i, _)| i % 2 == 0);
        let G: Vec<_> = G.iter().map(|&(_, p)| p).collect();
        let H: Vec<_> = H.iter().map(|&(_, p)| p).collect();

        Generators { n, m, B, B_b, G, H }
    }

    /// Returns a view on the entirety of the generators.
    pub fn all(&self) -> GeneratorsView {
        GeneratorsView {
            B: &self.B,
            B_b: &self.B_b,
            G: &self.G[..],
            H: &self.H[..]
        }
    }

    /// Returns j-th share of generators,
    /// with an appropriate slice of vectors G and H.
    pub fn share(&self, j: usize) -> GeneratorsView {
        let range = j*self.n..(j+1)*self.n;
        GeneratorsView {
            B: &self.B,
            B_b: &self.B_b,
            G: &self.G[range.clone()],
            H: &self.H[range]
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
            [gens.all().G[n..][..n].to_vec(), gens.all().H[n..][..n].to_vec()],
            [gens.share(1).G[..].to_vec(), gens.share(1).H[..].to_vec()]
        );
        assert_eq!(
            [gens.all().G[2*n..][..n].to_vec(), gens.all().H[2*n..][..n].to_vec()],
            [gens.share(2).G[..].to_vec(), gens.share(2).H[..].to_vec()]
        );
    }

    #[test]
    fn mutable_api() {
        let mut gens = GeneratorsChain::new();
        let G = gens.next().unwrap();
        let H = gens.next().unwrap();
        let J = gens.next().unwrap();

        let GHJ: Vec<_> = GeneratorsChain::new().take(3).collect();
        let HJ: Vec<_> = GeneratorsChain::at(&H).take(2).collect();
        let J_vec: Vec<_> = GeneratorsChain::at(&J).take(1).collect();

        assert_eq!(vec![G, H, J], GHJ);
        assert_eq!(vec![H, J], HJ);
        assert_eq!(vec![J], J_vec);
    }

    #[test]
    fn iterator_api() {
        let mut gens = GeneratorsChain::new();
        let G = gens.next().unwrap();
        let H = gens.next().unwrap();
        let J = gens.next().unwrap();

        let GHJ: Vec<_> = GeneratorsChain::new().take(3).collect();
        let HJ: Vec<_> = GeneratorsChain::at(&H).take(2).collect();
        let J_vec: Vec<_> = GeneratorsChain::at(&J).take(1).collect();

        assert_eq!(vec![G, H, J], GHJ);
        assert_eq!(vec![H, J], HJ);
        assert_eq!(vec![J], J_vec);
    }
}
