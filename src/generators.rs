//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use digest::{ExtendableOutput, Input, XofReader};
use sha3::{Sha3XofReader, Shake256};

/// The `GeneratorsChain` creates an arbitrary-long sequence of orthogonal generators.
/// The sequence can be deterministically produced starting with an arbitrary point.
struct GeneratorsChain {
    reader: Sha3XofReader,
}

impl GeneratorsChain {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut shake = Shake256::default();
        shake.process(b"GeneratorsChain");
        shake.process(label);

        GeneratorsChain {
            reader: shake.xof_result(),
        }
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
        let mut uniform_bytes = [0u8; 64];
        self.reader.read(&mut uniform_bytes);

        Some(RistrettoPoint::from_uniform_bytes(&uniform_bytes))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// The `Generators` struct contains all the generators needed for
/// aggregating `m` range proofs of `n` bits each.
#[derive(Clone)]
pub struct Generators {
    /// Number of bits in a rangeproof
    pub n: usize,
    /// Number of values or parties
    pub m: usize,
    /// Bases for Pedersen commitments
    pub pedersen_gens: PedersenGenerators,
    /// Per-bit generators for the bit values
    pub G: Vec<RistrettoPoint>,
    /// Per-bit generators for the bit blinding factors
    pub H: Vec<RistrettoPoint>,
}

/// The `GeneratorsView` is produced by `Generators::share()`.
///
/// The `Generators` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `GeneratorsView`
/// represents the generators for one of the `m` parties' shares.
#[derive(Copy, Clone)]
pub struct GeneratorsView<'a> {
    /// Bases for Pedersen commitments
    pub pedersen_gens: &'a PedersenGenerators,
    /// Per-bit generators for the bit values
    pub G: &'a [RistrettoPoint],
    /// Per-bit generators for the bit blinding factors
    pub H: &'a [RistrettoPoint],
}

/// Represents a pair of base points for Pedersen commitments.
#[derive(Copy, Clone)]
pub struct PedersenGenerators {
    /// Base for the committed value
    pub B: RistrettoPoint,

    /// Base for the blinding factor
    pub B_blinding: RistrettoPoint,
}

impl PedersenGenerators {
    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: Scalar, blinding: Scalar) -> RistrettoPoint {
        RistrettoPoint::multiscalar_mul(&[value, blinding], &[self.B, self.B_blinding])
    }
}

impl Default for PedersenGenerators {
    fn default() -> Self {
        PedersenGenerators {
            B: GeneratorsChain::new(b"Bulletproofs.Generators.B")
                .next()
                .unwrap(),
            B_blinding: GeneratorsChain::new(b"Bulletproofs.Generators.B_blinding")
                .next()
                .unwrap(),
        }
    }
}

impl Generators {
    /// Creates generators for `m` range proofs of `n` bits each.
    pub fn new(pedersen_gens: PedersenGenerators, n: usize, m: usize) -> Self {
        let G = GeneratorsChain::new(pedersen_gens.B.compress().as_bytes())
            .take(n * m)
            .collect();
        let H = GeneratorsChain::new(pedersen_gens.B_blinding.compress().as_bytes())
            .take(n * m)
            .collect();

        Generators {
            pedersen_gens,
            n,
            m,
            G,
            H,
        }
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> GeneratorsView {
        let lower = self.n * j;
        let upper = self.n * (j + 1);
        GeneratorsView {
            pedersen_gens: &self.pedersen_gens,
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
        let gens = Generators::new(PedersenGenerators::default(), n, m);

        // The concatenation of shares must be the full generator set
        assert_eq!(
            [gens.G[..n].to_vec(), gens.H[..n].to_vec()],
            [gens.share(0).G[..].to_vec(), gens.share(0).H[..].to_vec()]
        );
        assert_eq!(
            [gens.G[n..][..n].to_vec(), gens.H[n..][..n].to_vec()],
            [gens.share(1).G[..].to_vec(), gens.share(1).H[..].to_vec()]
        );
        assert_eq!(
            [gens.G[2 * n..][..n].to_vec(), gens.H[2 * n..][..n].to_vec()],
            [gens.share(2).G[..].to_vec(), gens.share(2).H[..].to_vec()]
        );
    }
}
