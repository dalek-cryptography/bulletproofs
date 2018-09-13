//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use digest::{ExtendableOutput, Input, XofReader};
use sha3::{Sha3XofReader, Shake256};

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
    /// Bases for Pedersen commitments
    pub pedersen_gens: PedersenGenerators,
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Per-bit generators for the bit values
    G_vec: Vec<Vec<RistrettoPoint>>,
    /// Per-bit generators for the bit blinding factors
    H_vec: Vec<Vec<RistrettoPoint>>,
}

impl Generators {
    /// Create a new `Generators` object.
    ///
    /// # Inputs
    ///
    /// * `pedersen_gens` is a pair of generators used for Pedersen
    ///    commitments.
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.  For rangeproofs, it is sufficient to pass
    ///    `64`, the maximum bitsize of the rangeproofs.  For circuit
    ///    proofs, the capacity must be greater than the number of
    ///    multipliers, rounded up to the next power of two.
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn new(
        pedersen_gens: PedersenGenerators,
        gens_capacity: usize,
        party_capacity: usize,
    ) -> Self {
        use byteorder::{ByteOrder, LittleEndian};

        let G_vec = (0..party_capacity)
            .map(|i| {
                let party_index = i as u32;
                let mut label = [b'G', 0, 0, 0, 0];
                LittleEndian::write_u32(&mut label[1..5], party_index);

                GeneratorsChain::new(&label)
                    .take(gens_capacity)
                    .collect::<Vec<_>>()
            })
            .collect();

        let H_vec = (0..party_capacity)
            .map(|i| {
                let party_index = i as u32;
                let mut label = [b'H', 0, 0, 0, 0];
                LittleEndian::write_u32(&mut label[1..5], party_index);

                GeneratorsChain::new(&label)
                    .take(gens_capacity)
                    .collect::<Vec<_>>()
            })
            .collect();

        Generators {
            pedersen_gens,
            gens_capacity,
            party_capacity,
            G_vec,
            H_vec,
        }
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> GeneratorsView {
        GeneratorsView {
            pedersen_gens: &self.pedersen_gens,
            gens: &self,
            share: j,
        }
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    pub(crate) fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    pub(crate) fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a> {
    array: &'a Vec<Vec<RistrettoPoint>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a> Iterator for AggregatedGensIter<'a> {
    type Item = &'a RistrettoPoint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }

        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx][cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n * self.m;
        (size, Some(size))
    }
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
    /// The parent object that this is a view into
    gens: &'a Generators,
    /// Which share we are
    share: usize,
}

impl<'a> GeneratorsView<'a> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub(crate) fn G(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.H_vec[self.share].iter().take(n)
    }
}

#[cfg(test)]
mod tests {
    extern crate hex;
    use super::*;

    // XXX write tests

    #[test]
    fn aggregated_gens_iter_matches_flat_map() {
        let gens = Generators::new(PedersenGenerators::default(), 64, 8);

        let helper = |n: usize, m: usize| {
            let agg_G: Vec<RistrettoPoint> = gens.G(n, m).cloned().collect();
            let flat_G: Vec<RistrettoPoint> = gens
                .G_vec
                .iter()
                .take(m)
                .flat_map(move |G_j| G_j.iter().take(n))
                .cloned()
                .collect();

            let agg_H: Vec<RistrettoPoint> = gens.H(n, m).cloned().collect();
            let flat_H: Vec<RistrettoPoint> = gens
                .H_vec
                .iter()
                .take(m)
                .flat_map(move |H_j| H_j.iter().take(n))
                .cloned()
                .collect();

            assert_eq!(agg_G, flat_G);
            assert_eq!(agg_H, flat_H);
        };

        helper(64, 8);
        helper(64, 4);
        helper(64, 2);
        helper(64, 1);
        helper(32, 8);
        helper(32, 4);
        helper(32, 2);
        helper(32, 1);
        helper(16, 8);
        helper(16, 4);
        helper(16, 2);
        helper(16, 1);
    }
}
