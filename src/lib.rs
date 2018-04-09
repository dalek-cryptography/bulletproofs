#![cfg_attr(feature = "bench", feature(test))]
#![feature(nll)]
#![feature(test)]
#![feature(external_doc)]
#![doc(include = "../README.md")]

extern crate byteorder;
extern crate curve25519_dalek;
extern crate rand;
extern crate sha2;
extern crate tiny_keccak;

#[cfg(test)]
extern crate test;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}

mod proof_transcript;
mod generators;
mod range_proof;
mod inner_product_proof;

mod scalar;

pub use proof_transcript::ProofTranscript;
pub use range_proof::RangeProof;
pub use generators::{Generators, GeneratorsView};
