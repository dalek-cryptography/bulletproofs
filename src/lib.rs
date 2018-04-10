#![cfg_attr(feature = "bench", feature(test))]
#![feature(nll)]
#![feature(test)]
#![feature(external_doc)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

extern crate byteorder;
extern crate curve25519_dalek;
extern crate rand;
extern crate sha2;
extern crate subtle;
extern crate tiny_keccak;

#[macro_use]
extern crate serde_derive;

#[cfg(test)]
extern crate test;

#[cfg(test)]
extern crate bincode;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}

mod proof_transcript;
mod generators;
mod range_proof;
mod inner_product_proof;

pub use proof_transcript::ProofTranscript;
pub use range_proof::RangeProof;
pub use generators::{Generators, GeneratorsView};
