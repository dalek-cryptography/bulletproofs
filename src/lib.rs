#![cfg_attr(feature = "bench", feature(test))]
#![feature(nll)]
#![feature(test)]
#![feature(external_doc)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

extern crate core;
extern crate byteorder;
extern crate curve25519_dalek;
extern crate rand;
extern crate sha2;
extern crate subtle;
extern crate tiny_keccak;

#[macro_use]
extern crate serde_derive;
extern crate serde;

#[cfg(test)]
extern crate test;

#[cfg(test)]
extern crate bincode;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}
mod generators;
mod inner_product_proof;
mod proof_transcript;
mod range_proof;

pub use generators::{Generators, GeneratorsView, PedersenGenerators};
pub use proof_transcript::ProofTranscript;
pub use range_proof::RangeProof;

#[doc(include = "../docs/aggregation-api.md")]
pub mod aggregation {
    pub use range_proof::dealer;
    pub use range_proof::messages;
    pub use range_proof::party;
}
