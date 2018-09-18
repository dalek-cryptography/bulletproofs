#![cfg_attr(feature = "bench", feature(test))]
#![feature(nll)]
#![feature(test)]
#![feature(external_doc)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
#[macro_use]
extern crate failure;
extern crate merlin;
extern crate rand;
extern crate sha3;
extern crate subtle;
extern crate tiny_keccak;
#[macro_use]
extern crate serde_derive;
extern crate serde;

#[cfg(test)]
extern crate bincode;
#[cfg(test)]
extern crate test;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}
mod errors;
mod generators;
mod inner_product_proof;
mod range_proof;
mod transcript;

pub use merlin::Transcript;

pub use errors::ProofError;
pub use generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use range_proof::RangeProof;

#[doc(include = "../docs/aggregation-api.md")]
pub mod aggregation {
    pub use errors::MPCError;
    pub use range_proof::dealer;
    pub use range_proof::messages;
    pub use range_proof::party;
}
