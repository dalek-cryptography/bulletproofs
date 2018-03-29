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
mod notes {
}

pub mod proof_transcript;
pub mod generators;
mod range_proof;
mod inner_product_proof;

pub mod scalar;

pub use range_proof::*;
pub use generators::*;
