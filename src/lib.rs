#![cfg_attr(feature = "bench", feature(test))]
#![feature(nll)]
#![feature(test)]

extern crate curve25519_dalek;
extern crate sha2;
extern crate rand;
extern crate tiny_keccak;
extern crate test;

mod random_oracle;
mod range_proof;
mod inner_product_proof;

pub use range_proof::*;
