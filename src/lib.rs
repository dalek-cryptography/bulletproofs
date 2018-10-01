#![feature(nll)]
#![feature(external_doc)]
#![feature(try_trait)]
#![deny(missing_docs)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

extern crate byteorder;
extern crate core;
extern crate digest;
extern crate rand;
extern crate sha3;

extern crate curve25519_dalek;
extern crate merlin;
extern crate subtle;

#[macro_use]
extern crate serde_derive;
extern crate serde;

#[macro_use]
extern crate failure;

#[cfg(test)]
extern crate bincode;

mod util;

#[doc(include = "../docs/notes.md")]
mod notes {}
mod circuit_proof;
mod errors;
mod generators;
mod inner_product_proof;
mod range_proof;
mod transcript;

pub use errors::ProofError;
pub use generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use range_proof::RangeProof;

#[doc(include = "../docs/aggregation-api.md")]
pub mod rangeproof_mpc {
    pub use errors::MPCError;
    pub use range_proof::dealer;
    pub use range_proof::messages;
    pub use range_proof::party;
}

/// The rank-1 constraint system API for programmatically defining constraint systems.
///
/// XXX explain how the parts fit together here
///
pub mod r1cs {
    pub use circuit_proof::assignment::Assignment;
    pub use circuit_proof::prover::ProverCS;
    pub use circuit_proof::verifier::VerifierCS;
    pub use circuit_proof::ConstraintSystem;
    pub use circuit_proof::LinearCombination;
    pub use circuit_proof::R1CSProof;
    pub use circuit_proof::Variable;
    pub use errors::R1CSError;
}
