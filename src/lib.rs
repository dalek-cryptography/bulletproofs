#![cfg_attr(not(feature = "std"), no_std)]
#![feature(nll)]
#![feature(external_doc)]
#![feature(try_trait)]
#![deny(missing_docs)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]
#![doc(html_root_url = "https://docs.rs/bulletproofs/2.0.0")]

extern crate alloc;

#[macro_use]
extern crate serde_derive;

mod util;

#[doc(include = "../docs/notes-intro.md")]
mod notes {
    #[doc(include = "../docs/notes-ipp.md")]
    mod inner_product_proof {}
    #[doc(include = "../docs/notes-rp.md")]
    mod range_proof {}
    #[doc(include = "../docs/notes-r1cs.md")]
    mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
mod linear_proof;
mod range_proof;
mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::linear_proof::LinearProof;
pub use crate::range_proof::RangeProof;

#[doc(include = "../docs/aggregation-api.md")]
pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

#[cfg(feature = "yoloproofs")]
#[cfg(feature = "std")]
pub mod r1cs;
