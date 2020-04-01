#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "docs", feature(external_doc))]
#![cfg_attr(feature = "docs", deny(missing_docs))]
#![cfg_attr(feature = "docs", doc(include = "../README.md"))]
#![cfg_attr(
    feature = "docs",
    doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")
)]
#![cfg_attr(
    feature = "docs",
    doc(html_root_url = "https://docs.rs/bulletproofs/2.0.0")
)]

extern crate alloc;

#[macro_use]
extern crate serde_derive;

mod util;

#[cfg_attr(feature = "docs", doc(include = "../docs/notes-intro.md"))]
mod notes {
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-ipp.md"))]
    mod inner_product_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-rp.md"))]
    mod range_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-r1cs.md"))]
    mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
mod range_proof;
mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::range_proof::RangeProof;

#[cfg_attr(feature = "docs", doc(include = "../docs/aggregation-api.md"))]
pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

#[cfg(feature = "yoloproofs")]
#[cfg(feature = "std")]
pub mod r1cs;
