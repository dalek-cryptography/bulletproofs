#![cfg_attr(feature = "docs", doc = include_str!("../../docs/r1cs-docs-example.md"))]

#[cfg_attr(feature = "docs", doc = include_str!("../../docs/cs-proof.md"))]
mod notes {}

mod constraint_system;
mod linear_combination;
mod metrics;
mod proof;
mod prover;
mod verifier;

pub use self::{
    constraint_system::{ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem},
    linear_combination::{LinearCombination, Variable},
    metrics::Metrics,
    proof::R1CSProof,
    prover::Prover,
    verifier::Verifier,
};
pub use crate::errors::R1CSError;
