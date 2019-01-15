#![doc(include = "../docs/r1cs-docs-example.md")]

#[doc(include = "../docs/cs-proof.md")]
mod notes {}

mod constraint_system;
mod linear_combination;
mod proof;
mod prover;
mod verifier;

pub use self::constraint_system::{ConstraintSystem, RandomizedConstraintSystem};
pub use self::linear_combination::{LinearCombination, Variable};
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::Verifier;

pub use errors::R1CSError;
