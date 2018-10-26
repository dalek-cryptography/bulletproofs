#![doc(include = "../docs/cs-proof.md")]

pub mod assignment;
pub mod linear_combination;
pub mod opaque_scalar;
pub mod cs;
pub mod prover;
pub mod verifier;
pub mod proof;

pub use self::linear_combination::{LinearCombination};
pub use self::assignment::{Assignment,AssignmentValue};
pub use self::opaque_scalar::OpaqueScalar;
pub use self::cs::*;
pub use self::proof::*;

// #[cfg(test)]
// mod tests;
