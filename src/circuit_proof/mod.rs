#![doc(include = "../docs/circuit-proof-math.md")]

pub mod assignment;
pub mod prover;
pub mod verifier;

use std::iter::FromIterator;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use self::assignment::Assignment;
use errors::R1CSError;
use inner_product_proof::InnerProductProof;

/// A proof of some statement specified by a [`ConstraintSystem`].
///
/// Statements are specified by writing gadget functions which add
/// constraints to a `ConstraintSystem` implementation.  To construct
/// an `R1CSProof`, a prover constructs a
/// [`ProverCS`](::r1cs::ProverCS), then passes it to gadget functions
/// to build the constraint system, then consumes the constraint
/// system using [`ProverCS::prove`](::r1cs::ProverCS::prove) to
/// produce an `R1CSProof`.  To verify an `R1CSProof`, a verifier
/// constructs a [`VerifierCS`](::r1cs::VerifierCS), then passes it to
/// the same gadget functions to (re)build the constraint system, then
/// consumes the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug)]
pub enum Variable {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug)]
pub struct LinearCombination {
    terms: Vec<(Variable, Scalar)>,
}

impl Default for LinearCombination {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl FromIterator<(Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a> FromIterator<&'a (Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

/// The interface for a constraint system, abstracting over the prover
/// and verifier's roles.
///
/// Statements to be proved by an [`R1CSProof`] are specified by
/// programmatically constructing constraints.  These constraints need
/// to be identical between the prover and verifier, since the prover
/// and verifier need to construct the same statement.
///
/// To prevent code duplication or mismatches between the prover and
/// verifier, gadgets for the constraint system should be written
/// using the `ConstraintSystem` trait, so that the prover and
/// verifier share the logic for specifying constraints.
pub trait ConstraintSystem {
    /// Allocate variables for left, right, and output wires of multiplication,
    /// and assign them the Assignments that are passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_multiplier(
        &mut self,
        left: Assignment,
        right: Assignment,
        out: Assignment,
    ) -> Result<(Variable, Variable, Variable), R1CSError>;

    /// Allocate two uncommitted variables, and assign them the Assignments passed in.
    /// Prover will pass in `Value(Scalar)`s, and Verifier will pass in `Missing`s.
    fn assign_uncommitted(
        &mut self,
        val_1: Assignment,
        val_2: Assignment,
    ) -> Result<(Variable, Variable), R1CSError>;

    /// Enforce that the given `LinearCombination` is zero.
    fn add_constraint(&mut self, lc: LinearCombination);

    /// Obtain a challenge scalar bound to the assignments of all of
    /// the externally committed wires.
    ///
    /// This allows the prover to select a challenge circuit from a
    /// family of circuits parameterized by challenge scalars.
    ///
    /// # Warning
    ///
    /// The challenge scalars are bound only to the externally
    /// committed wires (high-level witness variables), and not to the
    /// assignments to all wires (low-level witness variables).  In
    /// the same way that it is the user's responsibility to ensure
    /// that the constraints are sound, it is **also** the user's
    /// responsibility to ensure that each challenge circuit is sound.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}

#[cfg(test)]
mod tests {
    use super::assignment::Assignment;
    use super::prover::ProverCS;
    use super::verifier::VerifierCS;
    use super::*;

    use errors::R1CSError;
    use generators::{BulletproofGens, PedersenGens};

    use curve25519_dalek::scalar::Scalar;
    use merlin::Transcript;

    use rand::thread_rng;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2),
    /// where c2 is a constant.
    #[allow(non_snake_case)]
    fn example_gadget<CS: ConstraintSystem>(
        cs: &mut CS,
        a1: (Variable, Assignment),
        a2: (Variable, Assignment),
        b1: (Variable, Assignment),
        b2: (Variable, Assignment),
        c1: (Variable, Assignment),
        c2: Scalar,
    ) -> Result<(), R1CSError> {
        // Make low-level variables (aL = v_a1 + v_a2, aR = v_b1 + v_b2, aO = v_c1 + v_c2)
        let (aL, aR, aO) =
            cs.assign_multiplier(a1.1 + a2.1, b1.1 + b2.1, c1.1 + Assignment::from(c2))?;

        // Tie high-level and low-level variables together
        let one = Scalar::one();
        cs.add_constraint([(aL, -one), (a1.0, one), (a2.0, one)].iter().collect());
        cs.add_constraint([(aR, -one), (b1.0, one), (b2.0, one)].iter().collect());
        cs.add_constraint(
            [(aO, -one), (c1.0, one), (Variable::One(), c2)]
                .iter()
                .collect(),
        );

        Ok(())
    }

    fn blinding_helper(len: usize) -> Vec<Scalar> {
        (0..len)
            .map(|_| Scalar::random(&mut thread_rng()))
            .collect()
    }

    fn example_gadget_roundtrip_helper(
        a1: u64,
        a2: u64,
        b1: u64,
        b2: u64,
        c1: u64,
        c2: u64,
    ) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // Prover's scope
        let (proof, commitments) = {
            // 0. Construct transcript
            let mut transcript = Transcript::new(b"R1CSExampleGadget");

            // 1. Construct HL witness
            let v: Vec<_> = [a1, a2, b1, b2, c1]
                .iter()
                .map(|x| Scalar::from(*x))
                .collect();
            let v_blinding = blinding_helper(v.len());

            // 2. Construct CS
            let (mut cs, vars, commitments) =
                ProverCS::new(&bp_gens, &pc_gens, &mut transcript, v.clone(), v_blinding);

            // 3. Add gadgets
            example_gadget(
                &mut cs,
                (vars[0], v[0].into()),
                (vars[1], v[1].into()),
                (vars[2], v[2].into()),
                (vars[3], v[3].into()),
                (vars[4], v[4].into()),
                c2.into(),
            )?;

            // 4. Prove.
            let proof = cs.prove()?;

            (proof, commitments)
        };

        // Verifier logic

        // 0. Construct transcript
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Construct CS using commitments to HL witness
        let (mut cs, vars) = VerifierCS::new(&bp_gens, &pc_gens, &mut transcript, commitments);

        // 2. Add gadgets
        example_gadget(
            &mut cs,
            (vars[0], Assignment::Missing()),
            (vars[1], Assignment::Missing()),
            (vars[2], Assignment::Missing()),
            (vars[3], Assignment::Missing()),
            (vars[4], Assignment::Missing()),
            c2.into(),
        )?;

        // 3. Verify.
        cs.verify(&proof).map_err(|_| R1CSError::VerificationError)
    }

    #[test]
    fn example_gadget_test() {
        // (3 + 4) * (6 + 1) = (40 + 9)
        assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
        // (3 + 4) * (6 + 1) != (40 + 10)
        assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
    }
}
