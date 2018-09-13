#![doc(include = "../docs/circuit-proof-math.md")]

pub mod assignment;
pub mod prover;
pub mod r1cs;
pub mod verifier;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use inner_product_proof::InnerProductProof;

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

#[cfg(test)]
mod tests {
    use super::assignment::Assignment;
    use super::prover::ProverCS;
    use super::r1cs::{ConstraintSystem, LinearCombination, Variable};
    use super::verifier::VerifierCS;

    use errors::R1CSError;
    use generators::{Generators, PedersenGenerators};

    use curve25519_dalek::scalar::Scalar;
    use merlin::Transcript;

    use rand::thread_rng;

    #[allow(non_snake_case)]
    fn example_gadget<CS: ConstraintSystem>(
        cs: &mut CS,
        a1: (Variable, Assignment),
        a2: (Variable, Assignment),
        b1: (Variable, Assignment),
        b2: (Variable, Assignment),
        c1: (Variable, Assignment),
        c2: (Variable, Assignment),
    ) -> Result<(), R1CSError> {
        let one = Scalar::one();
        let zer = Scalar::zero();

        // Make low-level variables (aL = v_a1 + v_a2, aR = v_b1 + v_b2, aO = v_c1 + v_c2)
        let (aL, aR, aO) = cs.assign_multiplier(a1.1 + a2.1, b1.1 + b2.1, c1.1 + c2.1)?;

        // Tie high-level and low-level variables together
        cs.add_constraint(LinearCombination::new(
            vec![(aL, -one), (a1.0, one), (a2.0, one)],
            zer,
        ));
        cs.add_constraint(LinearCombination::new(
            vec![(aR, -one), (b1.0, one), (b2.0, one)],
            zer,
        ));
        cs.add_constraint(LinearCombination::new(
            vec![(aO, -one), (c1.0, one), (c2.0, one)],
            zer,
        ));

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
        let gens = Generators::new(PedersenGenerators::default(), 1, 1);

        // Prover's scope
        let (proof, commitments) = {
            // 0. Construct transcript
            let mut transcript = Transcript::new(b"R1CSExampleGadget");

            // 1. Construct HL witness
            let v: Vec<_> = [a1, a2, b1, b2, c1, c2]
                .iter()
                .map(|x| Scalar::from(*x))
                .collect();
            let v_blinding = blinding_helper(v.len());

            // 2. Construct CS
            let (mut cs, vars, commitments) = ProverCS::new(
                &mut transcript,
                v.clone(),
                v_blinding,
                PedersenGenerators::default(),
            );

            // 3. Add gadgets
            example_gadget(
                &mut cs,
                (vars[0], v[0].into()),
                (vars[1], v[1].into()),
                (vars[2], v[2].into()),
                (vars[3], v[3].into()),
                (vars[4], v[4].into()),
                (vars[5], v[5].into()),
            )?;

            // 4. Prove.
            let proof = cs.prove(&gens)?;

            (proof, commitments)
        };

        // Verifier logic

        // 0. Construct transcript
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Construct CS using commitments to HL witness
        let (mut cs, vars) = VerifierCS::new(&mut transcript, commitments);

        // 2. Add gadgets
        example_gadget(
            &mut cs,
            (vars[0], Assignment::Missing()),
            (vars[1], Assignment::Missing()),
            (vars[2], Assignment::Missing()),
            (vars[3], Assignment::Missing()),
            (vars[4], Assignment::Missing()),
            (vars[5], Assignment::Missing()),
        )?;

        // 3. Verify.
        cs.verify(&proof, &gens, &mut thread_rng())
            .map_err(|_| R1CSError::VerificationError)
    }

    #[test]
    fn example_gadget_test() {
        // (3 + 4) * (6 + 1) = (40 + 9)
        assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
        // (3 + 4) * (6 + 1) != (40 + 10)
        assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
    }
}
