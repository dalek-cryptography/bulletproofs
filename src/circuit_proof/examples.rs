#![allow(non_snake_case)]

use super::r1cs::{ConstraintSystem, LinearCombination, Variable};
use curve25519_dalek::scalar::Scalar;
use errors::R1CSError;
use generators::{Generators, PedersenGenerators};
use proof_transcript::ProofTranscript;
use rand::rngs::OsRng;

// TODO: make a trait that all circuit examples need to implement

// 2-in 2-out merge circuit
pub struct Merge {}

impl Merge {
    pub fn new() -> Self {
        Merge {}
    }

    pub fn make_prover_cs(
        &self,
        type_0: Scalar,
        type_1: Scalar,
        val_in_0: Scalar,
        val_in_1: Scalar,
        val_out_0: Scalar,
        val_out_1: Scalar,
    ) -> (ConstraintSystem, Scalar) {
        // TODO: actually use a challenge variable for this - obviously unsafe
        let mut rng = OsRng::new().unwrap();
        let c = Scalar::random(&mut rng);

        let mut cs = ConstraintSystem::new();
        let t_0 = cs.alloc_assign_variable(type_0);
        let t_1 = cs.alloc_assign_variable(type_1);
        let in_0 = cs.alloc_assign_variable(val_in_0);
        let in_1 = cs.alloc_assign_variable(val_in_1);
        let out_0 = cs.alloc_assign_variable(val_out_0);
        let out_1 = cs.alloc_assign_variable(val_out_1);

        self.fill_cs(&mut cs, c, t_0, t_1, in_0, in_1, out_0, out_1);
        (cs, c)
    }

    pub fn make_verifier_cs(&self, c: Scalar) -> ConstraintSystem {
        let mut cs = ConstraintSystem::new();
        let t_0 = cs.alloc_variable();
        let t_1 = cs.alloc_variable();
        let in_0 = cs.alloc_variable();
        let in_1 = cs.alloc_variable();
        let out_0 = cs.alloc_variable();
        let out_1 = cs.alloc_variable();

        self.fill_cs(&mut cs, c, t_0, t_1, in_0, in_1, out_0, out_1);
        cs
    }

    fn fill_cs(
        &self,
        cs: &mut ConstraintSystem,
        c: Scalar,
        t_0: Variable,
        t_1: Variable,
        in_0: Variable,
        in_1: Variable,
        out_0: Variable,
        out_1: Variable,
    ) {
        // lc_a: in_0 * (-1) + in_1 * (-c) + out_0 + out_1 * (c)
        let lc_a = LinearCombination::new(
            vec![
                (in_0.clone(), -Scalar::one()),
                (in_1.clone(), -c),
                (out_0.clone(), Scalar::one()),
                (out_1.clone(), c),
            ],
            Scalar::zero(),
        );
        // lc_b: in_0 + in_1 + out_1 * (-1) + out_0 * (c) + t_0 * (-c*c) + t_1 * (c*c)
        let lc_b = LinearCombination::new(
            vec![
                (in_0, Scalar::one()),
                (in_1, Scalar::one()),
                (out_1, -Scalar::one()),
                (out_0, c),
                (t_0, -c * c),
                (t_1, c * c),
            ],
            Scalar::zero(),
        );
        let lc_c = LinearCombination::new(vec![], Scalar::zero());

        cs.constrain(lc_a, lc_b, lc_c);
    }
}

#[cfg(test)]
mod tests {
    use super::super::circuit::CircuitProof;
    use super::*;
    use rand::rngs::OsRng;

    #[test]
    fn merge_circuit() {
        let buck = Scalar::from(32u64);
        let yuan = Scalar::from(86u64);
        let a = Scalar::from(24u64);
        let b = Scalar::from(76u64);
        let a_plus_b = Scalar::from(100u64);
        let zero = Scalar::zero();

        assert!(merge_circuit_helper(buck, buck, a, a, a, a).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, a_plus_b).is_ok());
        assert!(merge_circuit_helper(buck, yuan, a, b, a, b).is_ok());
        assert!(merge_circuit_helper(buck, buck, a, b, a, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, yuan, a, b, zero, a_plus_b).is_err());
        assert!(merge_circuit_helper(buck, buck, a, b, zero, zero).is_err());
    }

    fn merge_circuit_helper(
        type_0: Scalar,
        type_1: Scalar,
        val_in_0: Scalar,
        val_in_1: Scalar,
        val_out_0: Scalar,
        val_out_1: Scalar,
    ) -> Result<(), R1CSError> {
        let (prover_cs, c) =
            Merge::new().make_prover_cs(type_0, type_1, val_in_0, val_in_1, val_out_0, val_out_1);

        let generators = Generators::new(PedersenGenerators::default(), prover_cs.get_n(), 1);
        let mut prover_transcript = ProofTranscript::new(b"CircuitProofTest");
        let mut rng = OsRng::new().unwrap();

        let (circuit_proof, V) = prover_cs
            .prove(&generators, &mut prover_transcript, &mut rng)
            .unwrap();

        let verifier_cs = Merge::new().make_verifier_cs(c);

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest");
        verifier_cs.verify(
            &circuit_proof,
            &V,
            &generators,
            &mut verify_transcript,
            &mut rng,
        )
    }
}
