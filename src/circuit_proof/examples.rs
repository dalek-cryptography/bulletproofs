#![allow(non_snake_case)]

use super::r1cs::{ConstraintSystem, LinearCombination, Variable};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use generators::Generators;
use proof_transcript::ProofTranscript;
use rand::{CryptoRng, Rng};

// TODO: make a trait that all circuit examples need to implement

// 2-in 2-out merge circuit
pub struct Merge {}

impl Merge {
    pub fn new() -> Self {
        Merge {}
    }

    pub fn fill_prover_cs<R: Rng + CryptoRng>(
        &self,
        gen: &Generators,
        rng: &mut R,
        transcript: &mut ProofTranscript,
        cs: &mut ConstraintSystem,
        type_0: Scalar,
        type_1: Scalar,
        val_in_0: Scalar,
        val_in_1: Scalar,
        val_out_0: Scalar,
        val_out_1: Scalar,
    ) -> (Vec<Scalar>, Vec<RistrettoPoint>) {
        let t_0 = cs.alloc_assign_variable(type_0);
        let t_1 = cs.alloc_assign_variable(type_1);
        let in_0 = cs.alloc_assign_variable(val_in_0);
        let in_1 = cs.alloc_assign_variable(val_in_1);
        let out_0 = cs.alloc_assign_variable(val_out_0);
        let out_1 = cs.alloc_assign_variable(val_out_1);

        let v_blinding: Vec<Scalar> = (0..cs.get_m()).map(|_| Scalar::random(rng)).collect();
        // todo: propogate error
        let V = cs.make_V(gen, &v_blinding).unwrap();
        for V_i in V.iter() {
            transcript.commit(V_i.compress().as_bytes());
        }
        let r = transcript.challenge_scalar();

        self.fill_cs(cs, r, t_0, t_1, in_0, in_1, out_0, out_1);

        (v_blinding, V)
    }

    pub fn fill_verifier_cs(
        &self,
        transcript: &mut ProofTranscript,
        cs: &mut ConstraintSystem,
        V: &Vec<RistrettoPoint>,
    ) {
        for V_i in V.iter() {
            transcript.commit(V_i.compress().as_bytes());
        }
        let r = transcript.challenge_scalar();

        let t_0 = cs.alloc_variable();
        let t_1 = cs.alloc_variable();
        let in_0 = cs.alloc_variable();
        let in_1 = cs.alloc_variable();
        let out_0 = cs.alloc_variable();
        let out_1 = cs.alloc_variable();

        self.fill_cs(cs, r, t_0, t_1, in_0, in_1, out_0, out_1);
    }

    fn fill_cs(
        &self,
        cs: &mut ConstraintSystem,
        r: Scalar,
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
                (in_1.clone(), -r),
                (out_0.clone(), Scalar::one()),
                (out_1.clone(), r),
            ],
            Scalar::zero(),
        );
        // lc_b: in_0 + in_1 + out_1 * (-1) + out_0 * (c) + t_0 * (-c*c) + t_1 * (c*c)
        let lc_b = LinearCombination::new(
            vec![
                (in_0, Scalar::one()),
                (in_1, Scalar::one()),
                (out_1, -Scalar::one()),
                (out_0, r),
                (t_0, -r * r),
                (t_1, r * r),
            ],
            Scalar::zero(),
        );
        let lc_c = LinearCombination::new(vec![], Scalar::zero());

        cs.constrain(lc_a, lc_b, lc_c);
    }
}

// 2-in 2-out shuffle circuit
pub struct Shuffle {}

impl Shuffle {
    pub fn new() -> Self {
        Shuffle {}
    }

    pub fn fill_prover_cs<R: Rng + CryptoRng>(
        &self,
        gen: &Generators,
        rng: &mut R,
        transcript: &mut ProofTranscript,
        cs: &mut ConstraintSystem,
        val_in_0: Scalar,
        val_in_1: Scalar,
        val_out_0: Scalar,
        val_out_1: Scalar,
    ) -> (Vec<Scalar>, Vec<RistrettoPoint>) {
        let v_blinding: Vec<Scalar> = (0..5).map(|_| Scalar::random(rng)).collect();

        let var_in_0 = cs.alloc_assign_variable(val_in_0);
        let var_in_1 = cs.alloc_assign_variable(val_in_1);
        let var_out_0 = cs.alloc_assign_variable(val_out_0);
        let var_out_1 = cs.alloc_assign_variable(val_out_1);

        // todo: propogate error
        let V = cs.make_V(gen, &v_blinding[..4].to_vec()).unwrap();
        for V_i in V.iter() {
            transcript.commit(V_i.compress().as_bytes());
        }
        let r = transcript.challenge_scalar();
        let var_mul = cs.alloc_assign_variable((val_in_0 - r) * (val_in_1 - r));

        self.fill_cs(cs, r, var_in_0, var_in_1, var_out_0, var_out_1, var_mul);
        let V = cs.make_V(gen, &v_blinding).unwrap();
        (v_blinding, V)
    }

    pub fn fill_verifier_cs(
        &self,
        transcript: &mut ProofTranscript,
        cs: &mut ConstraintSystem,
        V: &Vec<RistrettoPoint>,
    ) {
        for V_i in V[..4].iter() {
            transcript.commit(V_i.compress().as_bytes());
        }
        let r = transcript.challenge_scalar();

        let var_in_0 = cs.alloc_variable();
        let var_in_1 = cs.alloc_variable();
        let var_out_0 = cs.alloc_variable();
        let var_out_1 = cs.alloc_variable();
        let var_mul = cs.alloc_variable();

        self.fill_cs(cs, r, var_in_0, var_in_1, var_out_0, var_out_1, var_mul);
    }

    fn fill_cs(
        &self,
        cs: &mut ConstraintSystem,
        r: Scalar,
        in_0: Variable,
        in_1: Variable,
        out_0: Variable,
        out_1: Variable,
        mul: Variable,
    ) {
        // lc_0: (var_in_0 - z) * (var_in_1 - z) = var_mul
        let lc_0_a = LinearCombination::new(vec![(in_0, Scalar::one())], -r);
        let lc_0_b = LinearCombination::new(vec![(in_1, Scalar::one())], -r);
        let lc_0_c = LinearCombination::new(vec![(mul.clone(), Scalar::one())], Scalar::zero());
        cs.constrain(lc_0_a, lc_0_b, lc_0_c);

        // lc_1: (var_out_0 - z) * (var_out_1 - z) = var_mul
        let lc_1_a = LinearCombination::new(vec![(out_0, Scalar::one())], -r);
        let lc_1_b = LinearCombination::new(vec![(out_1, Scalar::one())], -r);
        let lc_1_c = LinearCombination::new(vec![(mul, Scalar::one())], Scalar::zero());
        cs.constrain(lc_1_a, lc_1_b, lc_1_c);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use errors::R1CSError;
    use generators::PedersenGenerators;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        rng: &mut OsRng,
        prover_transcript: &mut ProofTranscript,
        verifier_transcript: &mut ProofTranscript,
        prover_cs: ConstraintSystem,
        v_blinding: Vec<Scalar>,
        verifier_cs: ConstraintSystem,
    ) -> Result<(), R1CSError> {
        let generators = Generators::new(PedersenGenerators::default(), prover_cs.get_n(), 1);

        let (circuit_proof, V) = prover_cs
            .prove(&generators, prover_transcript, rng, v_blinding)
            .unwrap();

        verifier_cs.verify(&circuit_proof, &V, &generators, verifier_transcript, rng)
    }

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
        let generators = Generators::new(PedersenGenerators::default(), 1, 1);
        let mut rng = OsRng::new().unwrap();
        let mut prover_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        let mut prover_cs = ConstraintSystem::new();

        let (v_blinding, V) = Merge::new().fill_prover_cs(
            &generators,
            &mut rng,
            &mut prover_transcript,
            &mut prover_cs,
            type_0,
            type_1,
            val_in_0,
            val_in_1,
            val_out_0,
            val_out_1,
        );

        let mut verifier_cs = ConstraintSystem::new();
        let mut verifier_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        Merge::new().fill_verifier_cs(&mut verifier_transcript, &mut verifier_cs, &V);

        create_and_verify_helper(
            &mut rng,
            &mut prover_transcript,
            &mut verifier_transcript,
            prover_cs,
            v_blinding,
            verifier_cs,
        )
    }

    #[test]
    fn shuffle_circuit() {
        let three = Scalar::from(3u64);
        let seven = Scalar::from(7u64);
        assert!(shuffle_circuit_helper(three, seven, three, seven).is_ok());
        assert!(shuffle_circuit_helper(three, seven, seven, three).is_ok());
        assert!(shuffle_circuit_helper(three, seven, seven, seven).is_err());
        assert!(shuffle_circuit_helper(three, Scalar::one(), seven, three).is_err());
    }

    fn shuffle_circuit_helper(
        in_0: Scalar,
        in_1: Scalar,
        out_0: Scalar,
        out_1: Scalar,
    ) -> Result<(), R1CSError> {
        // todo: how to get the generator length from prover_cs / without hardcoding?
        let generators = Generators::new(PedersenGenerators::default(), 1, 1);
        let mut rng = OsRng::new().unwrap();
        let mut prover_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        let mut prover_cs = ConstraintSystem::new();

        let (v_blinding, V) = Shuffle::new().fill_prover_cs(
            &generators,
            &mut rng,
            &mut prover_transcript,
            &mut prover_cs,
            in_0,
            in_1,
            out_0,
            out_1,
        );

        let mut verifier_cs = ConstraintSystem::new();
        let mut verifier_transcript = ProofTranscript::new(b"R1CSExamplesTest");
        Shuffle::new().fill_verifier_cs(&mut verifier_transcript, &mut verifier_cs, &V);

        create_and_verify_helper(
            &mut rng,
            &mut prover_transcript,
            &mut verifier_transcript,
            prover_cs,
            v_blinding,
            verifier_cs,
        )
    }
}
