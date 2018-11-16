extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;

// Shuffle gadget (documented in markdown file)

/// A proof-of-shuffle.
struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: &[Variable], y: &[Variable]) {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");

        assert_eq!(x.len(), y.len());

        let k = x.len();
        if k == 1 {
            cs.constrain([(x[0], -one), (y[0], one)].iter().collect());
            return;
        }

        // Make last x multiplier for i = k-1 and k-2
        let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);

        // Make multipliers for x from i == [0, k-3]
        let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
            let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
            o
        });

        // Make last y multiplier for i = k-1 and k-2
        let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);

        // Make multipliers for y from i == [0, k-3]
        let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
            let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
            o
        });

        // Constrain last x mul output and last y mul output to be equal
        cs.constrain(
            [(first_muly_out, -one), (first_mulx_out, one)]
                .iter()
                .collect(),
        );
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
    ) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
        let k = input.len();

        // Prover makes a `ConstraintSystem` instance representing a shuffle gadget
        // Make v vector
        let mut v = Vec::with_capacity(2 * k);
        v.extend_from_slice(input);
        v.extend_from_slice(output);

        // Make v_blinding vector using RNG from transcript
        let mut rng = {
            let mut builder = transcript.build_rng();
            // commit the secret values
            for &v_i in &v {
                builder = builder.commit_witness_bytes(b"v_i", v_i.as_bytes());
            }
            use rand::thread_rng;
            builder.finalize(&mut thread_rng())
        };
        let v_blinding: Vec<Scalar> = (0..2 * k).map(|_| Scalar::random(&mut rng)).collect();
        let (mut prover_cs, variables, commitments) =
            ProverCS::new(&bp_gens, &pc_gens, transcript, v, v_blinding.clone());

        // Prover allocates variables and adds constraints to the constraint system
        let (input_vars, output_vars) = variables.split_at(k);
        KShuffleGadget::fill_cs(&mut prover_cs, input_vars, output_vars);

        // Prover generates proof
        let proof = prover_cs.prove()?;
        Ok((proof, commitments))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        proof: &R1CSProof,
        commitments: &Vec<CompressedRistretto>,
    ) -> Result<(), R1CSError> {
        let k = commitments.len() / 2;

        // Verifier makes a `ConstraintSystem` instance representing a shuffle gadget
        let (mut verifier_cs, variables) =
            VerifierCS::new(&bp_gens, &pc_gens, transcript, commitments.to_vec());

        // Verifier allocates variables and adds constraints to the constraint system
        let (input_vars, output_vars) = variables.split_at(k);
        KShuffleGadget::fill_cs(&mut verifier_cs, input_vars, output_vars);

        // Verifier verifies proof
        verifier_cs.verify(&proof)
    }
}

fn kshuffle_helper(k: usize) {
    use rand::Rng;

    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let mut transcript = Transcript::new(b"ShuffleTest");
    transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

    let (proof, commitments) = {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k)
            .map(|_| Scalar::from(rng.gen_range(min, max)))
            .collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        let mut prover_transcript = transcript.clone();
        KShuffleGadget::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output).unwrap()
    };

    {
        let mut verifier_transcript = transcript.clone();
        KShuffleGadget::verify(
            &pc_gens,
            &bp_gens,
            &mut verifier_transcript,
            &proof,
            &commitments,
        )
        .unwrap();
    }
}

#[test]
fn shuffle_gadget_test_1() {
    kshuffle_helper(1);
}

#[test]
fn shuffle_gadget_test_2() {
    kshuffle_helper(2);
}

#[test]
fn shuffle_gadget_test_3() {
    kshuffle_helper(3);
}

#[test]
fn shuffle_gadget_test_4() {
    kshuffle_helper(4);
}

#[test]
fn shuffle_gadget_test_5() {
    kshuffle_helper(5);
}

#[test]
fn shuffle_gadget_test_6() {
    kshuffle_helper(6);
}

#[test]
fn shuffle_gadget_test_7() {
    kshuffle_helper(7);
}

#[test]
fn shuffle_gadget_test_24() {
    kshuffle_helper(24);
}

#[test]
fn shuffle_gadget_test_42() {
    kshuffle_helper(42);
}

/// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
fn example_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a1: LinearCombination,
    a2: LinearCombination,
    b1: LinearCombination,
    b2: LinearCombination,
    c1: LinearCombination,
    c2: LinearCombination,
) {
    let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
    cs.constrain(c1 + c2 - c_var);
}

fn example_gadget_roundtrip_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    fn blinding_helper(len: usize) -> Vec<Scalar> {
        (0..len)
            .map(|_| Scalar::random(&mut thread_rng()))
            .collect()
    }

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
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            Scalar::from(c2).into(),
        );

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
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

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
