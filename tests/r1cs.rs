#![allow(non_snake_case)]
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
struct ShuffleProof(R1CSProof);

impl ShuffleProof {
    fn gadget<CS: ConstraintSystem>(cs: &mut CS, x: &[Variable], y: &[Variable]) {
        let z = cs.challenge_scalar(b"shuffle challenge");

        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
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
        cs.constrain(first_mulx_out - first_muly_out);
    }
}

impl ShuffleProof {
    /// Attempt to construct a proof that `output` is a permutation of `input`.
    ///
    /// Returns a tuple `(proof, input_commitments || output_commitments)`.
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
    ) -> Result<
        (
            ShuffleProof,
            Vec<CompressedRistretto>,
            Vec<CompressedRistretto>,
        ),
        R1CSError,
    > {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut prover = Prover::new(&bp_gens, &pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input
            .into_iter()
            .map(|v| prover.commit(*v, Scalar::random(&mut blinding_rng)))
            .unzip();

        let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output
            .into_iter()
            .map(|v| prover.commit(*v, Scalar::random(&mut blinding_rng)))
            .unzip();

        let mut cs = prover.finalize_inputs();

        ShuffleProof::gadget(&mut cs, &input_vars, &output_vars);

        let proof = cs.prove()?;

        Ok((ShuffleProof(proof), input_commitments, output_commitments))
    }
}

impl ShuffleProof {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<CompressedRistretto>,
        output_commitments: &Vec<CompressedRistretto>,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(&bp_gens, &pc_gens, transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let mut cs = verifier.finalize_inputs();

        ShuffleProof::gadget(&mut cs, &input_vars, &output_vars);

        cs.verify(&self.0)
    }
}

fn kshuffle_helper(k: usize) {
    use rand::Rng;

    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let (proof, input_commitments, output_commitments) = {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k)
            .map(|_| Scalar::from(rng.gen_range(min, max)))
            .collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
        ShuffleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_ok());
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
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    // Prover's scope
    let (proof, commitments) = {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(&bp_gens, &pc_gens, &mut transcript);

        // 2. Commit high-level variables
        let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
            .into_iter()
            .map(|x| prover.commit(Scalar::from(*x), Scalar::random(&mut thread_rng())))
            .unzip();

        // 3. Build a CS
        let mut cs = prover.finalize_inputs();

        example_gadget(
            &mut cs,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            Scalar::from(c2).into(),
        );

        // 4. Make a proof
        let proof = cs.prove()?;

        (proof, commitments)
    };

    // Verifier logic

    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&bp_gens, &pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 3. Build a CS
    let mut cs = verifier.finalize_inputs();
    example_gadget(
        &mut cs,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Verify the proof
    cs.verify(&proof).map_err(|_| R1CSError::VerificationError)
}

#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
}
