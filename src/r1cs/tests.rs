use rand::thread_rng;

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};

use super::*;

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
    cs.add_constraint(a1 + a2, b1 + b2, c1 + c2);
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

// Shuffle gadget tests

/* 
K-SHUFFLE GADGET SPECIFICATION:

Represents a permutation of a list of `k` scalars `{x_i}` into a list of `k` scalars `{y_i}`.

Algebraically it can be expressed as a statement that for a free variable `z`, 
the roots of the two polynomials in terms of `z` are the same up to a permutation:

    ∏(x_i - z) == ∏(y_i - z)

Prover can commit to blinded scalars `x_i` and `y_i` then receive a random challenge `z`, 
and build a proof that the above relation holds.

K-shuffle requires `2*(K-1)` multipliers.

For K > 1:

        (x_0 - z)---⊗------⊗---(y_0 - z)        // mulx[0], muly[0]
                    |      |
        (x_1 - z)---⊗      ⊗---(y_1 - z)        // mulx[1], muly[1]
                    |      |
                   ...    ...
                    |      |
    (x_{k-2} - z)---⊗      ⊗---(y_{k-2} - z)    // mulx[k-2], muly[k-2]
                   /        \
    (x_{k-1} - z)_/          \_(y_{k-1} - z)

    // Connect left and right sides of the shuffle statement
    mulx_out[0] = muly_out[0]

    // For i == [0, k-3]:
    mulx_left[i]  = x_i - z
    mulx_right[i] = mulx_out[i+1]
    muly_left[i]  = y_i - z
    muly_right[i] = muly_out[i+1]

    // last multipliers connect two last variables (on each side)
    mulx_left[k-2]  = x_{k-2} - z
    mulx_right[k-2] = x_{k-1} - z
    muly_left[k-2]  = y_{k-2} - z
    muly_right[k-2] = y_{k-1} - z

For K = 1:

    (x_0 - z)--------------(y_0 - z)

    // Connect x to y directly, omitting the challenge entirely as it cancels out
    x_0 = y_0
*/

// Make a gadget that adds constraints to a ConstraintSystem, such that the
// y variables are constrained to be a valid shuffle of the x variables.
struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");

        assert_eq!(x.len(), y.len());

        let k = x.len();
        if k == 1 {
            cs.add_auxiliary_constraint([(x[0], -one), (y[0], one)].iter().collect());
            return;
        }

        // Make last x multiplier for i = k-1 and k-2
        let (_, _, last_mulx_out) = cs.add_intermediate_constraint(x[k - 1] - z, x[k - 2] - z);

        // Make multipliers for x from i == [0, k-3]
        let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
            let (_, _, o) = cs.add_intermediate_constraint(prev_out.into(), x[i] - z);
            o
        });

        // Make last y multiplier for i = k-1 and k-2
        let (_, _, last_muly_out) = cs.add_intermediate_constraint(y[k - 1] - z, y[k - 2] - z);

        // Make multipliers for y from i == [0, k-3]
        let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
            let (_, _, o) = cs.add_intermediate_constraint(prev_out.into(), y[i] - z);
            o
        });

        // Check equality between last x mul output and last y mul output
        cs.add_auxiliary_constraint(
            [(first_muly_out, -one), (first_mulx_out, one)]
                .iter()
                .collect(),
        );
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &Vec<u64>,
        output: &Vec<u64>,
    ) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
        let k = input.len();

        // Prover makes a `ConstraintSystem` instance representing a shuffle gadget
        // Make v vector
        let mut v = Vec::with_capacity(2 * k);
        for i in 0..k {
            v.push(Scalar::from(input[i]));
        }
        for i in 0..k {
            v.push(Scalar::from(output[i]));
        }

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
        KShuffleGadget::fill_cs(
            &mut prover_cs,
            variables[0..k].to_vec(),
            variables[k..2 * k].to_vec(),
        );

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
        KShuffleGadget::fill_cs(
            &mut verifier_cs,
            variables[0..k].to_vec(),
            variables[k..2 * k].to_vec(),
        );

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
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
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
