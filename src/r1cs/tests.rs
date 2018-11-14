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

/*

// Make a gadget that adds constraints to a ConstraintSystem, such that the
// y variables are constrained to be a valid shuffle of the x variables.
struct KShuffleGadget {}

/// Represents an error during the proof creation of verification for a KShuffle gadget.
#[derive(Fail, Copy, Clone, Debug, Eq, PartialEq)]
pub enum KShuffleError {
    /// Error in the constraint system creation process
    #[fail(display = "Invalid KShuffle constraint system construction")]
    InvalidR1CSConstruction,
    /// Occurs when there are insufficient generators for the proof.
    #[fail(display = "Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength,
    /// Occurs when verification of an [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[fail(display = "R1CSProof did not verify correctly.")]
    VerificationError,
}

impl From<R1CSError> for KShuffleError {
    fn from(e: R1CSError) -> KShuffleError {
        match e {
            R1CSError::InvalidGeneratorsLength => KShuffleError::InvalidGeneratorsLength,
            R1CSError::MissingAssignment => KShuffleError::InvalidR1CSConstruction,
            R1CSError::VerificationError => KShuffleError::VerificationError,
        }
    }
}

impl KShuffleGadget {
    pub fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: Vec<(Variable, Assignment)>,
        y: Vec<(Variable, Assignment)>,
    ) -> Result<(), KShuffleError> {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");

        if x.len() != y.len() {
            return Err(KShuffleError::InvalidR1CSConstruction);
        }
        let k = x.len();
        if k == 1 {
            cs.add_constraint([(x[0].0, -one), (y[0].0, one)].iter().collect());
            return Ok(());
        }

        // Make last x multiplier for i = k-1 and k-2
        let last_mulx_out = KShuffleGadget::last_multiplier(cs, z, x[k - 1], x[k - 2]);

        // Make multipliers for x from i == [0, k-3]
        let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
            KShuffleGadget::intermediate_multiplier(cs, z, prev_out?, x[i])
        })?;

        // Make last y multiplier for i = k-1 and k-2
        let last_muly_out = KShuffleGadget::last_multiplier(cs, z, y[k - 1], y[k - 2]);

        // Make multipliers for y from i == [0, k-3]
        let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
            KShuffleGadget::intermediate_multiplier(cs, z, prev_out?, y[i])
        })?;

        // Check equality between last x mul output and last y mul output
        cs.add_constraint(
            [(first_muly_out.0, -one), (first_mulx_out.0, one)]
                .iter()
                .collect(),
        );

        Ok(())
    }

    fn last_multiplier<CS: ConstraintSystem>(
        cs: &mut CS,
        z: Scalar,
        left: (Variable, Assignment),
        right: (Variable, Assignment),
    ) -> Result<(Variable, Assignment), KShuffleError> {
        let one = Scalar::one();
        let var_one = Variable::One();

        let mul_left = left.1 - z;
        let mul_right = right.1 - z;
        let mul_out = mul_left * mul_right;

        // Make multiplier gate variables
        let (mul_left_var, mul_right_var, mul_out_var) =
            cs.assign_multiplier(mul_left, mul_right, mul_out)?;

        // Make multipliers
        cs.add_constraint(
            [(mul_left_var, -one), (var_one, -z), (left.0, one)]
                .iter()
                .collect(),
        );
        cs.add_constraint(
            [(mul_right_var, -one), (var_one, -z), (right.0, one)]
                .iter()
                .collect(),
        );

        Ok((mul_out_var, mul_out))
    }

    fn intermediate_multiplier<CS: ConstraintSystem>(
        cs: &mut CS,
        z: Scalar,
        left: (Variable, Assignment),
        right: (Variable, Assignment),
    ) -> Result<(Variable, Assignment), KShuffleError> {
        let one = Scalar::one();
        let var_one = Variable::One();

        let mul_left = left.1;
        let mul_right = right.1 - z;
        let mul_out = mul_left * mul_right;

        // Make multiplier gate variables
        let (mul_left_var, mul_right_var, mul_out_var) =
            cs.assign_multiplier(mul_left, mul_right, mul_out)?;

        // Make multipliers
        cs.add_constraint([(mul_left_var, -one), (left.0, one)].iter().collect());
        cs.add_constraint(
            [(mul_right_var, -one), (var_one, -z), (right.0, one)]
                .iter()
                .collect(),
        );

        Ok((mul_out_var, mul_out))
    }
}

// Helper functions for proof creation
fn kshuffle_prover_cs<'a, 'b>(
    pc_gens: &'b PedersenGens,
    bp_gens: &'b BulletproofGens,
    transcript: &'a mut Transcript,
    input: &Vec<u64>,
    output: &Vec<u64>,
) -> Result<(ProverCS<'a, 'b>, Vec<CompressedRistretto>), KShuffleError> {
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
    let in_pairs = variables[0..k]
        .iter()
        .zip(input.iter())
        .map(|(var_i, in_i)| (*var_i, Assignment::from(in_i.clone())))
        .collect();
    let out_pairs = variables[k..2 * k]
        .iter()
        .zip(output.iter())
        .map(|(var_i, out_i)| (*var_i, Assignment::from(out_i.clone())))
        .collect();
    KShuffleGadget::fill_cs(&mut prover_cs, in_pairs, out_pairs).unwrap();

    Ok((prover_cs, commitments))
}

// Helper functions for proof verification
fn kshuffle_verifier_cs<'a, 'b>(
    pc_gens: &'b PedersenGens,
    bp_gens: &'b BulletproofGens,
    transcript: &'a mut Transcript,
    commitments: &Vec<CompressedRistretto>,
) -> Result<VerifierCS<'a, 'b>, KShuffleError> {
    let k = commitments.len() / 2;

    // Verifier makes a `ConstraintSystem` instance representing a shuffle gadget
    let (mut verifier_cs, variables) =
        VerifierCS::new(&bp_gens, &pc_gens, transcript, commitments.to_vec());

    // Verifier allocates variables and adds constraints to the constraint system
    let in_pairs = variables[0..k]
        .iter()
        .map(|var_i| (*var_i, Assignment::Missing()))
        .collect();
    let out_pairs = variables[k..2 * k]
        .iter()
        .map(|var_i| (*var_i, Assignment::Missing()))
        .collect();
    KShuffleGadget::fill_cs(&mut verifier_cs, in_pairs, out_pairs)?;

    Ok(verifier_cs)
}

fn shuffle_gadget_test_helper(k: usize) {
    use merlin::Transcript;
    use rand::Rng;

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let mut transcript = Transcript::new(b"ShuffleTest");
    transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

    let (proof, commitments) = {
        // Generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        let mut prover_transcript = transcript.clone();
        let (prover_cs, commits) =
            kshuffle_prover_cs(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                .unwrap();
        let proof = prover_cs.prove().unwrap();
        (proof, commits)
    };

    {
        let mut verifier_transcript = transcript.clone();

        let verifier_cs =
            kshuffle_verifier_cs(&pc_gens, &bp_gens, &mut verifier_transcript, &commitments)
                .unwrap();
        verifier_cs.verify(&proof).unwrap();
    }
}

#[test]
fn shuffle_gadget_test_1() {
    shuffle_gadget_test_helper(1);
}

#[test]
fn shuffle_gadget_test_2() {
    shuffle_gadget_test_helper(2);
}

#[test]
fn shuffle_gadget_test_3() {
    shuffle_gadget_test_helper(3);
}

#[test]
fn shuffle_gadget_test_4() {
    shuffle_gadget_test_helper(4);
}

#[test]
fn shuffle_gadget_test_5() {
    shuffle_gadget_test_helper(5);
}

#[test]
fn shuffle_gadget_test_6() {
    shuffle_gadget_test_helper(6);
}

#[test]
fn shuffle_gadget_test_7() {
    shuffle_gadget_test_helper(7);
}

#[test]
fn shuffle_gadget_test_24() {
    shuffle_gadget_test_helper(24);
}

#[test]
fn shuffle_gadget_test_42() {
    shuffle_gadget_test_helper(42);
}

*/
