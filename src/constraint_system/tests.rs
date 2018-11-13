use super::assignment::Assignment;
use super::prover::ProverCS;
use super::verifier::VerifierCS;
use super::*;

use errors::ConstraintSystemError;
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
) -> Result<(), ConstraintSystemError> {
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
) -> Result<(), ConstraintSystemError> {
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
    cs.verify(&proof).map_err(|_| ConstraintSystemError::VerificationError)
}

#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
}

/// Shuffle gadget tests

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

impl From<ConstraintSystemError> for KShuffleError {
    fn from(e: ConstraintSystemError) -> KShuffleError {
        match e {
            ConstraintSystemError::InvalidGeneratorsLength => KShuffleError::InvalidGeneratorsLength,
            ConstraintSystemError::MissingAssignment => KShuffleError::InvalidR1CSConstruction,
            ConstraintSystemError::VerificationError => KShuffleError::VerificationError,
        }
    }
}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: Vec<(Variable, Assignment)>,
        y: Vec<(Variable, Assignment)>,
    ) -> Result<(), KShuffleError> {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-shuffle challenge");
        let neg_z = -z;
        if x.len() != y.len() {
            return Err(KShuffleError::InvalidR1CSConstruction);
        }
        let k = x.len();
        if k == 1 {
            cs.add_constraint([(x[0].0, -one), (y[0].0, one)].iter().collect());
            return Ok(());
        }
        // Make last x multiplier for i = k-1 and k-2
        let mut mulx_left = x[k - 1].1 + neg_z;
        let mut mulx_right = x[k - 2].1 + neg_z;
        let mut mulx_out = mulx_left * mulx_right;
        let mut mulx_out_var_prev = KShuffleGadget::multiplier_helper(
            cs,
            neg_z,
            mulx_left,
            mulx_right,
            mulx_out,
            x[k - 1].0,
            x[k - 2].0,
            true,
        )?;
        // Make multipliers for x from i == [0, k-3]
        for i in (0..k - 2).rev() {
            mulx_left = mulx_out;
            mulx_right = x[i].1 + neg_z;
            mulx_out = mulx_left * mulx_right;
            mulx_out_var_prev = KShuffleGadget::multiplier_helper(
                cs,
                neg_z,
                mulx_left,
                mulx_right,
                mulx_out,
                mulx_out_var_prev,
                x[i].0,
                false,
            )?;
        }
        // Make last y multiplier for i = k-1 and k-2
        let mut muly_left = y[k - 1].1 - z;
        let mut muly_right = y[k - 2].1 - z;
        let mut muly_out = muly_left * muly_right;
        let mut muly_out_var_prev = KShuffleGadget::multiplier_helper(
            cs,
            neg_z,
            muly_left,
            muly_right,
            muly_out,
            y[k - 1].0,
            y[k - 2].0,
            true,
        )?;
        // Make multipliers for y from i == [0, k-3]
        for i in (0..k - 2).rev() {
            muly_left = muly_out;
            muly_right = y[i].1 + neg_z;
            muly_out = muly_left * muly_right;
            muly_out_var_prev = KShuffleGadget::multiplier_helper(
                cs,
                neg_z,
                muly_left,
                muly_right,
                muly_out,
                muly_out_var_prev,
                y[i].0,
                false,
            )?;
        }
        // Check equality between last x mul output and last y mul output
        cs.add_constraint(
            [(muly_out_var_prev, -one), (mulx_out_var_prev, one)]
                .iter()
                .collect(),
        );
        Ok(())
    }

    fn multiplier_helper<CS: ConstraintSystem>(
        cs: &mut CS,
        neg_z: Scalar,
        left: Assignment,
        right: Assignment,
        out: Assignment,
        left_var: Variable,
        right_var: Variable,
        is_last_mul: bool,
    ) -> Result<Variable, KShuffleError> {
        let one = Scalar::one();
        let var_one = Variable::One();
        // Make multiplier gate variables
        let (left_mul_var, right_mul_var, out_mul_var) = cs.assign_multiplier(left, right, out)?;
        if is_last_mul {
            // Make last multiplier
            cs.add_constraint(
                [(left_mul_var, -one), (var_one, neg_z), (left_var, one)]
                    .iter()
                    .collect(),
            );
        } else {
            // Make intermediate multiplier
            cs.add_constraint([(left_mul_var, -one), (left_var, one)].iter().collect());
        }
        cs.add_constraint(
            [(right_mul_var, -one), (var_one, neg_z), (right_var, one)]
                .iter()
                .collect(),
        );
        Ok(out_mul_var)
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
