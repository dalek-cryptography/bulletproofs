#[macro_use]
extern crate failure;

extern crate bulletproofs;
use bulletproofs::constraint_system::{
    Assignment, ConstraintSystem, ConstraintSystemError, ProverCS, Variable, VerifierCS,
};
use bulletproofs::{BulletproofGens, PedersenGens};

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

extern crate merlin;
use merlin::Transcript;

extern crate rand;
use rand::Rng;

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

/// Enforces that the output variables `y` are a valid reordering of the inputs variables `x`.
/// The inputs and outputs are all tuples of the `Variable, Assignment`, where the `Assignment`
/// can be either assigned as `Value::Scalar` or unassigned as `Missing`.
pub fn fill_cs<CS: ConstraintSystem>(
    cs: &mut CS,
    x: Vec<(Variable, Assignment)>,
    y: Vec<(Variable, Assignment)>,
) -> Result<(), KShuffleError> {
    let one = Scalar::one();
    let z = cs.challenge_scalar(b"k-scalar shuffle challenge");

    if x.len() != y.len() {
        return Err(KShuffleError::InvalidConstraintSystemConstruction);
    }
    let k = x.len();
    if k == 1 {
        cs.add_constraint([(x[0].0, -one), (y[0].0, one)].iter().collect());
        return Ok(());
    }

    // Make last x multiplier for i = k-1 and k-2
    let last_mulx_out = last_multiplier(cs, z, x[k - 1], x[k - 2]);

    // Make multipliers for x from i == [0, k-3]
    let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
        intermediate_multiplier(cs, z, prev_out?, x[i])
    })?;

    // Make last y multiplier for i = k-1 and k-2
    let last_muly_out = last_multiplier(cs, z, y[k - 1], y[k - 2]);

    // Make multipliers for y from i == [0, k-3]
    let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
        intermediate_multiplier(cs, z, prev_out?, y[i])
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

/// Represents an error during the proof creation of verification for a KShuffle gadget.
#[derive(Fail, Copy, Clone, Debug, Eq, PartialEq)]
pub enum KShuffleError {
    /// Error in the constraint system creation process
    #[fail(display = "Invalid KShuffle constraint system construction")]
    InvalidConstraintSystemConstruction,
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
            ConstraintSystemError::InvalidGeneratorsLength => {
                KShuffleError::InvalidGeneratorsLength
            }
            ConstraintSystemError::MissingAssignment => {
                KShuffleError::InvalidConstraintSystemConstruction
            }
            ConstraintSystemError::VerificationError => KShuffleError::VerificationError,
        }
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
    fill_cs(&mut prover_cs, in_pairs, out_pairs).unwrap();

    Ok((prover_cs, commitments))
}

fn kshuffle_prove_helper(k: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle proof creation", k);

    c.bench_function(&label, move |b| {
        // Generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        // Make kshuffle proof
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        b.iter(|| {
            let mut prover_transcript = Transcript::new(b"ShuffleTest");
            let (prover_cs, _) =
                kshuffle_prover_cs(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                    .unwrap();
            prover_cs.prove().unwrap();
        })
    });
}

fn kshuffle_prove_8(c: &mut Criterion) {
    kshuffle_prove_helper(8, c);
}
fn kshuffle_prove_16(c: &mut Criterion) {
    kshuffle_prove_helper(16, c);
}
fn kshuffle_prove_32(c: &mut Criterion) {
    kshuffle_prove_helper(32, c);
}
fn kshuffle_prove_64(c: &mut Criterion) {
    kshuffle_prove_helper(64, c);
}
fn kshuffle_prove_17(c: &mut Criterion) {
    kshuffle_prove_helper(17, c);
}

criterion_group!{
    name = kshuffle_prove;
    config = Criterion::default();
    targets =
    kshuffle_prove_8,
    kshuffle_prove_16,
    kshuffle_prove_32,
    kshuffle_prove_64,
    kshuffle_prove_17,
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
    fill_cs(&mut verifier_cs, in_pairs, out_pairs)?;

    Ok(verifier_cs)
}

fn kshuffle_verify_helper(k: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle proof verification", k);

    c.bench_function(&label, move |b| {
        // Generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        // Make kshuffle proof
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let mut prover_transcript = Transcript::new(b"ShuffleTest");
        let (prover_cs, commitments) =
            kshuffle_prover_cs(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                .unwrap();
        let proof = prover_cs.prove().unwrap();

        // Verify kshuffle proof
        b.iter(|| {
            let mut verifier_transcript = Transcript::new(b"ShuffleTest");
            let verifier_cs =
                kshuffle_verifier_cs(&pc_gens, &bp_gens, &mut verifier_transcript, &commitments)
                    .unwrap();
            verifier_cs.verify(&proof).unwrap();
        })
    });
}

fn kshuffle_verify_8(c: &mut Criterion) {
    kshuffle_verify_helper(8, c);
}
fn kshuffle_verify_16(c: &mut Criterion) {
    kshuffle_verify_helper(16, c);
}
fn kshuffle_verify_32(c: &mut Criterion) {
    kshuffle_verify_helper(32, c);
}
fn kshuffle_verify_64(c: &mut Criterion) {
    kshuffle_verify_helper(64, c);
}
fn kshuffle_verify_17(c: &mut Criterion) {
    kshuffle_verify_helper(17, c);
}

criterion_group!{
    name = kshuffle_verify;
    config = Criterion::default();
    targets =
    kshuffle_verify_8,
    kshuffle_verify_16,
    kshuffle_verify_32,
    kshuffle_verify_64,
    kshuffle_verify_17,
}

criterion_main!(kshuffle_prove, kshuffle_verify);
