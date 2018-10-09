extern crate bulletproofs;
use bulletproofs::circuit_proof::assignment::Assignment;
use bulletproofs::circuit_proof::{prover, verifier, ConstraintSystem, Variable};
use bulletproofs::{BulletproofGens, PedersenGens, R1CSError};

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

// Make a gadget that adds constraints to a ConstraintSystem, such that the
// y variables are constrained to be a valid shuffle of the x variables.
struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: Vec<(Variable, Assignment)>,
        y: Vec<(Variable, Assignment)>,
    ) -> Result<(), R1CSError> {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-shuffle challenge");
        let neg_z = -z;
        if x.len() != y.len() {
            return Err(R1CSError::InvalidR1CSConstruction);
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
    ) -> Result<Variable, R1CSError> {
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
) -> Result<(prover::ProverCS<'a, 'b>, Vec<CompressedRistretto>), R1CSError> {
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
        prover::ProverCS::new(&bp_gens, &pc_gens, transcript, v, v_blinding.clone());

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

fn kshuffle_prove_helper(k: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle proof creation", k);

    c.bench_function(&label, move |b| {
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

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
) -> Result<verifier::VerifierCS<'a, 'b>, R1CSError> {
    let k = commitments.len() / 2;

    // Verifier makes a `ConstraintSystem` instance representing a shuffle gadget
    let (mut verifier_cs, variables) =
        verifier::VerifierCS::new(&bp_gens, &pc_gens, transcript, commitments.to_vec());

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

fn kshuffle_verify_helper(k: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle proof verification", k);

    c.bench_function(&label, move |b| {
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
        let mut output = input.clone();
        rand::thread_rng().shuffle(&mut output);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut prover_transcript = Transcript::new(b"ShuffleTest");
        let (prover_cs, commitments) =
            kshuffle_prover_cs(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                .unwrap();
        let proof = prover_cs.prove().unwrap();

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
