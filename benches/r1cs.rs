extern crate bulletproofs;
use bulletproofs::r1cs::{
    ConstraintSystem, Prover, R1CSError, R1CSProof, RandomizedConstraintSystem, Variable, Verifier,
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

// Make a gadget that adds constraints to a ConstraintSystem, such that the
// y variables are constrained to be a valid shuffle of the x variables.
struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: Vec<Variable>,
        y: Vec<Variable>,
    ) -> Result<(), R1CSError> {
        let one = Scalar::one();

        assert_eq!(x.len(), y.len());

        let k = x.len();
        if k == 1 {
            cs.constrain([(x[0], -one), (y[0], one)].iter().collect());
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

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

            Ok(())
        })
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
    ) -> Result<
        (
            R1CSProof,
            Vec<CompressedRistretto>,
            Vec<CompressedRistretto>,
        ),
        R1CSError,
    > {
        // Apply a domain separator with the shuffle parameters to the transcript
        let k = input.len();
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut prover = Prover::new(&pc_gens, transcript);

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

        Self::fill_cs(&mut prover, input_vars, output_vars)?;
        let proof = prover.prove(&bp_gens)?;

        Ok((proof, input_commitments, output_commitments))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        proof: &R1CSProof,
        input_commitments: &Vec<CompressedRistretto>,
        output_commitments: &Vec<CompressedRistretto>,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        let k = input_commitments.len();
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|commitment| verifier.commit(*commitment))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|commitment| verifier.commit(*commitment))
            .collect();

        Self::fill_cs(&mut verifier, input_vars, output_vars)?;
        verifier.verify(proof, &pc_gens, &bp_gens)
    }
}

fn bench_kshuffle_prove(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "k-shuffle proof creation",
        move |b, k| {
            // Generate inputs and outputs to kshuffle
            let mut rng = rand::thread_rng();
            let (min, max) = (0u64, std::u64::MAX);
            let input: Vec<Scalar> = (0..*k)
                .map(|_| Scalar::from(rng.gen_range(min, max)))
                .collect();
            let mut output = input.clone();
            rand::thread_rng().shuffle(&mut output);

            // Make kshuffle proof
            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(128, 1);
            b.iter(|| {
                let mut prover_transcript = Transcript::new(b"ShuffleTest");
                KShuffleGadget::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                    .unwrap();
            })
        },
        vec![8, 16, 32, 64, 17],
    );
}

criterion_group! {
    name = kshuffle_prove;
    config = Criterion::default();
    targets =
    bench_kshuffle_prove,
}

fn bench_kshuffle_verify(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "k-shuffle proof verification",
        move |b, k| {
            // Generate inputs and outputs to kshuffle
            let mut rng = rand::thread_rng();
            let (min, max) = (0u64, std::u64::MAX);
            let input: Vec<Scalar> = (0..*k)
                .map(|_| Scalar::from(rng.gen_range(min, max)))
                .collect();
            let mut output = input.clone();
            rand::thread_rng().shuffle(&mut output);

            // Make kshuffle proof
            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(128, 1);
            let mut prover_transcript = Transcript::new(b"ShuffleTest");
            let (proof, in_commitments, out_commitments) =
                KShuffleGadget::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                    .unwrap();

            // Verify kshuffle proof
            b.iter(|| {
                let mut verifier_transcript = Transcript::new(b"ShuffleTest");
                KShuffleGadget::verify(
                    &pc_gens,
                    &bp_gens,
                    &mut verifier_transcript,
                    &proof,
                    &in_commitments,
                    &out_commitments,
                )
                .unwrap();
            })
        },
        vec![8, 16, 32, 64, 17],
    );
}

criterion_group! {
    name = kshuffle_verify;
    config = Criterion::default();
    targets =
    bench_kshuffle_verify,
}

criterion_main!(kshuffle_prove, kshuffle_verify);
