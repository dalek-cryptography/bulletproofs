The rank-1 constraint system API for programmatically defining constraint systems.

XXX explain how the parts fit together here

```
extern crate bulletproofs;
use bulletproofs::r1cs::{ConstraintSystem, Variable, ProverCS, VerifierCS, R1CSError, R1CSProof};
use bulletproofs::{BulletproofGens, PedersenGens};

extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;

extern crate merlin;
use merlin::Transcript;

extern crate rand;

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
        KShuffleGadget::fill_cs(
            &mut prover_cs,
            input_vars,
            output_vars,
        );

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
        KShuffleGadget::fill_cs(
            &mut verifier_cs,
            input_vars,
            output_vars,
        );

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
        let input: Vec<Scalar> = (0..k).map(|_| Scalar::from(rng.gen_range(min, max))).collect();
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

# fn main() {
    kshuffle_helper(1);
    kshuffle_helper(2);
    kshuffle_helper(3);
    kshuffle_helper(4);
    kshuffle_helper(5);
    kshuffle_helper(10);
    kshuffle_helper(25);
# }
```
