extern crate failure;

extern crate bulletproofs;
use bulletproofs::r1cs::{ConstraintSystem, OpaqueScalar, R1CSError, R1CSProof, Variable};
use bulletproofs::{BulletproofGens, PedersenGens};

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
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
        x: Vec<Variable<OpaqueScalar>>,
        y: Vec<Variable<OpaqueScalar>>,
    ) -> Result<(), R1CSError> {
        if x.len() != y.len() {
            return Err(R1CSError::LayoutError {
                cause: "KShuffleGadget: inputs have different lengths",
            });
        }

        let k = x.len();

        if k == 1 {
            cs.add_constraint(x[0].equals(y[0]));
            return Ok(());
        }

        cs.challenge_scalar(b"k-scalar shuffle challenge", move |cs, z| {
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
            cs.add_constraint(first_mulx_out.equals(first_muly_out));

            Ok(())
        })?;

        Ok(())
    }

    fn last_multiplier<CS: ConstraintSystem>(
        cs: &mut CS,
        z: OpaqueScalar,
        left: Variable<OpaqueScalar>,
        right: Variable<OpaqueScalar>,
    ) -> Result<Variable<OpaqueScalar>, R1CSError> {
        let l = left - z;
        let r = right - z;

        let (al, ar, ao) = cs.assign_multiplier(l.eval(), r.eval(), l.eval() * r.eval())?;

        cs.add_constraint(al.equals(l));
        cs.add_constraint(ar.equals(r));

        Ok(ao)
    }

    fn intermediate_multiplier<CS: ConstraintSystem>(
        cs: &mut CS,
        z: OpaqueScalar,
        left: Variable<OpaqueScalar>,
        right: Variable<OpaqueScalar>,
    ) -> Result<Variable<OpaqueScalar>, R1CSError> {
        let r = right - z;

        let (al, ar, ao) =
            cs.assign_multiplier(left.assignment, r.eval(), left.assignment * r.eval())?;

        cs.add_constraint(al.equals(left));
        cs.add_constraint(ar.equals(r));

        Ok(ao)
    }
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

            let mut v = Vec::with_capacity(2 * k);
            v.extend_from_slice(&input);
            v.extend_from_slice(&output);
            let v_blinding = (0..v.len())
                .map(|_| Scalar::random(&mut rand::thread_rng()))
                .collect();

            R1CSProof::prove(
                &bp_gens,
                &pc_gens,
                &mut prover_transcript,
                v.into_iter().map(Scalar::from).collect(),
                v_blinding,
                |cs, vars| {
                    KShuffleGadget::fill_cs(
                        cs,
                        (&vars[0..k]).into_iter().map(|v| v.into_opaque()).collect(),
                        (&vars[k..2 * k])
                            .into_iter()
                            .map(|v| v.into_opaque())
                            .collect(),
                    )
                },
            )
            .unwrap()
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
        let base_transcript = Transcript::new(b"ShuffleTest");

        // Prover's scope
        let (proof, commitments) = {
            // Generate inputs and outputs to kshuffle
            let mut rng = rand::thread_rng();
            let (min, max) = (0u64, std::u64::MAX);
            let input: Vec<u64> = (0..k).map(|_| rng.gen_range(min, max)).collect();
            let mut output = input.clone();
            rand::thread_rng().shuffle(&mut output);

            let mut v = Vec::with_capacity(2 * k);
            v.extend_from_slice(&input);
            v.extend_from_slice(&output);
            let v_blinding = (0..v.len())
                .map(|_| Scalar::random(&mut rand::thread_rng()))
                .collect();

            R1CSProof::prove(
                &bp_gens,
                &pc_gens,
                &mut base_transcript.clone(),
                v.into_iter().map(Scalar::from).collect(),
                v_blinding,
                |cs, vars| {
                    KShuffleGadget::fill_cs(
                        cs,
                        (&vars[0..k]).into_iter().map(|v| v.into_opaque()).collect(),
                        (&vars[k..2 * k])
                            .into_iter()
                            .map(|v| v.into_opaque())
                            .collect(),
                    )
                },
            )
            .unwrap()
        };

        // Verify kshuffle proof
        b.iter(|| {
            proof
                .clone()
                .verify(
                    &bp_gens,
                    &pc_gens,
                    &mut base_transcript.clone(),
                    commitments.clone(),
                    |cs, vars| {
                        KShuffleGadget::fill_cs(
                            cs,
                            (&vars[0..k]).into_iter().map(|v| v.into_opaque()).collect(),
                            (&vars[k..2 * k])
                                .into_iter()
                                .map(|v| v.into_opaque())
                                .collect(),
                        )
                    },
                )
                .unwrap();
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
