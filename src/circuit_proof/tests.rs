use super::scalar_value::ScalarValue;
use super::opaque_scalar::OpaqueScalar;
use super::*;

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use rand::thread_rng;

/// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2),
/// where c2 is a constant.
#[allow(non_snake_case)]
fn example_gadget<S: ScalarValue, CS: ConstraintSystem>(
    cs: &mut CS,
    a1: Variable<S>,
    a2: Variable<S>,
    b1: Variable<S>,
    b2: Variable<S>,
    c1: Variable<S>,
    c2: Scalar,
) -> Result<(), R1CSError> {

    let one: S = Scalar::one().into();

    let l = LinearCombination::from((a1, one)) + (a2, one);
    let r = LinearCombination::from((b1, one)) + (b2, one);
    let o = LinearCombination::from((c1, one)) + c2;

    // Make low-level VariableIndexs (aL = v_a1 + v_a2, aR = v_b1 + v_b2, aO = v_c1 + v_c2)
    let (aL, aR, aO) =
        cs.assign_multiplier(l.eval(), r.eval(), o.eval())?;

    // Tie high-level and low-level variables together
    cs.add_constraint((l - (aL, one)).into());
    cs.add_constraint((r - (aR, one)).into());
    cs.add_constraint((o - (aO, one)).into());

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
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let base_transcript = Transcript::new(b"R1CSExampleGadget");

    // Prover's scope
    let (proof, commitments) = {

        let v: Vec<_> = [a1, a2, b1, b2, c1]
            .iter()
            .map(|x| Scalar::from(*x))
            .collect();
        let v_blinding = blinding_helper(v.len());

        R1CSProof::prove(
            &bp_gens,
            &pc_gens,
            &mut base_transcript.clone(),
            v,
            v_blinding,
            |cs, vars| {
                example_gadget(
                    cs,
                    vars[0],
                    vars[1],
                    vars[2],
                    vars[3],
                    vars[4],
                    c2.into(),
                )
            },
        ).unwrap()
    };

    // Verifier's scope

    proof.verify(
        &bp_gens,
        &pc_gens,
        &mut base_transcript.clone(),
        commitments,
        |cs, vars| {
            example_gadget(
                cs,
                vars[0],
                vars[1],
                vars[2],
                vars[3],
                vars[4],
                c2.into(),
            )
        }
    )
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

Algebraically it can be expressed as a statement that for a free VariableIndex `z`, 
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

    // last multipliers connect two last VariableIndexs (on each side)
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

    fn fill_cs<S: ScalarValue, CS: ConstraintSystem>(
        cs: &mut CS,
        x: &[Variable<S>],
        y: &[Variable<S>],
    ) -> Result<(), R1CSError> {

        let one = S::one();

        if x.len() != y.len() {
            return Err(R1CSError::LayoutError{cause: "KShuffleGadget: inputs have different lengths"});
        }
        
        let k = x.len();

        if k == 1 {
            cs.add_constraint((LinearCombination::from((x[0], one)) - (y[0], one)).into());
            return Ok(());
        }
        
        cs.after_commitment(|cs| {

            let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
            let neg_z = -z;

            // Make last x multiplier for i = k-1 and k-2
            let last_mulx_out = KShuffleGadget::last_multiplier(cs, neg_z, x[k - 1], x[k - 2]);

            // Make multipliers for x from i == [0, k-3]
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
                KShuffleGadget::intermediate_multiplier(cs, neg_z, prev_out?, x[i])
            })?;

            // Make last y multiplier for i = k-1 and k-2
            let last_muly_out = KShuffleGadget::last_multiplier(cs, z, y[k - 1], y[k - 2]);

            // Make multipliers for y from i == [0, k-3]
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
                KShuffleGadget::intermediate_multiplier(cs, neg_z, prev_out?, y[i])
            })?;

            // Check equality between last x mul output and last y mul output
            cs.add_constraint((LinearCombination::from((first_mulx_out, one)) - (first_muly_out, one)).into());

            Ok(())
        })?;

        Ok(())
    }

    fn last_multiplier<S: ScalarValue, CS: ConstraintSystem>(
        cs: &mut CS,
        neg_z: OpaqueScalar,
        left: Variable<S>,
        right: Variable<S>,
    ) -> Result<Variable<S>, R1CSError> {
        let one = S::one();

        let l = LinearCombination::from((left, one)) + neg_z;
        let r = LinearCombination::from((right, one)) + neg_z;

        let (al, ar, ao) =
            cs.assign_multiplier(l.eval(), r.eval(), l.eval()*r.eval())?;

        cs.add_constraint((l - (al, one)).into());
        cs.add_constraint((r - (ar, one)).into());

        Ok(ao)
    }

    fn intermediate_multiplier<S: ScalarValue, CS: ConstraintSystem>(
        cs: &mut CS,
        neg_z: OpaqueScalar,
        left: Variable<S>,
        right: Variable<S>,
    ) -> Result<Variable<S>, R1CSError> {
        let one = S::one();

        let l = LinearCombination::from((left, one));
        let r = LinearCombination::from((right, one)) + neg_z;

        let (al, ar, ao) =
            cs.assign_multiplier(l.eval(), r.eval(), l.eval()*r.eval())?;

        cs.add_constraint((l - (al, one)).into());
        cs.add_constraint((r - (ar, one)).into());

        Ok(ao)
    }
}

fn shuffle_gadget_test_helper(k: usize) {
    use merlin::Transcript;
    use rand::Rng;

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let mut base_transcript = Transcript::new(b"ShuffleTest");
    base_transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

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
        let v_blinding = blinding_helper(v.len());

        R1CSProof::prove(
            &bp_gens,
            &pc_gens,
            &mut base_transcript.clone(),
            v.into_iter().map(Scalar::from).collect(),
            v_blinding,
            |cs, vars| {
                KShuffleGadget::fill_cs(cs, &vars[0..k], &vars[k..2*k])
            },
        ).unwrap()
    };

    // Verifier's scope

    proof.verify(
        &bp_gens,
        &pc_gens,
        &mut base_transcript.clone(),
        commitments,
        |cs, vars| {
            KShuffleGadget::fill_cs(cs, &vars[0..k], &vars[k..2*k])
        }
    ).unwrap()
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
