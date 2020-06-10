The rank-1 constraint system API for programmatically defining constraint systems.

## Building a proof-of-shuffle constraint system

A shuffle is a permutation of a list of \\(k\\) scalars \\(x_i\\) into a list of \\(k\\) scalars \\(y_i\\).

Algebraically it can be expressed as a statement that for a free variable \\(z\\), the roots of the two polynomials in terms of \\(z\\) are the same up to a permutation:

\\[
\prod_i (x_i - z) = \prod_i (y_i - z)
\\]

The prover can commit to blinded scalars \\(x_i\\) and \\(y_i\\) then receive a random challenge \\(z\\),
and build a proof that the above relation holds.

K-shuffle requires \\( 2*(K-1) \\) multipliers.

For `K > 1`:

```ascii,no_run


        (x_0 - z)---⊗------⊗---(y_0 - z)        // mulx[0], muly[0]
                    |      |
        (x_1 - z)---⊗      ⊗---(y_1 - z)        // mulx[1], muly[1]
                    |      |
                   ...    ...
                    |      |
    (x_{k-2} - z)---⊗      ⊗---(y_{k-2} - z)    // mulx[k-2], muly[k-2]
                   /        \
    (x_{k-1} - z)_/          \_(y_{k-1} - z)
```

Connect the left and right sides of the shuffle statement:
```ascii,no_run
    mulx_out[0] = muly_out[0]
```
For `i == [0, k-3]`:
```ascii,no_run
    mulx_left[i]  = x_i - z
    mulx_right[i] = mulx_out[i+1]
    muly_left[i]  = y_i - z
    muly_right[i] = muly_out[i+1]
```
The last multipliers connect the two last variables (on each side)
```ascii,no_run
    mulx_left[k-2]  = x_{k-2} - z
    mulx_right[k-2] = x_{k-1} - z
    muly_left[k-2]  = y_{k-2} - z
    muly_right[k-2] = y_{k-1} - z
```
For `K = 1`:
Connect `x_0` to `y_0` directly. Since there is only one permuatation of a 1-element list, we can omit the challenge entirely as it cancels out.
```ascii,no_run
    x_0 = y_0
```
Code for creating constraints for a proof-of-shuffle constraint system:

```rust
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
    fn gadget<CS: RandomizableConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) -> Result<(),R1CSError> {

        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
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
            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
    }
}
```

In this example, `ShuffleProof::gadget()` is private function that adds constraints to the constraint system that enforce that \\(y\\) (the outputs) are a valid reordering of \\(x\\) (the inputs). 

First, the function gets a challenge scalar \\(z\\) by calling the `ConstraintSystem::challenge_scalar`. This challenge is generated from commitments to high-level variables that were passed to the `ConstraintSystem` when it was created. As noted in the `challenge_scalar` documentation, making sure that the challenge circuit is sound requires analysis. In this example, the challenge circuit is sound because the challenge is bound to all of the shuffle inputs and outputs, since the inputs and outputs are high-level variables.

After a check for the lengths of \\(x\\) and \\(y\\), the function then makes
multipliers to create polynomials in terms of the challenge scalar \\(z\\).
It starts with the last multipliers, representing `(x_{k-1} - z) *
(x_{k-2} - z)` and `(y_{k-1} - z) * (y_{k-2} - z)`. The outputs
to these last multipliers than become an input to the next multiplier.
This continues recursively until it reaches `x_0` and `y_0`.
Then, it adds a constraint that `mulx_out[0]` = `muly_out[0]`,
which constrains that the two polynomials in terms of challenge scalar
\\(z\\) are equal to each other. This is true if and only if \\(y\\) is a valid
reordering of \\(x\\).

## Constructing a proof

The prover prepares the input and output scalar lists, as well as the generators (which are needed to make commitments and to make the proof) and a transcript (which is needed to generate challenges). The `prove` function takes the list of scalar inputs and outputs, makes commitments to them, and creates a proof that the committed outputs are a valid reordering of the committed inputs. 

For simplicity, in this example the `prove` function does not take a list of blinding factors for the inputs and outputs, so it is not possible to make a proof for existing committed points. However, it is possible to modify the function to take in a list of blinding factors instead of generating them internally. Also, in this example the `prove` function does not return the list of blinding factors generated, so it is not possible for the prover to open the commitments in the future. This can also be easily modified.


```rust
# extern crate bulletproofs;
# extern crate curve25519_dalek;
# extern crate merlin;
# extern crate rand;
# 
# use bulletproofs::r1cs::*;
# use bulletproofs::{BulletproofGens, PedersenGens};
# use curve25519_dalek::ristretto::CompressedRistretto;
# use curve25519_dalek::scalar::Scalar;
# use merlin::Transcript;
# use rand::thread_rng;
# 
# // Shuffle gadget (documented in markdown file)
# 
# /// A proof-of-shuffle.
# struct ShuffleProof(R1CSProof);
# 
# impl ShuffleProof {
#     fn gadget<CS: RandomizableConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) -> Result<(),R1CSError> {
# 
#         assert_eq!(x.len(), y.len());
#         let k = x.len();
# 
#         if k == 1 {
#             cs.constrain(y[0] - x[0]);
#             return Ok(());
#         }
#
#         cs.specify_randomized_constraints(move |cs| {
#
#             let z = cs.challenge_scalar(b"shuffle challenge");
#
#             // Make last x multiplier for i = k-1 and k-2
#             let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);
# 
#             // Make multipliers for x from i == [0, k-3]
#             let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
#                 o
#             });
# 
#             // Make last y multiplier for i = k-1 and k-2
#             let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);
# 
#             // Make multipliers for y from i == [0, k-3]
#             let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
#                 o
#             });
# 
#             // Constrain last x mul output and last y mul output to be equal
#             cs.constrain(first_mulx_out - first_muly_out);
#
#             Ok(())
#         })
#     }
# }
 
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
    ) -> Result<(ShuffleProof, Vec<CompressedRistretto>, Vec<CompressedRistretto>), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        let k = input.len();
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut prover = Prover::new(&pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input.into_iter()
            .map(|v| {
                prover.commit(*v, Scalar::random(&mut blinding_rng))
            })
            .unzip();

        let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output.into_iter()
            .map(|v| {
                prover.commit(*v, Scalar::random(&mut blinding_rng))
            })
            .unzip();

        ShuffleProof::gadget(&mut prover, input_vars, output_vars)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((ShuffleProof(proof), input_commitments, output_commitments))
    }
}
```

## Verifiying a proof

The verifier receives a proof, and a list of committed inputs and outputs, from the prover. It passes these to the `verify` function, which verifies that, given a shuffle proof and a list of committed inputs and outputs, the outputs are a valid reordering of the inputs. The verifier receives a `Result::ok()` if the proof verified correctly and a `Result::error(R1CSError)` otherwise.


```rust
# extern crate bulletproofs;
# extern crate curve25519_dalek;
# extern crate merlin;
# extern crate rand;
# 
# use bulletproofs::r1cs::*;
# use bulletproofs::{BulletproofGens, PedersenGens};
# use curve25519_dalek::ristretto::CompressedRistretto;
# use curve25519_dalek::scalar::Scalar;
# use merlin::Transcript;
# use rand::thread_rng;
# 
# // Shuffle gadget (documented in markdown file)
# 
# /// A proof-of-shuffle.
# struct ShuffleProof(R1CSProof);
# 
# impl ShuffleProof {
#     fn gadget<CS: RandomizableConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) -> Result<(),R1CSError> {
# 
#         assert_eq!(x.len(), y.len());
#         let k = x.len();
# 
#         if k == 1 {
#             cs.constrain(y[0] - x[0]);
#             return Ok(());
#         }
#
#         cs.specify_randomized_constraints(move |cs| {
#
#             let z = cs.challenge_scalar(b"shuffle challenge");

#             // Make last x multiplier for i = k-1 and k-2
#             let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);
# 
#             // Make multipliers for x from i == [0, k-3]
#             let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
#                 o
#             });
# 
#             // Make last y multiplier for i = k-1 and k-2
#             let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);
# 
#             // Make multipliers for y from i == [0, k-3]
#             let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
#                 o
#             });
# 
#             // Constrain last x mul output and last y mul output to be equal
#             cs.constrain(first_mulx_out - first_muly_out);
#
#             Ok(())
#         })
#     }
# }
# 
# impl ShuffleProof {
#     /// Attempt to construct a proof that `output` is a permutation of `input`.
#     ///
#     /// Returns a tuple `(proof, input_commitments || output_commitments)`.
#     pub fn prove<'a, 'b>(
#         pc_gens: &'b PedersenGens,
#         bp_gens: &'b BulletproofGens,
#         transcript: &'a mut Transcript,
#         input: &[Scalar],
#         output: &[Scalar],
#     ) -> Result<(ShuffleProof, Vec<CompressedRistretto>, Vec<CompressedRistretto>), R1CSError> {
#         // Apply a domain separator with the shuffle parameters to the transcript
#         let k = input.len();
#         transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
#         transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());
# 
#         let mut prover = Prover::new(&pc_gens, transcript);
# 
#         // Construct blinding factors using an RNG.
#         // Note: a non-example implementation would want to operate on existing commitments.
#         let mut blinding_rng = rand::thread_rng();
# 
#         let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input.into_iter()
#             .map(|v| {
#                 prover.commit(*v, Scalar::random(&mut blinding_rng))
#             })
#             .unzip();
# 
#         let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output.into_iter()
#             .map(|v| {
#                 prover.commit(*v, Scalar::random(&mut blinding_rng))
#             })
#             .unzip();
#
#         ShuffleProof::gadget(&mut prover, input_vars, output_vars)?;
#
#         let proof = prover.prove(&bp_gens)?;
#
#         Ok((ShuffleProof(proof), input_commitments, output_commitments))
#     }
# }
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
        let k = input_commitments.len();
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments.iter().map(|commitment| {
            verifier.commit(*commitment)
        }).collect();

        let output_vars: Vec<_> = output_commitments.iter().map(|commitment| {
            verifier.commit(*commitment)
        }).collect();

        ShuffleProof::gadget(&mut verifier, input_vars, output_vars)?;

        verifier.verify(&self.0, &pc_gens, &bp_gens)
    }
}
```

## Using the `ShuffleProof`

Here, we use the `ShuffleProof` gadget by first constructing the common inputs to the `prove` and `verify` functions: the Pedersen and Bulletproofs generators. Next, the prover makes the other inputs to the `prove` function: the list of scalar inputs, the list of scalar outputs, and the prover transcript. The prover calls the `prove` function, and gets a proof and a list of committed points that represent the commitments to the input and output scalars.

The prover passes the proof and the commitments to the verifier. The verifier then makes the other inputs to the `verify` function: the verifier transcript. Note that the starting transcript state provides domain seperation between different applications, and must be the same for the prover and verifer transcript; if they are not, then the prover and verifier will receive different challenge scalars and the proof will not verify correctly. The verifier then calls the `verify` function, and gets back a `Result` representing whether or not the proof verified correctly.

Because only the prover knows the scalar values of the inputs and outputs, and the verifier only sees the committed inputs and outputs and not the scalar values themselves, the verifier has no knowledge of what the underlying inputs and outputs are. Therefore, the only information the verifier learns from this protocol is whether or not the committed outputs are a valid shuffle of the committed inputs - this is why it is a zero-knowledge proof.

```rust
# extern crate bulletproofs;
# extern crate curve25519_dalek;
# extern crate merlin;
# extern crate rand;
# 
# use bulletproofs::r1cs::*;
# use bulletproofs::{BulletproofGens, PedersenGens};
# use curve25519_dalek::ristretto::CompressedRistretto;
# use curve25519_dalek::scalar::Scalar;
# use merlin::Transcript;
# use rand::thread_rng;
# 
# // Shuffle gadget (documented in markdown file)
# 
# /// A proof-of-shuffle.
# struct ShuffleProof(R1CSProof);
# 
# impl ShuffleProof {
#     fn gadget<CS: RandomizableConstraintSystem>(cs: &mut CS, x: Vec<Variable>, y: Vec<Variable>) -> Result<(),R1CSError> {
# 
#         assert_eq!(x.len(), y.len());
#         let k = x.len();
# 
#         if k == 1 {
#             cs.constrain(y[0] - x[0]);
#             return Ok(());
#         }
#
#         cs.specify_randomized_constraints(move |cs| {
#
#             let z = cs.challenge_scalar(b"shuffle challenge");

#             // Make last x multiplier for i = k-1 and k-2
#             let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);
# 
#             // Make multipliers for x from i == [0, k-3]
#             let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
#                 o
#             });
# 
#             // Make last y multiplier for i = k-1 and k-2
#             let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);
# 
#             // Make multipliers for y from i == [0, k-3]
#             let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
#                 let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
#                 o
#             });
# 
#             // Constrain last x mul output and last y mul output to be equal
#             cs.constrain(first_mulx_out - first_muly_out);
#
#             Ok(())
#         })
#     }
# }
# 
# impl ShuffleProof {
#     /// Attempt to construct a proof that `output` is a permutation of `input`.
#     ///
#     /// Returns a tuple `(proof, input_commitments || output_commitments)`.
#     pub fn prove<'a, 'b>(
#         pc_gens: &'b PedersenGens,
#         bp_gens: &'b BulletproofGens,
#         transcript: &'a mut Transcript,
#         input: &[Scalar],
#         output: &[Scalar],
#     ) -> Result<(ShuffleProof, Vec<CompressedRistretto>, Vec<CompressedRistretto>), R1CSError> {
#         // Apply a domain separator with the shuffle parameters to the transcript
#         let k = input.len();
#         transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
#         transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());
# 
#         let mut prover = Prover::new(&pc_gens, transcript);
# 
#         // Construct blinding factors using an RNG.
#         // Note: a non-example implementation would want to operate on existing commitments.
#         let mut blinding_rng = rand::thread_rng();
# 
#         let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input.into_iter()
#             .map(|v| {
#                 prover.commit(*v, Scalar::random(&mut blinding_rng))
#             })
#             .unzip();
# 
#         let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output.into_iter()
#             .map(|v| {
#                 prover.commit(*v, Scalar::random(&mut blinding_rng))
#             })
#             .unzip();
#
#         ShuffleProof::gadget(&mut prover, input_vars, output_vars)?;
#
#         let proof = prover.prove(&bp_gens)?;
#
#         Ok((ShuffleProof(proof), input_commitments, output_commitments))
#     }
# }
# impl ShuffleProof {
#     /// Attempt to verify a `ShuffleProof`.
#     pub fn verify<'a, 'b>(
#         &self,
#         pc_gens: &'b PedersenGens,
#         bp_gens: &'b BulletproofGens,
#         transcript: &'a mut Transcript,
#         input_commitments: &Vec<CompressedRistretto>,
#         output_commitments: &Vec<CompressedRistretto>,
#     ) -> Result<(), R1CSError> {
#         // Apply a domain separator with the shuffle parameters to the transcript
#         let k = input_commitments.len();
#         transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
#         transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());
# 
#         let mut verifier = Verifier::new(transcript);
# 
#         let input_vars: Vec<_> = input_commitments.iter().map(|commitment| {
#             verifier.commit(*commitment)
#         }).collect();
# 
#         let output_vars: Vec<_> = output_commitments.iter().map(|commitment| {
#             verifier.commit(*commitment)
#         }).collect();
#
#         ShuffleProof::gadget(&mut verifier, input_vars, output_vars)?;
#
#         verifier.verify(&self.0, &pc_gens, &bp_gens)
#     }
# }
# fn main() {
// Construct generators. 1024 Bulletproofs generators is enough for 512-size shuffles.
let pc_gens = PedersenGens::default();
let bp_gens = BulletproofGens::new(1024, 1);

// Putting the prover code in its own scope means we can't
// accidentally reuse prover data in the test.
let (proof, in_commitments, out_commitments) = {
    let inputs = [
        Scalar::from(0u64),
        Scalar::from(1u64),
        Scalar::from(2u64),
        Scalar::from(3u64),
    ];
    let outputs = [
        Scalar::from(2u64),
        Scalar::from(3u64),
        Scalar::from(0u64),
        Scalar::from(1u64),
    ];

    let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
    ShuffleProof::prove(
        &pc_gens,
        &bp_gens,
        &mut prover_transcript,
        &inputs,
        &outputs,
    )
    .expect("error during proving")
};

let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
let verification_result = proof.verify(&pc_gens, &bp_gens, &mut verifier_transcript, &in_commitments, &out_commitments);
assert!(verification_result.is_ok(), "{:?}", verification_result);
# }
```
