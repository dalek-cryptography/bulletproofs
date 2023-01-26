#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use core::iter;

use bulletproofs::LinearProof;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

/// Different linear proof vector lengths to try
static TEST_SIZES: [usize; 5] = [64, 128, 256, 512, 1024];

fn create_linear_proof_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "linear proof creation",
        move |bench, n| {
            let mut rng = rand::thread_rng();

            let bp_gens = BulletproofGens::new(*n, 1);
            // Calls `.G()` on generators, which should be a pub(crate) function only.
            // For now, make that function public so it can be accessed from benches.
            // We don't want to use bp_gens directly because we don't need the H generators.
            let G: Vec<RistrettoPoint> = bp_gens.share(0).G(*n).cloned().collect();

            let pedersen_gens = PedersenGens::default();
            let F = pedersen_gens.B;
            let B = pedersen_gens.B_blinding;

            // a and b are the vectors for which we want to prove c = <a,b>
            let a: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();

            let mut transcript = Transcript::new(b"LinearProofBenchmark");

            // C = <a, G> + r * B + <a, b> * F
            let r = Scalar::random(&mut rng);
            let c = inner_product(&a, &b);
            let C = RistrettoPoint::vartime_multiscalar_mul(
                a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
                G.iter().chain(iter::once(&B)).chain(iter::once(&F)),
            )
            .compress();

            // Make linear proof
            bench.iter(|| {
                LinearProof::create(
                    &mut transcript,
                    &mut rng,
                    &C,
                    r,
                    a.clone(),
                    b.clone(),
                    G.clone(),
                    &F,
                    &B,
                )
                .unwrap();
            })
        },
        TEST_SIZES,
    );
}

/// Copied from src/inner_product_proof.rs
/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

criterion_group! {
    name = create_linear_proof;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    create_linear_proof_helper,
}

fn linear_verify(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "linear proof verification",
        move |bench, n| {
            let bp_gens = BulletproofGens::new(*n, 1);
            let mut rng = rand::thread_rng();

            // Calls `.G()` on generators, which should be a pub(crate) function only.
            // For now, make that function public so it can be accessed from benches.
            // We can't simply use bp_gens directly because we don't need the H generators.
            let G: Vec<RistrettoPoint> = bp_gens.share(0).G(*n).cloned().collect();
            let pedersen_gens = PedersenGens::default();
            let F = pedersen_gens.B;
            let B = pedersen_gens.B_blinding;

            let b: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();

            // Generate the proof in its own scope to prevent reuse of
            // prover variables by the verifier
            let (proof, C) = {
                // a and b are the vectors for which we want to prove c = <a,b>
                let a: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();

                let mut transcript = Transcript::new(b"LinearProofBenchmark");

                // C = <a, G> + r * B + <a, b> * F
                let r = Scalar::random(&mut rng);
                let c = inner_product(&a, &b);
                let C = RistrettoPoint::vartime_multiscalar_mul(
                    a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
                    G.iter().chain(iter::once(&B)).chain(iter::once(&F)),
                )
                .compress();

                let proof = LinearProof::create(
                    &mut transcript,
                    &mut rng,
                    &C,
                    r,
                    a.clone(),
                    b.clone(),
                    G.clone(),
                    &F,
                    &B,
                )
                .unwrap();

                (proof, C)
            };

            // Verify linear proof
            bench.iter(|| {
                let mut verifier_transcript = Transcript::new(b"LinearProofBenchmark");
                proof
                    .verify(&mut verifier_transcript, &C, &G, &F, &B, b.clone())
                    .unwrap();
            });
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = verify_linear_proof;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    linear_verify,
}

criterion_main!(create_linear_proof, verify_linear_proof);
