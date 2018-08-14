#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate rand;
use rand::{rngs::OsRng, Rng};

extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;

extern crate bulletproofs;
use bulletproofs::Transcript;
use bulletproofs::RangeProof;
use bulletproofs::{Generators, PedersenGenerators};

static AGGREGATION_SIZES: [usize; 6] = [1, 2, 4, 8, 16, 32];

fn create_aggregated_rangeproof_helper(n: usize, c: &mut Criterion) {
    let label = format!("Aggregated {}-bit rangeproof creation", n);

    c.bench_function_over_inputs(
        &label,
        move |b, &&m| {
            let generators = Generators::new(PedersenGenerators::default(), n, m);
            let mut rng = OsRng::new().unwrap();

            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");

                RangeProof::prove_multiple(
                    &generators,
                    &mut transcript,
                    &mut rng,
                    &values,
                    &blindings,
                    n,
                )
            })
        },
        &AGGREGATION_SIZES,
    );
}

fn create_aggregated_rangeproof_n_8(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(8, c);
}

fn create_aggregated_rangeproof_n_16(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(16, c);
}

fn create_aggregated_rangeproof_n_32(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(32, c);
}

fn create_aggregated_rangeproof_n_64(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(64, c);
}

fn verify_aggregated_rangeproof_helper(n: usize, c: &mut Criterion) {
    let label = format!("Aggregated {}-bit rangeproof verification", n);

    c.bench_function_over_inputs(
        &label,
        move |b, &&m| {
            let generators = Generators::new(PedersenGenerators::default(), n, m);
            let mut rng = OsRng::new().unwrap();

            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");
            let proof = RangeProof::prove_multiple(
                &generators,
                &mut transcript,
                &mut rng,
                &values,
                &blindings,
                n,
            ).unwrap();

            // XXX would be nice to have some convenience API for this
            let pg = &generators.pedersen_gens;
            let value_commitments: Vec<_> = values
                .iter()
                .zip(blindings.iter())
                .map(|(&v, &v_blinding)| pg.commit(Scalar::from(v), v_blinding))
                .collect();

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");

                proof.verify(
                    &value_commitments,
                    &generators,
                    &mut transcript,
                    &mut rng,
                    n,
                )
            });
        },
        &AGGREGATION_SIZES,
    );
}

fn verify_aggregated_rangeproof_n_8(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(8, c);
}

fn verify_aggregated_rangeproof_n_16(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(16, c);
}

fn verify_aggregated_rangeproof_n_32(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(32, c);
}

fn verify_aggregated_rangeproof_n_64(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(64, c);
}

criterion_group!{
    name = create_rp;
    config = Criterion::default().sample_size(10);
    targets =
    create_aggregated_rangeproof_n_8,
    create_aggregated_rangeproof_n_16,
    create_aggregated_rangeproof_n_32,
    create_aggregated_rangeproof_n_64,
}

criterion_group!{
    name = verify_rp;
    config = Criterion::default();
    targets =
    verify_aggregated_rangeproof_n_8,
    verify_aggregated_rangeproof_n_16,
    verify_aggregated_rangeproof_n_32,
    verify_aggregated_rangeproof_n_64,
}

criterion_main!(create_rp, verify_rp);
