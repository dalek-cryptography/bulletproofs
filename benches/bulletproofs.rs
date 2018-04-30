#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate rand;
use rand::{OsRng, Rng};

extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;

extern crate ristretto_bulletproofs;
use ristretto_bulletproofs::ProofTranscript;
use ristretto_bulletproofs::RangeProof;
use ristretto_bulletproofs::{Generators, PedersenGenerators};

fn bench_create_helper(n: usize, c: &mut Criterion) {
    c.bench_function(&format!("create_rangeproof_n_{}", n), move |b| {
        let generators = Generators::new(PedersenGenerators::default(), n, 1);
        let mut rng = OsRng::new().unwrap();

        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        b.iter(|| {
            // Each proof creation requires a clean transcript.
            let mut transcript = ProofTranscript::new(b"RangeproofTest");

            RangeProof::generate_proof(
                generators.share(0),
                &mut transcript,
                &mut rng,
                n,
                v,
                &v_blinding,
            )
        })
    });
}

fn bench_verify_helper(n: usize, c: &mut Criterion) {
    c.bench_function(&format!("verify_rangeproof_n_{}", n), move |b| {
        let pg = PedersenGenerators::default();
        let generators = Generators::new(pg.clone(), n, 1);
        let mut rng = OsRng::new().unwrap();

        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

        let vc = pg.commit(Scalar::from_u64(v), v_blinding);

        let rp = RangeProof::generate_proof(
            generators.share(0),
            &mut transcript,
            &mut rng,
            n,
            v,
            &v_blinding,
        );

        b.iter(|| {
            // Each verification requires a clean transcript.
            let mut transcript = ProofTranscript::new(b"RangeproofTest");

            rp.verify(&vc, generators.share(0), &mut transcript, &mut rng, n)
        });
    });
}

fn create_rp_64(c: &mut Criterion) {
    bench_create_helper(64, c);
}

fn create_rp_32(c: &mut Criterion) {
    bench_create_helper(32, c);
}

fn create_rp_16(c: &mut Criterion) {
    bench_create_helper(16, c);
}

fn create_rp_8(c: &mut Criterion) {
    bench_create_helper(8, c);
}

criterion_group!{
    name = create_rp;
    config = Criterion::default();
    targets = create_rp_8, create_rp_16, create_rp_32, create_rp_64
}

fn verify_rp_64(c: &mut Criterion) {
    bench_verify_helper(64, c);
}

fn verify_rp_32(c: &mut Criterion) {
    bench_verify_helper(32, c);
}

fn verify_rp_16(c: &mut Criterion) {
    bench_verify_helper(16, c);
}

fn verify_rp_8(c: &mut Criterion) {
    bench_verify_helper(8, c);
}

criterion_group!{
    name = verify_rp;
    config = Criterion::default();
    targets = verify_rp_8, verify_rp_16, verify_rp_32, verify_rp_64
}

static AGGREGATION_SIZES: [usize; 6] = [1, 2, 4, 8, 16, 32];

fn create_aggregated_rangeproof_helper(n: usize, c: &mut Criterion) {
    use ristretto_bulletproofs::aggregated_range_proof::SinglePartyAggregator;

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
                let mut transcript = ProofTranscript::new(b"AggregateRangeProofBenchmark");

                SinglePartyAggregator::generate_proof(
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

fn create_aggregated_rangeproof_n_32(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(32, c);
}

fn create_aggregated_rangeproof_n_64(c: &mut Criterion) {
    create_aggregated_rangeproof_helper(64, c);
}

fn verify_aggregated_rangeproof_helper(n: usize, c: &mut Criterion) {
    use ristretto_bulletproofs::aggregated_range_proof::SinglePartyAggregator;

    let label = format!("Aggregated {}-bit rangeproof verification", n);

    c.bench_function_over_inputs(
        &label,
        move |b, &&m| {
            let generators = Generators::new(PedersenGenerators::default(), n, m);
            let mut rng = OsRng::new().unwrap();

            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            let mut transcript = ProofTranscript::new(b"AggregateRangeProofBenchmark");
            let proof = SinglePartyAggregator::generate_proof(
                &generators,
                &mut transcript,
                &mut rng,
                &values,
                &blindings,
                n,
            ).unwrap();

            // XXX would be nice to have some convenience API for this
            let pg = &generators.all().pedersen_generators;
            let value_commitments: Vec<_> = values
                .iter()
                .zip(blindings.iter())
                .map(|(&v, &v_blinding)| pg.commit(Scalar::from_u64(v), v_blinding))
                .collect();

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = ProofTranscript::new(b"AggregateRangeProofBenchmark");

                proof.verify(
                    &value_commitments,
                    generators.all(),
                    &mut transcript,
                    &mut rng,
                    n,
                    m,
                )
            });
        },
        &AGGREGATION_SIZES,
    );
}

fn verify_aggregated_rangeproof_n_32(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(32, c);
}

fn verify_aggregated_rangeproof_n_64(c: &mut Criterion) {
    verify_aggregated_rangeproof_helper(64, c);
}

criterion_group!{
    name = aggregate_rp;
    config = Criterion::default();
    targets =
    create_aggregated_rangeproof_n_32,
    create_aggregated_rangeproof_n_64,
    verify_aggregated_rangeproof_n_32,
    verify_aggregated_rangeproof_n_64
}

criterion_main!(create_rp, verify_rp, aggregate_rp);
