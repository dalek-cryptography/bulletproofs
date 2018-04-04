#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate rand;
use rand::{OsRng, Rng};

extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;

extern crate ristretto_bulletproofs;
use ristretto_bulletproofs::{CommitmentGenerators, Generators};
use ristretto_bulletproofs::ProofTranscript;
use ristretto_bulletproofs::RangeProof;

fn bench_create_helper(n: usize, c: &mut Criterion) {
    c.bench_function(&format!("create_rangeproof_n_{}", n), move |b| {
        let generators = Generators::new(CommitmentGenerators::generators(), n, 1);
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
        let generators = Generators::new(CommitmentGenerators::generators(), n, 1);
        let mut rng = OsRng::new().unwrap();

        let mut transcript = ProofTranscript::new(b"RangeproofTest");
        let v: u64 = rng.gen_range(0, (1 << (n - 1)) - 1);
        let v_blinding = Scalar::random(&mut rng);

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

            rp.verify(generators.share(0), &mut transcript, &mut rng, n)
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

criterion_main!(create_rp, verify_rp);
