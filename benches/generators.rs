use bulletproofs::{BulletproofGens, PedersenGens};
use criterion::BenchmarkId;
use criterion::{Criterion, criterion_main, criterion_group};

fn pc_gens(c: &mut Criterion) {
    c.bench_function("PedersenGens::new", |b| b.iter(|| PedersenGens::default()));
}

fn bp_gens(c: &mut Criterion) {
    let mut group = c.benchmark_group("BulletproofGens::new");
    for size in (0..10).map(|i| 2 << i) {
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &size,
            |b, &size| b.iter(|| BulletproofGens::new(size, 1)),
        );
    }
}

criterion_group! {
    bp,
    bp_gens,
    pc_gens,
}

criterion_main!(bp);
