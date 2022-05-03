#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

use merlin::Transcript;

use bulletproofs::KHotProof;
use bulletproofs::{BulletproofGens, PedersenGens};

/// Run with `cargo bench --bench=k_hot_direct --features="yoloproofs"`
/// Different k-hot vector lengths to try
static TEST_SIZES: [usize; 6] = [1, 2, 32, 64, 1024, 16384];

fn create_k_hot_direct_helper(c: &mut Criterion) {
    let k = 1;
    let label = format!("{}-hot proof creation", k);

    c.bench_function_over_inputs(
        &label,
        move |b, n| {
            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(*n, 1);

            let mut secret_vec = vec![0; *n];
            // TODO: choose index randomly
            secret_vec[n - 1] = 1;

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                KHotProof::prove(&bp_gens, &pc_gens, &mut transcript, secret_vec.clone())
            })
        },
        TEST_SIZES,
    );
}

fn verify_k_hot_direct_helper(c: &mut Criterion) {
    let k = 1;
    let label = format!("{}-hot proof verification", k);
    let pc_gens = PedersenGens::default();

    // Make a generator that will accomodate the largest test case
    let max_test_size = TEST_SIZES.iter().max().unwrap();
    let bp_gens = BulletproofGens::new(*max_test_size, 1);

    c.bench_function_over_inputs(
        &label,
        move |b, n| {
            let proof = {
                let mut secret_vec = vec![0; *n];
                // TODO: choose index randomly
                secret_vec[0] = 1;

                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                KHotProof::prove(&bp_gens, &pc_gens, &mut transcript, secret_vec).unwrap()
            };

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                proof.verify(&bp_gens, &pc_gens, &mut transcript, *n)
            });
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = create_k_hot_direct;
    config = Criterion::default().sample_size(10);
    targets =
    create_k_hot_direct_helper,
}

criterion_group! {
    name = verify_k_hot_direct;
    config = Criterion::default().sample_size(10);
    targets =
    verify_k_hot_direct_helper,
}

criterion_main!(create_k_hot_direct, verify_k_hot_direct);
