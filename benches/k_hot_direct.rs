#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

use rand;
use rand::Rng;

use curve25519_dalek::scalar::Scalar;

use merlin::Transcript;

use bulletproofs::KHotProof;
use bulletproofs::{BulletproofGens, PedersenGens};

/// Run with `cargo bench k_hot_direct --features="yoloproofs"`
/// Different k-hot vector lengths to try
static TEST_SIZES: [usize; 6] = [1, 2, 32, 64, 1024, 16384];

fn create_k_hot_direct_helper(n: usize, c: &mut Criterion) {
    let k = 1;
    let label = format!("{}-bit {}-hot proof creation", n, k);

    c.bench_function_over_inputs(
        &label,
        move |b, _l| {
            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(n, 1);

            let mut secret_vec = vec![0; n];
            // TODO: choose index randomly
            secret_vec[n-1] = 1;

            b.iter(|| {
                // Each proof creation requires a clean transcript.
            let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                KHotProof::prove(
                    &bp_gens,
                    &pc_gens,
                    &mut transcript,
                    secret_vec.clone(),
                )
            })
        },
        TEST_SIZES,
    );
}

fn create_k_hot_direct_n_8(c: &mut Criterion) {
    create_k_hot_direct_helper(8, c);
}

fn create_k_hot_direct_n_16(c: &mut Criterion) {
    create_k_hot_direct_helper(16, c);
}

fn create_k_hot_direct_n_32(c: &mut Criterion) {
    create_k_hot_direct_helper(32, c);
}

fn create_k_hot_direct_n_64(c: &mut Criterion) {
    create_k_hot_direct_helper(64, c);
}

fn create_k_hot_direct_n_131072(c: &mut Criterion) {
    create_k_hot_direct_helper(131072, c);
}

fn create_k_hot_direct_n_524288(c: &mut Criterion) {
    create_k_hot_direct_helper(524288, c);
}

fn create_k_hot_direct_n_1048576(c: &mut Criterion) {
    create_k_hot_direct_helper(1048576, c);
}

fn verify_k_hot_direct_helper(n: usize, c: &mut Criterion) {
    let k = 1;
    let label = format!("{}-bit {}-hot proof verification", n, k);
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(n, 1);

    c.bench_function_over_inputs(
        &label,
        move |b, _l| {
            let proof = {

                let mut secret_vec = vec![0; n];
                // TODO: choose index randomly
                secret_vec[0] = 1;

                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                KHotProof::prove(
                    &bp_gens,
                    &pc_gens,
                    &mut transcript,
                    secret_vec,
                ).unwrap()
            };
            

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"KHotDirectBenchmark");

                proof.verify(&bp_gens, &pc_gens, &mut transcript, n)
            });
        },
        TEST_SIZES,
    );
}

fn verify_k_hot_direct_n_8(c: &mut Criterion) {
    verify_k_hot_direct_helper(8, c);
}

fn verify_k_hot_direct_n_16(c: &mut Criterion) {
    verify_k_hot_direct_helper(16, c);
}

fn verify_k_hot_direct_n_32(c: &mut Criterion) {
    verify_k_hot_direct_helper(32, c);
}

fn verify_k_hot_direct_n_64(c: &mut Criterion) {
    verify_k_hot_direct_helper(64, c);
}

fn verify_k_hot_direct_n_131072(c: &mut Criterion) {
    verify_k_hot_direct_helper(131072, c);
}

fn verify_k_hot_direct_n_524288(c: &mut Criterion) {
    verify_k_hot_direct_helper(524288, c);
}

fn verify_k_hot_direct_n_1048576(c: &mut Criterion) {
    verify_k_hot_direct_helper(1048576, c);
}

criterion_group! {
    name = create_k_hot_direct;
    config = Criterion::default().sample_size(10);
    targets =
    create_k_hot_direct_n_8,
    create_k_hot_direct_n_16,
    create_k_hot_direct_n_32,
    create_k_hot_direct_n_64,
    // create_k_hot_direct_n_131072,
    // create_k_hot_direct_n_524288,
    // create_k_hot_direct_n_1048576,
}

criterion_group! {
    name = verify_k_hot_direct;
    config = Criterion::default().sample_size(10);
    targets =
    verify_k_hot_direct_n_8,
    verify_k_hot_direct_n_16,
    verify_k_hot_direct_n_32,
    verify_k_hot_direct_n_64,
    // verify_k_hot_direct_n_131072,
    // verify_k_hot_direct_n_524288,
    // verify_k_hot_direct_n_1048576,
}

criterion_main!(create_k_hot_direct, verify_k_hot_direct);
