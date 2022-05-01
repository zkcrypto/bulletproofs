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
static TEST_SIZES:  [usize; 14] = [128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576];

fn create_linear_proof_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "linear proof creation",
        move |bench, n| {
            let mut rng = rand::thread_rng();

            let bp_gens = BulletproofGens::new(*n, 1);
            // Calls `.G()` on generators, which should be a pub(crate) function only.
            // For now, make that function public so it can be accessed from benches.
            // We can't simply use bp_gens directly because we don't need the H generators.
            let G: Vec<RistrettoPoint> = bp_gens.share(0).G(*n).cloned().collect();

            let pedersen_gens = PedersenGens::default();
            let F = pedersen_gens.B;
            let B = pedersen_gens.B_blinding;

            // a and b are the vectors for which we want to prove c = <a,b>
            let a: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<_> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();

            let mut transcript = Transcript::new(b"linearprooftest");

            // C = <a, G> + r * B + <a, b> * F
            let r = Scalar::random(&mut rng);
            let c = inner_product(&a, &b);
            let C = RistrettoPoint::vartime_multiscalar_mul(
                    a.iter()
                        .chain(iter::once(&r))
                        .chain(iter::once(&c)),
                    G.iter()
                        .chain(iter::once(&B))
                        .chain(iter::once(&F)),
                )
                .compress();

            // Make k-hot proof
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
                );
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

/*
fn linear_verify(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2 * MAX_SHUFFLE_SIZE, 1);

    c.bench_function_over_inputs(
        "k-hot proof verification",
        move |b, l| {
            // Generate the proof in its own scope to prevent reuse of
            // prover variables by the verifier
            let (proof, input_commitments) = {
                // Currently just proving k=1, aka one-hot vector.
                let k = 1;
                // Generate input to prove k-hot
                let mut input: Vec<u64> = vec![0; *l];
                use crate::rand::Rng;
                let mut rng = rand::thread_rng();
                for _ in 0..k {
                    let hot_index = rng.gen_range(0..*l);
                    input[hot_index] = 1;
                }

                // Make k-hot proof
                let mut prover_transcript = Transcript::new(b"KHotBenchmark");
                KHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input, k)
                    .unwrap()
            };

            // Verify kshuffle proof
            b.iter(|| {
                let mut verifier_transcript = Transcript::new(b"KHotBenchmark");
                proof
                    .verify(
                        &pc_gens,
                        &bp_gens,
                        &mut verifier_transcript,
                        &input_commitments,
                        1
                    )
                    .unwrap();
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = khot_verify;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_khot_verify,
}
*/

criterion_main!(create_linear_proof);
