#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// Run with `cargo bench --bench=k_hot_direct --features="yoloproofs"`
/// Different k-hot vector lengths to try
static TEST_SIZES: [usize; 32] = [
    41, 64, 103, 128, 164, 205, 256, 328, 410, 512, 656, 820, 1024, 1311, 1639, 2048, 2622, 3277,
    4096, 6554, 8192, 10486, 13108, 16384, 24576, 32768, 40960, 57344, 65536, 81920, 131072,
    155648,
];

// Blinded IPP gadget
// Proves that <a, b> = c where a, b, c are secret.
// Has a commitment A_I = h^alpha * vec(g)^vec(a) * vec(h)^vec(b)

/// A blinded inner product proof
struct BlindedIPProof(R1CSProof);

impl BlindedIPProof {
    /// Construct a proof that <a, b> = c
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        k: usize,
    ) -> Result<BlindedIPProof, R1CSError> {
        transcript.append_message(b"dom-sep", b"BlindedIPProof");
        transcript.append_u64(b"k", k as u64);

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, transcript);

        // 2. Generate arbitrary inputs to the blinded inner product argument.
        // Note that we don't have to explicitly commit to the inputs,
        // as they will be implicily committed to within the proof via A_I and A_O.
        let a: Vec<Scalar> = (0..k)
            .map(|_| Scalar::random(&mut rand::thread_rng()))
            .collect();
        let b: Vec<Scalar> = (0..k)
            .map(|_| Scalar::random(&mut rand::thread_rng()))
            .collect();
        let c: Scalar = a.iter().zip(b.iter()).map(|(a_i, b_i)| a_i * b_i).sum();

        // 3. Build a CS
        let mut sum_o = LinearCombination::from(prover.allocate(Some(c))?);
        for i in 0..a.len() {
            // Create low-level variables and add them to constraints
            let (_, _, o) = prover.allocate_multiplier(Some((a[i], b[i])))?;

            // Add `o` to the linear combination sum_o
            // in order to form the following constraint by the end of the loop:
            // 0 = c - Sum_i(x_i * y_i)
            // which gives us: c = Sum_i(x_i * y_i)
            sum_o = sum_o - o;
        }
        // Enforce that 0 = c - Sum_i(x_i * y_i)
        prover.constrain(sum_o);

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok(BlindedIPProof(proof))
    }

    /// Attempt to verify a blinded inner product proof.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        k: usize,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"BlindedIPProof");
        transcript.append_u64(b"k", k as u64);

        // 1. Create a verifier
        let mut verifier = Verifier::new(transcript);

        // 2. Don't need to make or receive commitments to the inputs,
        // as they are implicitly committed to within the proof via A_I and A_O.

        // 3. Build a CS
        let mut sum_o = LinearCombination::from(verifier.allocate(None)?);
        for _ in 0..k {
            // Create low-level variables and add them to constraints
            let (_, _, o) = verifier.allocate_multiplier(None)?;

            // Add `o` to the linear combination sum_o
            // in order to form the following constraint by the end of the loop:
            // 0 = c - Sum_i(x_i * y_i)
            // which gives us: c = Sum_i(x_i * y_i)
            sum_o = sum_o - o;
        }
        // Enforce that 0 = c - Sum_i(x_i * y_i)
        verifier.constrain(sum_o);

        // 4. Verify proof
        verifier.verify(&self.0, &pc_gens, &bp_gens)
    }
}

fn bench_blinded_ipp_prove(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    // Make a generator that will accomodate the largest test case
    let max_test_size = TEST_SIZES.iter().max().unwrap();
    let bp_gens = BulletproofGens::new(*max_test_size * 2, 1);

    c.bench_function_over_inputs(
        "blinded inner product proof creation",
        move |b, n| {
            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"BlindedIPPBenchmark");

                BlindedIPProof::prove(&pc_gens, &bp_gens, &mut transcript, *n)
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = blinded_ipp_prove;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_blinded_ipp_prove,
}

fn bench_blinded_ipp_verify(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    // Make a generator that will accomodate the largest test case
    let max_test_size = TEST_SIZES.iter().max().unwrap();
    let bp_gens = BulletproofGens::new(*max_test_size * 2, 1);

    c.bench_function_over_inputs(
        "blinded inner product proof verification",
        move |b, n| {
            let proof = {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"BlindedIPPBenchmark");

                BlindedIPProof::prove(&pc_gens, &bp_gens, &mut transcript, *n).unwrap()
            };

            println!("proof size: {:?} bytes", proof.0.serialized_size());

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"BlindedIPPBenchmark");

                proof.verify(&pc_gens, &bp_gens, &mut transcript, *n)
            });
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = blinded_ipp_verify;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_blinded_ipp_verify,
}

criterion_main!(blinded_ipp_prove, blinded_ipp_verify);
