#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

// Code below copied from ../tests/k_hot.rs
//
// Ideally we wouldn't duplicate it, but AFAIK criterion requires a
// seperate benchmark harness, while the test code uses a different
// test harness, so I (cathieyun) just copied the code over.  It
// should not be edited here.  In the future it would be good if
// someone wants to figure a way to use #[path] attributes or
// something to avoid the duplication.

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

// k-hot gadget

/// A proof-of-k-hotness, which means:
/// - all items in vector x are either 0 or 1
/// - the sum of all items in vector x is k
struct KHotProof(R1CSProof);

impl KHotProof {
    fn gadget<CS: ConstraintSystem>(
        cs: &mut CS,
        x: Vec<Variable>,
        x_assignment: Option<Vec<u64>>,
        k: u64,
    ) -> Result<(), R1CSError> {
        let n = x.len();

        // Allocate a variable to represent k, for the k-sum.
        let hotness = cs.allocate(Scalar::from(k).into())?;
        // Turn it variable a linear constraint to check that it is equal the vector sum.
        let mut hot_constr: LinearCombination = hotness.into();

        for i in 0..n {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate_multiplier(x_assignment.as_ref().map(|x_open| {
                let bit: u64 = x_open[i];
                ((1 - bit).into(), bit.into())
            }))?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - 1u64));

            // Add `-b_i` to the linear combination
            // in order to form the following constraint by the end of the loop:
            // hotness = k - Sum(b_i, i = 0..n-1)
            hot_constr = hot_constr - b;
        }

        // Enforce that hot_constr = 0, so that k = Sum(b_i, i = 0..n-1)
        cs.constrain(hot_constr);

        Ok(())
    }
}

impl KHotProof {
    /// Attempt to construct a proof that `input` is a k-hot vector
    ///
    /// Returns a tuple `(proof, input_commitments)`.
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: Vec<u64>,
        k: u64,
    ) -> Result<(KHotProof, Vec<CompressedRistretto>), R1CSError> {
        // Apply a domain separator with the k-hot parameters to the transcript
        // XXX should this be part of the gadget?
        let l = input.len();
        transcript.append_message(b"dom-sep", b"kHotProof");
        transcript.append_u64(b"len", l as u64);
        transcript.append_u64(b"k", k as u64);

        let mut prover = Prover::new(&pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input
            .clone()
            .into_iter()
            .map(|v| prover.commit(Scalar::from(v), Scalar::random(&mut blinding_rng)))
            .unzip();

        KHotProof::gadget(&mut prover, input_vars, Some(input), k)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((KHotProof(proof), input_commitments))
    }
}

impl KHotProof {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<CompressedRistretto>,
        k: u64,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the k-hot parameters to the transcript
        // XXX should this be part of the gadget?
        let l = input_commitments.len();
        transcript.append_message(b"dom-sep", b"kHotProof");
        transcript.append_u64(b"len", l as u64);
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        KHotProof::gadget(&mut verifier, input_vars, None, k)?;

        verifier.verify(&self.0, &pc_gens, &bp_gens)?;
        Ok(())
    }
}
// End of copied code.

/// Binary logarithm of maximum k-hot vector length.
const LG_MAX_SHUFFLE_SIZE: usize = 14;
/// Maximum k-hot vector length to benchmark.
const MAX_SHUFFLE_SIZE: usize = 1 << LG_MAX_SHUFFLE_SIZE;
/// Different k-hot vector lengths to try
// static TEST_SIZES: [usize; 6] = [1, 2, 32, 64, 1024, 16384];
static TEST_SIZES: [usize; 0] = [];

fn bench_khot_prove(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2 * MAX_SHUFFLE_SIZE, 1);

    c.bench_function_over_inputs(
        "k-hot proof creation",
        move |b, l| {
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
            b.iter(|| {
                let mut prover_transcript = Transcript::new(b"KHotBenchmark");
                KHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input.clone(), k)
                    .unwrap();
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = khot_prove;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_khot_prove,
}

fn bench_khot_verify(c: &mut Criterion) {
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
                KHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input, k).unwrap()
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
                        1,
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

criterion_main!(khot_prove, khot_verify);
