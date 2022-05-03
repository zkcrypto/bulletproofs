#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

// Code below copied from ../tests/one_hot.rs
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

// One-hot gadget

/// A proof-of-one-hotness, which means:
/// - all items in vector x are either 0 or 1
/// - the sum of all items in vector x is 1
///
/// The equation that is checked:
/// <x, r>^2 == <x, r.r>
/// Where:
/// - x is the one-hot vector
/// - r is a vector that is randomly generated after x is committed
/// - r.r is a vector with each entry the square of the corresponding value in r.
/// This should be cheap, since addition and multiplication by known scalars are efficient.
/// This trick is discussed and proven here: https://eprint.iacr.org/2018/707.pdf (p. 29)
///
/// Circuit sketch:
/// xr_left: a LinearConstraint representing <x, r>
/// xr_right: another LinearConstraint representing <x, r>
/// xr_sq_all: the multiplication gate output, from multiplying xr-left and xr-right.
///            represents <x, r>^2.
/// xr_sq_r: the LinearConstraint representing <x, r.r>
/// Final equality constraint: xr_sq_all == xr_sq_r

struct OneHotProof(R1CSProof);

impl OneHotProof {
    fn gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        x: Vec<Variable>,
    ) -> Result<(), R1CSError> {
        let n = x.len();

        let mut xr_left: LinearCombination = Scalar::zero().into();
        let mut xr_right: LinearCombination = Scalar::zero().into();
        let mut xr_sq_r: LinearCombination = Scalar::zero().into();

        cs.specify_randomized_constraints(move |cs| {
            for i in 0..n {
                let r_i = cs.challenge_scalar(b"one-hot challenge");
                xr_left = xr_left + x[i] * r_i;
                xr_right = xr_right + x[i] * r_i;
                xr_sq_r = xr_sq_r + x[i] * r_i * r_i;
            }

            let (_, _, xr_sq_all) = cs.multiply(xr_left, xr_right);
            cs.constrain(xr_sq_all - xr_sq_r);

            Ok(())
        })
    }
}

impl OneHotProof {
    /// Attempt to construct a proof that `input` is a k-hot vector
    ///
    /// Returns a tuple `(proof, input_commitments)`.
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: Vec<u64>,
    ) -> Result<(OneHotProof, Vec<CompressedRistretto>), R1CSError> {
        // Apply a domain separator with the k-hot parameters to the transcript
        // XXX should this be part of the gadget?
        let l = input.len();
        transcript.append_message(b"dom-sep", b"OneHotProof");
        transcript.append_u64(b"len", l as u64);

        let mut prover = Prover::new(&pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input
            .clone()
            .into_iter()
            .map(|x_i| prover.commit(Scalar::from(x_i), Scalar::random(&mut blinding_rng)))
            .unzip();

        OneHotProof::gadget(&mut prover, input_vars)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((OneHotProof(proof), input_commitments))
    }
}

impl OneHotProof {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<CompressedRistretto>,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the k-hot parameters to the transcript
        // XXX should this be part of the gadget?
        let l = input_commitments.len();
        transcript.append_message(b"dom-sep", b"OneHotProof");
        transcript.append_u64(b"len", l as u64);

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|X_i| verifier.commit(*X_i))
            .collect();

        OneHotProof::gadget(&mut verifier, input_vars)?;

        verifier.verify(&self.0, &pc_gens, &bp_gens)?;
        Ok(())
    }
}
// End of copied code.

/// Binary logarithm of maximum k-hot vector length.
const LG_MAX_SHUFFLE_SIZE: usize = 20;
/// Maximum one-hot vector length to benchmark.
const MAX_SHUFFLE_SIZE: usize = 1 << LG_MAX_SHUFFLE_SIZE;
/// Different k-hot vector lengths to try
static TEST_SIZES: [usize; 2] = [524288, 1048576];

fn bench_one_hot_prove(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2 * MAX_SHUFFLE_SIZE, 1);

    c.bench_function_over_inputs(
        "one-hot proof creation",
        move |b, l| {
            // Generate input to prove k-hot
            let mut input: Vec<u64> = vec![0; *l];
            use crate::rand::Rng;
            let mut rng = rand::thread_rng();
            let hot_index = rng.gen_range(0..*l);
            input[hot_index] = 1;

            // Make one-hot proof
            b.iter(|| {
                let mut prover_transcript = Transcript::new(b"OneHotBenchmark");
                OneHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input.clone())
                    .unwrap();
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = one_hot_prove;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_one_hot_prove,
}

fn bench_one_hot_verify(c: &mut Criterion) {
    // Construct Bulletproof generators externally
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2 * MAX_SHUFFLE_SIZE, 1);

    c.bench_function_over_inputs(
        "one-hot proof verification",
        move |b, l| {
            // Generate the proof in its own scope to prevent reuse of
            // prover variables by the verifier
            let (proof, input_commitments) = {
                // Generate input to prove k-hot
                let mut input: Vec<u64> = vec![0; *l];
                use crate::rand::Rng;
                let mut rng = rand::thread_rng();
                let hot_index = rng.gen_range(0..*l);
                input[hot_index] = 1;

                // Make k-hot proof
                let mut prover_transcript = Transcript::new(b"OneHotBenchmark");
                OneHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input).unwrap()
            };

            // Verify kshuffle proof
            b.iter(|| {
                let mut verifier_transcript = Transcript::new(b"OneHotBenchmark");
                proof
                    .verify(
                        &pc_gens,
                        &bp_gens,
                        &mut verifier_transcript,
                        &input_commitments,
                    )
                    .unwrap();
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = one_hot_verify;
    // Lower the sample size to run faster; larger shuffle sizes are
    // long so we're not microbenchmarking anyways.
    config = Criterion::default().sample_size(10);
    targets =
    bench_one_hot_verify,
}

criterion_main!(one_hot_prove, one_hot_verify);
