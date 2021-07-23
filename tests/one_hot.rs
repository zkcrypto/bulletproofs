#![allow(non_snake_case)]

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
            };

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
    ) -> Result<
        (
            OneHotProof,
            Vec<CompressedRistretto>,
        ),
        R1CSError,
    > {
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

fn one_hot_helper(l: usize) {
    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((l*2).next_power_of_two(), 1);

    let (proof, input_commitments) = {
        use rand::Rng;

        // Randomly generate inputs 
        let mut input: Vec<u64> = vec![0; l];
        let mut rng = rand::thread_rng();
        
        let one_hot_index = rng.gen_range(0..l);
        input[one_hot_index] = 1;
        
        let mut prover_transcript = Transcript::new(b"OneHotProofTest");
        OneHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"OneHotProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
            )
            .is_ok());
    }
}


#[test]
fn one_hot_gadget_test_1() {
    one_hot_helper(1);
}

#[test]
fn one_hot_gadget_test_2() {
    one_hot_helper(2);
}

#[test]
fn one_hot_gadget_test_16() {
    one_hot_helper(16);
}

#[test]
fn one_hot_gadget_test_128() {
    one_hot_helper(128);
}

#[test]
fn one_hot_gadget_test_1024() {
    one_hot_helper(1024);
}

#[test]
fn one_hot_gadget_test_16384() {
    one_hot_helper(16384);
}

#[test]
fn one_hot_gadget_fail_all_ones() {
    let l : usize = 1024;
    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((l*2).next_power_of_two(), 1);

    let (proof, input_commitments) = {
        // Generate a vector of all ones (should fail)
        let input: Vec<u64> = vec![1; l];

        let mut prover_transcript = Transcript::new(b"OneHotProofTest");
        OneHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"OneHotProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
            )
            .is_err());
    }
}

#[test]
fn one_hot_gadget_fail_large_k() {
    let l : usize = 1024;
    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((l*2).next_power_of_two(), 1);

    let (proof, input_commitments) = {
        // Generate a vector of all ones (should fail)
        let mut input: Vec<u64> = vec![0; l];
        input[12] = 15;

        let mut prover_transcript = Transcript::new(b"OneHotProofTest");
        OneHotProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, input).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"OneHotProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
            )
            .is_err());
    }
}
