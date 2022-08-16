#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use rand_core::{CryptoRng, RngCore};

use crate::errors::ProofError;
use crate::inner_product_proof::inner_product;
use crate::linear_proof::LinearProof;
use crate::transcript::TranscriptProtocol;

/// An "accumulator" for the linear proof, which will allow a user to append
/// vectors into the accumulator until they are ready to make the proof.
/// When they call "finalize", the accumulator will multiply the different
/// vectors by different powers of the challenge scalar, concatenate them,
/// and make a proof for the accumulated vector.
pub struct LinearProofAccumulator {
    // Secret scalar vectors a
    pub(crate) a_vec: Vec<Vec<Scalar>>,
    // Public scalar vectors b
    pub(crate) b_vec: Vec<Vec<Scalar>>,
}

pub struct AccumulatedLinearProof {
    pub proof: LinearProof,
    // The accumulated public `b` vector
    pub b_vec: Vec<Scalar>,
    // The list of intermediate `c` values, one per accumulation
    pub c_vec: Vec<Scalar>,
    // The commitment to the accumulated `c` value
    pub C: CompressedRistretto,
}

impl LinearProofAccumulator {
    pub fn create() -> LinearProofAccumulator {
        LinearProofAccumulator {
            a_vec: vec![],
            b_vec: vec![],
        }
    }

    pub fn append(
        &mut self,
        // Secret scalar vector a
        a_vec: Vec<Scalar>,
        // Public scalar vector b
        b_vec: Vec<Scalar>,
    ) -> Result<(), ProofError> {
        if a_vec.len() != b_vec.len() {
            return Err(ProofError::CreationError);
        }
        self.a_vec.push(a_vec);
        self.b_vec.push(b_vec);
        Ok(())
    }

    /// Finalize the accumulation, and produce the accumulated proof.
    pub fn finalize<T: RngCore + CryptoRng>(
        &self,
        transcript: &mut Transcript,
        rng: &mut T,
        // Generator vector
        G: Vec<RistrettoPoint>,
        // Pedersen generator F, for committing to the secret value
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding value
        B: &RistrettoPoint,
    ) -> Result<AccumulatedLinearProof, ProofError> {
        let n = self.a_vec.len();
        if n != self.b_vec.len() {
            return Err(ProofError::CreationError);
        }

        transcript.linearproof_domain_sep(n as u64);

        // Generate the output `c_i` values, and add them to the transcript
        let mut c_vec: Vec<Scalar> = vec![];
        for i in 0..n {
            let c_i = inner_product(&self.a_vec[i], &self.b_vec[i]);
            c_vec.push(c_i);
            transcript.append_scalar(b"c_i", &c_i);
        }

        // Get challenge scalar to combine the a_vec and b_vec vectors
        let x = transcript.challenge_scalar(b"x");
        let mut x_exp = Scalar::one();

        let mut a: Vec<Scalar> = vec![];
        let mut b: Vec<Scalar> = vec![];
        for i in 0..n {
            // Make sure the `a` and `b` vectors getting appended are the same length
            let m = self.a_vec[i].len();
            if m != self.b_vec[i].len() {
                return Err(ProofError::CreationError);
            }

            // Multiply each entry by the proper power of x, and append to the combined vector
            for j in 0..m {
                a.push(self.a_vec[i][j] * x_exp);
                b.push(self.b_vec[i][j] * x_exp);
            }

            // Raise x_exp to the next power of x
            x_exp = x_exp * x;
        }

        // C = <a, G> + r * B + <a, b> * F
        let r = Scalar::random(rng);
        let c = inner_product(&a, &b);
        let C = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
            G.iter().chain(Some(B)).chain(iter::once(F)),
        )
        .compress();

        let linear_proof =
            LinearProof::create(transcript, rng, &C, r, a, b.clone(), G.clone(), &F, &B);

        Ok(AccumulatedLinearProof {
            proof: linear_proof,
            b_vec: b,
            c_vec,
            c_accumulated: c,
            C,
        })
    }

    /// Check that the accumulation was computed correctly:
    /// This function allows the verifier to re-derive the challenge scalar `x`
    /// and check that it was used correctly to accumulate the vectors.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        // Generator vector
        G: Vec<RistrettoPoint>,
        // Pedersen generator F, for committing to the secret value
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding value
        B: &RistrettoPoint,
    ) -> Result<(), ProofError> {
        let n = self.c_vec.len();
        transcript.linearproof_domain_sep(n as u64);
        // Append each of the c_i values to the transcript
        for i in 0..n {
            transcript.append_scalar(b"c_i", &self.c_vec[i]);
        }
        // Get challenge scalar that was used to combine the a_vec and b_vec vectors
        let x = transcript.challenge_scalar(b"x");



        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_chacha::ChaChaRng;
    use rand_core::SeedableRng;

    // n is the number of vectors to aggregate,
    // m is the length of each vector (all vectors will be the same length).
    fn accumulator_test_helper(n: usize, m: usize) {
        let mut rng = ChaChaRng::from_seed([24u8; 32]);

        use crate::generators::{BulletproofGens, PedersenGens};
        let bp_gens = BulletproofGens::new(n * m, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n * m).cloned().collect();

        let pedersen_gens = PedersenGens::default();
        let F = pedersen_gens.B;
        let B = pedersen_gens.B_blinding;

        let mut accumulator = LinearProofAccumulator::create();

        for _ in 0..n {
            // a_i and b_i are the vectors for which we want to prove c_i = <a_i,b_i>
            // a_i is a private vector, b_i is a public vector
            let a_i: Vec<_> = (0..m).map(|_| Scalar::random(&mut rng)).collect();
            let b_i: Vec<_> = (0..m).map(|_| Scalar::random(&mut rng)).collect();
            println!("a_i: {:?}", a_i);
            println!("b_i: {:?}", b_i);
            assert!(accumulator.append(a_i, b_i).is_ok());
        }

        let mut prover_transcript = Transcript::new(b"accumulated linear proof test");

        let accumulated_linear_proof = accumulator
            .finalize(&mut prover_transcript, &mut rng, G.clone(), &F, &B)
            .unwrap();

        let mut verifier_transcript = Transcript::new(b"accumulated linear proof test");
        assert!(accumulated_linear_proof
            .verify(&mut verifier_transcript, &G, &F, &B)
            .is_ok());
    }

    #[test]
    fn test_accumulator_base() {
        accumulator_test_helper(1, 1);
    }

    #[test]
    fn test_accumulator_2_2() {
        accumulator_test_helper(2, 2);
    }

    #[test]
    fn test_accumulator_4_4() {
        accumulator_test_helper(4, 4);
    }

    #[test]
    fn test_accumulator_8_8() {
        accumulator_test_helper(8, 8);
    }

    #[test]
    fn test_accumulator_16_16() {
        accumulator_test_helper(16, 16);
    }
}
