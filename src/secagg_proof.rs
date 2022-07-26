#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use rand_core::{CryptoRng, RngCore};

use crate::linear_proof::LinearProof;
use crate::transcript::TranscriptProtocol;
use crate::inner_product_proof::inner_product;


/// A SecAgg proof, which is a combination of linear proofs.
///
/// Prove that <a, b_i> + <x, y_i> = c_i for i in [0, l) where:
/// - b_i and y_i are public vectors (therefore b, y are public matrices)
/// - c_i is a public scalar (therefore c is a public vector)
/// - a and x are secret vectors where a, x are the same across all constraints,
///   with commitments A, X defined by:
///   A = r_a * B + <a, G[:len(a)]>, X = r_x * B + <x, G[len(a):]>
///
/// The proof "accumulates" the b_i and y_i public vectors, into a vector:
/// acc = b_0 || y_0 + (b_1 || y_1)*rho + (b_2 || y_2)*rho^2 + ...
/// where rho is a random challenge scalar derived using the Fiat-Shamir protocol.
/// This public vector is then used as the input to a linear proof.
///
/// The commitment to the combination of c_i values is C:
/// C = r_total * B + < a || x, acc > * F + < a || x, G>
/// where r_total = r_a + r_x and < a || x, G > = < a, G[:half]> + <x, G[half:]>
/// so C = com_x + com_y + < a || x, acc > * F
#[derive(Clone, Debug)]
pub struct SecAggProof {
	linear_proof: LinearProof,
	a_commit: CompressedRistretto,
	x_commit: CompressedRistretto,
}

impl SecAggProof {
	pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        // Secret scalar vector a
        mut a: Vec<Scalar>,
        // Secret scalar vector x
        mut x: Vec<Scalar>,
        // Public scalar matrix b
        mut b: Vec<Vec<Scalar>>,
        // Public scalar matrix y
        mut y: Vec<Vec<Scalar>>,        
        // Generator vector
        mut G_vec: Vec<RistrettoPoint>,
        // Pedersen generator F, for committing to the secret values
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding values
        B: &RistrettoPoint,
	) -> SecAggProof {
		let a_len = a.len();
		let x_len = x.len();
		let acc = b.len();

		// The concatenated a and x lengths must be a power of two
		assert!((a_len + x_len).is_power_of_two());
		// The public scalar matrices b and y must have the same length
		assert_eq!(acc, y.len());

		// Create slice G, backed by its respective vector, for reslicing
		let mut G = &mut G_vec[..];
		let (G_a, G_x) = G.split_at_mut(a_len);

		// Make commitments to secret vectors a and x
		// A = r_a * B + <a, G[:len(a)]>
		let r_a = Scalar::random(rng);
        let A = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(iter::once(r_a)),
            G_a.iter().chain(iter::once(B)),
        ).compress();
        // X = r_x * B + <x, G[len(a):]>
		let r_x = Scalar::random(rng);
        let X = RistrettoPoint::vartime_multiscalar_mul(
            x.iter().chain(iter::once(r_x)),
            G_x.iter().chain(iter::once(B)),
        ).compress();

        // Append the lengths and private commitments to the transcript
        transcript.append_scalar(b"a len", a_len);
        transcript.append_scalar(b"x len", x_len);
        transcript.append_scalar(b"acc", acc);
        transcript.append_point(b"A", A);
        transcript.append_point(b"X", X);

        for i in 0..acc {
        	assert_eq!(a_len, b[i].len());
        	assert_eq!(x_len, y[i].len());
        	let c_i = inner_product(&a, b[i]) + inner_product(&x, y[i]);

        }


	}
}

