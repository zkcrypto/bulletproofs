#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use rand_core::{CryptoRng, RngCore};

use crate::inner_product_proof::inner_product;
use crate::linear_proof::LinearProof;
use crate::transcript::TranscriptProtocol;

/// A SecAgg proof, which is a combination of linear proofs.
///
/// Prove that <a, b_i> + <x, y_i> = c_i for i in [0, l) where:
/// - b_i and y_i are public vectors (therefore b, y are public matrices)
/// - c_i is a public scalar (therefore c is a public vector)
/// - a and x are secret vectors where a, x are the same across all constraints,
///   with commitments A, X defined by:
///   A = r_a * B + <a, G[:len(a)]>, X = r_x * B + <x, G[len(a):]>
///
/// The proof accumulates the b_i and y_i public vectors, into a vector:
/// acc_vec = b_0 || y_0 + (b_1 || y_1)*z + (b_2 || y_2)*z^2 + ...
/// where z is a random challenge scalar derived using the Fiat-Shamir protocol.
/// This public vector is then used as the input to a linear proof.
///
/// The commitment to the combination of c_i values is C:
/// C = r_total * B + < a || x, acc_vec > * F + < a || x, G>
/// where r_total = r_a + r_x and < a || x, G > = < a, G[:half]> + <x, G[half:]>
/// and < a || x, acc_vec> = c_0 + c_1*z + c_2*z^2 ... c_{acc-1}*z^{acc-1}
/// so C = com_x + com_y + sum{i=0^acc}(c_i * z^i) * F
#[derive(Clone, Debug)]
pub struct SecAggProof {
    pub linear_proof: LinearProof,
    pub A: CompressedRistretto,
    pub X: CompressedRistretto,
    pub C: CompressedRistretto,
    pub c_vec: Vec<Scalar>,
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
        let l = a_len + x_len;
        // The number of layers to accumulate for the public matrices
        let acc = b.len();
        // Append the proof parameters to the transcript
        transcript.append_u64(b"a len", a_len as u64);
        transcript.append_u64(b"x len", x_len as u64);
        transcript.append_u64(b"acc", acc as u64);

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
        let A_point = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(iter::once(&r_a)),
            G_a.iter().chain(iter::once(B)),
        );
        let A = A_point.compress();
        // X = r_x * B + <x, G[len(a):]>
        let r_x = Scalar::random(rng);
        let X_point = RistrettoPoint::vartime_multiscalar_mul(
            x.iter().chain(iter::once(&r_x)),
            G_x.iter().chain(iter::once(B)),
        );
        let X = X_point.compress();

        // Append the private commitments to the transcript
        transcript.append_point(b"A", &A);
        transcript.append_point(b"X", &X);

        // Append the c_i values to the transcript.
        // This binds the transcript to the public values
        let mut c_vec = vec![];
        for i in 0..acc {
            assert_eq!(a_len, b[i].len());
            assert_eq!(x_len, y[i].len());
            let c_i = inner_product(&a, &b[i]) + inner_product(&x, &y[i]);
            transcript.append_scalar(b"c_i", &c_i);
            c_vec.push(c_i);
        }

        // Get challenge scalar to flatten the b_vec and y_vec matrices into vectors
        let z = transcript.challenge_scalar(b"z");
        let mut z_exp = Scalar::one();

        // Build b_acc, y_acc, and c_acc to accumulate their respective values,
        // where the entries are combined with different powers of z:
        // b_acc = b[0] + b[1]*z + ... + b[acc-1]*z^{acc-1}
        let mut b_acc: Vec<Scalar> = vec![Scalar::zero(); a_len];
        // y_acc = b[0] + b[1]*z + ... + b[acc-1]*z^{acc-1}
        let mut y_acc: Vec<Scalar> = vec![Scalar::zero(); x_len];
        // c_acc = c[0] + c[1]*z + ... + c[acc-1]*z^{acc-1}
        let mut c_acc: Scalar = Scalar::zero();

        for i in 0..acc {
            for (j, b_j) in b[i].iter().enumerate() {
                b_acc[j] += b_j * z_exp;
            }
            for (j, y_j) in y[i].iter().enumerate() {
                y_acc[j] += y_j * z_exp;
            }
            c_acc += c_vec[i] * z_exp;
            // Raise z_exp to the next power of z
            z_exp = z_exp * z;
        }

        // Make a commitment to the secret and public values
        let C = (A_point + X_point + c_acc * F).compress();
        transcript.append_point(b"C", &C);

        // Assemble inputs to the linear proof
        // The blinding factor is the sum of the a and x commitment blinding factors
        let r = r_a + r_x;
        // priv_acc is the accumulated private values vector: priv_acc =  a || x
        let mut priv_acc: Vec<Scalar> = vec![];
        priv_acc.append(&mut a);
        priv_acc.append(&mut x);
        // pub_acc is the accumulated public values vector: pub_acc = b_acc || y_acc
        // such that pub_acc = b_0 || y_0 + (b_1 || y_1)*z + (b_2 || y_2)*z^2 + ...
        let mut pub_acc: Vec<Scalar> = vec![];
        pub_acc.append(&mut b_acc);
        pub_acc.append(&mut y_acc);

        let linear_proof =
            LinearProof::create(transcript, rng, &C, r, pub_acc, priv_acc, G_vec, &F, &B);

        SecAggProof {
            linear_proof,
            A,
            X,
            C,
            c_vec,
        }
    }
}
