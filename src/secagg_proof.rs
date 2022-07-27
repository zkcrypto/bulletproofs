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
    pub pub_acc: Vec<Scalar>,
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
        b: Vec<Vec<Scalar>>,
        // Public scalar matrix y
        y: Vec<Vec<Scalar>>,
        // Generator vector
        mut G_vec: Vec<RistrettoPoint>,
        // Pedersen generator F, for committing to the secret values
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding values
        B: &RistrettoPoint,
    ) -> SecAggProof {
        let a_len = a.len();
        let x_len = x.len();
        // The number of layers to accumulate for the public matrices
        let acc = b.len();
        // The public scalar matrices b and y must have the same length
        assert_eq!(acc, y.len());
        // The concatenated a and x lengths must be a power of two
        assert!((a_len + x_len).is_power_of_two());

        // Append the proof parameters to the transcript
        transcript.append_u64(b"a len", a_len as u64);
        transcript.append_u64(b"x len", x_len as u64);
        transcript.append_u64(b"acc", acc as u64);

        // Create slice G, backed by its respective vector, for reslicing
        let G = &mut G_vec[..];
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

        // Assemble inputs to the linear proof
        // Make a commitment to the secret and public values
        let C = (A_point + X_point + c_acc * F).compress();
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

        let linear_proof = LinearProof::create(
            transcript,
            rng,
            &C,
            r,
            priv_acc,
            pub_acc.clone(),
            G_vec,
            &F,
            &B,
        );

        SecAggProof {
            linear_proof,
            A,
            X,
            C,
            c_vec,
            pub_acc,
        }
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        // Public scalar matrix b
        b: Vec<Vec<Scalar>>,
        // Public scalar matrix y
        y: Vec<Vec<Scalar>>,
        // Generator vector
        G: &[RistrettoPoint],
        // Pedersen generator F, for committing to the secret value
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding value
        B: &RistrettoPoint,
    ) -> Result<(), ProofError> {
        let a_len = b[0].len();
        let x_len = y[0].len();
        // The number of layers to accumulate for the public matrices
        let acc = b.len();
        // The public scalar matrices b and y must have the same length
        assert_eq!(acc, y.len());
        // The concatenated a and x lengths must be a power of two
        assert!((a_len + x_len).is_power_of_two());

        // Append the proof parameters to the transcript
        transcript.append_u64(b"a len", a_len as u64);
        transcript.append_u64(b"x len", x_len as u64);
        transcript.append_u64(b"acc", acc as u64);

        // Append the private commitments to the transcript
        transcript.append_point(b"A", &self.A);
        transcript.append_point(b"X", &self.X);

        // Append the c_i values to the transcript.
        for i in 0..acc {
            assert_eq!(a_len, b[i].len());
            assert_eq!(x_len, y[i].len());
            transcript.append_scalar(b"c_i", &self.c_vec[i]);
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
            c_acc += self.c_vec[i] * z_exp;
            // Raise z_exp to the next power of z
            z_exp = z_exp * z;
        }

        // pub_acc is the accumulated public values vector: pub_acc = b_acc || y_acc
        // such that pub_acc = b_0 || y_0 + (b_1 || y_1)*z + (b_2 || y_2)*z^2 + ...
        let mut pub_acc: Vec<Scalar> = vec![];
        pub_acc.append(&mut b_acc);
        pub_acc.append(&mut y_acc);
        assert_eq!(pub_acc, self.pub_acc);

        let A_point = self.A.decompress().ok_or(ProofError::VerificationError)?;
        let X_point = self.X.decompress().ok_or(ProofError::VerificationError)?;
        let C = (A_point + X_point + c_acc * F).compress();
        assert_eq!(C, self.C);

        self.linear_proof.verify(
            a_len + x_len,
            transcript,
            &self.C,
            G,
            F,
            B,
            self.pub_acc.clone(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_chacha::ChaChaRng;
    use rand_core::SeedableRng;

    // n is the length of a, x public vectors
    // m is the accumulation depth for b, y matrices
    fn test_helper(n: usize, m: usize) {
        let mut rng = ChaChaRng::from_seed([24u8; 32]);

        use crate::generators::{BulletproofGens, PedersenGens};
        let bp_gens = BulletproofGens::new(2 * n, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(2 * n).cloned().collect();

        let pedersen_gens = PedersenGens::default();
        let F = pedersen_gens.B;
        let B = pedersen_gens.B_blinding;

        // a, x are vectors and b, y are matrices for which we want to prove:
        // <a, b_i> + <x, y_i> = c_i for i in [0, l)
        // Where a, x are private vectors, b, y are public matrices, and c_i is public
        let a: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let x: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<Vec<Scalar>> = (0..m)
            .map(|_| (0..n).map(|_| Scalar::random(&mut rng)).collect())
            .collect();
        let y: Vec<Vec<Scalar>> = (0..m)
            .map(|_| (0..n).map(|_| Scalar::random(&mut rng)).collect())
            .collect();

        let mut prover_transcript = Transcript::new(b"secaggprooftest");

        let proof = SecAggProof::create(
            &mut prover_transcript,
            &mut rng,
            a,
            x,
            b.clone(),
            y.clone(),
            G.clone(),
            &F,
            &B,
        );

        let mut verifier_transcript = Transcript::new(b"secaggprooftest");
        assert!(proof
            .verify(&mut verifier_transcript, b, y, &G, &F, &B)
            .is_ok());
    }

    #[test]
    fn test_secagg_proof_base() {
        test_helper(1, 1);
    }

    #[test]
    fn test_secagg_proof_small() {
        test_helper(1, 2);
        test_helper(2, 1);
        test_helper(2, 2);
    }

    #[test]
    fn test_secagg_proof_med() {
        test_helper(8, 16);
        test_helper(16, 32);
        test_helper(32, 16);
    }

    #[test]
    fn test_secagg_proof_large() {
        test_helper(64, 128);
        test_helper(128, 64);
        test_helper(128, 128);
    }
}
