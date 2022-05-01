#![allow(non_snake_case)]

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;
use crate::inner_product_proof::inner_product;

#[derive(Clone, Debug)]
pub struct LinearProof {
    pub(crate) L_vec: Vec<CompressedRistretto>,
    pub(crate) R_vec: Vec<CompressedRistretto>,
    /// Commitment to witness.
    /// This technically doesn't have to be a part of the proof (can remove to reduce proof size).
    pub(crate) C: CompressedRistretto,
    /// The last proof element
    pub(crate) S: CompressedRistretto,
    /// The last scalars
    pub(crate) a: Scalar,
    pub(crate) r: Scalar,
}

impl LinearProof {
    /// Create an linear proof, which is an optimized version of an inner-product proof.
    ///
    /// Protocol: Section E.3 of https://eprint.iacr.org/2021/1397.pdf
    /// C++ reference implementation: https://github.com/shaih/cpp-lwevss
    ///
    /// Prove that <a, b> = c where a is secret and b is public.
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        // Commitment to secrets,
        C: &CompressedRistretto,
        // Blinding factor for C
        mut r: Scalar,
        // Secret scalar vector
        mut a_vec: Vec<Scalar>,
        // Common input
        mut b_vec: Vec<Scalar>,
        // Generator vector
        mut G_vec: Vec<RistrettoPoint>,
        // Pedersen generator F, for committing to the secret value
        F: &RistrettoPoint,
        // Pedersen generator B, for committing to the blinding value
        B: &RistrettoPoint,
    ) -> LinearProof {
        let mut n = a_vec.len();

        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", &C);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let s_j = Scalar::random(rng);
            let t_j = Scalar::random(rng);

            // L = a_L * G_R + s_j * B + c_L * F
            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_L.iter()
                    .chain(iter::once(&s_j))
                    .chain(iter::once(&c_L)),
                G_R.iter()
                    .chain(iter::once(B))
                    .chain(iter::once(F)),
            )
            .compress();

            // R = a_R * G_L + t_j * B + c_R * F
            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_R.iter()
                    .chain(iter::once(&t_j))
                    .chain(iter::once(&c_R)),
                G_L.iter()
                    .chain(iter::once(B))
                    .chain(iter::once(F)),
            )
            .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let x_j = transcript.challenge_scalar(b"x_j");
            let x_j_inv = x_j.invert();

            for i in 0..n {
                // a_L = a_L + x_j_inv * a_R
                a_L[i] = a_L[i] + x_j_inv * a_R[i];
                // b_L = b_L + x_j * b_R
                b_L[i] = b_L[i] + x_j * b_R[i];
                // G_L = G_L + x_j * G_R
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(
                    &[Scalar::one(), x_j],
                    &[G_L[i], G_R[i]],
                );
            }

            a = a_L;
            b = b_L;
            G = G_L;
            r = r + x_j * s_j + x_j_inv * t_j;
        }

        let s_star = Scalar::random(rng);
        let t_star = Scalar::random(rng);
        let S = (t_star * B + s_star * b[0] * F + s_star * G[0]).compress();
        transcript.append_point(b"S", &S);
        let x_star = transcript.challenge_scalar(b"x_star");
        let a_star = s_star * a[0];
        let r_star = t_star + s_star * r;

        LinearProof {
            L_vec,
            R_vec,
            C: *C,
            S,
            a: a_star,
            r: r_star,
        }
    }
/*
    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use the `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication. (TODO: write `verification_scalars` function).
    #[allow(dead_code)]
    pub fn verify(
        &self,
        n: usize,
        transcript: &mut Transcript,
        F: &RistrettoPoint,
        B: &RistrettoPoint,
        G: &[RistrettoPoint],
    ) -> Result<(), ProofError>
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -ui);

        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let expect_P = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq),
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter()),
        );

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }
*/
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_helper_create(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::{BulletproofGens, PedersenGens};
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n).cloned().collect();

        let pedersen_gens = PedersenGens::default();
        let F = pedersen_gens.B;
        let B = pedersen_gens.B_blinding;

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

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

        let proof = LinearProof::create(
            &mut transcript,
            &mut rng,
            &C,
            r,
            a,
            b,
            G,
            &F,
            &B,
        );
    }

    #[test]
    fn test_linear_proof() {
        test_helper_create(16);
    }
}