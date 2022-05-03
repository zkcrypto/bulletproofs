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
    /// experimental
    pub(crate) G_0: RistrettoPoint,
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
            // println!("n: {:?}", n);
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
                G_L[i] = G_L[i] + x_j * G_R[i];
                // RistrettoPoint::vartime_multiscalar_mul(
                //     &[Scalar::one(), x_j],
                //     &[G_L[i], G_R[i]],
                // );
            }
            a = a_L;
            b = b_L;
            G = G_L;
            r = r + x_j * s_j + x_j_inv * t_j;
        }

        // let s_star = Scalar::random(rng);
        // let t_star = Scalar::random(rng);
        // Setting randomness to zero for debugging. TODO: set back
        let s_star = Scalar::zero();
        let t_star = Scalar::zero();
        let S = (t_star * B + s_star * b[0] * F + s_star * G[0]).compress();
        transcript.append_point(b"S", &S);
        let x_star = transcript.challenge_scalar(b"x_star");
        // Setting x_star to one for debugging. TODO: set back
        let a_star = a[0];
        let r_star = t_star + r;
        // let a_star = s_star * x_star * a[0];
        // let r_star = t_star + x_star * r;

        // println!("prover's b[0]: {:?}", b[0]);
        // println!("prover's base case G: {:?}", G[0]);

        LinearProof {
            L_vec,
            R_vec,
            C: *C,
            S,
            a: a_star,
            r: r_star,
            G_0: G[0],
        }
    }

    /// Computes vectors of verification scalars \\([x\_{i}]\\), \\([x\_{i}^{-1}]\\), \\([s\_{i}]\\)
    /// for combined multiscalar multiplication in a parent protocol. Also computes \\(b_0\\).
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
        mut b_vec: Vec<Scalar>,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", &self.C);

        // 1. Recompute x_k,...,x_1 based on the proof transcript
        // 2. Generate b_0 from the public vector b
        let mut n_mut = n;
        let mut b = &mut b_vec[..];
        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            let x_j = transcript.challenge_scalar(b"x_j");
            challenges.push(x_j);
            n_mut = n_mut / 2;
            let (b_L, b_R) = b.split_at_mut(n_mut);
            for i in 0..n_mut {
                b_L[i] = b_L[i] + x_j * b_R[i];
            }
            b = b_L;
        }
        // println!("verifier's b[0]: {:?}", b[0]);

        // 3. Compute the challenge inverses: 1/x_k, ..., 1/x_1
        let mut challenges_inv = challenges.clone();
        let all_inv = Scalar::batch_invert(&mut challenges_inv);

        // 4. Compute s values inductively.
        // for i = 1..n, s_i = product_(j=1^{log_2(n)}) x_j ^ b(i,j)
        // Where b(i,j) = 1 if the jth bit of (i-1) is 1, and 0 otherwise.
        // In other words, s is the subset-product of the x_j's.
        // In GHL'21 this is referred to as `x<i>`.
        //
        // Note that this is different from the Bulletproofs `s` generation,
        // where b(i, j) = 1 if the jth bit of (i-1) is 1, and -1 otherwise.
        let mut s = Vec::with_capacity(n);
        s.push(Scalar::one());
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so x_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i = challenges[(lg_n - 1) - lg_i];
            s.push(s[i - k] * x_lg_i);
        }

        // assert_eq!(s[1], challenges[challenges.len()-1]);
        // assert_eq!(s[2], challenges[challenges.len()-2]);
        // assert_eq!(s[3], challenges[challenges.len()-1] * challenges[challenges.len()-2]);
        // assert_eq!(s[n-1], all_inv.invert());

        Ok((challenges, challenges_inv, s, b[0]))
    }

    pub fn verify(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G: &[RistrettoPoint],
        F: &RistrettoPoint,
        B: &RistrettoPoint,
        b_vec: Vec<Scalar>,
    ) -> Result<(), ProofError>
    {
        let (x_vec, x_inv_vec, s, b_0) = self.verification_scalars(n, transcript, b_vec)?;

        transcript.append_point(b"S", &self.S);
        let x_star = transcript.challenge_scalar(b"x_star");

        // simple_factors = r_star * B + a_star * b_0 * F
        let simple_factors: RistrettoPoint = self.r * B + self.a * b_0 * F;

        // Decompress the compressed L values
        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        // Decompress the compressed R values
        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let C = self.C.decompress().ok_or(ProofError::VerificationError)?;
        let S = self.S.decompress().ok_or(ProofError::VerificationError)?;

        // L_R_factors = sum_{j=0}^{l-1} x_j^-1 * L_j + sum_{j=0}^{l-1} x_j * R_j
        let L_R_factors: RistrettoPoint = RistrettoPoint::vartime_multiscalar_mul(
            x_vec.iter()
                .chain(x_inv_vec.iter()),
            Ls.iter()
                .chain(Rs.iter()),
        );

        println!("L_R_factors: {:?}", L_R_factors);
        println!("S: {:?}", S);
        println!("r: {:?}", self.r);

        // x_factors = sum_{i=0}^{2^l-1} x<i> * G_i
        let _x_factors: RistrettoPoint = RistrettoPoint::vartime_multiscalar_mul(
            s.iter(),
            G.iter()
        );
        // println!("x_factors: {:?}", x_factors);

        // println!("self.a in verifier: {:?}", self.a);
        // println!("self.G_0 in verifier: {:?}", self.G_0);
        println!("b_0 in verifier: {:?}", b_0);

        // Setting x_star to one for debugging. TODO: set back
        // Also removing L_R_factors for n=1 case. TODO: set back
        let expect_S = simple_factors - C + self.a * self.G_0;
        // let expect_S = simple_factors - x_star * (C + L_R_factors) + self.a * self.G_0;

        // println!("expect_S: {:?}", expect_S);
        // println!("S: {:?}", S);
        if expect_S == S {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

/*
    pub fn verify(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G: Vec<RistrettoPoint>,
        F: &RistrettoPoint,
        B: &RistrettoPoint,
        mut b_vec: Vec<Scalar>,
    ) -> Result<(), ProofError>
    {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", &self.C);

        // 1. Recompute x_k,...,x_1 based on the proof transcript
        // 2. Generate b_0 from the public vector b
        let mut n_mut = n;
        let mut G_mut = &mut G.clone()[..];
        let mut b = &mut b_vec[..];
        let mut x_vec = Vec::with_capacity(lg_n);
        let mut x_inv_vec = Vec::with_capacity(lg_n);

        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;

            // Get challenge and challenge inverse
            let x_j = transcript.challenge_scalar(b"x_j");
            x_vec.push(x_j);
            x_inv_vec.push(x_j.invert());

            // Update the first half of b vector
            n_mut = n_mut / 2;
            let (G_L, G_R) = G_mut.split_at_mut(n_mut);
            let (b_L, b_R) = b.split_at_mut(n_mut);

            for i in 0..n_mut {
                b_L[i] = b_L[i] + x_j * b_R[i];
                // G_L = G_L + x_j * G_R
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(
                    &[Scalar::one(), x_j],
                    &[G_L[i], G_R[i]],
                );
            }
            b = b_L;
            G_mut = G_L;
        }
        // println!("verifier's b[0]: {:?}", b[0]);
        // println!("verifier's G[0]: {:?}", G_mut[0]);

        // Decompress the compressed L values
        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        // Decompress the compressed R values
        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let C = self.C.decompress().ok_or(ProofError::VerificationError)?;
        let S = self.S.decompress().ok_or(ProofError::VerificationError)?;

        transcript.append_point(b"S", &self.S);
        let x_star = transcript.challenge_scalar(b"x_star");

        let C_L_R = C + RistrettoPoint::vartime_multiscalar_mul(
            x_vec.iter()
                .chain(x_inv_vec.iter()),
            Ls.iter()
                .chain(Rs.iter()),
        );

        // let x_factors = self.subset_product(n, x_vec);
        // let x_factors_msm = RistrettoPoint::vartime_multiscalar_mul(
        //     x_factors.iter(),
        //     G.iter(),
        // );
        // println!("calculated x_factors_msm: {:?}", x_factors_msm);

        if C_L_R * x_star + S == self.r * B + self.a * b[0] * F + self.a * self.G_0 {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }
*/
    fn subset_product(
        &self,
        n: usize,
        challenges: Vec<Scalar>,
    ) -> Vec<Scalar> {
        let lg_n = self.L_vec.len();

        // Compute s values inductively.
        // for i = 1..n, s_i = product_(j=1^{log_2(n)}) x_j ^ b(i,j)
        // Where b(i,j) = 1 if the jth bit of (i-1) is 1, and 0 otherwise.
        // In other words, s is the subset-product of the x_j's.
        // In GHL'21 this is referred to as `x<i>`.
        //
        // Note that this is different from the Bulletproofs `s` generation,
        // where b(i, j) = 1 if the jth bit of (i-1) is 1, and -1 otherwise.
        let mut s = Vec::with_capacity(n);
        s.push(Scalar::one());
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so x_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i = challenges[(lg_n - 1) - lg_i];
            // println!("i: {:?}, k: {:?}, i-k: {:?}", i, k, i-k);
            // println!("lg_i: {:?}", lg_i);
            s.push(s[i - k] * x_lg_i);
        }

        let chal_len = challenges.len();
        assert_eq!(s[1], challenges[chal_len-1]);
        assert_eq!(s[2], challenges[chal_len-2]);
        assert_eq!(s[3], challenges[chal_len-1] * challenges[chal_len-2]);

        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_core::SeedableRng;
    use rand_chacha::ChaChaRng;

    fn test_helper(n: usize) {
        let mut rng = ChaChaRng::from_seed([24u8; 32]);

        use crate::generators::{BulletproofGens, PedersenGens};
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n).cloned().collect();

        let pedersen_gens = PedersenGens::default();
        let F = pedersen_gens.B;
        let B = pedersen_gens.B_blinding;

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

        println!("a: {:?}", a);
        println!("b: {:?}", b);
        println!("G_0: {:?}", G[0]);

        let mut prover_transcript = Transcript::new(b"linearprooftest");

        // C = <a, G> + r * B + <a, b> * F
        let r = Scalar::random(&mut rng);
        println!("r: {:?}", r);
        let c = inner_product(&a, &b);
        let C = RistrettoPoint::vartime_multiscalar_mul(
                a.iter()
                    .chain(iter::once(&r))
                    .chain(iter::once(&c)),
                G.iter()
                    .chain(Some(&B))
                    .chain(iter::once(&F)),
            )
            .compress();

        let proof = LinearProof::create(
            &mut prover_transcript,
            &mut rng,
            &C,
            r,
            a,
            b.clone(),
            G.clone(),
            &F,
            &B,
        );

        let mut verifier_transcript = Transcript::new(b"linearprooftest");
        assert!(proof.verify(
            n,
            &mut verifier_transcript,
            &G,
            &F,
            &B,
            b,
        ).is_ok());
    }

    #[test]
    fn test_linear_proof() {
        test_helper(1);
    }
}