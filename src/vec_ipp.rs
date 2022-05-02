#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../../docs/range-proof-protocol.md"))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "std")]
use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;

use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

/// The `VecInnerProductProof` struct represents a proof that the inner
/// product between a secret vector and a public vector is a certain commitment.
/// The secret vector is committed to via a Vector Pedersen Commitment.

#[derive(Clone, Debug)]
pub struct VecInnerProductProof {
    /// Commitment to the bits of the vector
    A: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl VecInnerProductProof {
    /// Create a VecInnerProductProof for a given vector.
    #[allow(dead_code)]
    pub fn prove(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: Scalar,
        n: usize,
        secret_vec: Vec<u8>,
        public_vec: Vec<u8>, // TODO: replace this with challenge scalars
    ) -> Result<(VecInnerProductProof, CompressedRistretto), ProofError> {
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.k_hot_proof_domain_sep(n as u64);

        let V = pc_gens.commit(v.into(), v_blinding).compress();

        let rng = &mut thread_rng();
        let a_blinding = Scalar::random(rng);

        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding
        let mut A = pc_gens.B_blinding * a_blinding;

        use subtle::{Choice, ConditionallySelectable};
        let mut i = 0;
        for G_i in bp_gens.G(n, 1) {
            // If secret[i] = 0, we add the zero scalar.
            // If secret[i] = 1, we add G[i].
            let secret_i = Choice::from(secret_vec[i]);
            let mut point = G_i * Scalar::zero();
            point.conditional_assign(G_i, secret_i);
            A += point;
            i += 1;
        }

        let s_blinding = Scalar::random(rng);
        let s_L: Vec<Scalar> = (0..n).map(|_| Scalar::random(rng)).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()),
            iter::once(&pc_gens.B_blinding).chain(bp_gens.G(n, 1)),
        );

        // Commit aggregated A, S
        transcript.append_point(b"A", &A.compress());
        transcript.append_point(b"S", &S.compress());

        let y = transcript.challenge_scalar(b"y");
        let _z = transcript.challenge_scalar(b"z");

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l_poly = util::VecPoly1::zero(n);
        let mut r_poly = util::VecPoly1::zero(n);

        for i in 0..n {
            l_poly.0[i] = Scalar::from(secret_vec[i]);
            l_poly.1[i] = s_L[i];
            r_poly.0[i] = Scalar::from(public_vec[i]);
            r_poly.1[i] = Scalar::zero();
        }

        let t_poly = l_poly.inner_product(&r_poly);

        // Generate x by committing to T_1, T_2 (line 49-54)
        let t_1_blinding = Scalar::random(rng);
        let T_1 = pc_gens.commit(t_poly.1, t_1_blinding);

        transcript.append_point(b"T_1", &T_1.compress());
        let x = transcript.challenge_scalar(b"x");

        let t_blinding_poly = util::Poly2(
            v_blinding,
            t_1_blinding,
            Scalar::zero(),
        );

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let e_blinding = a_blinding + s_blinding * x;
        let l_vec = l_poly.eval(x);
        let r_vec = r_poly.eval(x);

        transcript.append_scalar(b"t_x", &t_x);
        transcript.append_scalar(b"t_x_blinding", &t_x_blinding);
        transcript.append_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar(b"w");
        let Q = w * pc_gens.B;

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();
        let H_factors: Vec<Scalar> = util::exp_iter(y.invert())
            .take(n)
            .collect();

        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            &G_factors,
            &H_factors,
            bp_gens.G(n, 1).cloned().collect(),
            bp_gens.H(n, 1).cloned().collect(),
            l_vec,
            r_vec,
        );

        Ok((VecInnerProductProof {
            A: A.compress(),
            S: S.compress(),
            T_1: T_1.compress(),
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        }, V))
    }

    /// Verify a VecInnerProductProof
    #[allow(dead_code)]
    pub fn verify(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        n: usize,
        V: CompressedRistretto,
    ) -> Result<(), ProofError> {
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        let rng = &mut thread_rng();

        transcript.k_hot_proof_domain_sep(n as u64);

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let _y = transcript.challenge_scalar(b"y");
        let _z = transcript.challenge_scalar(b"z");

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let _w = transcript.challenge_scalar(b"w");

        // Challenge value for batching statements to be verified
        let _c = Scalar::random(rng);

        let (_x_sq, _x_inv_sq, s) = self.ipp_proof.verification_scalars(n, transcript)?;
        let _s_inv = s.iter().rev();

        let _a = self.ipp_proof.a;
        let _b = self.ipp_proof.b;
        let V_decomp = V.decompress().ok_or_else(|| ProofError::FormatError)?;
        let T_1_decomp = self.T_1.decompress().ok_or_else(|| ProofError::FormatError)?;

        let V_check_left = pc_gens.B * self.t_x + pc_gens.B_blinding * self.t_x_blinding;
        let V_check_right = V_decomp + T_1_decomp * x;
        if !(V_check_left == V_check_right) {
            return Err(ProofError::VerificationError);
        }
 
        Ok(())
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * four compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        // 7 elements: points A, S, T1, T2, scalars tx, tx_bl, e_bl.
        let mut buf = Vec::with_capacity(7 * 32 + self.ipp_proof.serialized_size());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `VecInnerProductProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<VecInnerProductProof, ProofError> {
        if slice.len() % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 6 * 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        let A = CompressedRistretto(read32(&slice[0 * 32..]));
        let S = CompressedRistretto(read32(&slice[1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[2 * 32..]));

        let t_x = Scalar::from_canonical_bytes(read32(&slice[3 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Scalar::from_canonical_bytes(read32(&slice[4 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Scalar::from_canonical_bytes(read32(&slice[5 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[6 * 32..])?;

        Ok(VecInnerProductProof {
            A,
            S,
            T_1,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

impl Serialize for VecInnerProductProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for VecInnerProductProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct VecInnerProductProofVisitor;

        impl<'de> Visitor<'de> for VecInnerProductProofVisitor {
            type Value = VecInnerProductProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("a valid VecInnerProductProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<VecInnerProductProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return VecInnerProductProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return VecInnerProductProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(VecInnerProductProofVisitor)
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n} \rangle - z^3 \cdot n
/// \\]
#[allow(dead_code)]
fn delta(n: usize, y: &Scalar, z: &Scalar) -> Scalar {
    // let z2 = z * z;
    // let z3 = z2 * z;
    // let sum_y = util::sum_of_powers(y, n);

    // (z - z2) * sum_y - z3 * Scalar::from(n as u64)
    let m = 1;
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;
/*
    #[test]
    fn test_delta() {
        let mut rng = rand::thread_rng();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3;

            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        assert_eq!(power_g, delta(n, &y, &z));
    }
*/
    fn create_and_verify_helper(n: usize) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n, 1);

        // Prover's scope
        let (proof_bytes, V) = {
            // 0. Create witness data
            let mut secret_vec = vec![0; n];
            // TODO: choose index randomly
            secret_vec[n-1] = 1;
            let public_vec = vec![1; n];
            
            // 1. Create the proof
            let mut transcript = Transcript::new(b"VecInnerProductProofTest");
            let (proof, V) = VecInnerProductProof::prove(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                1, 
                Scalar::zero(),
                n,
                secret_vec,
                public_vec,
            )
            .unwrap();

            // 2. Return serialized proof and value commitments
            (bincode::serialize(&proof).unwrap(), V)
        };

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: VecInnerProductProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut transcript = Transcript::new(b"VecInnerProductProofTest");

            assert!(proof
                .verify(&bp_gens, &pc_gens, &mut transcript, n, V)
                .is_ok());
        }

    }

    #[test]
    fn test_n_1() {
        create_and_verify_helper(1);
    }
    #[test]
    fn test_n_2() {
        create_and_verify_helper(2);
    }
    #[test]
    fn test_n_4() {
        create_and_verify_helper(4);
    }
}
