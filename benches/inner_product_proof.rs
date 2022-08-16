#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::InnerProductProof;
use bulletproofs::{BulletproofGens, PedersenGens};
use core::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

/// Different IPP input vector lengths to try
static TEST_SIZES: [usize; 15] = [
    64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576,
];

fn create_ipp_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "inner product proof creation",
        move |bench, n| {
            let mut transcript = Transcript::new(b"IPPBenchmark");

            let pedersen_gens = PedersenGens::default();
            let Q = pedersen_gens.B_blinding;

            let mut rng = rand::thread_rng();

            let bp_gens = BulletproofGens::new(*n, 1);
            let G_vec: Vec<RistrettoPoint> = bp_gens.share(0).G(*n).cloned().collect();
            let H_vec: Vec<RistrettoPoint> = bp_gens.share(0).H(*n).cloned().collect();

            let a_vec: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let b_vec: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();

            let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(*n).collect();
            // y_inv is (the inverse of) a random challenge
            let y_inv = Scalar::random(&mut rng);
            let H_factors: Vec<Scalar> = exp_iter(y_inv).take(*n).collect();

            // Make linear proof
            bench.iter(|| {
                InnerProductProof::create(
                    &mut transcript,
                    &Q,
                    &G_factors[..],
                    &H_factors[..],
                    G_vec.clone(),
                    H_vec.clone(),
                    a_vec.clone(),
                    b_vec.clone(),
                );
            })
        },
        TEST_SIZES,
    );
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

criterion_group! {
    name = create_ipp;
    config = Criterion::default().sample_size(10);
    targets = create_ipp_helper,
}

fn verify_ipp_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "inner product proof verification",
        move |bench, n| {
            let mut transcript = Transcript::new(b"IPPBenchmark");

            let pedersen_gens = PedersenGens::default();
            let Q = pedersen_gens.B_blinding;

            let mut rng = rand::thread_rng();

            let bp_gens = BulletproofGens::new(*n, 1);
            let G: Vec<RistrettoPoint> = bp_gens.share(0).G(*n).cloned().collect();
            let H: Vec<RistrettoPoint> = bp_gens.share(0).H(*n).cloned().collect();

            let a: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let b: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let ip = inner_product(&a, &b);

            let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(*n).collect();
            // y_inv is (the inverse of) a random challenge
            let y_inv = Scalar::random(&mut rng);
            let H_factors: Vec<Scalar> = exp_iter(y_inv).take(*n).collect();

            let ipp = InnerProductProof::create(
                &mut transcript,
                &Q,
                &G_factors[..],
                &H_factors[..],
                G.clone(),
                H.clone(),
                a.clone(),
                b.clone(),
            );

            // P would be determined upstream, but we need a correct P to check the proof.
            //
            // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
            //             P = <a,G> + <b',H> + <a,b> Q,
            // where b' = b \circ y^(-n)
            let b_prime = b.iter().zip(exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
            // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
            let a_prime = a.iter().cloned();

            let P = RistrettoPoint::vartime_multiscalar_mul(
                a_prime.chain(b_prime).chain(iter::once(ip)),
                G.iter().chain(H.iter()).chain(iter::once(&Q)),
            );

            // Verify ipp
            bench.iter(|| {
                let mut verifier = Transcript::new(b"IPPBenchmark");
                ipp.verify(
                    *n,
                    &mut verifier,
                    &G_factors[..],
                    &H_factors[..],
                    &P,
                    &Q,
                    &G,
                    &H,
                );
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = verify_ipp;
    config = Criterion::default().sample_size(10);
    targets = verify_ipp_helper,
}

criterion_main!(create_ipp, verify_ipp);
