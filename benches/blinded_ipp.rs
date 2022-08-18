#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::BlindedInnerProductProof;
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

fn create_blinded_ipp_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "blinded inner product proof creation",
        move |bench, n| {
            let mut transcript = Transcript::new(b"BlindedIPPBenchmark");

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
                BlindedInnerProductProof::create(
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
    name = create_blinded_ipp;
    config = Criterion::default().sample_size(10);
    targets = create_blinded_ipp_helper,
}

criterion_main!(create_blinded_ipp);
