use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::linear_proof::LinearProof;
use core::iter;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand::distributions::WeightedIndex;
use rand::prelude::*;
use rand::thread_rng;

#[derive(Clone, Debug)]
pub struct ApproxRangeProof {
    pub R_x_proofs: Vec<LinearProof>,
    pub y_mu_proofs: Vec<LinearProof>,
    pub y_commit: CompressedRistretto,
    pub x_commit: CompressedRistretto,
    pub R: Vec<Vec<i64>>,
    pub z: i64,
}

impl ApproxRangeProof {
    pub fn create(
        transcript: &mut Transcript,
        // Message = the vector x of length L
        x: Vec<u64>,
        // The bounds for x, such that x \in [0, t)
        t: u64,
        // Generators for making vector commitments
        bp_generators: &BulletproofGens,
        // Generators for making Pedersen commitments
        pc_gens: &PedersenGens,
    ) -> ApproxRangeProof {
        // TODO(cathie): change function to take in an RNG that is generic over
        // RngCore, CryptoRng, Rng instead (Rng needed for gen_range() impl).
        let mut rng = thread_rng();
        // Repetition parameter
        let r = 20;
        // Soundnesss parameter lambda
        let lambda = 128;
        // Message length
        let L = x.len();
        // Gap factor gamma
        let gamma = 2.0 * 9.75 * (lambda as f64) * (L as f64).sqrt();
        // Take the first share of the generators, since it's a 1-party computation
        let gens = bp_generators.share(0);

        // Create a commitment to x: com(x)
        let x_r: Vec<Scalar> = (0..L).map(|_| Scalar::random(&mut rng)).collect();
        let com_x = RistrettoPoint::vartime_multiscalar_mul(
            x_r.iter().chain(x.iter().map(|x_i| &Scalar::from(*x_i))),
            gens.H(L).chain(gens.G(L)),
        );

        let y_bounds = (t / 2 * (1 + 1 / lambda)) as i64;
        let r_choices = [-1, 0, 1];
        let r_weights = [1, 2, 1];
        let r_dist = WeightedIndex::new(&r_weights).unwrap();

        for i in 0..r {
            // Sample y_i <- [+/- round(t/2 * (1 + 1/lambda))]^lambda
            let y_i: Vec<i64> = (0..lambda)
                .into_iter()
                .map(|_| rng.gen_range(-y_bounds..y_bounds))
                .collect();

            // Sample R_i, the centered binomial distribution over {0, +/- 1} with p=0.5.
            // ie D(0) = 1/2, D(1) = 1/4, D(-1) = -1/4, R_i sampled from D.
            let R_i: Vec<Vec<i64>> = (0..lambda)
                .into_iter()
                .map(|_| {
                    (0..L)
                        .into_iter()
                        .map(|_| r_choices[r_dist.sample(&mut rng)])
                        .collect()
                })
                .collect();

            // z_i = R_i * x + y_i
            let R_times_x: Vec<i64> = R_i
                .iter()
                .map(|R_row| {
                    R_row
                        .iter()
                        .zip(x.iter())
                        .map(|(R_entry, x_entry)| R_entry * (*x_entry as i64))
                        .sum()
                })
                .collect();
            let z_i: Vec<i64> = R_times_x
                .iter()
                .zip(y_i.iter())
                .map(|(Rx_j, y_i_j)| Rx_j + y_i_j)
                .collect();

            let R_x_max = R_times_x.iter().max();
            let z_i_max = z_i.iter().max();
            if (R_x_max <= t / 2 * lambda) & (z_i_max <= t / 2) {
                println!("success!");
                let mut R_x_proofs = vec![];
                let mut y_mu_proofs = vec![];

                // Create a commitment to y: com(y)
                // TODO: fix, since currently y_i_j can be negative and you can't make a
                // scalar from a negative number.
                let y_r: Vec<Scalar> = (0..L).map(|_| Scalar::random(&mut rng)).collect();
                let com_y = RistrettoPoint::vartime_multiscalar_mul(
                    y_r.iter()
                        .chain(y_i.iter().map(|y_i_j| &Scalar::from(*y_i_j))),
                    gens.H(L).chain(gens.G(L)),
                );

                for j in 0..L {
                    // Make proof of <R_i[j], x> = R_x
                    let R_x_rand = Scalar::random(&mut rng);
                    let R_x = R_times_x[j];
                    // C = <a, G> + r * B + <a, b> * F
                    // where a is the secret vector, b is the public vector
                    let R_x_commit = RistrettoPoint::vartime_multiscalar_mul(
                        x.iter()
                            .chain(iter::once(&R_x_rand))
                            .chain(iter::once(&R_x)),
                        gens.G(L)
                            .iter()
                            .chain(iter::once(&pc_gens.B_blinding))
                            .chain(iter::once(&pc_gens.B)),
                    )
                    .compress();

                    let R_x_proof = LinearProof::create(
                        &mut transcript,
                        &mut rng,
                        &R_x_commit,
                        R_x_rand,
                        x.clone(),
                        R_i[j].clone(),
                        gens.G(L).clone(),
                        &pc_gens.B,
                        &pc_gens.B_blinding,
                    );
                    R_x_proofs.push(R_x_proof);

                    // Make proof of <y_i, mu_j> = y_mu
                    let y_mu_rand = Scalar::random(&mut rng);
                    let y_mu = y_i[j];
                    // mu_j is a vector where mu_j[j] = 1 and mu_j[h] = 0 for h != j
                    let mut mu_j = vec![0; lambda];
                    mu_j[j] = 1;

                    // C = <a, G> + r * B + <a, b> * F
                    // where a is the secret vector, b is the public vector
                    let y_mu_commit = RistrettoPoint::vartime_multiscalar_mul(
                        y_i.iter()
                            .chain(iter::once(&y_mu_rand))
                            .chain(iter::once(&y_mu)),
                        gens.G(L)
                            .iter()
                            .chain(iter::once(&pc_gens.B_blinding))
                            .chain(iter::once(&pc_gens.B)),
                    )
                    .compress();

                    let y_mu_proof = LinearProof::create(
                        &mut transcript,
                        &mut rng,
                        &y_mu_commit,
                        y_mu_rand,
                        y_i.clone(),
                        mu_j.clone(),
                        gens.G(L).clone(),
                        &pc_gens.B,
                        &pc_gens.B_blinding,
                    );
                    y_mu_proofs.push(y_mu_proof);

                    // TODO(cathie):
                    // Make proof of R_x + y_mu = z_i[j]
                    // (Open the commitment, since z is public?)

                    // Return an ApproxRangeProof
                    ApproxRangeProof(R_x_proofs, y_mu_proofs, com_y, com_x, R_i, z_i)
                }
            }
        }
    }
}
