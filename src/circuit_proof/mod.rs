#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};
use std::iter;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use generators::Generators;
use proof_transcript::ProofTranscript;  
use util;

#[derive(Clone, Debug)]
pub struct CircuitProof {
  pub A_I: RistrettoPoint,
  pub A_O: RistrettoPoint,
  pub S: RistrettoPoint,

}

impl CircuitProof {
  pub fn generate_proof<R: Rng + CryptoRng>(
    gen: Generators,
    transcript: &mut ProofTranscript,
    rng: &mut R,

    n: usize,
    m: usize,
    q: usize,

    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    c: Vec<Scalar>,
    W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
    W_R: Vec<Vec<Scalar>>,
    W_O: Vec<Vec<Scalar>>,
  ) -> CircuitProof {
    transcript.commit_u64(n as u64);
    transcript.commit_u64(m as u64);
    transcript.commit_u64(q as u64);
    // TODO: check n, m, q against input sizes

    let i_blinding = Scalar::random(rng);
    let o_blinding = Scalar::random(rng);
    let s_blinding = Scalar::random(rng);
    let s_L: Vec<Scalar> = (0..n).map(|_| Scalar::random(rng)).collect();
    let s_R: Vec<Scalar> = (0..n).map(|_| Scalar::random(rng)).collect();

    // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
    let A_I = RistrettoPoint::multiscalar_mul(
      iter::once(&i_blinding).chain(a_L.iter()).chain(a_R.iter()),
      iter::once(&gen.pedersen_generators.B_blinding)
        .chain(gen.G.iter())
        .chain(gen.H.iter()),
    );

    // A_O = <a_O, G> + o_blinding * B_blinding
    let A_O = RistrettoPoint::multiscalar_mul(
      iter::once(&o_blinding).chain(a_O.iter()),
      iter::once(&gen.pedersen_generators.B_blinding)
        .chain(gen.G.iter()),
    );

    // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
    let S = RistrettoPoint::multiscalar_mul(
      iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
      iter::once(&gen.pedersen_generators.B_blinding)
        .chain(gen.G.iter())
        .chain(gen.H.iter()),
    );

    transcript.commit(A_I.compress().as_bytes());
    transcript.commit(A_O.compress().as_bytes());
    transcript.commit(S.compress().as_bytes());
    let y = transcript.challenge_scalar();
    let z = transcript.challenge_scalar();

    let mut l_poly = util::VecPoly3::zero(n);
    let mut r_poly = util::VecPoly3::zero(n);

    let powers_of_z: Vec<Scalar>= util::exp_iter(z).take(q).collect();
    let z_zQ_WL: Vec<Scalar> = powers_of_z.clone(); // TODO: implement
    let z_zQ_WR: Vec<Scalar> = powers_of_z.clone(); // TODO: implement
    let z_zQ_WO: Vec<Scalar> = powers_of_z.clone(); // TODO: implement

    let mut exp_y = Scalar::one(); // y^n starting at n=0
    let mut exp_y_inv = Scalar::one(); // y^-n starting at n=0
    let y_inv = y.invert();

    // l_poly.0 = 0
    // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
    // l_poly.2 = a_O
    // l_poly.3 = s_L
    // r_poly.0 = (z * z^Q * W_O) - y^n
    // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
    // r_poly.2 = 0
    // r_poly.3 = y^n * s_R
    for i in 0..n {
      l_poly.1[i] = a_L[i] + exp_y_inv * z_zQ_WR[i];
      l_poly.2[i] = a_O[i];
      l_poly.3[i] = s_L[i];
      r_poly.0[i] = z_zQ_WO[i] - exp_y;
      r_poly.1[i] = exp_y * a_R[i] + z_zQ_WL[i];
      r_poly.3[i] = exp_y * s_R[i];

      exp_y = exp_y * y; // y^i -> y^(i+1)
      exp_y_inv = exp_y_inv * y_inv; // y^-i -> y^-(i+1)
    }
    unimplemented!()
  }
}