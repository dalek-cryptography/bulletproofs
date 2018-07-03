#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};
use std::iter;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use generators::GeneratorsView;
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
    gen: GeneratorsView,
    transcript: &mut ProofTranscript,
    rng: &mut R,

    n: usize,
    m: usize,
    q: usize,

    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    c: Vec<Scalar>,
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

    unimplemented!()
  }
}