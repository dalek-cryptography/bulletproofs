#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};
use std::iter;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use generators::Generators;
use proof_transcript::ProofTranscript;  
use util;
use inner_product_proof::inner_product;

#[derive(Clone, Debug)]
pub struct CircuitProof {
    pub A_I: RistrettoPoint,
    pub A_O: RistrettoPoint,
    pub S: RistrettoPoint,
    pub T_1: RistrettoPoint,
    pub T_3: RistrettoPoint,
    pub T_4: RistrettoPoint,
    pub T_5: RistrettoPoint,
    pub T_6: RistrettoPoint,
    pub t_x: Scalar,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,
    pub l_vec: Vec<Scalar>,
    pub r_vec: Vec<Scalar>,
}

impl CircuitProof {
    pub fn generate_proof<R: Rng + CryptoRng>(
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    
        n: usize, // or we can just calculate parameters ourselves
        m: usize,
        q: usize,

        W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>, // Q vectors, of length m each
        _c: Vec<Scalar>,   
        a_L: Vec<Scalar>,
        a_R: Vec<Scalar>,
        a_O: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
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
        
        let z_zQ_WL: Vec<Scalar> = matrix_flatten(W_L, z);
        let z_zQ_WR: Vec<Scalar> = matrix_flatten(W_R, z);
        let z_zQ_WO: Vec<Scalar> = matrix_flatten(W_O, z);
    
        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let mut exp_y_inv = Scalar::one(); // y^-n starting at n=0
        let y_inv = y.invert();
    
        for i in 0..n {
          // l_poly.0 = 0
          // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
          l_poly.1[i] = a_L[i] + exp_y_inv * z_zQ_WR[i];
          // l_poly.2 = a_O
          l_poly.2[i] = a_O[i];
          // l_poly.3 = s_L
          l_poly.3[i] = s_L[i];
          // r_poly.0 = (z * z^Q * W_O) - y^n
          r_poly.0[i] = z_zQ_WO[i] - exp_y;
          // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
          r_poly.1[i] = exp_y * a_R[i] + z_zQ_WL[i];
          // r_poly.2 = 0
          // r_poly.3 = y^n * s_R
          r_poly.3[i] = exp_y * s_R[i];
    
          exp_y = exp_y * y; // y^i -> y^(i+1)
          exp_y_inv = exp_y_inv * y_inv; // y^-i -> y^-(i+1)
        }
        
        let t_poly = l_poly.inner_product(&r_poly);
    
        let t_1_blinding = Scalar::random(rng);
        let t_3_blinding = Scalar::random(rng);
        let t_4_blinding = Scalar::random(rng);
        let t_5_blinding = Scalar::random(rng);
        let t_6_blinding = Scalar::random(rng);

        // TODO: acheive this with a map & zip to make it neater
        let mut W_V_blinded = vec![Scalar::zero(); m];
        for row in 0..q {
            for col in 0..m{
                W_V_blinded[row] += W_V[row][col] * v_blinding[col];
            }
        }
        let mut t_2_blinding = Scalar::zero();
        // TODO: use inner_product function here instead 
        let mut exp_z = z; // z^n starting at n=1
        for row in 0..q {
            t_2_blinding += W_V_blinded[row] * exp_z;
            exp_z = exp_z * z; // z^n -> z^(n+1)
        }

        let t_blinding_poly = util::Poly6 {
            t1: t_1_blinding,
            t2: t_1_blinding, // TODO: actually compute the t_2 component
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };

        let T_1 = gen.pedersen_generators.commit(t_poly.t1, t_1_blinding);
        let T_3 = gen.pedersen_generators.commit(t_poly.t3, t_3_blinding);
        let T_4 = gen.pedersen_generators.commit(t_poly.t4, t_4_blinding);
        let T_5 = gen.pedersen_generators.commit(t_poly.t5, t_5_blinding);
        let T_6 = gen.pedersen_generators.commit(t_poly.t6, t_6_blinding);
        transcript.commit(T_1.compress().as_bytes());
        transcript.commit(T_3.compress().as_bytes());
        transcript.commit(T_4.compress().as_bytes());
        transcript.commit(T_5.compress().as_bytes());
        transcript.commit(T_6.compress().as_bytes());
    
        let x = transcript.challenge_scalar();
    
        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let l_vec = l_poly.eval(x);
        let r_vec = r_poly.eval(x);
        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));
    
        CircuitProof {
            A_I, A_O, S,
            T_1, T_3, T_4, T_5, T_6,
            t_x, t_x_blinding, e_blinding,
            l_vec, r_vec,
        }
    }

    pub fn verify_proof(
        &self,
        gen: &Generators,
        transcript: &mut ProofTranscript,

        n: usize, // potentially calculate parameters ourselves
        m: usize,
        q: usize,

        W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>, // Q vectors, of length m each
        c: Vec<Scalar>,   
    ) -> Result<(), ()> {
        // TODO: check n, m, q against input sizes
        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        transcript.commit_u64(q as u64);
        transcript.commit(self.A_I.compress().as_bytes());
        transcript.commit(self.A_O.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();  

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_3.compress().as_bytes());
        transcript.commit(self.T_4.compress().as_bytes());
        transcript.commit(self.T_5.compress().as_bytes());
        transcript.commit(self.T_6.compress().as_bytes());
        let x = transcript.challenge_scalar();      

        let z_zQ_WL: Vec<Scalar> = matrix_flatten(W_L, z);
        let z_zQ_WR: Vec<Scalar> = matrix_flatten(W_R, z);
        let z_zQ_WO: Vec<Scalar> = matrix_flatten(W_O, z);
        let z_zQ_WV: Vec<Scalar> = matrix_flatten(W_V, z);

        if self.t_x == inner_product(&self.l_vec, &self.r_vec) {
            return Ok(());
        } else {
            return Err(());
        }
    }
}

// Computes z * z^Q * W, where W is a qxn matrix and z is a scalar.
pub fn matrix_flatten(W: Vec<Vec<Scalar>>, z: Scalar) -> Vec<Scalar> {
    let q = W.len();
    let n = W[0].len();
    let mut result = vec![Scalar::zero(); n];
    let mut exp_z = z; // z^n starting at n=1

    for row in 0..q {
        for col in 0..n {
            result[n] += z * W[row][col]
        }
        exp_z = exp_z * z; // z^n -> z^(n+1)
    }
    
    result
}

#[cfg(test)]
mod tests {
    use super::*;   
    use rand::rngs::OsRng;
    use generators::PedersenGenerators;

    #[test]
    // test basic multiplication circuit that computes a*b=c
    // potentially doesn't have to have any linear constraints (it's redundant).
    fn test_circuit_mult() {
        let n = 1;
        let m = 0;
        let q = 3;

        let zer = Scalar::zero();
        let one = Scalar::one();

        let W_L = vec![vec![zer], vec![zer], vec![one]];
        let W_R = vec![vec![zer], vec![one], vec![zer]];
        let W_O = vec![vec![one], vec![zer], vec![zer]];
        let W_V = vec![vec![], vec![], vec![]];
        let c = vec![Scalar::from_u64(6), Scalar::from_u64(3), Scalar::from_u64(2)];    
        let a_L = vec![Scalar::from_u64(2)];
        let a_R = vec![Scalar::from_u64(3)];
        let a_O = vec![Scalar::from_u64(6)];
        let v_blinding = vec![Scalar::zero(); 3]; // since we don't have anything to blind

        let generators = Generators::new(PedersenGenerators::default(), n, 1);
        let mut proof_transcript = ProofTranscript::new(b"CircuitProofTest-Multiplication");
        let mut rng = OsRng::new().unwrap();

        let circuit_proof = CircuitProof::generate_proof(
            &generators, &mut proof_transcript, &mut rng,
            n, m, q,
            W_L.clone(), W_R.clone(), W_O.clone(), W_V.clone(), c.clone(), a_L, a_R, a_O, v_blinding);

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest-Multiplication");

        assert!(circuit_proof.verify_proof(
            &generators,
            &mut verify_transcript,
            n, m, q,
            W_L, W_R, W_O, W_V, c, 
            )
        .is_ok());
    }
}