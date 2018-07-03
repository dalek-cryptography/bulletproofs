#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};
use std::iter;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, MultiscalarMul, VartimeMultiscalarMul};

use generators::Generators;
use proof_transcript::ProofTranscript;  
use util;
use inner_product_proof::{inner_product, InnerProductProof};

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
    pub ipp_proof: InnerProductProof,
}

impl CircuitProof {
    // XXX removed `c` (constants vector) from prover input, since prover doesn't use it to create proof.
    pub fn prove<R: Rng + CryptoRng>(
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    
        n: usize,
        m: usize,
        q: usize,

        W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>, // Q vectors, of length m each
        a_L: Vec<Scalar>,
        a_R: Vec<Scalar>,
        a_O: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
    ) -> Result<CircuitProof, &'static str> {
        if W_L.len() != q || W_R.len() != q || W_O.len() != q || W_V.len() != q {
            return Err("Matrix size doesn't match specified parameters.");
        }
        if a_L.len() != n || a_R.len() != n || a_O.len() != n || v_blinding.len() != m {
            return Err("Input vector size doesn't match specified parameters.");
        }
        if gen.n != n {
            return Err("Generator length doesn't match specified parameters.");
        }

        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);
        transcript.commit_u64(q as u64);
    
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
        
        let z_zQ_WL: Vec<Scalar> = matrix_flatten(W_L, z, n);
        let z_zQ_WR: Vec<Scalar> = matrix_flatten(W_R, z, n);
        let z_zQ_WO: Vec<Scalar> = matrix_flatten(W_O, z, n);
    
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

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = W_V.iter()
            .zip(util::exp_iter(z))
            .map(|(W_V_i, exp_z)| z * exp_z * inner_product(&W_V_i, &v_blinding))
            .sum();

        let t_blinding_poly = util::Poly6 {
            t1: t_1_blinding,
            t2: t_2_blinding, 
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };
    
        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);
        let l_vec = l_poly.eval(x);
        let r_vec = r_poly.eval(x);
        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        transcript.commit(t_x.as_bytes());
        transcript.commit(t_x_blinding.as_bytes());
        transcript.commit(e_blinding.as_bytes());

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar();
        let Q = w * gen.pedersen_generators.B;

        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            util::exp_iter(y.invert()),
            gen.G.to_vec(),
            gen.H.to_vec(),
            l_vec.clone(),
            r_vec.clone(),
        );
    
        Ok(CircuitProof {
            A_I, A_O, S,
            T_1, T_3, T_4, T_5, T_6,
            t_x, t_x_blinding, e_blinding,
            l_vec, r_vec, ipp_proof,
        })
    }

    pub fn verify_proof<R: Rng + CryptoRng>(
        &self,
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,

        n: usize,
        m: usize,
        q: usize,

        W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>, // Q vectors, of length m each
        c: Vec<Scalar>,
        V: Vec<RistrettoPoint>, // Vector of commitments, length m
    ) -> Result<(), &'static str> {
        if W_L.len() != q || W_R.len() != q || W_O.len() != q || W_V.len() != q {
            return Err("Matrix size doesn't match specified parameters.");
        }
        if c.len() != q || V.len() != m {
            return Err("Input vector size doesn't match specified parameters.");
        }
        if gen.n != n {
            return Err("Generator length doesn't match specified parameters.");
        }

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

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());
        let w = transcript.challenge_scalar();

        let r = Scalar::random(rng);

        // Calculte points that represent the matrices
        let H_prime: Vec<RistrettoPoint> = gen.H
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(H_i, exp_y_inv)| H_i * exp_y_inv)
            .collect();
        // W_L_point = <h * y^-n , z * z^Q * W_L>, line 81
        let W_L_flatten: Vec<Scalar> = matrix_flatten(W_L, z, n);
        let W_L_point = RistrettoPoint::vartime_multiscalar_mul(
            W_L_flatten.clone(),
            H_prime.iter()
        );
        // W_R_point = <g , y^-n * z * z^Q * W_R>, line 82
        let W_R_flatten: Vec<Scalar> = matrix_flatten(W_R, z, n);
        let W_R_flatten_yinv: Vec<Scalar> = W_R_flatten
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(W_R_right_i, exp_y_inv)| W_R_right_i * exp_y_inv)
            .collect();
        let W_R_point = RistrettoPoint::vartime_multiscalar_mul(
            W_R_flatten_yinv.clone(),
            gen.G.iter()
        );  
        // W_O_point = <h * y^-n , z * z^Q * W_O>, line 83
        let W_O_flatten: Vec<Scalar> = matrix_flatten(W_O, z, n);
        let W_O_point = RistrettoPoint::vartime_multiscalar_mul(
            W_O_flatten,
            H_prime.iter()
        );

        // Get IPP variables
        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev().take(n);
        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // define parameters for P check
        let g = s.iter().take(n).map(|s_i| - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .map(|(s_i_inv, exp_y_inv)| - exp_y_inv * b * s_i_inv - Scalar::one());

        // define parameters for t check
        let delta = inner_product(&W_R_flatten_yinv, &W_L_flatten);
        let powers_of_z: Vec<Scalar> = util::exp_iter(z).take(q).collect();
        let z_c = z * inner_product(&powers_of_z, &c);
        let W_V_flatten: Vec<Scalar> = matrix_flatten(W_V, z, m);
        let V_multiplier = W_V_flatten.iter().map(|W_V_i| r * x * x * W_V_i);

        let mega_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(x) // A_I
                .chain(iter::once(x * x)) // A_O
                .chain(iter::once(x)) // W_L_point
                .chain(iter::once(x)) // W_R_point
                .chain(iter::once(Scalar::one())) // W_O_point
                .chain(iter::once(x * x * x)) // S
                .chain(iter::once(w * (self.t_x - a * b) + r * (x * x * (delta + z_c) - self.t_x))) // B
                .chain(iter::once(-self.e_blinding - r * self.t_x_blinding)) // B_blinding
                .chain(g) // G
                .chain(h) // H
                .chain(x_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(x_inv_sq.iter().cloned()) // ipp_proof.R_vec
                .chain(V_multiplier) // V
                .chain(iter::once(r * x)) // T_1
                .chain(iter::once(r * x * x * x)) // T_3
                .chain(iter::once(r * x * x * x * x)) // T_4
                .chain(iter::once(r * x * x * x * x * x)) // T_5
                .chain(iter::once(r * x * x * x * x * x * x)), // T_6
            iter::once(&self.A_I)
                .chain(iter::once(&self.A_O))
                .chain(iter::once(&W_L_point))
                .chain(iter::once(&W_R_point))
                .chain(iter::once(&W_O_point))
                .chain(iter::once(&self.S))
                .chain(iter::once(&gen.pedersen_generators.B))
                .chain(iter::once(&gen.pedersen_generators.B_blinding))
                .chain(gen.G.iter())
                .chain(gen.H.iter())
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter())
                .chain(V.iter())
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_3))
                .chain(iter::once(&self.T_4))
                .chain(iter::once(&self.T_5))
                .chain(iter::once(&self.T_6))
        );

        if !mega_check.is_identity() {
            return Err("Circuit did not verify correctly.");
        }

        Ok(())
    }
}

// Computes z * z^Q * W, where W is a qxn matrix and z is a scalar.
// Input: Qxn matrix of scalars and scalar z
// Output: length n vector of Scalars
pub fn matrix_flatten(W: Vec<Vec<Scalar>>, z: Scalar, output_dim: usize) -> Vec<Scalar> {
    let q = W.len();
   
    let mut result = vec![Scalar::zero(); output_dim];
    let mut exp_z = z; // z^n starting at n=1

    for row in 0..q {
        for col in 0..output_dim {
            result[col] += exp_z * W[row][col];
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

    fn create_and_verify_helper(
        n: usize,
        m: usize,
        q: usize,
        W_L: Vec<Vec<Scalar>>, // Q vectors, of length n each
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>, // Q vectors, of length m each
        c: Vec<Scalar>,  
        a_L: Vec<Scalar>,
        a_R: Vec<Scalar>,
        a_O: Vec<Scalar>,
        V: Vec<RistrettoPoint>, 
        v_blinding: Vec<Scalar>,
    ) -> Result<(), &'static str> {
        let generators = Generators::new(PedersenGenerators::default(), n, 1);
        let mut proof_transcript = ProofTranscript::new(b"CircuitProofTest");
        let mut rng = OsRng::new().unwrap();

        let circuit_proof = CircuitProof::prove(
            &generators, &mut proof_transcript, &mut rng,
            n, m, q,
            W_L.clone(), W_R.clone(), W_O.clone(), W_V.clone(), 
            a_L, a_R, a_O, v_blinding).unwrap();    

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest");

        circuit_proof.verify_proof(
            &generators,
            &mut verify_transcript,
            &mut rng,
            n, m, q,
            W_L, W_R, W_O, W_V, c, V,
        )
    }

    fn blinding_helper(v: &Vec<Scalar>) -> (Vec<RistrettoPoint>, Vec<Scalar>) {
        let generators = Generators::new(PedersenGenerators::default(), 1, 1);
        let mut rng = OsRng::new().unwrap();
        let m = v.len();

        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();
        let V: Vec<RistrettoPoint> = v.iter()
            .zip(v_blinding.clone())
            .map(|(v_i, v_blinding_i)| 
                generators.pedersen_generators.commit(*v_i, v_blinding_i)
            )
            .collect();

        (V, v_blinding)
    }

    #[test]
    // Test that a basic multiplication circuit on inputs (with linear contraints) succeeds
    // LINEAR CONSTRAINTS:
    // a_L[0] = 2
    // a_R[0] = 3
    // a_O[0] = 6
    // MUL CONSTRAINTS (implicit):
    // a_L[0] * a_R[0] = a_O[0]
    fn mul_circuit_1_succeed() {
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
        let V = vec![]; 
        let v_blinding = vec![]; // since we don't have anything to blind

        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_ok());
    }

    #[test]
    // Test that a basic multiplication circuit on inputs (with linear constraints) fails
    // LINEAR CONSTRAINTS:
    // a_L[0] = 2
    // a_R[0] = 3
    // a_O[0] = 7
    // MUL CONSTRAINTS (implicit):
    // a_L[0] * a_R[0] = a_O[0]    
    fn mul_circuit_1_fail() {
        let n = 1;
        let m = 0;
        let q = 3;

        let zer = Scalar::zero();
        let one = Scalar::one();

        let W_L = vec![vec![zer], vec![zer], vec![one]];
        let W_R = vec![vec![zer], vec![one], vec![zer]];
        let W_O = vec![vec![one], vec![zer], vec![zer]];
        let W_V = vec![vec![], vec![], vec![]];
        let c = vec![Scalar::from_u64(7), Scalar::from_u64(3), Scalar::from_u64(2)];  
        let a_L = vec![Scalar::from_u64(2)];
        let a_R = vec![Scalar::from_u64(3)];
        let a_O = vec![Scalar::from_u64(7)];
        let V = vec![];  
        let v_blinding = vec![]; // since we don't have anything to blind

        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_err());
    }

    #[test]
    // Test that a basic multiplication circuit on inputs (without linear contraints) succeeds
    // LINEAR CONSTRAINTS: none
    // MUL CONSTRAINTS:
    // a_L[0] * a_R[0] = a_O[0]
    fn mul_circuit_2_succeed() {
        let n = 1;
        let m = 0;
        let q = 0;

        let W_L = vec![];
        let W_R = vec![];
        let W_O = vec![];
        let W_V = vec![];
        let c = vec![];    
        let a_L = vec![Scalar::from_u64(2)];
        let a_R = vec![Scalar::from_u64(3)];
        let a_O = vec![Scalar::from_u64(6)];
        let V = vec![]; 
        let v_blinding = vec![]; 

        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_ok());
    }

    #[test]
    // Test that a basic multiplication circuit on inputs (without linear contraints) fails
    // LINEAR CONSTRAINTS: none
    // MUL CONSTRAINTS:
    // a_L[0] * a_R[0] = a_O[0]
    fn mul_circuit_2_fail() {
        let n = 1;
        let m = 0;
        let q = 0;

        let W_L = vec![];
        let W_R = vec![];
        let W_O = vec![];
        let W_V = vec![];
        let c = vec![];    
        let a_L = vec![Scalar::from_u64(2)];
        let a_R = vec![Scalar::from_u64(3)];
        let a_O = vec![Scalar::from_u64(7)];
        let V = vec![]; 
        let v_blinding = vec![]; 

        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_err());
    }

    #[test]
    // Test that a basic addition circuit (without multiplication gates) succeeds
    // LINEAR CONSTRAINTS:
    // V[0] + V[1] = V[2]
    // MUL CONSTRAINTS: none
    fn add_circuit_succeed() {
        let n = 0;
        let m = 3;
        let q = 1;

        let one = Scalar::one();
        let zer = Scalar::zero();

        let W_L = vec![vec![]];
        let W_R = vec![vec![]];
        let W_O = vec![vec![]];
        let W_V = vec![vec![one, one, -one]];
        let c = vec![zer];
        let a_L = vec![]; 
        let a_R = vec![]; 
        let a_O = vec![];    

        let v = vec![one, Scalar::from_u64(3), Scalar::from_u64(4)];
        let (V, v_blinding) = blinding_helper(&v);
        
        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_ok());
    }

    #[test]
    // Test that a basic addition circuit (without multiplication gates) fails
    // LINEAR CONSTRAINTS:
    // V[0] + V[1] = V[2]
    // MUL CONSTRAINTS: none
    fn add_circuit_fail() {
        let n = 0;
        let m = 3;
        let q = 1;

        let one = Scalar::one();
        let zer = Scalar::zero();

        let W_L = vec![vec![]];
        let W_R = vec![vec![]];
        let W_O = vec![vec![]];
        let W_V = vec![vec![one, one, -one]];
        let c = vec![zer];
        let a_L = vec![]; 
        let a_R = vec![]; 
        let a_O = vec![];    

        let v = vec![zer, Scalar::from_u64(3), Scalar::from_u64(4)];
        let (V, v_blinding) = blinding_helper(&v);
        
        assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_err());
    }

    #[test]
    // Test that a 2 in 2 out shuffle circuit succeeds
    // LINEAR CONSTRAINTS:
    // a_O[0] = a_O[1]
    // a_L[0] = V[0] - z
    // a_L[1] = V[2] - z
    // a_R[0] = V[1] - z
    // a_R[1] = V[3] - z
    // MUL CONSTRAINTS:
    // a_L[0] * a_R[0] = a_O[0]
    // a_L[1] * a_R[1] = a_O[1]
    fn shuffle_circuit_succeed() {
        let n = 2;
        let m = 4;
        let q = 5;

        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut rng = OsRng::new().unwrap();
        // TODO: is this the best way to generate z? Maybe z generation should be deterministic, 
        // based on public inputs, so you can't maliciously choose a z value.
        let z = Scalar::random(&mut rng); 

        let W_L = vec![vec![zer, zer], vec![one, zer], vec![zer, one], vec![zer, zer], vec![zer, zer]];
        let W_R = vec![vec![zer, zer], vec![zer, zer], vec![zer, zer], vec![one, zer], vec![zer, one]];
        let W_O = vec![vec![one, -one], vec![zer, zer], vec![zer, zer], vec![zer, zer], vec![zer, zer]];
        let W_V = vec![vec![zer, zer, zer, zer],
                       vec![one, zer, zer, zer],
                       vec![zer, zer, one, zer],
                       vec![zer, one, zer, zer],
                       vec![zer, zer, zer, one]];
        let c = vec![zer, -z, -z, -z, -z];

        let v = vec![Scalar::from_u64(3), Scalar::from_u64(7), Scalar::from_u64(7), Scalar::from_u64(3)];
        let (V, v_blinding) = blinding_helper(&v);

        let a_L = vec![v[0] - z, v[2] - z];
        let a_R = vec![v[1] - z, v[3] - z];
        let a_O = vec![a_L[0] * a_R[0], a_L[1] * a_R[1]];

       assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_ok());
    }

    #[test]
    // Test that a 2 in 2 out shuffle circuit fails
    // LINEAR CONSTRAINTS:
    // a_O[0] = a_O[1]
    // a_L[0] = V[0] - z
    // a_L[1] = V[2] - z
    // a_R[0] = V[1] - z
    // a_R[1] = V[3] - z
    // MUL CONSTRAINTS:
    // a_L[0] * a_R[0] = a_O[0]
    // a_L[1] * a_R[1] = a_O[1]
    fn shuffle_circuit_fail() {
        let n = 2;
        let m = 4;
        let q = 5;

        let one = Scalar::one();
        let zer = Scalar::zero();

        let mut rng = OsRng::new().unwrap();
        let z = Scalar::random(&mut rng);

        let W_L = vec![vec![zer, zer], vec![one, zer], vec![zer, one], vec![zer, zer], vec![zer, zer]];
        let W_R = vec![vec![zer, zer], vec![zer, zer], vec![zer, zer], vec![one, zer], vec![zer, one]];
        let W_O = vec![vec![one, -one], vec![zer, zer], vec![zer, zer], vec![zer, zer], vec![zer, zer]];
        let W_V = vec![vec![zer, zer, zer, zer],
                       vec![one, zer, zer, zer],
                       vec![zer, zer, one, zer],
                       vec![zer, one, zer, zer],
                       vec![zer, zer, zer, one]];
        let c = vec![zer, -z, -z, -z, -z];

        let v = vec![Scalar::from_u64(3), Scalar::from_u64(7), Scalar::from_u64(8), Scalar::from_u64(3)];
        let (V, v_blinding) = blinding_helper(&v);

        let a_L = vec![v[0] - z, v[2] - z];
        let a_R = vec![v[1] - z, v[3] - z];
        let a_O = vec![a_L[0] * a_R[0], a_L[1] * a_R[1]];

       assert!(create_and_verify_helper(
            n, m, q,
            W_L, W_R, W_O, W_V,
            c, a_L, a_R, a_O, 
            V, v_blinding,
        ).is_err());
    }
}