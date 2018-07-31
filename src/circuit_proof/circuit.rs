#![allow(non_snake_case)]

use rand::{CryptoRng, Rng};
use std::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, MultiscalarMul, VartimeMultiscalarMul};

use generators::Generators;
use inner_product_proof::{inner_product, InnerProductProof};
use proof_transcript::ProofTranscript;
use util;

#[derive(Clone, Debug)]
pub struct Circuit {
    pub n: usize,
    m: usize,
    q: usize,
    c: Vec<Scalar>,        // vector of constants, length q
    W_L: Vec<Vec<Scalar>>, // q vectors, of length n each
    W_R: Vec<Vec<Scalar>>,
    W_O: Vec<Vec<Scalar>>,
    W_V: Vec<Vec<Scalar>>, // q vectors, of length m each
}

impl Circuit {
    pub fn check_parameters(&self) -> Result<(), &'static str> {
        if self.W_L.len() != self.q
            || self.W_R.len() != self.q
            || self.W_O.len() != self.q
            || self.W_V.len() != self.q
        {
            return Err("Circuit matrix size doesn't match specified parameters.");
        }
        if self.c.len() != self.q {
            return Err("Circuit constants vector size doesn't match specified parameters.");
        }
        Ok(())
    }

    // does not check that the parameters are valid.
    pub fn new(
        n: usize,
        m: usize,
        q: usize,
        c: Vec<Scalar>,
        W_L: Vec<Vec<Scalar>>,
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>,
    ) -> Self {
        Circuit {
            n,
            m,
            q,
            c,
            W_L,
            W_R,
            W_O,
            W_V,
        }
    }
}

pub struct ProverInput {
    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    v_blinding: Vec<Scalar>,
}

impl ProverInput {
    pub fn new(
        a_L: Vec<Scalar>,
        a_R: Vec<Scalar>,
        a_O: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
    ) -> Self {
        ProverInput {
            a_L,
            a_R,
            a_O,
            v_blinding,
        }
    }
}

pub struct VerifierInput {
    V: Vec<RistrettoPoint>,
}

impl VerifierInput {
    pub fn new(V: Vec<RistrettoPoint>) -> Self {
        VerifierInput { V }
    }
}

#[derive(Clone, Debug)]
pub struct CircuitProof {
    /// Commitment to the values of input wires
    A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    T_6: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl CircuitProof {
    pub fn new(
        A_I: CompressedRistretto,
        A_O: CompressedRistretto,
        S: CompressedRistretto,
        T_1: CompressedRistretto,
        T_3: CompressedRistretto,
        T_4: CompressedRistretto,
        T_5: CompressedRistretto,
        T_6: CompressedRistretto,
        t_x: Scalar,
        t_x_blinding: Scalar,
        e_blinding: Scalar,
        ipp_proof: InnerProductProof,
    ) -> Self {
        CircuitProof {
            A_I, 
            A_O,
            S,
            T_1,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        }
    }
    /// Create a circuit proof.
    /// `circuit.n` must be either 0 or a power of 2, for the inner product proof to work.
    pub fn prove<R: Rng + CryptoRng>(
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        circuit: &Circuit,
        prover_input: &ProverInput,
    ) -> Result<CircuitProof, &'static str> {
        circuit.check_parameters()?;
        if prover_input.a_L.len() != circuit.n
            || prover_input.a_R.len() != circuit.n
            || prover_input.a_O.len() != circuit.n
            || prover_input.v_blinding.len() != circuit.m
        {
            return Err("Input vector size doesn't match specified parameters.");
        }
        if gen.n != circuit.n {
            return Err("Generator length doesn't match specified parameters.");
        }
        if !(circuit.n.is_power_of_two() || circuit.n == 0) {
            return Err("Circuit's n parameter must be either 0 or a power of 2.");
        }

        transcript.commit_u64(circuit.n as u64);
        transcript.commit_u64(circuit.m as u64);
        transcript.commit_u64(circuit.q as u64);

        let i_blinding = Scalar::random(rng);
        let o_blinding = Scalar::random(rng);
        let s_blinding = Scalar::random(rng);
        let s_L: Vec<Scalar> = (0..circuit.n).map(|_| Scalar::random(rng)).collect();
        let s_R: Vec<Scalar> = (0..circuit.n).map(|_| Scalar::random(rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding)
                .chain(prover_input.a_L.iter())
                .chain(prover_input.a_R.iter()),
            iter::once(&gen.pedersen_gens.B_blinding)
                .chain(gen.G.iter())
                .chain(gen.H.iter()),
        ).compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding).chain(prover_input.a_O.iter()),
            iter::once(&gen.pedersen_gens.B_blinding).chain(gen.G.iter()),
        ).compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(&gen.pedersen_gens.B_blinding)
                .chain(gen.G.iter())
                .chain(gen.H.iter()),
        ).compress();

        transcript.commit(A_I.as_bytes());
        transcript.commit(A_O.as_bytes());
        transcript.commit(S.as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        let mut l_poly = util::VecPoly3::zero(circuit.n);
        let mut r_poly = util::VecPoly3::zero(circuit.n);

        let z_zQ_WL: Vec<Scalar> = matrix_flatten(&circuit.W_L, z, circuit.n)?;
        let z_zQ_WR: Vec<Scalar> = matrix_flatten(&circuit.W_R, z, circuit.n)?;
        let z_zQ_WO: Vec<Scalar> = matrix_flatten(&circuit.W_O, z, circuit.n)?;

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let mut exp_y_inv = Scalar::one(); // y^-n starting at n=0
        let y_inv = y.invert();

        for i in 0..circuit.n {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = prover_input.a_L[i] + exp_y_inv * z_zQ_WR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = prover_input.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = s_L[i];
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = z_zQ_WO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * prover_input.a_R[i] + z_zQ_WL[i];
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

        let T_1 = gen.pedersen_gens.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = gen.pedersen_gens.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = gen.pedersen_gens.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = gen.pedersen_gens.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = gen.pedersen_gens.commit(t_poly.t6, t_6_blinding).compress();

        transcript.commit(T_1.as_bytes());
        transcript.commit(T_3.as_bytes());
        transcript.commit(T_4.as_bytes());
        transcript.commit(T_5.as_bytes());
        transcript.commit(T_6.as_bytes());
        let x = transcript.challenge_scalar();

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = circuit
            .W_V
            .iter()
            .zip(util::exp_iter(z))
            .map(|(W_V_i, exp_z)| z * exp_z * inner_product(&W_V_i, &prover_input.v_blinding))
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
        let Q = w * gen.pedersen_gens.B;

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
            A_I,
            A_O,
            S,
            T_1,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }

    pub fn verify<R: Rng + CryptoRng>(
        &self,
        gen: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        circuit: &Circuit,
        verifier_input: &VerifierInput,
    ) -> Result<(), &'static str> {
        circuit.check_parameters()?;
        if verifier_input.V.len() != circuit.m {
            return Err("Commitments vector size doesn't match specified parameters.");
        }
        if gen.n != circuit.n {
            return Err("Generator length doesn't match specified parameters.");
        }

        transcript.commit_u64(circuit.n as u64);
        transcript.commit_u64(circuit.m as u64);
        transcript.commit_u64(circuit.q as u64);
        transcript.commit(self.A_I.as_bytes());
        transcript.commit(self.A_O.as_bytes());
        transcript.commit(self.S.as_bytes());
        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();

        transcript.commit(self.T_1.as_bytes());
        transcript.commit(self.T_3.as_bytes());
        transcript.commit(self.T_4.as_bytes());
        transcript.commit(self.T_5.as_bytes());
        transcript.commit(self.T_6.as_bytes());
        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());
        let w = transcript.challenge_scalar();

        let r = Scalar::random(rng);
        let xx = x * x;

        // Decompress points
        let S = self.S.decompress().ok_or_else(|| "Invalid proof point")?;
        let A_I = self.A_I.decompress().ok_or_else(|| "Invalid proof point")?;
        let A_O = self.A_O.decompress().ok_or_else(|| "Invalid proof point")?;
        let T_1 = self.T_1.decompress().ok_or_else(|| "Invalid proof point")?;
        let T_3 = self.T_3.decompress().ok_or_else(|| "Invalid proof point")?;
        let T_4 = self.T_4.decompress().ok_or_else(|| "Invalid proof point")?;
        let T_5 = self.T_5.decompress().ok_or_else(|| "Invalid proof point")?;
        let T_6 = self.T_6.decompress().ok_or_else(|| "Invalid proof point")?;

        // Calculate points that represent the matrices
        let H_prime: Vec<RistrettoPoint> = gen
            .H
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(H_i, exp_y_inv)| H_i * exp_y_inv)
            .collect();

        // W_L_point = <h * y^-n , z * z^Q * W_L>, line 81
        let W_L_flatten: Vec<Scalar> = matrix_flatten(&circuit.W_L, z, circuit.n)?;
        let W_L_point =
            RistrettoPoint::vartime_multiscalar_mul(W_L_flatten.clone(), H_prime.iter());

        // W_R_point = <g , y^-n * z * z^Q * W_R>, line 82
        let W_R_flatten: Vec<Scalar> = matrix_flatten(&circuit.W_R, z, circuit.n)?;
        let W_R_flatten_yinv: Vec<Scalar> = W_R_flatten
            .iter()
            .zip(util::exp_iter(y.invert()))
            .map(|(W_R_right_i, exp_y_inv)| W_R_right_i * exp_y_inv)
            .collect();
        let W_R_point =
            RistrettoPoint::vartime_multiscalar_mul(W_R_flatten_yinv.clone(), gen.G.iter());

        // W_O_point = <h * y^-n , z * z^Q * W_O>, line 83
        let W_O_flatten: Vec<Scalar> = matrix_flatten(&circuit.W_O, z, circuit.n)?;
        let W_O_point = RistrettoPoint::vartime_multiscalar_mul(W_O_flatten, H_prime.iter());

        // Get IPP variables
        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev().take(circuit.n);
        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // define parameters for P check
        let g = s.iter().take(circuit.n).map(|s_i| -a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .map(|(s_i_inv, exp_y_inv)| -exp_y_inv * b * s_i_inv - Scalar::one());

        // define parameters for t check
        let delta = inner_product(&W_R_flatten_yinv, &W_L_flatten);
        let powers_of_z: Vec<Scalar> = util::exp_iter(z).take(circuit.q).collect();
        let z_c = z * inner_product(&powers_of_z, &circuit.c);
        let W_V_flatten: Vec<Scalar> = matrix_flatten(&circuit.W_V, z, circuit.m)?;
        let V_multiplier = W_V_flatten.iter().map(|W_V_i| r * xx * W_V_i);

        // group the T_scalars and T_points together
        let T_scalars = [
            r * x,
            r * xx * x,
            r * xx * xx,
            r * xx * xx * x,
            r * xx * xx * xx,
        ];
        let T_points = [T_1, T_3, T_4, T_5, T_6];

        // Decompress L and R points from inner product proof
        let Ls = self
            .ipp_proof
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or("RangeProof's L point is invalid"))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .ipp_proof
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or("RangeProof's R point is invalid"))
            .collect::<Result<Vec<_>, _>>()?;

        let mega_check = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(x) // A_I
                .chain(iter::once(xx)) // A_O
                .chain(iter::once(x)) // W_L_point
                .chain(iter::once(x)) // W_R_point
                .chain(iter::once(Scalar::one())) // W_O_point
                .chain(iter::once(x * xx)) // S
                .chain(iter::once(w * (self.t_x - a * b) + r * (xx * (delta + z_c) - self.t_x))) // B
                .chain(iter::once(-self.e_blinding - r * self.t_x_blinding)) // B_blinding
                .chain(g) // G
                .chain(h) // H
                .chain(x_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(x_inv_sq.iter().cloned()) // ipp_proof.R_vec
                .chain(V_multiplier) // V
                .chain(T_scalars.iter().cloned()), // T_points
            iter::once(&A_I)
                .chain(iter::once(&A_O))
                .chain(iter::once(&W_L_point))
                .chain(iter::once(&W_R_point))
                .chain(iter::once(&W_O_point))
                .chain(iter::once(&S))
                .chain(iter::once(&gen.pedersen_gens.B))
                .chain(iter::once(&gen.pedersen_gens.B_blinding))
                .chain(gen.G.iter())
                .chain(gen.H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter())
                .chain(verifier_input.V.iter())
                .chain(T_points.iter()),
        );

        if !mega_check.is_identity() {
            return Err("Circuit did not verify correctly.");
        }

        Ok(())
    }
}

// Computes z * z^Q * W, where W is a qx(n or m) matrix and z is a scalar.
// Input: Qx(n or m) matrix of scalars and scalar z
// Output: length (n or m) vector of Scalars
// Note: output_dim parameter is necessary in case W is `qxn` where `q=0`,
//       such that it is not possible to derive `n` from looking at W.
pub fn matrix_flatten(
    W: &Vec<Vec<Scalar>>,
    z: Scalar,
    output_dim: usize,
) -> Result<Vec<Scalar>, &'static str> {
    let mut result = vec![Scalar::zero(); output_dim];
    let mut exp_z = z; // z^n starting at n=1

    for row in 0..W.len() {
        if W[row].len() != output_dim {
            return Err("Matrix size doesn't match specified parameters in matrix_flatten");
        }
        for col in 0..output_dim {
            result[col] += exp_z * W[row][col];
        }
        exp_z = exp_z * z; // z^n -> z^(n+1)
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use generators::PedersenGenerators;
    use rand::rngs::OsRng;

    fn create_and_verify_helper(
        n: usize,
        m: usize,
        q: usize,
        c: Vec<Scalar>,
        W_L: Vec<Vec<Scalar>>,
        W_R: Vec<Vec<Scalar>>,
        W_O: Vec<Vec<Scalar>>,
        W_V: Vec<Vec<Scalar>>,
        a_L: Vec<Scalar>,
        a_R: Vec<Scalar>,
        a_O: Vec<Scalar>,
        V: Vec<RistrettoPoint>,
        v_blinding: Vec<Scalar>,
    ) -> Result<(), &'static str> {
        let generators = Generators::new(PedersenGenerators::default(), n, 1);
        let mut proof_transcript = ProofTranscript::new(b"CircuitProofTest");
        let mut rng = OsRng::new().unwrap();
        let circuit = Circuit::new(n, m, q, c, W_L, W_R, W_O, W_V);

        let prover_input = ProverInput::new(a_L, a_R, a_O, v_blinding);

        let circuit_proof = CircuitProof::prove(
            &generators,
            &mut proof_transcript,
            &mut rng,
            &circuit.clone(),
            &prover_input,
        ).unwrap();

        let mut verify_transcript = ProofTranscript::new(b"CircuitProofTest");

        let verifier_input = VerifierInput { V };

        circuit_proof.verify(
            &generators,
            &mut verify_transcript,
            &mut rng,
            &circuit,
            &verifier_input,
        )
    }

    fn blinding_helper(v: &Vec<Scalar>) -> (Vec<RistrettoPoint>, Vec<Scalar>) {
        let generators = Generators::new(PedersenGenerators::default(), 1, 1);
        let mut rng = OsRng::new().unwrap();
        let m = v.len();

        let v_blinding: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();
        let V: Vec<RistrettoPoint> = v
            .iter()
            .zip(v_blinding.clone())
            .map(|(v_i, v_blinding_i)| generators.pedersen_gens.commit(*v_i, v_blinding_i))
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
        let c = vec![Scalar::from(6u64), Scalar::from(3u64), Scalar::from(2u64)];
        let a_L = vec![Scalar::from(2u64)];
        let a_R = vec![Scalar::from(3u64)];
        let a_O = vec![Scalar::from(6u64)];
        let V = vec![];
        let v_blinding = vec![]; // since we don't have anything to blind

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_ok()
        );
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
        let c = vec![Scalar::from(7u64), Scalar::from(3u64), Scalar::from(2u64)];
        let a_L = vec![Scalar::from(2u64)];
        let a_R = vec![Scalar::from(3u64)];
        let a_O = vec![Scalar::from(7u64)];
        let V = vec![];
        let v_blinding = vec![]; // since we don't have anything to blind

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_err()
        );
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
        let a_L = vec![Scalar::from(2u64)];
        let a_R = vec![Scalar::from(3u64)];
        let a_O = vec![Scalar::from(6u64)];
        let V = vec![];
        let v_blinding = vec![];

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_ok()
        );
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
        let a_L = vec![Scalar::from(2u64)];
        let a_R = vec![Scalar::from(3u64)];
        let a_O = vec![Scalar::from(7u64)];
        let V = vec![];
        let v_blinding = vec![];

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_err()
        );
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

        let v = vec![one, Scalar::from(3u64), Scalar::from(4u64)];
        let (V, v_blinding) = blinding_helper(&v);

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_ok()
        );
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

        let v = vec![zer, Scalar::from(3u64), Scalar::from(4u64)];
        let (V, v_blinding) = blinding_helper(&v);

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_err()
        );
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

        let W_L = vec![
            vec![zer, zer],
            vec![one, zer],
            vec![zer, one],
            vec![zer, zer],
            vec![zer, zer],
        ];
        let W_R = vec![
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
            vec![one, zer],
            vec![zer, one],
        ];
        let W_O = vec![
            vec![one, -one],
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
        ];
        let W_V = vec![
            vec![zer, zer, zer, zer],
            vec![one, zer, zer, zer],
            vec![zer, zer, one, zer],
            vec![zer, one, zer, zer],
            vec![zer, zer, zer, one],
        ];
        let c = vec![zer, -z, -z, -z, -z];

        let v = vec![
            Scalar::from(3u64),
            Scalar::from(7u64),
            Scalar::from(7u64),
            Scalar::from(3u64),
        ];
        let (V, v_blinding) = blinding_helper(&v);

        let a_L = vec![v[0] - z, v[2] - z];
        let a_R = vec![v[1] - z, v[3] - z];
        let a_O = vec![a_L[0] * a_R[0], a_L[1] * a_R[1]];

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_ok()
        );
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

        let W_L = vec![
            vec![zer, zer],
            vec![one, zer],
            vec![zer, one],
            vec![zer, zer],
            vec![zer, zer],
        ];
        let W_R = vec![
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
            vec![one, zer],
            vec![zer, one],
        ];
        let W_O = vec![
            vec![one, -one],
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
            vec![zer, zer],
        ];
        let W_V = vec![
            vec![zer, zer, zer, zer],
            vec![one, zer, zer, zer],
            vec![zer, zer, one, zer],
            vec![zer, one, zer, zer],
            vec![zer, zer, zer, one],
        ];
        let c = vec![zer, -z, -z, -z, -z];

        let v = vec![
            Scalar::from(3u64),
            Scalar::from(7u64),
            Scalar::from(8u64),
            Scalar::from(3u64),
        ];
        let (V, v_blinding) = blinding_helper(&v);

        let a_L = vec![v[0] - z, v[2] - z];
        let a_R = vec![v[1] - z, v[3] - z];
        let a_O = vec![a_L[0] * a_R[0], a_L[1] * a_R[1]];

        assert!(
            create_and_verify_helper(n, m, q, c, W_L, W_R, W_O, W_V, a_L, a_R, a_O, V, v_blinding,)
                .is_err()
        );
    }
}
