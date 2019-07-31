#![allow(non_snake_case)]

use clear_on_drop::clear::Clear;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::InnerProductProof;
use transcript::TranscriptProtocol;

/// An entry point for creating a R1CS proof.
///
/// The lifecycle of a `Prover` is as follows. The proving code
/// commits high-level variables and their blinding factors `(v, v_blinding)`,
/// `Prover` generates commitments, adds them to the transcript and returns
/// the corresponding variables.
///
/// After all variables are committed, the proving code calls `finalize_inputs`,
/// which consumes `Prover` and returns `ProverCS`.
/// The proving code then allocates low-level variables and adds constraints to the `ProverCS`.
///
/// When all constraints are added, the proving code calls `prove`
/// on the instance of the constraint system and receives the complete proof.
pub struct Prover<'a, 'b> {
    /// Number of high-level variables
    m: u64,

    /// Constraint system implementation
    cs: ProverCS<'a, 'b>,
}

/// A [`ConstraintSystem`] implementation for use by the prover.
pub struct ProverCS<'a, 'b> {
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    /// The constraints accumulated so far.
    constraints: Vec<LinearCombination>,
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<Scalar>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<Scalar>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<Scalar>,
    /// High-level witness data (value openings to V commitments)
    v: Vec<Scalar>,
    /// High-level witness data (blinding openings to V commitments)
    v_blinding: Vec<Scalar>,
}

/// Overwrite secrets with null bytes when they go out of scope.
impl<'a, 'b> Drop for ProverCS<'a, 'b> {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.clear();

        // Important: due to how ClearOnDrop auto-implements InitializableFromZeroed
        // for T: Default, calling .clear() on Vec compiles, but does not
        // clear the content. Instead, it only clears the Vec's header.
        // Clearing the underlying buffer item-by-item will do the job, but will
        // keep the header as-is, which is fine since the header does not contain secrets.
        for e in self.a_L.iter_mut() {
            e.clear();
        }
        for e in self.a_R.iter_mut() {
            e.clear();
        }
        for e in self.a_O.iter_mut() {
            e.clear();
        }
        // XXX use ClearOnDrop instead of doing the above
    }
}

impl<'a, 'b> ConstraintSystem for ProverCS<'a, 'b> {
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let (l, r, o) = assign_fn()?;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Prover<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Prover {
            m: 0,
            cs: ProverCS {
                pc_gens,
                bp_gens,
                transcript,
                v: Vec::new(),
                v_blinding: Vec::new(),
                constraints: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
            },
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitment to the external variable for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, v: Scalar, v_blinding: Scalar) -> (CompressedRistretto, Variable) {
        let i = self.m as usize;
        self.m += 1;
        self.cs.v.push(v);
        self.cs.v_blinding.push(v_blinding);

        // Add the commitment to the transcript.
        let V = self.cs.pc_gens.commit(v, v_blinding).compress();
        self.cs.transcript.append_point(b"V", &V);

        (V, Variable::Committed(i))
    }

    /// Consume the `Prover`, provide the `ConstraintSystem` implementation to the closure,
    /// and produce a proof.
    pub fn finalize_inputs(self) -> ProverCS<'a, 'b> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.cs.transcript.append_u64(b"m", self.m);
        self.cs
    }
}

impl<'a, 'b> ProverCS<'a, 'b> {
    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                coeff
                    * match var {
                        Variable::MultiplierLeft(i) => self.a_L[*i],
                        Variable::MultiplierRight(i) => self.a_R[*i],
                        Variable::MultiplierOutput(i) => self.a_O[*i],
                        Variable::Committed(i) => self.v[*i],
                        Variable::One() => Scalar::one(),
                    }
            })
            .sum()
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(mut self) -> Result<R1CSProof, R1CSError> {
        use std::iter;
        use util;

        // 0. Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.a_L.len();
        let padded_n = self.a_L.len().next_power_of_two();
        let pad = padded_n - n;

        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.bp_gens.share(0);

        // 1. Create a `TranscriptRng` from the high-level witness data
        //
        // The prover wants to rekey the RNG with its witness data.
        //
        // This consists of the high level witness data (the v's and
        // v_blinding's), as well as the low-level witness data (a_L,
        // a_R, a_O).  Since the low-level data should (hopefully) be
        // determined by the high-level data, it doesn't give any
        // extra entropy for reseeding the RNG.
        //
        // Since the v_blindings should be random scalars (in order to
        // protect the v's in the commitments), we don't gain much by
        // committing the v's as well as the v_blinding's.
        let mut rng = {
            let mut builder = self.transcript.build_rng();

            // Commit the blinding factors for the input wires
            for v_b in &self.v_blinding {
                builder = builder.rekey_with_witness_bytes(b"v_blinding", v_b.as_bytes());
            }

            use rand::thread_rng;
            builder.finalize(&mut thread_rng())
        };

        // 3. Choose blinding factors and form commitments to low-level witness data

        let i_blinding = Scalar::random(&mut rng);
        let o_blinding = Scalar::random(&mut rng);
        let s_blinding = Scalar::random(&mut rng);

        let mut s_L: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding)
                .chain(self.a_L.iter())
                .chain(self.a_R.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n))
                .chain(gens.H(n)),
        )
        .compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding).chain(self.a_O.iter()),
            iter::once(&self.pc_gens.B_blinding).chain(gens.G(n)),
        )
        .compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n))
                .chain(gens.H(n)),
        )
        .compress();

        self.transcript.append_point(b"A_I", &A_I);
        self.transcript.append_point(b"A_O", &A_O);
        self.transcript.append_point(b"S", &S);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let y_inv = y.invert();
        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();

        for i in 0..n {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = self.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = s_L[i];
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = wO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * self.a_R[i] + wL[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * s_R[i];

            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let t_poly = util::VecPoly3::special_inner_product(&l_poly, &r_poly);

        let t_1_blinding = Scalar::random(&mut rng);
        let t_3_blinding = Scalar::random(&mut rng);
        let t_4_blinding = Scalar::random(&mut rng);
        let t_5_blinding = Scalar::random(&mut rng);
        let t_6_blinding = Scalar::random(&mut rng);

        let T_1 = self.pc_gens.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = self.pc_gens.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = self.pc_gens.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = self.pc_gens.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = self.pc_gens.commit(t_poly.t6, t_6_blinding).compress();

        self.transcript.append_point(b"T_1", &T_1);
        self.transcript.append_point(b"T_3", &T_3);
        self.transcript.append_point(b"T_4", &T_4);
        self.transcript.append_point(b"T_5", &T_5);
        self.transcript.append_point(b"T_6", &T_6);

        let x = self.transcript.challenge_scalar(b"x");

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = wV
            .iter()
            .zip(self.v_blinding.iter())
            .map(|(c, v_blinding)| c * v_blinding)
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
        let mut l_vec = l_poly.eval(x);
        l_vec.append(&mut vec![Scalar::zero(); pad]);

        let mut r_vec = r_poly.eval(x);
        r_vec.append(&mut vec![Scalar::zero(); pad]);

        // XXX this should refer to the notes to explain why this is correct
        for i in n..padded_n {
            r_vec[i] = -exp_y;
            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        self.transcript.append_scalar(b"t_x", &t_x);
        self.transcript
            .append_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.append_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let ipp_proof = InnerProductProof::create(
            self.transcript,
            &Q,
            &exp_y_inv,
            gens.G(padded_n).cloned().collect(),
            gens.H(padded_n).cloned().collect(),
            l_vec,
            r_vec,
        );

        // We do not yet have a ClearOnDrop wrapper for Vec<Scalar>.
        // When PR 202 [1] is merged, we can simply wrap s_L and s_R at the point of creation.
        // [1] https://github.com/dalek-cryptography/curve25519-dalek/pull/202
        for e in s_L.iter_mut() {
            e.clear();
        }
        for e in s_R.iter_mut() {
            e.clear();
        }

        Ok(R1CSProof {
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
}
