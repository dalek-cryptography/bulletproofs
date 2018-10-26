#![allow(non_snake_case)]

use clear_on_drop::clear::Clear;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;

use super::{
    Assignment, AssignmentValue, CommittedConstraintSystem, Constraint, ConstraintSystem,
    OpaqueScalar, R1CSProof, Variable, VariableIndex,
};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::InnerProductProof;
use transcript::TranscriptProtocol;

/// A [`ConstraintSystem`] implementation for use by the prover.
///
/// The lifecycle of a `ProverCS` is as follows.  The proving code
/// assembles openings `(v, v_blinding)` to the commitments to the
/// inputs to the constraint system, then passes them, along with
/// generators and a transcript, to [`ProverCS::new`].  This
/// initializes the `ProverCS` and returns [`Variable`]s corresponding
/// to the inputs.
///
/// The prover can then pass the `ProverCS` and the external variables
/// to gadget code to build the constraints, before finally calling
/// [`ProverCS::prove`], which consumes the `ProverCS`, synthesizes
/// the witness, and constructs the proof.
pub struct ProverCS<'a, 'b> {
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    constraints: Vec<Constraint>,
    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    v: Vec<Scalar>,
    v_blinding: Vec<Scalar>,
    callbacks: Vec<Box<Fn(&mut CommittedProverCS<'a, 'b>) -> Result<(), R1CSError>>>,
}

pub struct CommittedProverCS<'a, 'b> {
    cs: ProverCS<'a, 'b>,
    committed_variables_count: usize,
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
    }
}

impl<'a, 'b> ConstraintSystem for ProverCS<'a, 'b> {
    type CommittedCS = CommittedProverCS<'a, 'b>;

    fn assign_multiplier<S: AssignmentValue + Into<OpaqueScalar>>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {
        // Unwrap all of l,r,o up front to ensure we leave the CS in a
        // consistent state if any are missing assignments
        let l = left?;
        let r = right?;
        let o = out?;
        // Now commit to the assignment
        self.a_L.push(l.into().internal_scalar);
        self.a_R.push(r.into().internal_scalar);
        self.a_O.push(o.into().internal_scalar);
        Ok((
            Variable {
                index: VariableIndex::MultiplierLeft(self.a_L.len() - 1),
                assignment: left,
            },
            Variable {
                index: VariableIndex::MultiplierRight(self.a_R.len() - 1),
                assignment: right,
            },
            Variable {
                index: VariableIndex::MultiplierOutput(self.a_O.len() - 1),
                assignment: out,
            },
        ))
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(constraint);
    }

    /// Adds a callback for when the constraint system’s free variables are committed.
    fn after_commitment<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        for<'t> F: 'static + Fn(&'t mut Self::CommittedCS) -> Result<(), R1CSError>,
    {
        self.callbacks.push(Box::new(callback));
        Ok(())
    }
}

impl<'a, 'b> ConstraintSystem for CommittedProverCS<'a, 'b> {
    type CommittedCS = CommittedProverCS<'a, 'b>;

    fn assign_multiplier<S: AssignmentValue + Into<OpaqueScalar>>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {
        self.cs.assign_multiplier(left, right, out)
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        self.cs.add_constraint(constraint)
    }

    /// Adds a callback for when the constraint system’s free variables are committed.
    fn after_commitment<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        for<'t> F: 'static + Fn(&'t mut Self::CommittedCS) -> Result<(), R1CSError>,
    {
        callback(self)
    }
}

impl<'a, 'b> CommittedConstraintSystem for CommittedProverCS<'a, 'b> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> OpaqueScalar {
        self.cs.transcript.challenge_scalar(label).into()
    }
}

impl<'a, 'b> ProverCS<'a, 'b> {
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
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitments to the external variables for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars, commitments)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    ///
    /// The third element is a list of the Pedersen commitments to the
    /// external inputs, returned for convenience.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        v: Vec<Scalar>,
        v_blinding: Vec<Scalar>,
    ) -> (Self, Vec<Variable<Scalar>>, Vec<CompressedRistretto>) {
        // Check that the input lengths are consistent
        assert_eq!(v.len(), v_blinding.len());
        let m = v.len();
        transcript.r1cs_domain_sep(m as u64);

        let mut variables = Vec::with_capacity(m);
        let mut commitments = Vec::with_capacity(m);

        for i in 0..m {
            // Generate pedersen commitment and commit it to the transcript
            let V = pc_gens.commit(v[i], v_blinding[i]).compress();
            transcript.commit_point(b"V", &V);
            commitments.push(V);

            // Allocate and return a variable for v_i
            variables.push(Variable {
                index: VariableIndex::Committed(i),
                assignment: v[i].into()
            });
        }

        let cs = ProverCS {
            pc_gens,
            bp_gens,
            transcript,
            v,
            v_blinding,
            constraints: vec![],
            a_L: vec![],
            a_R: vec![],
            a_O: vec![],
            callbacks: vec![],
        };

        (cs, variables, commitments)
    }

    pub(crate) fn commit(self) -> CommittedProverCS<'a,'b> {

        // TBD: create intermediate commitments,
        // send them to the transcript, continue.

        CommittedProverCS {
            committed_variables_count: self.a_L.len(),
            cs: self,
            // TBD: add commitment points here
        }
    }
}

impl<'a, 'b> CommittedProverCS<'a, 'b> {

    pub(crate) fn process_callbacks(&mut self) -> Result<(), R1CSError> {
         for closure in self.cs.callbacks.drain(..) {
             closure(&mut self)?
         }
         Ok(())
    }

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
        let n = self.cs.a_L.len();
        let m = self.cs.v.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];

        let mut exp_z = *z;
        for lc in self.cs.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    VariableIndex::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::Committed(i) => {
                        wV[*i] -= exp_z * coeff.internal_scalar;
                    }
                    VariableIndex::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(mut self) -> Result<R1CSProof, R1CSError> {
        use std::iter;
        use util;

        // 0. Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.cs.a_L.len();
        let padded_n = self.cs.a_L.len().next_power_of_two();
        let pad = padded_n - n;

        if self.cs.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.cs.bp_gens.share(0);

        // 1. Create a `TranscriptRng` from the high-level witness data

        let mut rng = {
            let mut builder = self.cs.transcript.build_rng();

            // Commit the blinding factors for the input wires
            for v_b in &self.cs.v_blinding {
                builder = builder.commit_witness_bytes(b"v_blinding", v_b.as_bytes());
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
                .chain(self.cs.a_L.iter())
                .chain(self.cs.a_R.iter()),
            iter::once(&self.cs.pc_gens.B_blinding)
                .chain(gens.G(n))
                .chain(gens.H(n)),
        )
        .compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding).chain(self.cs.a_O.iter()),
            iter::once(&self.cs.pc_gens.B_blinding).chain(gens.G(n)),
        )
        .compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
            iter::once(&self.cs.pc_gens.B_blinding)
                .chain(gens.G(n))
                .chain(gens.H(n)),
        )
        .compress();

        self.cs.transcript.commit_point(b"A_I", &A_I);
        self.cs.transcript.commit_point(b"A_O", &A_O);
        self.cs.transcript.commit_point(b"S", &S);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = self.cs.transcript.challenge_scalar(b"y");
        let z = self.cs.transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let y_inv = y.invert();
        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();

        for i in 0..n {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = self.cs.a_L[i] + exp_y_inv[i] * wR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = self.cs.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = s_L[i];
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = wO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * self.cs.a_R[i] + wL[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * s_R[i];

            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

        let t_1_blinding = Scalar::random(&mut rng);
        let t_3_blinding = Scalar::random(&mut rng);
        let t_4_blinding = Scalar::random(&mut rng);
        let t_5_blinding = Scalar::random(&mut rng);
        let t_6_blinding = Scalar::random(&mut rng);

        let T_1 = self.cs.pc_gens.commit(t_poly.t1, t_1_blinding).compress();
        let T_3 = self.cs.pc_gens.commit(t_poly.t3, t_3_blinding).compress();
        let T_4 = self.cs.pc_gens.commit(t_poly.t4, t_4_blinding).compress();
        let T_5 = self.cs.pc_gens.commit(t_poly.t5, t_5_blinding).compress();
        let T_6 = self.cs.pc_gens.commit(t_poly.t6, t_6_blinding).compress();

        self.cs.transcript.commit_point(b"T_1", &T_1);
        self.cs.transcript.commit_point(b"T_3", &T_3);
        self.cs.transcript.commit_point(b"T_4", &T_4);
        self.cs.transcript.commit_point(b"T_5", &T_5);
        self.cs.transcript.commit_point(b"T_6", &T_6);

        let x = self.cs.transcript.challenge_scalar(b"x");

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = wV
            .iter()
            .zip(self.cs.v_blinding.iter())
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

        for i in n..padded_n {
            r_vec[i] = -exp_y;
            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        self.cs.transcript.commit_scalar(b"t_x", &t_x);
        self.cs.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.cs.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.cs.transcript.challenge_scalar(b"w");
        let Q = w * self.cs.pc_gens.B;

        let ipp_proof = InnerProductProof::create(
            self.cs.transcript,
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
