#![allow(non_snake_case)]

use circuit_proof::constraints::Constraint;
use circuit_proof::opaque_scalar::OpaqueScalar;
use clear_on_drop::clear::Clear;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::{Transcript, TranscriptRng};

use super::{Assignment, ConstraintSystem, R1CSProof, ScalarValue, Variable, VariableIndex};

use super::cs::{ConstraintSystemState, NoScalar};

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
    cs_state: ConstraintSystemState<ProverCS<'a, 'b>>,
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    v: Vec<Scalar>,
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
    }
}

impl<'a, 'b> ConstraintSystem for ProverCS<'a, 'b> {
    fn assign_multiplier<S: ScalarValue>(
        &mut self,
        left: Assignment<S>,
        right: Assignment<S>,
        out: Assignment<S>,
    ) -> Result<(Variable<S>, Variable<S>, Variable<S>), R1CSError> {
        // Unwrap all of l,r,o up front to ensure we leave the CS in a
        // consistent state if any are missing assignments
        let l = left.into_transparent()?;
        let r = right.into_transparent()?;
        let o = out.into_transparent()?;

        // Now commit to the assignment
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        self.cs_state.assign_multiplier(left, right, out)
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        self.cs_state.add_constraint(constraint);
    }

    fn challenge_scalar<F>(&mut self, label: &'static [u8], callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self, OpaqueScalar) -> Result<(), R1CSError>,
    {
        match self.cs_state.store_challenge_callback(label, callback) {
            Some(callback) => {
                let challenge = self.transcript.challenge_scalar(label);
                callback(self, challenge.into())
            }
            None => Ok(()),
        }
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
    ) -> (Self, Vec<CompressedRistretto>) {
        // Check that the input lengths are consistent
        assert_eq!(v.len(), v_blinding.len());

        let commitments = v
            .iter()
            .zip(v_blinding.iter())
            .map(|(v, v_b)| pc_gens.commit(*v, *v_b).compress())
            .collect::<Vec<_>>();

        let cs_state = ConstraintSystemState::new(transcript, &commitments[..]);

        let cs = Self {
            cs_state,
            transcript,
            pc_gens,
            bp_gens,
            v,
            v_blinding,
            a_L: vec![],
            a_R: vec![],
            a_O: vec![],
        };

        (cs, commitments)
    }

    /// Creates an RNG out of the current state of the transcript
    /// and the blinding factors for the external variables.
    fn rng(&mut self) -> TranscriptRng {
        let mut builder = self.transcript.build_rng();

        // Commit the blinding factors for the input wires
        for v_b in &self.v_blinding {
            builder = builder.commit_witness_bytes(b"v_blinding", v_b.as_bytes());
        }

        use rand::thread_rng;
        builder.finalize(&mut thread_rng())
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove<F>(mut self, builder: F) -> Result<R1CSProof, R1CSError>
    where
        F: FnOnce(&mut Self, Vec<Variable<Scalar>>) -> Result<(), R1CSError>,
    {
        use std::iter;
        use util;

        // 0. Convert the external secrets into the variables
        let variables = self
            .v
            .iter()
            .enumerate()
            .map(|(i, v)| Variable {
                index: VariableIndex::Committed(i),
                assignment: (*v).into(),
            })
            .collect::<Vec<_>>();

        // 1. Build the constraint system.
        builder(&mut self, variables)?;

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = self.bp_gens.share(0);

        // Create RNG from the transcript and the external secrets.
        let mut rng = self.rng();

        // 2. Commit to the first-phase low-level witness data
        let n1 = self.a_L.len();

        let i_blinding1 = Scalar::random(&mut rng);
        let o_blinding1 = Scalar::random(&mut rng);
        let s_blinding1 = Scalar::random(&mut rng);

        let mut s_L1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I1 = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding1)
                .chain(self.a_L.iter())
                .chain(self.a_R.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        )
        .compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O1 = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding1).chain(self.a_O.iter()),
            iter::once(&self.pc_gens.B_blinding).chain(gens.G(n1)),
        )
        .compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S1 = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        )
        .compress();

        self.transcript.commit_point(b"A_I1", &A_I1);
        self.transcript.commit_point(b"A_O1", &A_O1);
        self.transcript.commit_point(b"S1", &S1);

        // 3. Process the second phase of the CS, allocating more variables
        //    and adding more constraints.
        for (label, callback) in self.cs_state.complete_constraints().into_iter() {
            let challenge = self.transcript.challenge_scalar(label);
            callback(&mut self, challenge.into())?;
        }

        // 4. Pad the CS to the power-of-two number of multipliers.
        let n = self.a_L.len();
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // 5. Commit to the second-phase low-level witness data
        let n2 = n - n1;

        let i_blinding2 = Scalar::random(&mut rng);
        let o_blinding2 = Scalar::random(&mut rng);
        let s_blinding2 = Scalar::random(&mut rng);

        let mut s_L2: Vec<Scalar> = (0..n2).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R2: Vec<Scalar> = (0..n2).map(|_| Scalar::random(&mut rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I2 = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding2)
                .chain(self.a_L.iter().skip(n1))
                .chain(self.a_R.iter().skip(n1)),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n).skip(n1))
                .chain(gens.H(n).skip(n1)),
        )
        .compress();

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O2 = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding2).chain(self.a_O.iter().skip(n1)),
            iter::once(&self.pc_gens.B_blinding).chain(gens.G(n).skip(n1)),
        )
        .compress();

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S2 = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding2)
                .chain(s_L2.iter())
                .chain(s_R2.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n).skip(n1))
                .chain(gens.H(n).skip(n1)),
        )
        .compress();

        self.transcript.commit_point(b"A_I2", &A_I2);
        self.transcript.commit_point(b"A_O2", &A_O2);
        self.transcript.commit_point(b"S2", &S2);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV, _) = self.cs_state.flattened_constraints::<NoScalar>(&z);

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let y_inv = y.invert();

        // Note: the sequence of `y^{-i}` is computed up to `padded_n`
        // for use in the IPP via `H_factors`, even though only `n` items
        // are used for `l` and `r` calculation.
        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();

        let sLsR = s_L1
            .iter()
            .chain(s_L2.iter())
            .zip(s_R1.iter().chain(s_R2.iter()));
        for (i, (sl, sr)) in sLsR.enumerate() {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = self.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = *sl;
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = wO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * self.a_R[i] + wL[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * sr;

            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let t_poly = l_poly.inner_product(&r_poly);

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

        self.transcript.commit_point(b"T_1", &T_1);
        self.transcript.commit_point(b"T_3", &T_3);
        self.transcript.commit_point(b"T_4", &T_4);
        self.transcript.commit_point(b"T_5", &T_5);
        self.transcript.commit_point(b"T_6", &T_6);

        // Challenges for evaluating the polynomial and combining two phases of the protocol.
        let e = self.transcript.challenge_scalar(b"e");
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

        for i in n..padded_n {
            r_vec[i] = -exp_y;
            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        let i_blinding = i_blinding1 + e * i_blinding2;
        let o_blinding = o_blinding1 + e * o_blinding2;
        let s_blinding = s_blinding1 + e * s_blinding2;

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let G_factors = iter::repeat(Scalar::one())
            .take(n1)
            .chain(iter::repeat(e).take(n2 + pad))
            .collect::<Vec<_>>();
        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y, e_or_1)| y * e_or_1)
            .collect::<Vec<_>>();

        let ipp_proof = InnerProductProof::create(
            self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            gens.G(padded_n).cloned().collect(),
            gens.H(padded_n).cloned().collect(),
            l_vec,
            r_vec,
        );

        // We do not yet have a ClearOnDrop wrapper for Vec<Scalar>.
        // When PR 202 [1] is merged, we can simply wrap s_L and s_R at the point of creation.
        // [1] https://github.com/dalek-cryptography/curve25519-dalek/pull/202
        for scalar in s_L1
            .iter_mut()
            .chain(s_L2.iter_mut())
            .chain(s_R1.iter_mut())
            .chain(s_R2.iter_mut())
        {
            scalar.clear();
        }

        Ok(R1CSProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
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
