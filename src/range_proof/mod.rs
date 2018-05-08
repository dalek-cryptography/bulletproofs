#![allow(non_snake_case)]
#![doc(include = "../docs/range-proof-protocol.md")]

use rand::Rng;
use std::iter;
use std::borrow::Borrow;

use curve25519_dalek::ristretto;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use generators::{Generators, GeneratorsView};
use inner_product_proof::InnerProductProof;
use proof_transcript::ProofTranscript;
use util;

// Modules for MPC protocol

pub mod dealer;
pub mod messages;
pub mod party;

/// The `RangeProof` struct represents a single range proof.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    A: RistrettoPoint,
    /// Commitment to the blinding factors
    S: RistrettoPoint,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: RistrettoPoint,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: RistrettoPoint,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    ///
    /// XXX add doctests
    pub fn prove_single<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
    ) -> Result<RangeProof, &'static str> {
        RangeProof::prove_multiple(generators, transcript, rng, &[v], &[*v_blinding], n)
    }

    /// Create a rangeproof for a set of values.
    ///
    /// XXX add doctests
    pub fn prove_multiple<R: Rng>(
        generators: &Generators,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<RangeProof, &'static str> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err("mismatched values and blindings len");
        }

        let dealer = Dealer::new(generators.all(), n, values.len(), transcript)?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| {
                Party::new(v, v_blinding, n, &generators)
            })
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>,_>>()?;

        let (parties, value_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| p.assign_position(j, rng))
            .unzip();

        let (dealer, value_challenge) = dealer.receive_value_commitments(&value_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&value_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(&poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>,_>>()?;

        dealer.receive_trusted_shares(&proof_shares)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify` for the `m=1` case.
    ///
    /// XXX add doctests
    pub fn verify_single<R: Rng>(
        &self,
        V: &RistrettoPoint,
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Result<(), &'static str> {
        self.verify(&[*V], gens, transcript, rng, n)
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    ///
    /// XXX add doctests
    pub fn verify<R: Rng>(
        &self,
        value_commitments: &[RistrettoPoint],
        gens: GeneratorsView,
        transcript: &mut ProofTranscript,
        rng: &mut R,
        n: usize,
    ) -> Result<(), &'static str> {
        RangeProof::verify_batch(
            iter::once((self, value_commitments)),
            n,
            gens,
            transcript,
            rng,
        )
    }

    /// Verifies multiple range proofs at once.
    /// If any range proof is invalid, the whole batch is invalid.
    /// Proofs may use different ranges (`n`) or different number of aggregated commitments (`m`).
    /// You must provide big enough view into generators (`gens`) that covers
    /// the biggest proof
    pub fn verify_batch<'a,'b,I,R,P,V>(
        proofs: I, 
        n: usize,
        gens: GeneratorsView, // must have enough points to cover max(m*n)
        transcript: &mut ProofTranscript,
        rng: &mut R
    ) -> Result<(), &'static str> 
    where
    R: Rng,
    I: IntoIterator<Item = (P, V)>,
    P: Borrow<RangeProof>,
    V: AsRef<[RistrettoPoint]>
    {
        let mut m: usize = 0;
        let mut dyn_bases_count:usize = 0;
        let batch = proofs.into_iter().map(|(p, vcs)| {
            let m_curr = vcs.as_ref().len();
            let v = p.borrow().prepare_verification(n, vcs, &mut transcript.clone(), rng);
            dyn_bases_count += m_curr /*V*/ + 4 /*A,S,T1,T2*/ + 2*p.borrow().ipp_proof.L_vec.len();
            m = m.max(m_curr);
            v
        }).collect::<Vec<_>>();

        if gens.G.len() < (n * m) {
            return Err(
                "The generators view does not have enough generators for the largest proof",
            );
        }

        // First statement is used without a random factor
        let mut pedersen_base_scalars: (Scalar, Scalar) = (Scalar::zero(), Scalar::zero());
        let mut g_scalars: Vec<Scalar> = iter::repeat(Scalar::zero()).take(n*m).collect();
        let mut h_scalars: Vec<Scalar> = iter::repeat(Scalar::zero()).take(n*m).collect();

        let mut dynamic_base_scalars: Vec<Scalar> = Vec::with_capacity(dyn_bases_count);
        let mut dynamic_bases: Vec<RistrettoPoint> = Vec::with_capacity(dyn_bases_count);

        // Other statements are added with a random factor per statement
        for verification in batch {

            pedersen_base_scalars.0 += verification.pedersen_base_scalars.0;
            pedersen_base_scalars.1 += verification.pedersen_base_scalars.1;

            // Note: this loop may be shorter than the total amount of scalars if `m < max({m})`
            for (i, s) in verification.g_scalars.iter().enumerate() {
                g_scalars[i] += s;
            }
            for (i, s) in verification.h_scalars.iter().enumerate() {
                h_scalars[i] += s;
            }

            dynamic_base_scalars.extend(verification.dynamic_base_scalars);
            dynamic_bases.extend(verification.dynamic_bases);
        }

        let mega_check = ristretto::vartime::multiscalar_mul(
            iter::once(&pedersen_base_scalars.0)
                .chain(iter::once(&pedersen_base_scalars.1))
                .chain(g_scalars.iter())
                .chain(h_scalars.iter())
                .chain(dynamic_base_scalars.iter()),
            iter::once(&gens.pedersen_generators.B)
                .chain(iter::once(&gens.pedersen_generators.B_blinding))
                .chain(gens.G.iter())
                .chain(gens.H.iter())
                .chain(dynamic_bases.iter()),
        );

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err("Verification failed")
        }
    }

    /// Prepares a `Verification` struct
    /// that can be combined with others in a batch.
    fn prepare_verification<R, V>(
        &self,
        n: usize,
        value_commitments: V,
        transcript: &mut ProofTranscript,
        rng: &mut R,
    ) -> Verification
    where
    R: Rng, 
    V: AsRef<[RistrettoPoint]>
    {
        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.

        let m = value_commitments.as_ref().len();

        transcript.commit_u64(n as u64);
        transcript.commit_u64(m as u64);

        for V in value_commitments.as_ref().iter() {
            transcript.commit(V.borrow().compress().as_bytes());
        }
        transcript.commit(self.A.compress().as_bytes());
        transcript.commit(self.S.compress().as_bytes());

        let y = transcript.challenge_scalar();
        let z = transcript.challenge_scalar();
        let zz = z * z;
        let minus_z = -z;

        transcript.commit(self.T_1.compress().as_bytes());
        transcript.commit(self.T_2.compress().as_bytes());

        let x = transcript.challenge_scalar();

        transcript.commit(self.t_x.as_bytes());
        transcript.commit(self.t_x_blinding.as_bytes());
        transcript.commit(self.e_blinding.as_bytes());

        let w = transcript.challenge_scalar();

        // Challenge value for combining two statements within a rangeproof.
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(transcript);
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from_u64(2)).take(n).collect();
        let powers_of_z = util::exp_iter(z).take(m);
        let concat_z_and_2 =
            powers_of_z.flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z));

        let g = s.iter()
            .map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2)
            .map(|((s_i_inv, exp_y_inv), z_and_2)| {
                z + exp_y_inv * (zz * z_and_2 - b * s_i_inv)
            });

        let value_commitment_scalars = util::exp_iter(z)
            .take(m)
            .map(|z_exp| c * zz * z_exp);

        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        // Challenge value for combining the complete range proof statement with other range proof statements.
        let batch_challenge = Scalar::random(rng);

        Verification {
            pedersen_base_scalars: (
                batch_challenge*basepoint_scalar, 
                batch_challenge*(-self.e_blinding - c * self.t_x_blinding)
            ),
            g_scalars: g.map(|s| batch_challenge*s ).collect(),
            h_scalars: h.map(|s| batch_challenge*s ).collect(),
            dynamic_base_scalars: iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(value_commitment_scalars)
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .map(|s| batch_challenge*s )
                .collect(),
            dynamic_bases: iter::once(&self.A)
                .chain(iter::once(&self.S))
                .chain(value_commitments.as_ref().iter())
                .chain(iter::once(&self.T_1))
                .chain(iter::once(&self.T_2))
                .chain(self.ipp_proof.L_vec.iter())
                .chain(self.ipp_proof.R_vec.iter())
                .cloned()
                .collect(),
        }
    }
}

/// Represents a deferred computation to verify a single rangeproof.
/// Multiple instances can be verified more efficient as a batch using
/// `RangeProof::verify_batch` function.
struct Verification {
    /// Pair of scalars multiplying pedersen bases `B`, `B_blinding`.
    pedersen_base_scalars: (Scalar, Scalar),

    /// List of scalars for `n*m` `G` bases. These are separated from `h_scalars`
    /// so we can easily pad them when verifying proofs with different `m`s.
    g_scalars: Vec<Scalar>,

    /// List of scalars for `n*m` `H` bases. These are separated from `g_scalars`
    /// so we can easily pad them when verifying proofs with different `m`s.
    h_scalars: Vec<Scalar>,

    /// List of scalars for any number of dynamic bases.
    dynamic_base_scalars: Vec<Scalar>,

    /// List of dynamic bases for the corresponding scalars.
    dynamic_bases: Vec<RistrettoPoint>,
}


/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle 1, {\mathbf{y}}^{nm} \rangle + z^{3} \langle \mathbf{1}, {\mathbf{2}}^{nm} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from_u64(2), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    use generators::PedersenGenerators;

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        use bincode;

        // Both prover and verifier have access to the generators and the proof
        let generators = Generators::new(PedersenGenerators::default(), n, m);

        let (proof_bytes, value_commitments) = singleparty_create_helper(n, m);

        println!(
            "Aggregated rangeproof of m={} proofs of n={} bits has size {} bytes",
            m,
            n,
            proof_bytes.len(),
        );

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut rng = OsRng::new().unwrap();
            let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

            assert!(
                proof
                    .verify(
                        &value_commitments,
                        generators.all(),
                        &mut transcript,
                        &mut rng,
                        n,
                    )
                    .is_ok()
            );
        }
    }

    /// Generates and verifies a number of proofs in a batch
    /// with the given pairs of `n,m` parameters (range in bits, number of commitments).
    fn batch_verify_helper(nm: &[(usize, usize)]) {
        use bincode;

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let inputs = nm.iter()
            .map(|(n, m)| {
                let (p, vc) = singleparty_create_helper(*n, *m);
                let proof = bincode::deserialize::<RangeProof>(&p).unwrap();
                (proof, vc)
            });

        let max_n = nm.iter().map(|(n,_)| *n).max().unwrap_or(0);
        let max_m = nm.iter().map(|(_,m)| *m).max().unwrap_or(0);

        let generators = Generators::new(PedersenGenerators::default(), max_n, max_m);

        assert!(RangeProof::verify_batch(inputs, max_n, generators.all(), &mut transcript, &mut rng).is_ok());
    }


    /// Generates a `n`-bit rangeproof for `m` commitments.
    /// Returns serialized proof and the list of commitments.
    fn singleparty_create_helper(n: usize, m: usize) -> (Vec<u8>, Vec<RistrettoPoint>) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        use bincode;

        // Both prover and verifier have access to the generators and the proof
        let generators = Generators::new(PedersenGenerators::default(), n, m);

        // Serialized proof data
        let proof_bytes: Vec<u8>;
        let value_commitments: Vec<RistrettoPoint>;

        // 1. Generate the proof

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
        let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
        let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

        let proof = RangeProof::prove_multiple(
            &generators,
            &mut transcript,
            &mut rng,
            &values,
            &blindings,
            n,
        ).unwrap();

        // 2. Serialize
        proof_bytes = bincode::serialize(&proof).unwrap();

        let pg = &generators.all().pedersen_generators;

        // XXX would be nice to have some convenience API for this
        value_commitments = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| {
                pg.commit(Scalar::from_u64(v), v_blinding)
            })
            .collect();

        (proof_bytes, value_commitments)
    }

    #[test]
    fn create_and_verify_n_32_m_1() {
        singleparty_create_and_verify_helper(32, 1);
    }

    #[test]
    fn create_and_verify_n_32_m_2() {
        singleparty_create_and_verify_helper(32, 2);
    }

    #[test]
    fn create_and_verify_n_32_m_4() {
        singleparty_create_and_verify_helper(32, 4);
    }

    #[test]
    fn create_and_verify_n_32_m_8() {
        singleparty_create_and_verify_helper(32, 8);
    }

    #[test]
    fn create_and_verify_n_64_m_1() {
        singleparty_create_and_verify_helper(64, 1);
    }

    #[test]
    fn create_and_verify_n_64_m_2() {
        singleparty_create_and_verify_helper(64, 2);
    }

    #[test]
    fn create_and_verify_n_64_m_4() {
        singleparty_create_and_verify_helper(64, 4);
    }

    #[test]
    fn create_and_verify_n_64_m_8() {
        singleparty_create_and_verify_helper(64, 8);
    }

    #[test]
    fn batch_verify_n_32_m_1() {
        batch_verify_helper(&[(32, 1)]);
        batch_verify_helper(&[(32, 1), (32, 1)]);
        batch_verify_helper(&[(32, 1), (32, 1), (32, 1)]);
    }

    #[test]
    fn batch_verify_n_64_m_differ() {
        batch_verify_helper(&[(32, 1), (32, 2)]);
        batch_verify_helper(&[(32, 1), (32, 2), (32, 4)]);
    }

    #[test]
    fn batch_verify_n_differ_m_differ_total_64() {
        batch_verify_helper(&[(64, 1), (32, 2), (16, 4)]);
    }

    #[test]
    fn batch_verify_n_differ_m_differ_total_256() {
        batch_verify_helper(&[(16, 1), (32, 2), (64, 4)]);
    }

    #[test]
    fn detect_dishonest_party_during_aggregation() {
        use self::dealer::*;
        use self::party::*;

        // Simulate four parties, two of which will be dishonest and use a 64-bit value.
        let m = 4;
        let n = 32;

        let generators = Generators::new(PedersenGenerators::default(), n, m);

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        // Parties 0, 2 are honest and use a 32-bit value
        let v0 = rng.next_u32() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(v0, v0_blinding, n, &generators).unwrap();

        let v2 = rng.next_u32() as u64;
        let v2_blinding = Scalar::random(&mut rng);
        let party2 = Party::new(v2, v2_blinding, n, &generators).unwrap();

        // Parties 1, 3 are dishonest and use a 64-bit value
        let v1 = rng.next_u64();
        let v1_blinding = Scalar::random(&mut rng);
        let party1 = Party::new(v1, v1_blinding, n, &generators).unwrap();

        let v3 = rng.next_u64();
        let v3_blinding = Scalar::random(&mut rng);
        let party3 = Party::new(v3, v3_blinding, n, &generators).unwrap();

        let dealer = Dealer::new(generators.all(), n, m, &mut transcript).unwrap();

        let (party0, value_com0) = party0.assign_position(0, &mut rng);
        let (party1, value_com1) = party1.assign_position(1, &mut rng);
        let (party2, value_com2) = party2.assign_position(2, &mut rng);
        let (party3, value_com3) = party3.assign_position(3, &mut rng);

        let (dealer, value_challenge) = dealer
            .receive_value_commitments(&[value_com0, value_com1, value_com2, value_com3])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&value_challenge, &mut rng);
        let (party1, poly_com1) = party1.apply_challenge(&value_challenge, &mut rng);
        let (party2, poly_com2) = party2.apply_challenge(&value_challenge, &mut rng);
        let (party3, poly_com3) = party3.apply_challenge(&value_challenge, &mut rng);

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(&[poly_com0, poly_com1, poly_com2, poly_com3])
            .unwrap();

        let share0 = party0.apply_challenge(&poly_challenge).unwrap();
        let share1 = party1.apply_challenge(&poly_challenge).unwrap();
        let share2 = party2.apply_challenge(&poly_challenge).unwrap();
        let share3 = party3.apply_challenge(&poly_challenge).unwrap();

        match dealer.receive_shares(&mut rng, &[share0, share1, share2, share3]) {
            Ok(_proof) => {
                panic!("The proof was malformed, but it was not detected");
            }
            Err(e) => {
                // XXX when we have error types, check that it was party 1 that did it
                assert_eq!(e, "proof failed to verify");
            }
        }
    }

    #[test]
    fn detect_dishonest_dealer_during_aggregation() {
        use self::dealer::*;
        use self::party::*;

        // Simulate one party
        let m = 1;
        let n = 32;

        let generators = Generators::new(PedersenGenerators::default(), n, m);

        let mut rng = OsRng::new().unwrap();
        let mut transcript = ProofTranscript::new(b"AggregatedRangeProofTest");

        let v0 = rng.next_u32() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(v0, v0_blinding, n, &generators).unwrap();

        let dealer = Dealer::new(generators.all(), n, m, &mut transcript).unwrap();

        // Now do the protocol flow as normal....

        let (party0, value_com0) = party0.assign_position(0, &mut rng);

        let (dealer, value_challenge) = dealer
            .receive_value_commitments(&[value_com0])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&value_challenge, &mut rng);

        let (_dealer, mut poly_challenge) = dealer
            .receive_poly_commitments(&[poly_com0])
            .unwrap();

        // But now simulate a malicious dealer choosing x = 0
        poly_challenge.x = Scalar::zero();

        let maybe_share0 = party0.apply_challenge(&poly_challenge);

        // XXX when we have error types, check finer info than "was error"
        assert!(maybe_share0.is_err());
    }

    #[test]
    fn test_delta() {
        let mut rng = OsRng::new().unwrap();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        assert_eq!(power_g, delta(n, 1, &y, &z),);
    }
}
