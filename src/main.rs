// The #-commented lines are hidden in Rustdoc but not in raw
// markdown rendering, and contain boilerplate code so that the
// code in the README.md is actually run as part of the test suite.
extern crate rand;
use rand::thread_rng;
extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;
extern crate merlin;
use merlin::Transcript;
extern crate bulletproofs;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};

extern crate hex;


fn main() {
    // Generators for Pedersen commitments.  These can be selected
    // independently of the Bulletproofs generators.
    let pc_gens = PedersenGens::default();

    // Generators for Bulletproofs, valid for proofs up to bitsize 64
    // and aggregation size up to 1.
    let bp_gens = BulletproofGens::new(64, 1);

    // A secret value we want to prove lies in the range [0, 2^32)
    // let secret_value = 1037578891u64;
    let secret_value = 2u64;
    let secret_value_1 = 1u64;
    let secret_value_2 = 1u64;

    // The API takes a blinding factor for the commitment.
    let blinding = Scalar::random(&mut thread_rng());

    // The proof can be chained to an existing transcript.
    // Here we create a transcript with a doctest domain separator.
    let mut prover_transcript = Transcript::new(b"doctest example");

    // Create a 32-bit rangeproof.
    let (proof, committed_value) = RangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        secret_value,
        &blinding,
        64,
    ).expect("A real program could handle errors");

    let (proof_1, committed_value_1) = RangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        secret_value_1,
        &blinding,
        64,
    ).expect("A real program could handle errors");

    let (proof_2, committed_value_2) = RangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        secret_value_2,
        &blinding,
        64,
    ).expect("A real program could handle errors");


    // let bytes_commit = to_bytes(&committed_value);
    // for x in 0..bytes_commit.len() {
    //     print!("{}", x);
    // }

    // let bytes_commit_1 = committed_value_1.to_bytes();
    // for x in 0..bytes_commit_1.len() {
    //     print!("{}", x);
    // }
    println!("committed_value_1 = \"{}\"", hex::encode(committed_value_1.to_bytes()));
    println!("committed_value_2 = \"{}\"", hex::encode(committed_value_2.to_bytes()));
    println!("committed_value_3 = \"{}\"", hex::encode(committed_value.to_bytes()));
    println!("bp = \"{}\"", bp_gens.gens_capacity);
    // println!("p = \"{}\"", pc_gens.B_blinding.to_bytes());
    // println!("b = \"{}\"", hex::encode(bp_gens.to_bytes()));



    // for x in 0..committed_value_1.len() {
    //     print!("{}", x);
    // }

    // let bytes_commit_2 = committed_value_2.to_bytes();
    // for x in 0..bytes_commit_2.len() {
    //     print!("{}", x);
    // }
    // println!("upper is 2's committed_value {}", '\n');

    // println!("committed_value is {} ", bytes_commit);

    // println!("committed_value is {} ", committed_value);

    // Verification requires a transcript with identical initial state:
    let mut verifier_transcript = Transcript::new(b"doctest example");
    assert!(
        proof
            .verify_single(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &committed_value,
                64
            )
            .is_ok()
    );
    assert_eq!((committed_value_1), committed_value_2);
    assert_eq!((committed_value), committed_value_2);
}

// fn main() {
// // Generators for Pedersen commitments.  These can be selected
// // independently of the Bulletproofs generators.
// let pc_gens = PedersenGens::default();

// // Generators for Bulletproofs, valid for proofs up to bitsize 64
// // and aggregation size up to 1.
// let bp_gens = BulletproofGens::new(64, 1);

// // A secret value we want to prove lies in the range [0, 2^32)
// // let secret_value = 1037578891u64;
// let secret_value : Vec<u64> = [1, 2, 3].to_vec();

// // The API takes a blinding factor for the commitment.
// // let blinding = Scalar::random(&mut thread_rng());
// let mut rng = rand::thread_rng();
// let blindings: Vec<Scalar> = (0..2).map(|_| Scalar::random(&mut rng)).collect();

// // The proof can be chained to an existing transcript.
// // Here we create a transcript with a doctest domain separator.
// let mut prover_transcript = Transcript::new(b"doctest example");

// // Create a 32-bit rangeproof.
// let (proof, committed_value) = RangeProof::prove_multiple(
//     &bp_gens,
//     &pc_gens,
//     &mut prover_transcript,
//     &secret_value,
//     &blindings,
//     64,
// ).expect("A real program could handle errors");

// // Verification requires a transcript with identical initial state:
// let mut verifier_transcript = Transcript::new(b"doctest example");
// assert!(
//     proof
//         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
//         .is_ok()
// );
// }
