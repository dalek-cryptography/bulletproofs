#[cfg(feature = "scalar_range_proof")]
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
#[cfg(feature = "scalar_range_proof")]
use curve25519_dalek::scalar::Scalar;
#[cfg(feature = "scalar_range_proof")]
use hex;
#[cfg(feature = "scalar_range_proof")]
use merlin::Transcript;
#[cfg(feature = "scalar_range_proof")]
use rand_chacha::ChaChaRng;
#[cfg(feature = "scalar_range_proof")]
use rand_core::SeedableRng;

// This function generates test vectors and dumps them to stdout.
// It can be run by uncommenting the #[test] annotation.
// We allow(dead_code) to ensure that it continues to compile.
//#[test]
#[cfg(feature = "scalar_range_proof")]
#[allow(dead_code)]
fn generate_test_vectors() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 8);

    // Use a deterministic RNG for proving, so the test vectors can be
    // generated reproducibly.
    let mut test_rng = ChaChaRng::from_seed([24u8; 32]);

    let value_range = 0u64..8;
    let values = value_range.clone().map(Scalar::from).collect::<Vec<_>>();
    let blindings = value_range
        .map(|_| Scalar::random(&mut test_rng))
        .collect::<Vec<_>>();

    for n in &[8, 16, 32, 64, 128] {
        for m in &[1, 2, 4, 8] {
            let mut transcript = Transcript::new(b"Deserialize-And-Verify Test");
            let (proof, value_commitments) = RangeProof::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values[0..*m],
                &blindings[0..*m],
                *n,
            )
            .unwrap();

            println!("n,m = {}, {}", n, m);
            println!("proof = \"{}\"", hex::encode(proof.to_bytes()));
            println!("vc = [");
            for com in &value_commitments {
                println!("    \"{}\"", hex::encode(com.as_bytes()));
            }
            println!("]\n");
        }
    }

    panic!();
}
