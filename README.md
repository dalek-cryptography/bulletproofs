# Bulletproofs

<img
 width="100%"
 src="https://doc.dalek.rs/assets/bulletproofs-rangeproof.png"
/>

The fastest [Bulletproofs][bp_website] implementation ever, featuring
single and aggregated range proofs, strongly-typed multiparty
computation, and a programmable constraint system API for proving
arbitrary statements (under development).

This library implements Bulletproofs using [Ristretto][ristretto],
using the `ristretto255` implementation in
[`curve25519-dalek`][curve25519_dalek].  When using the [parallel
formulas][parallel_edwards] in the `curve25519-dalek` AVX2 backend, it
can verify 64-bit rangeproofs **approximately twice as fast** as the
original `libsecp256k1`-based Bulletproofs implementation.

This library provides implementations of:

* Single-party proofs of single or multiple ranges, using the
  aggregated rangeproof construction;

* Online multi-party computation for rangeproof aggregation between
  multiple parties, using [session types][session_type_blog] to
  statically enforce correct protocol flow;
  
* A programmable constraint system API for expressing rank-1
  constraint systems, and proving and verifying proofs of arbitrary
  statements (unstable, under development with the `yoloproofs` feature);
  
* Online multi-party computation for aggregated constraint system proofs
  (planned future work).

These proofs are implemented using [Merlin transcripts][doc_merlin],
allowing them to be arbitrarily composed with other proofs without
implementation changes.

The development roadmap can be found in the
[Milestones][gh_milestones] section of the [Github repo][gh_repo].

The constraint system API is provided **FOR EXPERIMENTS ONLY**, and must be
enabled by specifying the `yoloproofs` feature.  It is not covered by semver
compatibility and is **SUBJECT TO CHANGE WITHOUT NOTICE**.  

Currently, the `yoloproofs` feature is disabled in the published version of the
crate, so it can only be used by specifying a git dependency on the `develop`
branch.  This means that it is not possible to publish a crate using the R1CS
API, because it is **FOR EXPERIMENTS ONLY**.

## Documentation
  
The user-facing documentation for this functionality can be [found
here][doc_external].  In addition, the library *also* contains
extensive notes on how Bulletproofs work.  These notes can be found in
the library's [internal documentation][doc_internal]:

* how [Bulletproofs work][bp_notes];
* how [the range proof protocol works][rp_notes];
* how [the inner product proof protocol works][ipp_notes];
* how [the aggregation protocol works][agg_notes];
* how the Bulletproof constraint system proofs work (under development);
* how the constraint system reduction works (under development);
* how the aggregated constraint system proofs work (future work).

## Comparative Performance

The following table gives comparative timings for proving and verification of a
64-bit rangeproof on an Intel Skylake-X i7-7800X (@3.5GHz, Turbo Boost
disabled).  Times are in microseconds (lower is better), with the relative
speed compared to the fastest implementation.

| Implementation | Group            | Proving (μs) |       rel | Verification (μs) |       rel |
|----------------|------------------|-------------:|----------:|------------------:|----------:|
| ours (avx2)    | ristretto255     |         7300 | **1.00x** |              1040 | **1.00x** |
| ours (u64)     | ristretto255     |        11300 | **1.54x** |              1490 | **1.43x** |
| libsecp+endo   | secp256k1        |        14300 | **1.96x** |              1900 | **1.83x** |
| libsecp-endo   | secp256k1        |        16800 | **2.30x** |              2080 | **2.00x** |
| Monero         | ed25519 (unsafe) |        53300 | **7.30x** |              4810 | **4.63x** |

Use of the `curve25519-dalek` IFMA backend gives another 1.5x speedup on a
Cannonlake i3-8121U, increasing the verification speedup **3x** over libsecp
and **7x** over Monero, but these processors are not yet generally available.

This crate also contains other benchmarks; see the *Tests and Benchmarks*
section below for details on how to run them all.

## Example

The following example shows how to create and verify a 32-bit rangeproof.

```rust
# // The #-commented lines are hidden in Rustdoc but not in raw
# // markdown rendering, and contain boilerplate code so that the
# // code in the README.md is actually run as part of the test suite.
#
# extern crate rand;
# use rand::thread_rng;
#
# extern crate curve25519_dalek;
# use curve25519_dalek::scalar::Scalar;
#
# extern crate merlin;
# use merlin::Transcript;
#
# extern crate bulletproofs;
# use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
#
# fn main() {
// Generators for Pedersen commitments.  These can be selected
// independently of the Bulletproofs generators.
let pc_gens = PedersenGens::default();

// Generators for Bulletproofs, valid for proofs up to bitsize 128
// and aggregation size up to 1.
let bp_gens = BulletproofGens::new(128, 1);

// A secret value we want to prove lies in the range [0, 2^32)
# #[cfg(not(feature = "scalar_range_proof"))]
let secret_value = 1037578891u128;
# #[cfg(feature = "scalar_range_proof")]
# let secret_value = &Scalar::from(1037578891u128);

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
    32,
).expect("A real program could handle errors");

// Verification requires a transcript with identical initial state:
let mut verifier_transcript = Transcript::new(b"doctest example");
assert!(
    proof
        .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
        .is_ok()
);
# }
```
## Building

To compile successfully, you will need to have nightly Rust installed, rather than stable.

You can install nightly Rust with rustup:

```text
rustup default nightly
```

## Tests and Benchmarks

Run tests with `cargo test`.  Run benchmarks with `cargo bench`.  This crate
uses [criterion.rs][criterion] for benchmarks. 

## Features

The `yoloproofs` feature enables support for rank-1 constraint system proofs.
It is **UNSTABLE AND UNSUITABLE FOR DEPLOYMENT**, and **PROVIDED FOR TESTING
ONLY**.

The `avx2_backend` feature enables `curve25519-dalek`'s AVX2 backend,
which implements curve arithmetic using [parallel
formulas][parallel_edwards].  To use it for Bulletproofs, the
`target_cpu` must support AVX2:

```text
RUSTFLAGS="-C target_cpu=skylake" cargo bench --features "avx2_backend"
```

Skylake-X CPUs have double the AVX2 registers. To use them, try

```text
RUSTFLAGS="-C target_cpu=skylake-avx512" cargo bench --features "avx2_backend"
```

This prevents spills in the AVX2 parallel field multiplication code, but causes
worse code generation elsewhere ¯\\\_(ツ)\_/¯

## About

This is a research project sponsored by [Interstellar][interstellar],
developed by Henry de Valence, Cathie Yun, and Oleg Andreev.

[bp_website]: https://crypto.stanford.edu/bulletproofs/
[ristretto]: https://ristretto.group
[doc_merlin]: https://doc.dalek.rs/merlin/index.html
[doc_external]: https://doc.dalek.rs/bulletproofs/index.html
[doc_internal]: https://doc-internal.dalek.rs/bulletproofs/index.html
[bp_notes]: https://doc-internal.dalek.rs/bulletproofs/notes/index.html
[rp_notes]: https://doc-internal.dalek.rs/bulletproofs/range_proof/index.html
[ipp_notes]: https://doc-internal.dalek.rs/bulletproofs/inner_product_proof/index.html
[agg_notes]: https://doc-internal.dalek.rs/bulletproofs/notes/index.html#aggregated-range-proof
[criterion]: https://github.com/japaric/criterion.rs
[session_type_blog]: https://blog.chain.com/bulletproof-multi-party-computation-in-rust-with-session-types-b3da6e928d5d
[curve25519_dalek]: https://doc.dalek.rs/curve25519_dalek/index.html
[parallel_edwards]: https://medium.com/@hdevalence/accelerating-edwards-curve-arithmetic-with-parallel-formulas-ac12cf5015be
[gh_repo]: https://github.com/dalek-cryptography/bulletproofs/
[gh_milestones]: https://github.com/dalek-cryptography/bulletproofs/milestones
[interstellar]: https://interstellar.com/
