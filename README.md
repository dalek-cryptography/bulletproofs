# Ristretto Bulletproofs

A pure-Rust implementation of [Bulletproofs][bp_website] using [Ristretto][ristretto].

This crate contains both an implementation and a set of notes on how and why
Bulletproofs work.  The [external documentation][doc_external] describes how to use this
crate’s API, while the [internal documentation][doc_internal] contains the notes.

## WARNING

This code is still research-quality.  It is not (yet) suitable for deployment.

## Documentation

* [Public API documentation][doc_external]
* [Internal documentation][doc_internal]
  * [Notes on how Bulletproofs work][bp_notes] (located in the internal `notes` module)
  * [Range proof protocol description][rp_notes]
  * [Inner product protocol description][ipp_notes]


Unfortunately, `cargo doc` does not yet have support for custom HTML injection
and for documenting private members, so the documentation is built using:

```text
make doc           # Builds external documentation
make doc-internal  # Builds internal documentation
```

Note: `cargo doc --open` rebuilds the docs without the custom
invocation, so it may be necessary to rerun `make`.

## Tests

Run tests with `cargo test`.

## Benchmarks

This crate uses [criterion.rs][criterion] for benchmarks.  Run benchmarks with
`cargo bench`.

## Features

The `yolocrypto` feature enables the `yolocrypto` feature in
`curve25519-dalek`, which enables the experimental AVX2 backend.  To use it for
Bulletproofs, the `target_cpu` must support AVX2:

```text
RUSTFLAGS="-C target_cpu=skylake" cargo bench --features "yolocrypto"
```

Skylake-X CPUs have double the AVX2 registers. To use them, try

```text
RUSTFLAGS="-C target_cpu=skylake-avx512" cargo bench --features "yolocrypto"
```

This prevents spills in the AVX2 parallel field multiplication code, but causes
worse code generation elsewhere ¯\\\_(ツ)\_/¯

## About

This is a research project being built for Chain, Inc, by Henry de Valence,
Cathie Yun, and Oleg Andreev.

[bp_website]: https://crypto.stanford.edu/bulletproofs/
[ristretto]: https://doc.dalek.rs/curve25519_dalek/ristretto/index.html
[doc_external]: https://doc.dalek.rs/ristretto_bulletproofs/index.html
[doc_internal]: https://doc-internal.dalek.rs/ristretto_bulletproofs/index.html
[bp_notes]: https://doc-internal.dalek.rs/ristretto_bulletproofs/notes/index.html
[rp_notes]: https://doc-internal.dalek.rs/ristretto_bulletproofs/range_proof/index.html
[ipp_notes]: https://doc-internal.dalek.rs/ristretto_bulletproofs/inner_product_proof/index.html
[criterion]: https://github.com/japaric/criterion.rs
