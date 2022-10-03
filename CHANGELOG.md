# Changelog

All notable changes to this project will be documented in this file. See [standard-version](https://github.com/conventional-changelog/standard-version) for commit guidelines.

## [4.3.0](https://github.com/tari-project/bulletproofs/compare/v4.2.1...v4.3.0) (2022-10-03)


### Features

* port over to dalek lib ([#17](https://github.com/tari-project/bulletproofs/issues/17)) ([a9828c7](https://github.com/tari-project/bulletproofs/commit/a9828c7586ffa113d8a2c287bbe1033d152267ca))

### [4.2.1](https://github.com/tari-project/bulletproofs/compare/v4.2.0...v4.2.1) (2022-06-23)

## [4.2.0](https://github.com/tari-project/bulletproofs/compare/v4.1.2...v4.2.0) (2022-05-25)


### Features

* swap out curve25519-dalek-ng for curve25519-dalek ([#14](https://github.com/tari-project/bulletproofs/issues/14)) ([b8ff1f0](https://github.com/tari-project/bulletproofs/commit/b8ff1f0694575957d1ca928b60710c23bd85d260))

## 4.0.0

* Update to `rand_core` `0.6`.  This requires a major version bump but the API
  is otherwise unchanged from the `3.x` series.

## 3.0.1

* Update repository URL.

## 3.0.0

* Add support for stable Rust.
* Update `curve25519-dalek` and internal dependencies.
* Tweaks to the (unstable) R1CS API.

## 2.0.0

* Switch from `failure` to `std`-compatible errors via `thiserror`.
* Update `rand`, `curve25519-dalek`, `merlin` versions.
* Adds `no_std` support by @xoloki.

## 1.0.4

* Change doc-include paths to allow compilation on the latest Rust nightly
  (which changed the path root).
* Various changes to the (unreleased, unstable) R1CS implementation, which is
  disabled in the released version of the code.

## 1.0.3

* Mistakes were made. Yanked and replaced by 1.0.4 above.

## 1.0.2

* Updates the library to use the renamed functions in Merlin 1.1.
* Adds additional validation checks to prevent identity points being used as
  part of a proof.  This does not appear to have security content, but is
  intended as a defense-in-depth mechanism.  
  See [this comment][identity_comment] for more motivation.
* Documentation tweaks.

## 1.0.1

* Tweaks to crate metadata.
* Minor documentation changes.
* Adds a regression test for deserialize-and-verify for proofs created using
  v1.0.0, to ensure they continue to verify in future versions.

## 1.0.0

* Minor tweaks to the prerelease version.  
* Preliminary support for R1CS proofs, but this feature is hard-disabled in the
  published crate.

## 1.0.0-pre.0

Initial prerelease version, supporting single and aggregated range proofs, and
multiparty proof aggregation.

[identity_comment]: https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r251916724
