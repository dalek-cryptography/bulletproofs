# Changelog

Entries are listed in reverse chronological order.

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
