# Contributing

We welcome code and documentation PRs.  It's probably best to start by
opening or commenting on an existing issue, since the code is in a state
of flux.

# Workflow

## Branches

Currently, the work on the `bulletproofs` crate is in two branches:

* `main` holds the latest released version;

* `develop` holds ongoing development work.

Pull requests should be made against `develop`, **not** `main`.

It's best to start a PR for every in-progress branch so that it's possible
to track all ongoing development work.  Adding the `PTAL` (please take a 
look) label indicates that the branch is ready for code review.

## Labels

Labels starting with `T-` are for labeling topics (`T-api`, `T-r1cs`, etc).

The `T-research` label indicates unsolved open problems.

Labels starting with `P-` are for priority levels.

Labels starting with `E-` are for effort estimates.

## CI

We enforce style in CI using `cargo fmt`.

The `bulletproofs` repo currently pins a Rust nightly.  This means that
all `cargo` invocations made inside of the `bulletproofs` repo use the
pinned nightly version.  This means that running `cargo fmt` in the
`bulletproofs` repo requires that `rustfmt` is installed *for the pinned
nightly toolchain*.  To do this, run
```
rustup component add rustfmt-preview
```
while in the `bulletproofs` repo.

To run `rustfmt`, use
```
cargo fmt
```
