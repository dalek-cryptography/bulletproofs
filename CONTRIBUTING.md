# Contributing

We welcome code and documentation PRs.  It's probably best to start by
opening or commenting on an existing issue, since the code is in a state
of flux.

# Workflow

## Branches

Currently, the work on the `bulletproofs` crate is in two branches:

* `main`, currently focused on having a production-ready implementation
  of the rangeproof protocol;

* `circuit`, currently focused on exploratory work around circuit
  proofs.

Changes affecting the rangeproof parts of the code should be made
against the `main` branch.

Changes affecting the circuit parts of the code should be made as PRs
against the `circuit` branch.  This allows piecewise review of the
circuit code while it's in development, as well as allowing a complete
review when we eventually merge it into the `main` branch.

The `main` branch is regularly merged into the `circuit` branch, so that
the circuit work stays in sync.

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
