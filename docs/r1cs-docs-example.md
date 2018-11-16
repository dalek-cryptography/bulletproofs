The rank-1 constraint system API for programmatically defining constraint systems.

## Building a proof-of-shuffle constraint system

```ascii,no_run
A shuffle is a permutation of a list of `k` scalars `{x_i}` into a list of `k` scalars `{y_i}`.

Algebraically it can be expressed as a statement that for a free variable `z`, the roots of the two polynomials in terms of `z` are the same up to a permutation:

    ∏(x_i - z) == ∏(y_i - z)

The prover can commit to blinded scalars `x_i` and `y_i` then receive a random challenge `z`,
and build a proof that the above relation holds.

K-shuffle requires `2*(K-1)` multipliers.

For K > 1:

        (x_0 - z)---⊗------⊗---(y_0 - z)        // mulx[0], muly[0]
                    |      |
        (x_1 - z)---⊗      ⊗---(y_1 - z)        // mulx[1], muly[1]
                    |      |
                   ...    ...
                    |      |
    (x_{k-2} - z)---⊗      ⊗---(y_{k-2} - z)    // mulx[k-2], muly[k-2]
                   /        \
    (x_{k-1} - z)_/          \_(y_{k-1} - z)

	Connect left and right sides of the shuffle statement
	    mulx_out[0] = muly_out[0]

	For i == [0, k-3]:
	    mulx_left[i]  = x_i - z
	    mulx_right[i] = mulx_out[i+1]
	    muly_left[i]  = y_i - z
	    muly_right[i] = muly_out[i+1]

	The last multipliers connect two last variables (on each side)
	    mulx_left[k-2]  = x_{k-2} - z
	    mulx_right[k-2] = x_{k-1} - z
	    muly_left[k-2]  = y_{k-2} - z
	    muly_right[k-2] = y_{k-1} - z

For K = 1:
	Connect x to y directly, omitting the challenge entirely as it cancels out
    	x_0 = y_0
```

This shuffle `prove` function takes a list of scalar inputs and outputs, makes commitments to them, and creates a proof that the committed outputs are a valid reordering of the committed inputs. 
The shuffle `verify` function verifies that, given a shuffle proof and a list of committed inputs and outputs, the outputs are a valid reordering of the inputs.

Because only the prover knows the scalar values of the inputs and outputs, and the verifier only sees the (blinded) committed inputs and outputs, the verifier has no knowledge of what the underlying inputs and output values are. Therefore, the only information the verifier learns from this protocol is whether or not the committed outputs are a valid shuffle of the committed inputs - this is why it is a zero-knowledge proof.


```rust,no_run
gadget code (fill_cs function)
```

In this example, `fill_cs` is private function that adds constraints to the constraint system that enforce that `y` (the outputs) are a valid reordering of `x` (the inputs). 

First, the function gets a challenge scalar `z` by calling the `ConstraintSystem::challenge_scalar`. This challenge is generated from commitments to high-level variables that were passed to the `ConstraintSystem` when it was created. As noted in the `challenge_scalar` documentation, it is important to ensure that the challenge is sound by making sure that low-level variables are bound to the high-level variables. 

After a check for the lengths of `x` and `y`, the function then makes multipliers to create polynomials in terms of the challenge scalar `z`. It starts with the last multipliers, representing \\( (x_{k-1} - z) * (x_{k-2} - z) \\) and \\( (y_{k-1} - z) * (y_{k-2} - z) \\). The outputs to these last multipliers than become an input to the next multiplier. This continues recursively until it reaches \\( x_0 \\) and \\(y_0\\). Then, it adds a constraint that \\( x_0 = y_0 \\), which constrains that the two polynomials in terms of challenge scalar `z` are equal to each other. This is true if and only if `y` is a valid reordering of `x`.


## Constructing a proof

leadin to proof construction

```rust,no_run
```

## Verifiying a proof

leadin to verify

```rust,no_run
```

## Using the `ShuffleProof`

```rust,no_run
```
