The rank-1 constraint system API for programmatically defining constraint systems.

## Building a proof-of-shuffle constraint system

How this shuffle proof works

```ascii,no_run
Represents a permutation of a list of `k` scalars `{x_i}` into a list of `k` scalars `{y_i}`.

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

Leadin to shuffle gadget code

```rust,no_run
gadget code
```

explanation of gadget code

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
