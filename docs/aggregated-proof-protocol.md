The `aggregated_range_proof` module contains an API for producing a proof that multiple integer values are within a certain range.

Aggregated proof protocol
=========================

This is a documentation for the internal implementation of an aggregated range proof. You may find the introduction to all the pieces of the protocol in the [notes](../notes/index.html) module, and an introduction to how a single-value range proof works in the [range proof module](../range_proof/index.html).

We want to create an aggregated range proof for `m` values that is more efficient to create and verify than `m` individual range proofs.

The aggregated range proof has the same form as the individual range proof, but differs in that different parties are seperated by different powers of the challenge scalars `y` and `z`.

First principles
----------------

We want to prove that:
\\[
\begin{aligned}
  v_j \in [0, 2^n - 1] \forall j \in [1, m], \\\\
  v = v_0 || v_1 || ... || v_j
\end{aligned}
\\]

Write the bits of \\(v\\) as \\({\mathbf{a}}\\). Then:
\\[
\begin{aligned}
  {\langle {\mathbf{a}}, {\mathbf{2}}^{n \cdot m} \rangle} &= v,  \\\\
  {\mathbf{a}} \circ ({\mathbf{a}} - {\mathbf{1}}) &= {\mathbf{0}}^{n \cdot m} .
\end{aligned}
\\]





Per-party computations
----------------------



Aggregated proof statements
---------------------------






