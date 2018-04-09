The `range_proof` module contains API for producing a range proof for a given integer value.

Range proof protocol
====================

This is a documentation for the internal implementation of a range proof. 
You may find the introduction to all the pieces of the protocol in the [notes](../notes/index.html) module.

The range proof is a zero-knowledge proof of the following relation
\\[
\operatorname{ZK-PK}\left\\{
  v \in {\mathbb Z\_p}
  : v \in [0, 2^n)
\right\\}
\\] where \\(n = 2^{k}\\) is a power of \\(2\\).

The protocol begins by computing three commitments: to the value \\(v\\), to the bits of that value \\(\mathbf{a}\_{L,R}\\), and to the per-bit blinding factors \\(\mathbf{s}\_{L,R}\\).

Each bit \\(a_i\\) is committed twice: as \\(a\_{L,i} = a\_i\\) and as \\(a\_{R,i} = a_i - 1\\).
Similarly for the blinding factors \\(\mathbf{s}\_{L,R}\\).

\\[
\begin{aligned}
V &= \operatorname{Com}(v, {\widetilde{v}})                   && = v \cdot B + {\widetilde{v}} \cdot {\widetilde{B}} \\\\
A &= \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}) && = {\langle {\mathbf{a}}\_L, {\mathbf{G}} \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{H}} \rangle} + {\widetilde{a}} {\widetilde{B}} \\\\
S &= \operatorname{Com}({\mathbf{s}}\_{L}, {\mathbf{s}}\_{R}) && = {\langle {\mathbf{s}}\_L, {\mathbf{G}} \rangle} + {\langle {\mathbf{s}}\_R, {\mathbf{H}} \rangle} + {\widetilde{s}} {\widetilde{B}} \\\\
\end{aligned}
\\] where \\(\widetilde{v}, \widetilde{a}, \widetilde{s}\\) are sampled randomly from \\({\mathbb Z\_p}\\) and \\(\mathbf{s}\_{L,R}\\) are sampled randomly from \\({\mathbb Z\_p}^{n}\\).




<!--
OLD STUFF:

\\[

{\mathbf{s}}\_{L}, {\mathbf{s}}\_{R} \\;{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n},

\operatorname{PK}\left\\{
  ({\mathbf{G}}, {\mathbf{H}} \in {\mathbb G}^n, P, Q \in {\mathbb G}; {\mathbf{a}}, {\mathbf{b}} \in {\mathbb Z\_p}^n)
  : P = {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} + {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} Q
\right\\}
\\] where \\(n = 2^{k}\\) is a power of \\(2\\).
-->