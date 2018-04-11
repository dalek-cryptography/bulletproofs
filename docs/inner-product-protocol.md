The `inner_product_proof` module contains API for producing a compact proof of an inner product of two vectors.

Inner product argument protocol
===============================

These notes explain how the protocol is implemented in the [`InnerProductProof`](struct.InnerProductProof.html) type.

We want to prove the relation
\\[
\operatorname{PK}\left\\{
  ({\mathbf{G}}, {\mathbf{H}} \in {\mathbb G}^n, P', Q \in {\mathbb G}; {\mathbf{a}}, {\mathbf{b}} \in {\mathbb Z\_p}^n)
  : P' = {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} + {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} Q
\right\\}
\\] where \\(n = 2^{k}\\) is a power of \\(2\\).

Prover’s algorithm
------------------

To start, we sketch the
interactive version of this protocol, and then describe the
optimizations discussed in the Bulletproofs paper for the
non-interactive version.

The protocol consists of \\(k = \lg n\\) rounds, indexed by
\\(j = k,\ldots,1\\). In the \\(j\\)-th round, the prover computes
\\[
\begin{aligned}
  L\_{j} &\gets {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{G}}\_{\operatorname{hi}} \rangle} + {\langle {\mathbf{b}}\_{\operatorname{hi}}, {\mathbf{H}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{b}}\_{\operatorname{hi}} \rangle} Q, \\\\
  R\_{j} &\gets {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{G}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{b}}\_{\operatorname{lo}}, {\mathbf{H}}\_{\operatorname{hi}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{b}}\_{\operatorname{lo}} \rangle} Q,
\end{aligned}
\\]
and sends \\(L\_{j}, R\_{j}\\) to the verifier. The verifier responds with a
challenge value \\(u\_{j} {\xleftarrow{\\$}}{\mathbb{Z}\_p}\\). The prover uses
\\(u\_{j}\\) to compute
\\[
\begin{aligned}
  {\mathbf{a}} &\gets {\mathbf{a}}\_{\operatorname{lo}} \cdot u\_{j} + u\_{j}^{-1} \cdot {\mathbf{a}}\_{\operatorname{hi}}, \\\\
  {\mathbf{b}} &\gets {\mathbf{b}}\_{\operatorname{lo}} \cdot u\_{j}^{-1} + u\_{j} \cdot {\mathbf{a}}\_{\operatorname{hi}},
\end{aligned}
\\]
the prover and verifier both compute
\\[
\begin{aligned}
  {\mathbf{G}} &\gets {\mathbf{G}}\_{\operatorname{lo}} \cdot u\_{j}^{-1} + u\_{j} \cdot {\mathbf{G}}\_{\operatorname{hi}}, \\\\
  {\mathbf{H}} &\gets {\mathbf{H}}\_{\operatorname{lo}} \cdot u\_{j} + u\_{j}^{-1} \cdot {\mathbf{H}}\_{\operatorname{hi}},
\end{aligned}
\\]
and use these vectors (all of length \\(2^{j-1}\\)) for the next round.
After the last (\\(j = 1\\)) round, the prover sends
\\(a, b = {\mathbf{a}}\_{0}, {\mathbf{b}}\_{0}\\) to the verifier, who accepts
if and only if
\\[
\begin{aligned}
L\_{1} u\_{1}^{2} + \cdots + L\_{k} u\_{k}^{2} + P' + R\_{k} u\_{k}^{-2} + \cdots + R\_{1} u\_{1}^{-2}&\overset ? = aG + bH + abQ,
\end{aligned}
\\]
where \\(G, H = {\mathbf{G}}\_{0}, {\mathbf{H}}\_{0}\\).

To make the protocol noninteractive, we replace the transmission of the
\\(L\_{j}\\) and \\(R\_{j}\\) and the response \\(u\_{j}\\) with a Fiat-Shamir
challenge, so that each \\(u\_{j}\\) is generated as a hash of the transcript
\\(L\_{k},R\_{k},\ldots,L\_{j},R\_{j}\\). At the end of the prover’s
computation, they send \\(a,b,L\_{k},R\_{k},\ldots,L\_{1},R\_{1}\\) to the
verifier.

Verifier’s algorithm
--------------------

Since the final \\(G\\) and \\(H\\) values are functions of the challenges
\\(u\_{k},\ldots,u\_{1}\\), the verifier has to compute them as part of the
verification process. However, while the prover needs to compute the
intermediate vectors \\({\mathbf{G}}\\), \\({\mathbf{H}}\\) in order to compute
the \\(L\_{j}\\) and \\(R\_{j}\\), the verifier doesn’t, and can compute the final
\\(G\\), \\(H\\) directly from the vectors \\({\mathbf{G}}\\), \\({\mathbf{H}}\\) and
the challenges \\(u\_{k}, \ldots, u\_{1}\\).

Let \\({\mathbf{G}}^{(j)}\\) be the value of \\({\mathbf{G}}\\) in the \\(j\\)-th
round, and let \\(G\_{i}\\) be the \\(i\\)-th entry of the initial vector
\\({\mathbf{G}}^{(k)} =
(G\_{0}, \ldots, G\_{n-1})\\). We have \\[
\begin{aligned}
  {\mathbf{G}}^{(j-1)} = ({\mathbf{G}}^{(j)})\_{\operatorname{lo}} u\_{j}^{-1} + ({\mathbf{G}}^{(j)})\_{\operatorname{hi}} u\_{j},\end{aligned}
\\]
so the coefficient of \\(G\_{i}\\) in the final \\(G\\) value is
\\[
\begin{aligned}
  s\_{i} &= u\_{k}^{b(i,k)} \cdots u\_1^{b(i,1)},\end{aligned}
\\] where
\\(b(i,j)\\) is either \\(-1\\) or \\(+1\\), according to whether \\(G\_{i}\\) appears in
the left or right half of \\({\mathbf{G}}^{(j)}\\). Since \\(G\_{i}\\) appears in
the \\((i \mod 2^{j})\\)-th entry of \\({\mathbf{G}}^{j}\\), this is
\\[
  b(i,j) =
           \begin{cases}
             -1 & \text{if $(i \mod 2^{j})  <  2^{j-1}$ }\\\\
             +1 & \text{if $(i \mod 2^{j}) \ge 2^{j-1}$ }\\\\
           \end{cases}.
\\]
But this is exactly
\\[
  b(i,j) =
           \begin{cases}
             -1 & \text{if bit $j-1$ of $i$ is 0} \\\\
             +1 & \text{if bit $j-1$ of $i$ is 1} \\\\
           \end{cases}.
\\]
This shows that
\\(G = {\langle {\mathbf{s}}, {\mathbf{G}} \rangle}\\). This formula differs
slightly from the one in the paper, because we index vectors and bits
from \\(0\\).

Since \\(H\\) is computed similarly, but with the roles of
\\({\mathbf{H}}\_{\operatorname{lo}}\\) and
\\({\mathbf{H}}\_{\operatorname{hi}}\\) reversed, a similar argument shows
that \\(H = {\langle 1/{\mathbf{s}}, {\mathbf{H}} \rangle}\\).

Notice that if \\(i'\\) is the bitwise \\(\texttt{NOT}\\) of \\(i\\), then \\(s\_{i'} = 1/s\_{i}\\),
and as \\(i\\) runs from \\(0\\) to \\((2^k - 1)\\), \\(i'\\) runs from \\((2^k - 1)\\) to \\(0\\),
so the vector of inverses \\(1/{\mathbf{s}}\\) is a reversed
vector \\({\mathbf{s}}\\) and no additional computation is required to
obtain the \\(1/s\_{i}\\).

### Verification equation

The verifier’s computation then becomes
\\[
\begin{aligned}
P' \overset ? =& aG +bH +abQ - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right) \\\\
=& {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} + {\langle b /{\mathbf{s}}, {\mathbf{H}} \rangle} + abQ - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right),
\end{aligned}
\\]
a single multiscalar multiplication with
\\(n + n + 1 + k + k = 2(n+k) + 1\\) points.

In order to combine the computation above with other checks in a parent protocol, we can provide these scalars:

\\[
  \\{u\_{1}^{2}, \dots, u\_{k}^{2}, u\_{1}^{-2}, \dots, u\_{k}^{-2}, s_0, \dots, s_{n-1}\\}.
\\]

Use the [`InnerProductProof::verification_scalars`](struct.InnerProductProof.html#method.verification_scalars) method to produce these scalars for a given inner product proof.
