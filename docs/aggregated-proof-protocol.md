The `aggregated_range_proof` module contains an API for producing a proof that multiple integer values are within a certain range.

Aggregated proof protocol
=========================

This is a documentation for the internal implementation of an aggregated range proof. You may find the introduction to all the pieces of the protocol, including how the aggregated range proof math works, in the [notes](../notes/index.html#aggregated-range-proof) module, and an introduction to the implementation of the single-value range proof in the [range proof module](../range_proof/index.html).

Prover's algorithm
------------------

In the aggregated proof case, the prover can be broken down into the individual `m` parties, and the one dealer that coordinates messages and provides challenges.

The protocol begins with each party `j` computing three commitments: to the value \\(v_j\\), to the bits of that value \\(\mathbf{a}\_{Lj}, \mathbf{a}\_{Rj}\\), and to the per-bit blinding factors \\(\mathbf{s}\_{Lj}, \mathbf{s}\_{Rj}\\).

\\[
\begin{aligned}
V_j &\gets \operatorname{Com}(v_j, {\widetilde{v}}\_j)                   && = v_j \cdot B + {\widetilde{v}}\_j \cdot {\widetilde{B}} \\\\
A_j &\gets \operatorname{Com}({\mathbf{a}}\_{Lj}, {\mathbf{a}}\_{Rj}) && = {\langle {\mathbf{a}}\_{Lj}, {\mathbf{G}}\_j \rangle} + {\langle {\mathbf{a}}\_{Rj}, {\mathbf{H}}\_j \rangle} + {\widetilde{a}}\_j {\widetilde{B}} \\\\
S_j &\gets \operatorname{Com}({\mathbf{s}}\_{Lj}, {\mathbf{s}}\_{Rj}) && = {\langle {\mathbf{s}}\_{Lj}, {\mathbf{G}}\_j \rangle} + {\langle {\mathbf{s}}\_{Rj}, {\mathbf{H}}\_j \rangle} + {\widetilde{s}}\_j {\widetilde{B}} \\\\
\end{aligned}
\\] where \\(\widetilde{v}\_j, \widetilde{a}\_j, \widetilde{s}\_j\\) are sampled randomly
from \\({\mathbb Z\_p}\\) and \\(\mathbf{s}\_{Lj}, \mathbf{s}\_{Rj}\\) are sampled randomly from \\({\mathbb Z\_p}^{n}\\).

The parties all send their \\(V_j\\), \\(A_j\\), and \\(S_j\\) values to the dealer. The dealer adds each \\(V_j\\) value to the protocol transcript, in order. The dealer then computes \\(A = \sum_{j=0}^{m-1} A_j\\) and \\(S = \sum_{j=0}^{m-1} S_j\\), and adds \\(A\\) and \\(S\\) to the protocol transcript and obtains challenge scalars \\(y,z \in {\mathbb Z\_p}\\), which it sends to all of the parties.

Using the challenges and the secret vectors, each party `j` contructs the vector polynomials \\(\mathbf{l}\_j(x)\\) and \\(\mathbf{r}\_j(x)\\), as well as the polynomial \\(t_j(x)\\). (See the [notes](../notes/index.html#blinding-the-inner-product-1) for more details on how these are constructed.)

As in the single-value range proof, each party uses Karatsuba’s method to compute the coefficients of the polynomial \\(t_j(x)\\).

Each party `j` commits to the terms \\(t_{j1}, t_{j2}\\):
\\[
\begin{aligned}
T\_{j1} &\gets \operatorname{Com}(t\_{j1}, {\tilde{t}\_{j1}})  && = t\_{j1} \cdot B + {\tilde{t}\_{j1}} \cdot {\widetilde{B}} \\\\
T\_{j2} &\gets \operatorname{Com}(t\_{j2}, {\tilde{t}\_{j2}})  && = t\_{j2} \cdot B + {\tilde{t}\_{j2}} \cdot {\widetilde{B}}
\end{aligned}
\\] where \\(\tilde{t}\_{j1}, \tilde{t}\_{j2}\\) are sampled randomly from \\({\mathbb Z\_p}\\).

The parties all send their \\(T_{j1}\\) and \\(T_{j2}\\) values to the dealer. The dealer then computes \\(T_1 = \sum_{j=0}^{m-1} T_{j1}\\) and \\(T_2 = \sum_{j=0}^{m-1} T_{j2}\\), and adds \\(T_1\\) and \\(T_2\\) to the protocol transcript. The dealer then obtains a challenge scalar \\(x \in {\mathbb Z\_p}\\), and sends \\(x\\) to all of the parties.

Each party uses \\(x\\) to evaluate the polynomials \\(\mathbf{l}\_j(x), \mathbf{r}\_j(x), t\_j(x)\\). They then compute the synthetic blinding factors:

\\[
\begin{aligned}
  {\tilde{t}}\_j(x) &\gets z^{2} {\tilde{v}}\_j + x {\tilde{t}}\_{j1} + x^{2} {\tilde{t}}\_{j2} \\\\
   \tilde{e}\_j     &\gets {\widetilde{a}}\_j   + x {\widetilde{s}}\_j
\end{aligned}
\\]

The parties all send their values \\(t_j(x), {\tilde{t}}\_j(x), \tilde{e}\_j, \mathbf{l}\_j(x), \mathbf{r}\_j(x)\\) to the dealer. The dealer then computes \\(t(x) = \sum_{j=0}^{m-1} t_j(x), {\tilde{t}}(x) = \sum_{j=0}^{m-1} {\tilde{t}}\_j(x),  {\tilde{e}} = \sum_{j=0}^{m-1} \tilde{e}\_j\\), and adds \\(t(x), {\tilde{t}}(x), {\tilde{e}}\\) to the protocol transcript. The dealer then obtains a challenge scalar \\(w \in {\mathbb Z\_p}\\), and uses it to create a point \\(Q\\):

\\[
	Q \gets  w \cdot B
\\]

The dealer creates the aggregated vector polynomials \\(\mathbf{l}(x), \mathbf{r}(x)\\) by concatenating all of the individual party \\(\mathbf{l}\_j(x)\\) and \\(\mathbf{r}\_j(x) \\) values.

The the prover then performs the [inner product argument](../inner_product_proof/index.html) to prove the relation:
\\[
\operatorname{PK}\left\\{
  ({\mathbf{G}}, {\mathbf{H}}' \in {\mathbb G}^{n \cdot m}, P', Q \in {\mathbb G}; {\mathbf{l}}, {\mathbf{r}} \in {\mathbb Z\_p}^{n\cdot m})
  : P' = {\langle {\mathbf{l}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}, {\mathbf{H}}' \rangle} + {\langle {\mathbf{l}}, {\mathbf{r}} \rangle} Q
\right\\}
\\] where \\({\mathbf{H}}' = {\mathbf{y}}^{-n \cdot m} \circ {\mathbf{H}}\\).

The result of the inner product proof is a list of \\(2k\\) points and \\(2\\) scalars, where \\(k = \log_2(n \cdot m)\\): \\(\\{L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}\\).

The complete range proof consists of \\(9+2k\\) 32-byte elements:
\\[
  \\{A, S, T_1, T_2, t(x), {\tilde{t}}(x), \tilde{e}, L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}
\\]

Verifier's algorithm
--------------------

The input to the verifier is the aggregated proof, which contains the range size `n`, the `m` value commitments \\(V_j\\), and \\(32 \cdot (9 + 2 k)\\) bytes of the proof data where \\(k = \log_2(n \cdot m)\\):

\\[
  \\{A, S, T_1, T_2, t(x), {\tilde{t}}(x), \tilde{e}, L\_{k}, R\_{k}, \\dots, L\_1, R\_1, a, b\\}
\\]

Verifier uses Fiat-Shamir transform to obtain challenges by adding the appropriate data sequentially to the protocol transcript:

1. \\(V_0, V_1, \dots, V_m, A, S\\) are added to obtain challenge scalars \\(y,z \in {\mathbb Z\_p}\\),
2. \\(T_1, T_2\\) are added to obtain a challenge \\(x \in {\mathbb Z\_p}\\),
3. \\(t(x), {\tilde{t}}(x), \tilde{e}\\) are added to obtain a challenge \\(w \in {\mathbb Z\_p}\\).

Verifier computes the following scalars for the [inner product argument](../inner_product_proof/index.html):

\\[
	\\{u\_{1}^{2}, \dots, u\_{k}^{2}, u\_{1}^{-2}, \dots, u\_{k}^{-2}, s_0, \dots, s_{n-1}\\}
\\]

The goal of the verifier is to check two equations:

1. First, verify the constant term of the polynomial \\(t(x)\\) (see [notes](../notes/index.html#proving-that-t_0-is-correct-1)):

\\[
\begin{aligned}
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} \sum_{j=0}^{m-1} z^{j+2} V_j + \delta(y,z) B + x T\_{1} + x^{2} T\_{2},\\\\
  \delta(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n \cdot m} \rangle} - \sum_{j=0}^{m-1} z^{j+3} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle}\\\\
\end{aligned}
\\]

  Rewriting as a comparison with the identity point:
  \\[
  0 \stackrel{?}{=} \sum_{j=0}^{m-1} z^{j+2} V_j + \delta(y,z) B + x T\_{1} + x^{2} T\_{2} - t(x) B - {\tilde{t}}(x) {\widetilde{B}}.
  \\]


stopped conversion here


2. Second, verify the inner product argument for the vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\) that form the \\(t(x)\\) (see [inner-product protocol](../inner_product_proof/index.html#verification-equation))
  
  \\[
  P' \overset ? = {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{y}^{-n}} \circ (b /{\mathbf{s}}), {\mathbf{H}} \rangle} + abQ - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right).
  \\]

  Rewriting as a comparison with the identity point and expanding \\(Q = wB\\) and \\(P' = P + t(x) wB\\) as [needed for transition to the inner-product protocol](../notes/index.html#inner-product-proof):
  
  \\[
  0 \overset ? = P + t(x) wB - {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} - {\langle {\mathbf{y}^{-n}} \circ (b /{\mathbf{s}}), {\mathbf{H}} \rangle} - abwB + \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right),
  \\]
  where the [definition](../notes/index.html#proving-that-mathbflx-mathbfrx-are-correct) of \\(P\\) is:
  \\[
  P  = -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{1}} + z^2 {\mathbf{y}^{-n}} \circ {\mathbf{2}}^n, {\mathbf{H}} \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle}.
\\]

Verifier combines two equations in one by sampling a random factor \\(c \\; {\xleftarrow{\\$}} \\; {\mathbb Z\_p}\\),
multiplying the first equation by \\(c\\), and adding it with the second equation.

Finally, verifier groups all scalars per each point and performs a single multiscalar multiplication over \\((7 + 2n + 2k)\\) points:

\\[
\begin{aligned}
0 \quad \stackrel{?}{=} & \quad 1       \cdot A \\\\
                      + & \quad x       \cdot S \\\\
                      + & \quad cz^2    \cdot V \\\\
                      + & \quad cx      \cdot T_1 \\\\
                      + & \quad cx^2    \cdot T_2 \\\\
                      + & \quad \Big(w \big(t(x) - ab\big) + c \big(\delta(y,z) - t(x)\big) \Big) \cdot B\\\\
                      + & \quad (-{\widetilde{e}} - c{\tilde{t}}(x)) \cdot \widetilde{B} \\\\
                      + & \quad {\langle {-z\mathbf{1} - a\mathbf{s}}, {\mathbf{G}} \rangle}\\\\
                      + & \quad {\langle {z\mathbf{1} + {\mathbf{y}}^{-n} \circ (z^2\mathbf{2}^n - b/{\mathbf{s}})}, {\mathbf{H}} \rangle}\\\\
                      + & \quad {\langle [u_{1}^2,    \dots, u_{k}^2    ], [L_1, \dots, L_{k}] \rangle}\\\\
                      + & \quad {\langle [u_{1}^{-2}, \dots, u_{k}^{-2} ], [R_1, \dots, R_{k}] \rangle}
\end{aligned}
\\] where \\(1/{\mathbf{s}}\\) are inverses of \\(\mathbf{s}\\), computed as a reversed list of \\(\mathbf{s}\\).


State machines for Party and Dealer
-------------------------------------







