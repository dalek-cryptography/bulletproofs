The `range_proof` module contains an API for producing a proof that multiple integer values are within a certain range.

Aggregated range proof protocol
===============================

This is a documentation for the internal implementation of the aggregated range proof. You may find the introduction to all the pieces of the range proof protocol in the [notes](../notes/index.html) module.

The aggregated range proof is a zero-knowledge proof of the following relation:
\\[
\operatorname{ZK-PK}\left\\{
  v_{(0)}, v_{(1)}, \dots, v_{(m-1)}  \in {\mathbb Z\_p}
  : v_{(0)}, v_{(1)}, \dots, v_{(m-1)} \in [0, 2^n)
\right\\}
\\] 

where \\(n\\) and \\(m\\) are both a power of \\(2\\).

Party and Dealer's algorithm
----------------------------

To create the aggregated range proof, \\(m\\) individual parties which each have a secret value \\(v_{(j)}\\)exchange messages with one dealer, without revealing their secrets. You may find more information on how the parties and dealers are implemented in [aggregated protocol notes](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

The protocol begins with each party \\(j\\) computing three commitments: to the value \\(v_{(j)}\\), to the bits of that value \\(\mathbf{a}\_{L, (j)}, \mathbf{a}\_{R, (j)}\\), and to the per-bit blinding factors \\(\mathbf{s}\_{L, (j)}, \mathbf{s}\_{R, (j)}\\).

\\[
\begin{aligned}
V_{(j)} &\gets \operatorname{Com}(v_{(j)}, {\widetilde{v}\_{(j)}})                   && = v\_{(j)} \cdot B + {\widetilde{v}\_{(j)}} \cdot {\widetilde{B}} \\\\
A_{(j)} &\gets \operatorname{Com}({\mathbf{a}}\_{L, (j)}, {\mathbf{a}}\_{R, (j)}) && = {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{G}\_{(j)}} \rangle} + {\langle {\mathbf{a}}\_{R, (j)}, {\mathbf{H}\_{(j)}} \rangle} + {\widetilde{a}\_{(j)}} {\widetilde{B}} \\\\
S_{(j)} &\gets \operatorname{Com}({\mathbf{s}}\_{L, (j)}, {\mathbf{s}}\_{R, (j)}) && = {\langle {\mathbf{s}}\_{L, (j)}, {\mathbf{G}\_{(j)}} \rangle} + {\langle {\mathbf{s}}\_{R, (j)}, {\mathbf{H}\_{(j)}} \rangle} + {\widetilde{s}\_{(j)}} {\widetilde{B}} \\\\
\end{aligned}
\\] where \\(\widetilde{v}\_{(j)}, \widetilde{a}\_{(j)}, \widetilde{s}\_{(j)}\\) are sampled randomly
from \\({\mathbb Z\_p}\\) and \\(\mathbf{s}\_{L, (j)}, \mathbf{s}\_{R, (j)}\\) are sampled randomly from \\({\mathbb Z\_p}^{n}\\).

The parties all send their \\(V_{(j)}\\), \\(A_{(j)}\\), and \\(S_{(j)}\\) values to the dealer as `BitCommitment`. The dealer adds each \\(V_{(j)}\\) value to the protocol transcript, in order. The dealer then computes \\(A\\) and \\(S\\) as follows:

\\[
\begin{aligned}
	A &= \sum_{j=0}^{m-1} A_{(j)} \\\\
	S &= \sum_{j=0}^{m-1} S_{(j)}
\end{aligned}
\\]

The dealer adds \\(A\\) and \\(S\\) to the protocol transcript and obtains challenge scalars \\(y,z \in {\mathbb Z\_p}\\) from the transcript. The dealer sends \\(y, z\\) as `BitChallenge` to all of the parties.

Using their secret vectors and the challenges \\(y, z\\) from `BitChallenge`, each party constructs vector polynomials:
\\[
\begin{aligned}
  {\mathbf{l}}\_{(j)}(x) &= {\mathbf{l}}\_{0, (j)} + {\mathbf{l}}\_{1, (j)} x \\\\
  {\mathbf{r}}\_{(j)}(x) &= {\mathbf{r}}\_{0, (j)} + {\mathbf{r}}\_{1, (j)} x \\\\
  {\mathbf{l}}\_{0, (j)} &\gets {\mathbf{a}}\_{L, (j)} - z {\mathbf{1}} \\\\
  {\mathbf{l}}\_{1, (j)} &\gets {\mathbf{s}}\_{L, (j)} \\\\
  {\mathbf{r}}\_{0, (j)} &\gets {\mathbf{y}}^{n}\_{(j)} \circ ({\mathbf{a}}\_{R, (j)}   + z {\mathbf{1}}) + z^{2} z_{(j)}{\mathbf{2}}^{n} \\\\
  {\mathbf{r}}\_{1, (j)} &\gets {\mathbf{y}}^{n}\_{(j)} \circ {\mathbf{s}}\_{R, (j)}
\end{aligned}
\\]

The inner product of the above vector polynomials is:
\\[
  t\_{(j)}(x) = {\langle {\mathbf{l}}\_{(j)}(x), {\mathbf{r}}\_{(j)}(x) \rangle} = t\_{0, (j)} + t\_{1, (j)} x + t\_{2, (j)} x^{2}, 
\\]

Each party uses Karatsuba’s method to compute the coefficients of that polynomial as follows:
\\[
\begin{aligned}
  t\_{0, (j)} &\gets {\langle {\mathbf{l}}\_{0, (j)}, {\mathbf{r}}\_{0, (j)} \rangle},  \\\\
  t\_{2, (j)} &\gets {\langle {\mathbf{l}}\_{1, (j)}, {\mathbf{r}}\_{1, (j)} \rangle},  \\\\
  t\_{1, (j)} &\gets {\langle {\mathbf{l}}\_{0, (j)}+ {\mathbf{l}}\_{1, (j)}, {\mathbf{r}}\_{0, (j)} + {\mathbf{r}}\_{1, (j)} \rangle} - t\_{0, (j)} - t\_{2, (j)} 
\end{aligned}
\\]

The party commits to the terms \\(t\_{1, (j)}, t\_{2, (j)}\\):
\\[
\begin{aligned}
T\_{1, (j)} &\gets \operatorname{Com}(t\_{1, (j)}, {\tilde{t}\_{(j1}})  && = t\_{1, (j)} \cdot B + {\tilde{t}\_{1, (j)}} \cdot {\widetilde{B}} \\\\
T\_{2, (j)} &\gets \operatorname{Com}(t\_{2, (j)}, {\tilde{t}\_{2, (j)}})  && = t\_{2, (j)} \cdot B + {\tilde{t}\_{2, (j)}} \cdot {\widetilde{B}}
\end{aligned}
\\] where \\(\tilde{t}\_{1, (j)}, \tilde{t}\_{2, (j)}\\) are sampled randomly from \\({\mathbb Z\_p}\\).

The parties all send their \\(T_{1, (j)}\\) and \\(T_{2, (j)}\\) values to the dealer as `PolyCommitment`. The dealer then computes \\(T_1\\) and \\(T_2\\) as follows:
\\[
\begin{aligned}
	T_1 &= \sum_{j=0}^{m-1} T_{1, (j)} \\\\
	T_2 &= \sum_{j=0}^{m-1} T_{2, (j)} \\\\
\end{aligned}
\\]

The dealer adds \\(T_1\\) and \\(T_2\\) to the protocol transcript and obtains a challenge scalar \\(x \in {\mathbb Z\_p}\\) from the transcript. The dealer sends \\(x\\) as `PolyChallenge` to all of the parties.

Each party uses \\(x\\) to evaluate their polynomials \\(\mathbf{l}\_{(j)}(x), \mathbf{r}\_{(j)}(x), t\_{(j)}(x)\\):

\\[
\begin{aligned}
  \mathbf{l}\_{(j)}  &\gets  {\mathbf{l}}\_{0, (j)} + {\mathbf{l}}\_{1, (j)} x\\\\
  \mathbf{r}\_{(j)}  &\gets  {\mathbf{r}}\_{0, (j)} + {\mathbf{r}}\_{1, (j)} x\\\\
  t\_{(j)}(x)        &\gets  t\_{0, (j)} + t\_{1, (j)} x + t\_{2, (j)} x^{2}
\end{aligned}
\\]

Next, each party computes their synthetic blinding factors:
\\[
\begin{aligned}
  {\tilde{t}}\_{(j)}(x) &\gets z^{2} {\tilde{v}}\_{(j)} + x {\tilde{t}}\_{1, (j)} + x^{2} {\tilde{t}}\_{2, (j)} \\\\
   \tilde{e}\_{(j)}     &\gets {\widetilde{a}}\_{(j)}   + x {\widetilde{s}}\_{(j)}
\end{aligned}
\\]

The parties all send their values \\(t_{(j)}(x), {\tilde{t}}\_{(j)}(x), \tilde{e}\_{(j)}, \mathbf{l}\_{(j)}(x), \mathbf{r}\_{(j)}(x)\\) to the dealer as `ProofShare`. The dealer then computes \\(t(x), \tilde{t}(x), \tilde{e}\\) as follows:
\\[
\begin{aligned}
	t(x) &= \sum_{j=0}^{m-1} t_{(j)}(x) \\\\
	{\tilde{t}}(x) &= \sum_{j=0}^{m-1} {\tilde{t}}\_{(j)}(x) \\\\
	{\tilde{e}} &= \sum_{j=0}^{m-1} \tilde{e}\_{(j)}
\end{aligned}
\\]

The dealer adds \\(t(x), {\tilde{t}}(x), {\tilde{e}}\\) to the protocol transcript, obtains a challenge scalar \\(w \in {\mathbb Z\_p}\\), and uses it to create a point \\(Q\\):

\\[
	Q \gets  w \cdot B
\\]

The dealer creates the aggregated vector polynomials \\(\mathbf{l}(x), \mathbf{r}(x)\\) by concatenating all of the individual party \\(\mathbf{l}\_{(j)}(x)\\) and \\(\mathbf{r}\_{(j)}(x) \\) values:

\\[
\begin{aligned}
	{\mathbf{l}}(x) &= {\mathbf{l}}\_{(0)}(x) || {\mathbf{l}}\_{(1)}(x) || \dots || {\mathbf{l}}\_{(m-1)}(x) \\\\
	{\mathbf{r}}(x) &= {\mathbf{r}}\_{(0)}(x) || {\mathbf{r}}\_{(1)}(x) || \dots || {\mathbf{r}}\_{(m-1)}(x) \\\\
\end{aligned}
\\]

The dealer then performs the [inner product argument](../inner_product_proof/index.html) to prove the relation:
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

The input to the verifier is the aggregated proof, which contains the range size \\(n\\), the \\(m\\) value commitments \\(V_{(j)}\\), and \\(32 \cdot (9 + 2 k)\\) bytes of the proof data where \\(k = \log_2(n \cdot m)\\):

\\[
  \\{A, S, T_1, T_2, t(x), {\tilde{t}}(x), \tilde{e}, L\_{k}, R\_{k}, \\dots, L\_1, R\_1, a, b\\}
\\]

The verifier uses the Fiat-Shamir transform to obtain challenges by adding the appropriate data sequentially to the protocol transcript:

1. \\(V_{(0)}, V_{(1)}, \dots, V_{(m)}, A, S\\) are added to obtain challenge scalars \\(y,z \in {\mathbb Z\_p}\\),
2. \\(T_1, T_2\\) are added to obtain a challenge \\(x \in {\mathbb Z\_p}\\),
3. \\(t(x), {\tilde{t}}(x), \tilde{e}\\) are added to obtain a challenge \\(w \in {\mathbb Z\_p}\\).

The verifier computes the following scalars for the [inner product argument](../inner_product_proof/index.html):

\\[
	\\{u\_{1}^{2}, \dots, u\_{k}^{2}, u\_{1}^{-2}, \dots, u\_{k}^{-2}, s_0, \dots, s_{n-1}\\}
\\]

The goal of the verifier is to check two equations:

1. First, verify the constant term of the polynomial \\(t(x)\\) (see [notes](../notes/index.html#proving-that-t_0-is-correct-1)):

  \\[
  \begin{aligned}
    t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} \sum_{j=0}^{m-1} z^{j+2} V_{(j)} + \delta(y,z) B + x T\_{1} + x^{2} T\_{2},\\\\
    \delta(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n \cdot m} \rangle} - \sum_{j=0}^{m-1} z^{j+3} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle}\\\\
  \end{aligned}
  \\]

  If we rewrite the check as a comparison with the identity point, we get:
  \\[
  0 \stackrel{?}{=} \sum_{j=0}^{m-1} z^{j+2} V_{(j)} + \delta(y,z) B + x T\_{1} + x^{2} T\_{2} - t(x) B - {\tilde{t}}(x) {\widetilde{B}}.
  \\]

2. Second, verify the inner product argument for the vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\) that form the \\(t(x)\\) (see [inner-product protocol](../inner_product_proof/index.html#verification-equation))
  
  \\[
  P' \overset ? = {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{y}^{-n \cdot m}} \circ (b /{\mathbf{s}}), {\mathbf{H}} \rangle} + abQ - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right).
  \\]

  Rewriting as a comparison with the identity point and expanding \\(Q = wB\\) and \\(P' = P + t(x) wB\\) as [needed for transition to the inner-product protocol](../notes/index.html#inner-product-proof):
  
  \\[
  0 \overset ? = P + t(x) wB - {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} - {\langle {\mathbf{y}^{-n \cdot m}} \circ (b /{\mathbf{s}}), {\mathbf{H}} \rangle} - abwB + \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right),
  \\]
  where the [definition](../notes/index.html#proving-that-mathbflx-mathbfrx-are-correct-1) of \\(P\\) is:

\\[
\begin{aligned}
  P &= -{\widetilde{e}} {\widetilde{B}} + A + x S - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle} + z{\langle {\mathbf{y}}^{n \cdot m}, {\mathbf{H}'} \rangle} + \sum_{j=0}^{m-1} {\langle z^{j+2} \cdot {\mathbf{2}}^n, {\mathbf{H}'}\_{[j \cdot n : (j+1) \cdot n]} \rangle}  \\\\
  &= -{\widetilde{e}} {\widetilde{B}} + A + x S - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle} + z{\langle {\mathbf{1}}, {\mathbf{H}} \rangle} + \sum_{j=0}^{m-1} {\langle z^{j+2} \cdot {\mathbf{2}}^n \circ {\mathbf{y}}^{n \cdot m}\_{[j \cdot n : (j+1) \cdot n]}, {\mathbf{H}}\_{[j \cdot n : (j+1) \cdot n]} \rangle}\\\\
  &= -{\widetilde{e}} {\widetilde{B}} + A + x S - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle} + z{\langle {\mathbf{1}}, {\mathbf{H}} \rangle} + {\langle {{\mathbf{y}}^{-n \cdot m} \circ z^2 (z^0 \mathbf{2}^n || z^1 \mathbf{2}^n || \dots || z^{m-1} \mathbf{2}^n)}, {\mathbf{H}} \rangle}
\end{aligned}
\\]



The verifier combines two equations in one by sampling a random factor \\(c \\; {\xleftarrow{\\$}} \\; {\mathbb Z\_p}\\),
multiplying the first equation by \\(c\\), and adding it with the second equation.

Finally, verifier groups all scalars by each point and performs a single multiscalar multiplication:

\\[
\begin{aligned}
0 \quad \stackrel{?}{=} & \quad 1       \cdot A \\\\
                      + & \quad x       \cdot S \\\\
                      + & \quad cz^2    \cdot V_{(0)} + cz^3 \cdot V_{(1)} + \dots + cz^{m+1} \cdot V_{(m-1)} \\\\
                      + & \quad cx      \cdot T_1 \\\\
                      + & \quad cx^2    \cdot T_2 \\\\
                      + & \quad \Big(w \big(t(x) - ab\big) + c \big(\delta(y,z) - t(x)\big) \Big) \cdot B\\\\
                      + & \quad (-{\widetilde{e}} - c{\tilde{t}}(x)) \cdot \widetilde{B} \\\\
                      + & \quad {\langle {-z\mathbf{1} - a\mathbf{s}}, {\mathbf{G}} \rangle}\\\\
                      + & \quad {\langle {z\mathbf{1} + {\mathbf{y}}^{-n \cdot m} \circ (z^2 (z^0 \mathbf{2}^n || z^1 \mathbf{2}^n || \dots || z^{m-1} \mathbf{2}^n) - b/{\mathbf{s}})}, {\mathbf{H}} \rangle}\\\\
                      + & \quad {\langle [u_{1}^2,    \dots, u_{k}^2    ], [L_1, \dots, L_{k}] \rangle}\\\\
                      + & \quad {\langle [u_{1}^{-2}, \dots, u_{k}^{-2} ], [R_1, \dots, R_{k}] \rangle}
\end{aligned}
\\] where \\(1/{\mathbf{s}}\\) are inverses of \\(\mathbf{s}\\), computed as a reversed list of \\(\mathbf{s}\\).

Individual share validation
---------------------------

If the dealer is aggregating a proof across \\(m\\) parties, and if one of those parties is faulty (or malicious) and creates an invalid `ProofShare`, then the `AggregatedProof` that the dealer creates will also be invalid. Therefore, it is helpful to be able to check the validity of an individual `ProofShare`, in order to determine if a party is at fault and if so, to block it.



The math for checking `ProofShare` validity is very similar to checking `AggregatedProof` validity, but does not require combining values from multiple parties. The goal of checking `ProofShare` validity is to verify three equations:

1. Verify that \\(\langle \mathbf{l}\_{(j)}(x), \mathbf{r}\_{(j)}(x) \rangle = t_{(j)}(x)\\)

The dealer can perform this check by simply taking the inner product of \\(\mathbf{l}\_{(j)}(x)\\) and \\( \mathbf{r}\_{(j)}(x)\\) and verifying that it is equal to \\(t_{(j)}(x)\\). Note that the dealer is not creating a proof, and thus the proof compactness of the inner product protocol is not a benefit in this situation, so it is sufficient to just perform an inner product multiplication.

2. Verify the constant term of the polynomial \\(t_{(j)}(x)\\)

The dealer wants to check if this statement is correct: 
  \\[
  \begin{aligned}
    t\_{(j)}(x) B + {\tilde{t}}\_{(j)}(x) {\widetilde{B}} \stackrel{?}{=} z^{2} z\_{(j)} V_{(j)} + \delta(y,z)\_{(j)} B + x T\_{1, (j)} + x^{2} T\_{2, (j)},\\\\
    \delta\_{(j)}(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n}\_{(j)} \rangle} - z^{3} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n} \rangle}\\\\
  \end{aligned}
  \\]

  If we rewrite the check as a comparison with the identity point, and plug in the definitions \\(z_{(j)} = z^j\\) and \\({\mathbf{y}}^{n}\_{(j)} = {\mathbf{y}}^{n \cdot m}\_{[j\cdot n : (j+1) \cdot n]} = {\mathbf{y}}^n y^{j \cdot n}\\), we get:

  \\[
  \begin{aligned}
    0 \stackrel{?}{=} z^{j+2} V_{(j)} + \delta(y,z)\_{(j)} B + x T\_{1, (j)} + x^{2} T\_{2, (j)} - t\_{(j)}(x) B - {\tilde{t}}\_{(j)}(x) {\widetilde{B}},\\\\
    \delta\_{(j)}(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^n \cdot y^{j \cdot n} \rangle} - z^{j+3} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n} \rangle}\\\\
  \end{aligned}
  \\]


3. Prove that \\( \mathbf{l}\_{(j)}(x), \mathbf{r}\_{(j)}(x) \\) are correct

The dealer wants to check if this statement is correct: 
\\[
\begin{aligned}
	A_{(j)} + xS_{(j)} - z{\langle {\mathbf{1}}, {\mathbf{G}}\_{(j)} \rangle} + z{\langle {\mathbf{1}}, {\mathbf{H}}\_{(j)} \rangle} + {\langle z^{2} z_{(j)} (\mathbf{y}^{n}\_{(j)})^{-1} \circ {\mathbf{2}}^n, {\mathbf{H}}\_{(j)} \rangle} \stackrel{?}{=} {\widetilde{e}}\_{(j)} {\widetilde{B}} + {\langle \mathbf{l}\_{(j)}(x), {\mathbf{G}}\_{(j)} \rangle} + {\langle \mathbf{r}\_{(j)}(x) \circ (\mathbf{y}^{n}\_{(j)})^{-1}, {\mathbf{H}}\_{(j)} \rangle}
\end{aligned}
\\]

If we rewrite the check as a comparison with the identity point, and plug in the definitions \\(z_{(j)} = z^j\\) and \\({\mathbf{y}}^{n}\_{(j)} = {\mathbf{y}}^{n \cdot m}\_{[j\cdot n : (j+1) \cdot n]} = {\mathbf{y}}^n y^{j \cdot n}\\), we get:

\\[
\begin{aligned}
	0 \stackrel{?}{=}A_{(j)} + xS_{(j)} - z{\langle {\mathbf{1}}, {\mathbf{G}}\_{(j)} \rangle} + z{\langle {\mathbf{1}}, {\mathbf{H}}\_{(j)} \rangle} + {\langle z^{j+2} \cdot \mathbf{y}^{-n} y^{-j \cdot n} \circ {\mathbf{2}}^n, {\mathbf{H}}\_{(j)} \rangle} - {\widetilde{e}}\_{(j)} {\widetilde{B}} - {\langle \mathbf{l}\_{(j)}(x), {\mathbf{G}}\_{(j)} \rangle} - {\langle \mathbf{r}\_{(j)}(x) \circ \mathbf{y}^{-n} y^{-j \cdot n} , {\mathbf{H}}\_{(j)} \rangle}
\end{aligned}
\\]

The dealer can combine equations `2` and `3` into one by sampling a random factor \\(c \\; {\xleftarrow{\\$}} \\; {\mathbb Z\_p}\\),
multiplying equation `2` by \\(c\\), and adding it with equation `3`. Finally, the dealer groups all scalars by each point and performs a single multiscalar multiplication:

\\[
\begin{aligned}
0 \quad \stackrel{?}{=} & \quad 1       \cdot A_{(j)} \\\\
                      + & \quad x       \cdot S_{(j)} \\\\
                      + & \quad (-{\widetilde{e}\_{(j)}} - c{\tilde{t}}\_{(j)}(x)) \cdot \widetilde{B} \\\\
                      + & \quad c \big(\delta_{(j)}(y,z) - t_{(j)}(x)\big) \cdot B\\\\
                      + & \quad cz^{j+2}    \cdot V_{(j)} \\\\
                      + & \quad cx      \cdot T_{1, (j)} \\\\
                      + & \quad cx^2    \cdot T_{2, (j)} \\\\
                      + & \quad {\langle {- \mathbf{l}\_{(j)}(x)} -z\mathbf{1}, {\mathbf{G}\_{(j)}} \rangle}\\\\
                      + & \quad {\langle {- \mathbf{r}\_{(j)}(x)} \circ \mathbf{y}^{-n} y^{-j \cdot n} + z\mathbf{1} + z^{j+2} \cdot \mathbf{y}^{-n} y^{-j \cdot n} \circ {\mathbf{2}}^n, {\mathbf{H}}\_{(j)} \rangle}\\\\
\end{aligned}
\\]
