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

Prover’s algorithm
------------------

The protocol begins by computing three commitments: to the value \\(v\\),
to the bits of that value \\(\mathbf{a}\_{L,R}\\),
and to the per-bit blinding factors \\(\mathbf{s}\_{L,R}\\).

Each bit \\(a_i\\) is committed twice: as \\(a\_{L,i} \gets a\_i\\) and as \\(a\_{R,i} \gets a_i - 1\\).
Similarly for the blinding factors \\(\mathbf{s}\_{L,R}\\).

\\[
\begin{aligned}
V &\gets \operatorname{Com}(v, {\widetilde{v}})                   && = v \cdot B + {\widetilde{v}} \cdot {\widetilde{B}} \\\\
A &\gets \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}) && = {\langle {\mathbf{a}}\_L, {\mathbf{G}} \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{H}} \rangle} + {\widetilde{a}} {\widetilde{B}} \\\\
S &\gets \operatorname{Com}({\mathbf{s}}\_{L}, {\mathbf{s}}\_{R}) && = {\langle {\mathbf{s}}\_L, {\mathbf{G}} \rangle} + {\langle {\mathbf{s}}\_R, {\mathbf{H}} \rangle} + {\widetilde{s}} {\widetilde{B}} \\\\
\end{aligned}
\\] where \\(\widetilde{v}, \widetilde{a}, \widetilde{s}\\) are sampled randomly
from \\({\mathbb Z\_p}\\) and \\(\mathbf{s}\_{L,R}\\) are sampled randomly from \\({\mathbb Z\_p}^{n}\\).

The prover then obtains challenge scalars \\(y,z \in {\mathbb Z\_p}\\) using a Fiat-Shamir transform,
so that each scalar is generated as a hash of the transcript of \\(\\{V, A, S\\}\\).

Using the challenges and the secret vectors, the prover constructs vector polynomials:
\\[
\begin{aligned}
  {\mathbf{l}}(x) &= {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1} x \\\\
  {\mathbf{r}}(x) &= {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} x \\\\
  {\mathbf{l}}\_{0} &\gets {\mathbf{a}}\_{L} - z {\mathbf{1}} \\\\
  {\mathbf{l}}\_{1} &\gets {\mathbf{s}}\_{L} \\\\
  {\mathbf{r}}\_{0} &\gets {\mathbf{y}}^{n} \circ ({\mathbf{a}}\_{R}   + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} \\\\
  {\mathbf{r}}\_{1} &\gets {\mathbf{y}}^{n} \circ {\mathbf{s}}\_{R}
\end{aligned}
\\]

The inner product of the above vector polynomials is:
\\[
  t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} = t\_{0} + t\_{1} x + t\_{2} x^{2}, 
\\]

The prover uses Karatsuba’s method to compute the coefficients of that polynomial as follows:
\\[
\begin{aligned}
  t\_{0} &\gets {\langle {\mathbf{l}}\_{0}, {\mathbf{r}}\_{0} \rangle},  \\\\
  t\_{2} &\gets {\langle {\mathbf{l}}\_{1}, {\mathbf{r}}\_{1} \rangle},  \\\\
  t\_{1} &\gets {\langle {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1}, {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} \rangle} - t\_{0} - t\_{2} 
\end{aligned}
\\]

The prover commits to the terms \\(t_1, t_2\\):
\\[
\begin{aligned}
T\_1 &\gets \operatorname{Com}(t\_1, {\tilde{t}\_1})  && = t\_1 \cdot B + {\tilde{t}\_1} \cdot {\widetilde{B}} \\\\
T\_2 &\gets \operatorname{Com}(t\_2, {\tilde{t}\_2})  && = t\_2 \cdot B + {\tilde{t}\_2} \cdot {\widetilde{B}}
\end{aligned}
\\] where \\(\tilde{t}\_1, \tilde{t}\_2\\) are sampled randomly from \\({\mathbb Z\_p}\\).

The prover then obtains a challenge scalar \\(x \in {\mathbb Z\_p}\\) using a Fiat-Shamir transform
by hashing \\(\\{T_1, T_2\\}\\) to the transcript of the protocol,
and uses it to evaluate the polynomials \\(\\{\mathbf{l}(x), \mathbf{r}(x), t(x)\\}\\):
\\[
\begin{aligned}
  \mathbf{l}  &\gets  {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1} x\\\\
  \mathbf{r}  &\gets  {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} x\\\\
  t(x)        &\gets  t\_{0} + t\_{1} x + t\_{2} x^{2}
\end{aligned}
\\]

Next, the prover computes the synthetic blinding factors:
\\[
\begin{aligned}
  {\tilde{t}}(x) &\gets z^{2} {\tilde{v}} + x {\tilde{t}}\_{1} + x^{2} {\tilde{t}}\_{2} \\\\
   \tilde{e}     &\gets {\widetilde{a}}   + x {\widetilde{s}}
\end{aligned}
\\]

The prover obtains another challenge scalar \\(w \in {\mathbb Z\_p}\\) using a Fiat-Shamir transform
by hashing \\(\\{t(x), {\tilde{t}}(x), \tilde{e}\\}\\) to the transcript of the protocol,
and uses it to create a unique point \\(Q\\):
\\[
	Q  \gets  w \cdot B
\\]

The the prover then performs the [inner product argument](../inner_product_proof/index.html) to prove the relation:
\\[
\operatorname{PK}\left\\{
  ({\mathbf{G}}, {\mathbf{H}}' \in {\mathbb G}^n, P, Q \in {\mathbb G}; {\mathbf{l}}, {\mathbf{r}} \in {\mathbb Z\_p}^n)
  : P = {\langle {\mathbf{l}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}, {\mathbf{H}}' \rangle} + {\langle {\mathbf{l}}, {\mathbf{r}} \rangle} Q
\right\\}
\\] where
\\[
\begin{aligned}
	P &= -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{H}}' \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle}; \\\\
	{\mathbf{H}}' &= {\mathbf{y}}^{-n} \circ {\mathbf{H}}
\end{aligned}
\\]

The result of the inner product proof is a list of \\(2k\\) points and \\(2\\) scalars: \\(\\{L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}\\).

The complete range proof consists of \\(9+2k\\) 32-byte elements:
\\[
  \\{A, S, T_1, T_2, t(x), {\tilde{t}}(x), \tilde{e}, L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}
\\]


Verifier’s algorithm
--------------------

Verifier’s input is the range size \\(n\\) (in bits), value commitment \\(V\\), and \\(32 \cdot (9 + 2 \lg n)\\) bytes of the proof data:
\\[
  \\{A, S, T_1, T_2, t(x), {\tilde{t}}(x), \tilde{e}, L\_{\lg n}, R\_{\lg n}, \\dots, L\_1, R\_1, a, b\\}
\\]

Verifier uses Fiat-Shamir transform to obtain challenges by hashing the appropriate data sequentially into the transcript of the protocol:

1. \\(\\{V, A, S\\}\\) are hashed to obtain challenge scalars \\(y,z \in {\mathbb Z\_p}\\),
2. \\(\\{T_1, T_2\\}\\) are hashed to obtain a challenge \\(x \in {\mathbb Z\_p}\\),
3. \\(\\{t(x), {\tilde{t}}(x), \tilde{e}\\}\\) are hased to obtain a challenge \\(w \in {\mathbb Z\_p}\\).

Verifier computes the following scalars for the [inner product argument](../inner_product_proof/index.html):

\\[
	\\{x\_{1}^{2}, x\_{1}^{-2}, \dots, x\_{\lg n}^{2}, x\_{\lg n}^{-2}, s_0, \dots, s_{n-1}\\}
\\]

The goal is to verify these two equations:

\\[
\begin{aligned}
 -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{y}}^{-n} \circ {\mathbf{H}} \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle} + t(x)wB \stackrel{?}{=}\\\\
\stackrel{?}{=} {\langle a \cdot {\mathbf{s}}, {\mathbf{G}} \rangle} + {\langle b /{\mathbf{s}}, {\mathbf{y}}^{-n} \circ {\mathbf{H}} \rangle} + abwB - \sum\_{j=1}^{k} \left( L\_{j} x\_{j}^{2} + x\_{j}^{-2} R\_{j} \right)\\\\
t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} z^2 V + \delta(y,z) B + x T\_{1} + x^{2} T\_{2}
\end{aligned}
\\] where \\(\delta(y,z) = (z - z^{2}) \langle 1, {\mathbf{y}}^{n} \rangle + z^{3} \langle \mathbf{1}, {\mathbf{2}}^{n} \rangle\\).

Verifier combines two equations in one by sampling a random factor \\(c \\; {\xleftarrow{\\$}} \\; {\mathbb Z\_p}\\),
multiplying the second equation by \\(c\\), and adding it to the first equation.

Finally, verifier groups all scalars per each point and performs a single multi-scalar multiplication over \\((7 + 2n + 2\\lg n)\\) points:

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
                      + & \quad {\langle {z\mathbf{1} + {\mathbf{y}}^{-n} \circ (x^2\mathbf{2}^n - b/{\mathbf{s}})}, {\mathbf{H}} \rangle}\\\\
                      + & \quad {\langle [x_{1}^2,    \dots, x_{\lg n}^2    ], [L_1, \dots, L_{\lg n}] \rangle}\\\\
                      + & \quad {\langle [x_{1}^{-2}, \dots, x_{\lg n}^{-2} ], [R_1, \dots, R_{\lg n}] \rangle}
\end{aligned}
\\] where \\(1/{\mathbf{s}}\\) are inverses of \\(\mathbf{s}\\), computed as a reversed list of \\(\mathbf{s}\\).






