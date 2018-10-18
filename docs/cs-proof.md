Constraint system proof protocol
================================

The `circuit_proof` module contains an API for producing a proof that a set of secret values satisfies a given constraint system.

For more background on the constraint system proofs, see these two sections in the `notes` module:

* [Constraint system](../notes/index.html#constraint-system): description of the constraint system architecture.
* [Constraint system proof](../notes/index.html#constraint-system-proof): the math behind the constraint system proofs.

Prover’s algorithm
------------------

The protocol begins with the prover computing commitments to the secret values \\(\mathbf{v}\\) and adding all commitments to the protocol transcript.

\\[
V_i \gets \operatorname{Com}(v_i, {\widetilde{v}\_i}) = v\_i \cdot B + {\widetilde{v}\_i} \cdot {\widetilde{B}}
\\] where each \\(\widetilde{v}\_i\\) is sampled randomly.

The prover then [builds constraints](#building-constraints), allocating necessary multiplication gates on the fly,
generating challenge values bound to the commitments \\(V_i\\), filling in weights \\(\mathbf{W}\_L,\mathbf{W}\_R,\mathbf{W}\_O,\mathbf{W}\_V\\), and assigning values to the left, right and output wires
of the multiplication gates (\\(\mathbf{a}\_{L}, \mathbf{a}\_{R}, \mathbf{a}\_{O}\\)).

Once all multiplication wires are assigned, the prover commits to them via vector Pedersen commitments:

\\[
\begin{aligned}
\tilde{a} \\;&{\xleftarrow{\\$}}\\; \mathbb Z\_p \\\\
\tilde{o} \\;&{\xleftarrow{\\$}}\\; \mathbb Z\_p \\\\
A_I          &\gets \widetilde{B} \cdot \tilde{a} + \langle \mathbf{G} , \mathbf{a}\_L \rangle + \langle \mathbf{H}, \mathbf{a}\_R \rangle \\\\
A_O          &\gets \widetilde{B} \cdot \tilde{o} + \langle \mathbf{G} , \mathbf{a}\_O \rangle \\\\
\end{aligned}
\\]

The prover also computes blinding factors \\(\mathbf{s}\_L, \mathbf{s}\_R\\)
for the left and right multiplication values and commits to them:

\\[
\begin{aligned}
\mathbf{s}\_{L} \\; &{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n} \\\\
\mathbf{s}\_{R} \\; &{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n} \\\\
\tilde{s} \\;       &{\xleftarrow{\\$}}\\; \mathbb Z\_p \\\\
S                   &\gets \widetilde{B} \cdot \tilde{s} + \langle \mathbf{G} , \mathbf{s}\_L \rangle + \langle \mathbf{H}, \mathbf{s}\_R \rangle
\end{aligned}
\\]

The prover adds \\(A_I\\), \\(A_O\\) and \\(S\\) to the protocol transcript
and obtains challenge scalars \\(y,z \in {\mathbb Z\_p}\\) from the transcript.

The prover then flattens the constraints using \\(q\\) powers of challenge \\(z\\):

\\[
\begin{aligned}
\mathbf{w}\_L &\gets z \mathbf{z}^q \cdot \mathbf{W}\_L, \\\\
\mathbf{w}\_R &\gets z \mathbf{z}^q \cdot \mathbf{W}\_R, \\\\
\mathbf{w}\_O &\gets z \mathbf{z}^q \cdot \mathbf{W}\_O, \\\\
\mathbf{w}\_V &\gets z \mathbf{z}^q \cdot \mathbf{W}\_V,
\end{aligned}
\\]
where each of \\(\mathbf{w}\_L, \mathbf{w}\_R, \mathbf{w}\_O\\) has length \\(n\\) and \\(\mathbf{w}\_V\\) has length \\(m\\).

The prover then constructs the blinded polynomials and their inner product:

\\[
\begin{aligned}
  {\mathbf{l}}(x)  &\gets \mathbf{a}\_L \cdot x + \mathbf{s}\_L \cdot x^3 + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + \mathbf{a}\_O \cdot x^2 \\\\
  {\mathbf{r}}(x)  &\gets \mathbf{y}^n \circ \mathbf{a}\_R \cdot x + \mathbf{y}^n \circ \mathbf{s}\_R \cdot x^3 + \mathbf{w}\_L \cdot x - \mathbf{y}^n + \mathbf{w}\_O \\\\
  t(x)             &\gets {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}
\end{aligned}
\\]

The prover generates blinding factors for terms \\(t\_1, t\_3, t\_4, t\_5, t\_6\\) and creates Pedersen commitments to them
(term \\(t\_0\\) is known to be zero and term \\(t\_2\\) is being proven):

\\[
\begin{aligned}
  &\tilde{t}\_1, \tilde{t}\_3, \tilde{t}\_4, \tilde{t}\_5, \tilde{t}\_6 \\;{\xleftarrow{\\$}}\\; \mathbb Z\_p \\\\
  &T_i \gets \operatorname{Com}(t_i, {\tilde{t}\_i}) = t\_i \cdot B + {\tilde{t}\_i} \cdot {\widetilde{B}} \\\\
\end{aligned}
\\]

The prover adds \\(T_1, T_3, T_4, T_5, T_6\\) to the protocol transcript
and obtains a challenge scalar \\(x \in {\mathbb Z\_p}\\) from the transcript.

Using the concrete value \\(x\\), the prover computes
the synthetic blinding factors \\({\tilde{t}}(x)\\) and \\(\tilde{e}\\):

\\[
\begin{aligned}
  \tilde{t}\_2    &\gets \langle \mathbf{w}\_V, \tilde{\mathbf{v}} \rangle \\\\
  {\tilde{t}}(x)  &\gets \sum\_{i = 1}^{6} x^i \tilde{t}\_{i} \\\\
  {\tilde{e}}     &\gets \tilde{a} \cdot x + \tilde{o} \cdot x^2 + \tilde{s} \cdot x^3 \\\\
\end{aligned}
\\]

The prover adds \\(t(x), {\tilde{t}}(x), {\tilde{e}}\\) to the protocol transcript, obtains a challenge scalar \\(w \in {\mathbb Z\_p}\\), and uses it to create a point \\(Q\\):

\\[
	Q \gets  w \cdot B
\\]

The prover evaluates polynomials \\(\mathbf{l}(x), \mathbf{r}(x)\\) and
[pads them to the next power of two](#padding-mathbflx-and-mathbfrx-for-the-inner-product-proof) \\(n \rightarrow n^{+}\\):

\\[
\begin{aligned}
             n^{+} &= 2^{\lceil \log_2 n \rceil} \\\\
\mathbf{l}^{+}     &= \mathbf{l}(x) \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{r}^{+}     &= \mathbf{r}(x) \hspace{0.1cm} || \hspace{0.1cm} [-y^n,...,-y^{n^{+}-1}]
\end{aligned}
\\]

The prover also takes a larger slice of the generators \\(\mathbf{G}, \mathbf{H}\\):

\\[
\begin{aligned}
\mathbf{G}^{+}     &= \mathbf{G}    \hspace{0.1cm} || \hspace{0.1cm} [G_n,...,G_{n^{+}-1}] \\\\
{\mathbf{H}'}^{+}  &= \mathbf{H}'   \hspace{0.1cm} || \hspace{0.1cm} \Big( [y^n,...,y^{n^{+}-1}] \circ [H_n,...,H_{n^{+}-1}] \Big) \\\\
\end{aligned}
\\]

Finally, the prover performs the [inner product argument](../inner_product_proof/index.html) to prove the relation:
\\[
\operatorname{PK}\left\\{
  (\mathbf{G}^{+}, {\mathbf{H}'}^{+} \in {\mathbb G}^{n^{+}}, P', Q \in {\mathbb G}; \mathbf{l}^{+}, \mathbf{r}^{+} \in {\mathbb Z\_p}^{n^{+}})
  : P' = {\langle \mathbf{l}^{+}, \mathbf{G}^{+} \rangle} + {\langle \mathbf{r}^{+}, {\mathbf{H}'}^{+} \rangle} + {\langle \mathbf{l}^{+}, \mathbf{r}^{+} \rangle} Q
\right\\}
\\] where \\({\mathbf{H}'}^{+} = {\mathbf{y}}^{-n^{+}} \circ \mathbf{H}^{+}\\).

The result of the inner product proof is a list of \\(2k\\) points and \\(2\\) scalars, where \\(k = \lceil \log_2(n) \rceil\\): \\(\\{L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}\\).

The complete proof consists of \\(13+2k\\) 32-byte elements:
\\[
  \\{A\_I, A\_O, S, T\_1, T\_3, T\_4, T\_5, T\_6, t(x), {\tilde{t}}(x), \tilde{e}, L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}
\\]



Verifier’s algorithm
--------------------

The input to the verifier is the aggregated proof, which contains the \\(m\\) value commitments \\(V_{(j)}\\),
and \\(32 \cdot (13 + 2 k)\\) bytes of the proof data where \\(k = \lceil \log_2(n) \rceil\\) and \\(n\\) is a number of [multiplication gates](#multiplication-gates):

\\[
  \\{A\_I, A\_O, S, T\_1, T\_3, T\_4, T\_5, T\_6, t(x), {\tilde{t}}(x), \tilde{e}, L\_k, R\_k, \\dots, L\_1, R\_1, a, b\\}
\\]

The verifier starts by adding all value commitments \\(V_i\\) to the protocol transcript.

The verifier then [builds constraints](#building-constraints), allocating necessary multiplication gates on the fly and
generating challenge values bound to the commitments \\(V_i\\).

The verifier uses the Fiat-Shamir transform to obtain challenges by adding the appropriate data sequentially to the protocol transcript:

1. \\(A_I, A_O, S\\) are added to obtain challenge scalars \\(y,z \in {\mathbb Z\_p}\\),
2. \\(T_1, T_3, T_4, T_5, T_6\\) are added to obtain a challenge \\(x \in {\mathbb Z\_p}\\),
3. \\(t(x), {\tilde{t}}(x), \tilde{e}\\) are added to obtain a challenge \\(w \in {\mathbb Z\_p}\\).

The verifier flattens constraints:

\\[
\begin{aligned}
\mathbf{w}\_L &\gets z \mathbf{z}^q \cdot \mathbf{W}\_L, \\\\
\mathbf{w}\_R &\gets z \mathbf{z}^q \cdot \mathbf{W}\_R, \\\\
\mathbf{w}\_O &\gets z \mathbf{z}^q \cdot \mathbf{W}\_O, \\\\
\mathbf{w}\_V &\gets z \mathbf{z}^q \cdot \mathbf{W}\_V, \\\\
         w\_c &\gets \langle z \mathbf{z}^q, \mathbf{c} \rangle,
\end{aligned}
\\]
where each of \\(\mathbf{w}\_L, \mathbf{w}\_R, \mathbf{w}\_O\\) has length \\(n\\) and \\(\mathbf{w}\_V\\) has length \\(m\\).

The verifier [pads the proof data](#padding-mathbflx-and-mathbfrx-for-the-inner-product-proof)
by taking a larger slice of the generators \\(\mathbf{G},\mathbf{H}\\) and more powers of challenges \\(y\\) up to \\((n^{+}-1)\\):

\\[
\begin{aligned}
             n^{+} &= 2^{\lceil \log_2 n \rceil} \\\\
\mathbf{G}^{+}     &= \mathbf{G}   \hspace{0.1cm} || \hspace{0.1cm} [G_n,...,G_{n^{+}-1}] \\\\
\mathbf{H}^{+}     &= \mathbf{H}   \hspace{0.1cm} || \hspace{0.1cm} [H_n,...,H_{n^{+}-1}] \\\\
\mathbf{y}^{n^{+}} &= \mathbf{y}^n \hspace{0.1cm} || \hspace{0.1cm} [y^n,...,y^{n^{+}-1}] \\\\
\end{aligned}
\\]

The verifier computes the following scalars for the [inner product argument](../inner_product_proof/index.html):

\\[
	\\{u\_{1}^{2}, \dots, u\_{k}^{2}, u\_{1}^{-2}, \dots, u\_{k}^{-2}, s_0, \dots, s_{n^{+}-1}\\}
\\]

The goal of the verifier is to check two equations.

**First**, verify the second term of the polynomial \\(t(x)\\) (see [notes](#proving-that-t_2-is-correct)):

\\[
\begin{aligned}
t(x) B + {\tilde{t}}(x) {\widetilde{B}}
&\stackrel{?}{=}
x^2 \langle \mathbf{w}\_V, \mathbf{V} \rangle + x^2 \big(w\_c + \delta(y,z)\big) B + \sum\_{i = 1,3,4,5,6} x^i T\_{i},\\\\
\delta(y, z) &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{w}\_L \rangle \\\\
\end{aligned}
\\]

If we rewrite the check as a comparison with the identity point, we get:
\\[
0 \stackrel{?}{=} x^2 \langle \mathbf{w}\_V, \mathbf{V} \rangle + x^2 \big(w\_c + \delta(y,z)\big) B + \sum\_{i = 1,3,4,5,6} x^i T\_{i} - t(x) B - {\tilde{t}}(x) {\widetilde{B}}
\\]

**Second**, verify the inner product argument for the vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\) that form the \\(t(x)\\) (see [inner-product protocol](../inner_product_proof/index.html#verification-equation))
  
\\[
P' \overset ? = {\langle a \cdot \mathbf{s}, \mathbf{G}^{+} \rangle} + {\langle {\mathbf{y}^{-n^{+}}} \circ (b /{\mathbf{s}}), \mathbf{H}^{+} \rangle} + abQ - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right).
\\]

Rewriting as a comparison with the identity point and expanding \\(Q = wB\\) and \\(P' = P^{+} + t(x) wB\\) as [needed for transition to the inner-product protocol](../notes/index.html#inner-product-proof):

\\[
0 \overset ? = P^{+} + t(x) wB - {\langle a \cdot \mathbf{s}, \mathbf{G}^{+} \rangle} - {\langle \mathbf{y}^{-n^{+}} \circ (b /\mathbf{s}), \mathbf{H}^{+} \rangle} - abwB + \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right),
\\]
where the [definition](#proving-that-mathbflx-mathbfrx-are-correct) of \\(P^{+}\\) is:

\\[
\begin{aligned}
  P^{+}   = -{\widetilde{e}} {\widetilde{B}} + x \cdot A_I + x^2 \cdot A_O - \langle \mathbf{1}, \mathbf{H}^{+} \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot S
\end{aligned}
\\]
\\[
\begin{aligned}
  W_L &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_L, \mathbf{H} \rangle \\\\
  W_R &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{G} \rangle \\\\
  W_O &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_O, \mathbf{H} \rangle \\\\
\end{aligned}
\\]

The verifier combines two equations in one by sampling a random factor \\(r \\; {\xleftarrow{\\$}} \\; {\mathbb Z\_p}\\),
multiplying the first equation by \\(r\\), and adding it with the second equation.

Finally, verifier groups all scalars by each point and performs a single multiscalar multiplication:

\\[
\begin{aligned}
0 \quad \stackrel{?}{=} & \quad x       \cdot A\_I \\\\
                      + & \quad x^2     \cdot A\_O \\\\
                      + & \quad x^3     \cdot S \\\\
                      + & \quad \langle r x^2 \mathbf{w}\_V, \mathbf{V} \rangle \\\\
                      + & \quad \sum\_{i = 1,3,4,5,6} r x^i T\_{i} \\\\
                      + & \quad \Big(w \big(t(x) - ab\big) + r \big(x^2 (w\_c + \delta(y,z)) - t(x)\big) \Big) \cdot B \\\\
                      + & \quad (-{\widetilde{e}} - r{\tilde{t}}(x)) \cdot \widetilde{B} \\\\
                      + & \quad {\langle \big( x \mathbf{y}^{-n} \circ \mathbf{w}\_R \big) || \mathbf{0} - a\mathbf{s}, \mathbf{G}^{+} \rangle}\\\\
                      + & \quad {\langle -\mathbf{1} + \mathbf{y}^{-n^{+}} \circ \big( (x \mathbf{w}\_L + \mathbf{w}\_O) || \mathbf{0} - (b /{\mathbf{s}}) \big), \mathbf{H}^{+} \rangle}\\\\
                      + & \quad {\langle [u_{1}^2,    \dots, u_{k}^2    ], [L_1, \dots, L_{k}] \rangle}\\\\
                      + & \quad {\langle [u_{1}^{-2}, \dots, u_{k}^{-2} ], [R_1, \dots, R_{k}] \rangle}
\end{aligned}
\\] where \\(1/{\mathbf{s}}\\) are inverses of \\(\mathbf{s}\\), computed as a [reversed list](../inner_product_proof/index.html#verifiers-algorithm) of \\(\mathbf{s}\\).


