Arithmetic Circuit Proofs
=========================

An arithmetic circuit is a directed acyclic graph, where every node with indegree zero is an input gate, and every other node is either a multiplication gate or an addition gate. Multiplication gates can either be variable multiplication gates, where two variables are multiplied together, or constant multiplication gates, where a variable is multiplied by a constant. Addition gates can also be either variable addition gates or constant addition gates. 

The goal of an *arithmetic circuit proof* is for a prover to convince a verifier that a particular set of values \\(v\\) satisfy the constraints represented by the arithmetic circuit, without revealing any additional information about the values \\(v\\).

The prover will use the efficient inner product protocol to do this, so we want to work towards expressing the arithmetic circuit's conditions in terms of a single inner product. The prover begins with a vector of secret values \\(v\\), and a vector of commitments to those secret values \\(V\\). The prover will send \\(V\\) to the verifier, along with the proof.

Notation for arithmetic circuit proofs
------------------------------------------

In the paper, matrices are labeled as \\( \textbf{W}\_L, \textbf{W}\_R, \textbf{W}\_O, \textbf{W}\_V \\). We will keep this notation, but will note to readers not to confuse the \\(\textbf{W}\_{L,R,O,V}\\) notation for being a vector of points. 

We will use the notation described in the [`notation`](../notes/index.html#notation) section of the notes. In addition, we rename one more variable from the paper, to make it clear which variables are blinding factors:
\\[
\begin{aligned}
    \beta         &\xrightarrow{} \tilde{o} \\\\
\end{aligned}
\\]

Proving statements about arithmetic circuits gates
--------------------------------------------------

An arithmetic circuit represents a set of constraints on some inputs, where the constraints are satisfied if and only if the inputs are correctly applied to the circuit and all of the gates in the arithmetic circuit graph perform their operations correctly. Therefore, an arithmetic circuit can also be expressed as a set of constraints on inputs. To convert a circuit into a constraint system, take each of its inputs as variables and reconnect them with consistency equations. 

One type of gate in an arithmetic circuit is a variable multiplication gate, which takes two input variables and multiplies them to get an output. If for all of the multiplication gates in a circuit, \\(\textbf{a}\_L\\) is the vector of the first input to each gate, \\(\textbf{a}\_R\\) is the vector of the second input to each gate, and \\(\textbf{a}\_O\\) is the vector of results, then the following equation will represent the relationship between the wires of all the multiplication gates in the circuit:

\\[
\textbf{a}\_L \circ \textbf{a}\_R = \textbf{a}\_O
\\]

Other types of gates in arithmetic circuits are constant multiplication gates, constant addition gates, and variable addition gates. All of these gates can be represented as a collection of linear constraints. Constant multiplication gates are represented by multiplying the input variable by a corresponding constant in a matrix (\\( \textbf{W}\_L, \textbf{W}\_R, \textbf{W}\_O, \textbf{W}\_V \\) ), constant addition gates are represented by multiplying the input variable by one and adding the constant in \\( \textbf{c}\\), and variable addition gates are represented by multiplying both input variables by one. All of these constraints are represented together in the following equation:

\\[
\textbf{W}\_L \cdot \textbf{a}\_L +
\textbf{W}\_R \cdot \textbf{a}\_R +
\textbf{W}\_O \cdot \textbf{a}\_O =
\textbf{W}\_V \cdot \textbf{v} +
\textbf{c}
\\]

Combining statements using challenge variables
----------------------------------------------

We can rewrite the statement about multiplication gates into an inner product equation, using the challenge variable \\(y\\). We can do this for a random challenge \\(y\\) because \\({\mathbf{b}} = {\mathbf{0}}\\) if and only
if[^4] \\({\langle {\mathbf{b}}, {\mathbf{y}}^{n} \rangle} = 0\\). The equation \\(\textbf{a}\_L \circ \textbf{a}\_R = \textbf{a}\_O\\) becomes:

\\[
\langle \textbf{a}\_L \circ \textbf{a}\_R - \textbf{a}\_O ,
\textbf{y}^n \rangle = 0
\\]

We can rewrite the statement about the linear constraints into an inner product equation, using the challenge variable \\(z\\). We can do this for a random challenge \\(z\\), for the same reason as above. The equation
\\(
\textbf{W}\_L \cdot \textbf{a}\_L +
\textbf{W}\_R \cdot \textbf{a}\_R +
\textbf{W}\_O \cdot \textbf{a}\_O =
\textbf{W}\_V \cdot \textbf{v} +
\textbf{c}
\\) 
becomes:

\\[
\langle z \textbf{z}^Q, 
\textbf{W}\_L \cdot \textbf{a}\_L +
\textbf{W}\_R \cdot \textbf{a}\_R +
\textbf{W}\_O \cdot \textbf{a}\_O -
\textbf{W}\_V \cdot \textbf{v} -
\textbf{c}
\rangle = 0
\\]

We can combine these two inner product equations, since they are offset by different multiples of challenge variable \\(z\\). The statement about multiplication gates is multiplied by \\(z^0\\), while the statements about addition and scalar multiplication gates are multiplied by a power of \\(z\\) between \\(z^1\\) and \\(z \cdot z^Q\\). Combining the two equations gives us:

\\[
\langle \textbf{a}\_L \circ \textbf{a}\_R - \textbf{a}\_O ,
\textbf{y}^n \rangle +
\langle z \textbf{z}^Q, 
\textbf{W}\_L \cdot \textbf{a}\_L +
\textbf{W}\_R \cdot \textbf{a}\_R +
\textbf{W}\_O \cdot \textbf{a}\_O -
\textbf{W}\_V \cdot \textbf{v} -
\textbf{c}
\rangle = 0
\\]

[^4]: This is because the polynomial in terms of \\(y\\) is zero at every point
if and only if every term of it is zero. The verifier is going to sample
a random \\(y\\) after the prover commits to all the values forming the terms of
that polynomial, making the probability that the prover cheated negligible.
This trick allows implementing logical `AND` with any number of terms.

Rearranging into a single inner product statement
-------------------------------------------------

We want to work towards expressing the arithmetic circuit's conditions in terms of a single inner product, so that we can use the inner product argument to represent it in a more compact and efficient-to-verify form. 
Our goal is to rearrange the equation above so that terms
involving \\({\mathbf{a}}\_{L}\\) and \\({\mathbf{a}}\_{O}\\) appear only on the left-hand side, terms
involving \\({\mathbf{a}}\_{R}\\) appear only on the right-hand side, and
non-secret terms (which the verifier can compute on its own) are
factored out into a new term \\(\delta(y, z) \\).

If we break apart the equation into individual terms, we can write it as:

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle =
\langle \textbf{a}\_L \circ \textbf{a}\_R, \textbf{y}^n \rangle -
\langle \textbf{a}\_O, \textbf{y}^n \rangle + 
\langle z \textbf{z}^Q, 
\textbf{W}\_L \cdot \textbf{a}\_L \rangle +
\langle z \textbf{z}^Q, 
\textbf{W}\_R \cdot \textbf{a}\_R \rangle +
\langle z \textbf{z}^Q, 
\textbf{W}\_O \cdot \textbf{a}\_O \rangle
\\]

Merge the statements containing \\(\textbf{a}\_O \\).

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle =
\langle \textbf{a}\_L, 
\textbf{y}^n \circ \textbf{a}\_R \rangle + 
\langle \textbf{a}\_L,
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle +
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle +
\langle \textbf{a}\_R, 
z \textbf{z}^Q \cdot \textbf{W}\_R \rangle
\\]

Multiply the \\( \langle \textbf{a}\_R, 
z \textbf{z}^Q \cdot \textbf{W}\_R \rangle \\) term by \\(\textbf{y}^n\\) one one side of the inner product and by \\(\textbf{y}^{-n}\\) on the other side:

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle =
\langle \textbf{a}\_L, 
\textbf{y}^n \circ \textbf{a}\_R \rangle + 
\langle \textbf{a}\_L,
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle +
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle +
\langle \textbf{y}^n \circ \textbf{a}\_R, 
\textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \rangle
\\]

Merge the statements containing \\(\textbf{y}^n \circ \textbf{a}\_R\\).

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle =
\langle \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), 
\textbf{y}^n \circ \textbf{a}\_R \rangle + 
\langle \textbf{a}\_L,
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle +
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle
\\]

Add \\(\delta(y, z) = \langle \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), z \textbf{z}^Q \cdot \textbf{W}\_L \rangle \\) to both sides. 

\\[
\begin{aligned}
\langle z \textbf{z}^Q,
\textbf{c} &+ \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) \\\\
&= \langle \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), 
\textbf{y}^n \circ \textbf{a}\_R \rangle + 
\langle \textbf{a}\_L,
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle \\\\ &+
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle + 
\langle \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), z \textbf{z}^Q \cdot \textbf{W}\_L \rangle
\end{aligned}
\\]

Merge the terms containing \\(z \textbf{z}^Q \cdot \textbf{W}\_L\\).

\\[
\begin{aligned}
\langle z \textbf{z}^Q,
\textbf{c} &+ \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) \\\\
&= \langle \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), 
\textbf{y}^n \circ \textbf{a}\_R \rangle + 
\langle \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R),
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle +
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle
\end{aligned}
\\]

Merge the terms containing \\(\textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R)\\).

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) =
\langle \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R), 
\textbf{y}^n \circ \textbf{a}\_R +
z \textbf{z}^Q \cdot \textbf{W}\_L \rangle +
\langle \textbf{a}\_O, 
-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle
\\]

Note: if you want to combine \\( \langle a, b \rangle + \langle c, d \rangle\\) into one inner product, you can do so by taking a degree of the linear combination with respect to a challenge scalar. For example, the 2nd degree of \\( \langle a \cdot x + c \cdot x^2, b \cdot x + d \cdot x^0 \rangle \\) is equal to \\( \langle a, b \rangle + \langle c, d \rangle\\). We can use this technique for the above equation by assigning \\(a, b, c, d\\) the following values:

\\[
\begin{aligned}
a &= \textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \\\\
b &= \textbf{y}^n \circ \textbf{a}\_R +
z \textbf{z}^Q \cdot \textbf{W}\_L\\\\
c &= \textbf{a}\_O \\\\
d &= -\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O
\end{aligned}
\\]

Next, we combine \\(a, b, c, d\\) using the equation \\( \langle a \cdot x + c \cdot x^2, b \cdot x + d \cdot x^0 \rangle \\). When we take its second degree, we recover a single inner product, which was our original goal:

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) = 
\text{2nd degree of }
\langle (\textbf{a}\_L + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R)) \cdot x + 
\textbf{a}\_O \cdot x^2,
(\textbf{y}^n \circ \textbf{a}\_R +
z \textbf{z}^Q \cdot \textbf{W}\_L) \cdot x +
(-\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O) \cdot x^0 \rangle 
\\]

Distribute the \\(x\\) values: 

\\[
\langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) = 
\text{2nd degree of }
\langle \textbf{a}\_L \cdot x + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \cdot x + 
\textbf{a}\_O \cdot x^2,
\textbf{y}^n \circ \textbf{a}\_R \cdot x +
z \textbf{z}^Q \cdot \textbf{W}\_L \cdot x -
\textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \rangle
\\]

This is equivalent to the equation we started with, but has a single
inner product with \\({\mathbf{a}}\_{L}\\) and \\({\mathbf{a}}\_{O}\\) on the left, \\({\mathbf{a}}\_{R}\\) on
the right, and non-secret terms factored out.

Blinding the inner product
--------------------------

The prover cannot send the vectors in the inner-product equation to the verifier without revealing information about the values \\(v\\). Also, since the inner-product argument is not zero-knowledge, the vectors cannot be used in the inner-product argument without revealing information about \\(v\\) either. To solve this problem, the prover chooses vectors of blinding factors

\\[
{\mathbf{s}}\_{L}, {\mathbf{s}}\_{R} \\;{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n},
\\]

and uses them to blind \\(\mathbf{a}\_L\\) and \\(\mathbf{a}\_R\\).

\\[
\begin{aligned}
\mathbf{a}\_{L} &\leftarrow \mathbf{a}\_{L} + \mathbf{s}\_{L} \cdot x^2 \\\\
\mathbf{a}\_{R} &\leftarrow \mathbf{a}\_{R} + \mathbf{s}\_{R} \cdot x^2
\end{aligned}
\\]

Note: the blinding factors are multiplied by \\(x^2\\) so that when the substitution is made into the \\(\textbf{l}(x)\\) and \\(\textbf{r}(x)\\) equations, \\({\mathbf{s}}\_{L}\\) will be in the third degree of \\(x\\) in \\(\textbf{l}(x)\\), and \\({\mathbf{s}}\_{L}\\) will be in the third degree of \\(x\\) in \\(\textbf{r}(x)\\). As a result, the blinding factors will not interfere with the value \\(t_2\\), which is the 2nd degree of \\(\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle\\).

We construct vector polynomials \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\), which represent the left and right sides of the input to the inner-product equation, with these new definitions:
\\[
\begin{aligned}
  {\mathbf{l}}(x) &= (\textbf{a}\_L + \textbf{s}\_L \cdot x^2) \cdot x + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \cdot x + \textbf{a}\_O \cdot x^2 \\\\
  &= \textbf{a}\_L \cdot x + \textbf{s}\_L \cdot x^3 + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \cdot x + \textbf{a}\_O \cdot x^2 \\\\
  {\mathbf{r}}(x) &= \textbf{y}^n \circ (\textbf{a}\_R + \textbf{s}\_R \cdot x^2) \cdot x + z \textbf{z}^Q \cdot \textbf{W}\_L \cdot x - \textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O \\\\
  &= \textbf{y}^n \circ \textbf{a}\_R \cdot x + \textbf{y}^n \circ \textbf{s}\_R \cdot x^3 + z \textbf{z}^Q \cdot \textbf{W}\_L \cdot x - \textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O
\end{aligned}
\\]

When we take the inner product of \\({\mathbf{l}}(x)\\) and \\({\mathbf{l}}(x)\\), we get:

\\[
\begin{aligned}
  t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} &= t\_{1} x + t\_{2} x^{2} + t\_{3} x^{3} + t\_{4} x^{4} + t\_{5} x^{5} + t\_{6} x^{6} \\\\
  &= \sum_{i=1}^{6} t_i x^i
\end{aligned}
\\]

Notice that the second degree of \\(t(x)\\) does not include any blinding factors (because the blinding factors end up in the third or greater degrees of \\(t(x)\\)). The second degree also conveniently includes the inner product forms of the initial arithmetic gate statements that we are trying to prove:

\\[
\begin{aligned}
t_2 &= \text{2nd degree of } \langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle
\\\\
&= \langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) \\\\
&= \langle \textbf{a}\_L \circ \textbf{a}\_R, \textbf{y}^n \rangle -
\langle \textbf{a}\_O, \textbf{y}^n \rangle + 
\langle z \textbf{z}^Q, 
\textbf{W}\_L \cdot \textbf{a}\_L \rangle +
\langle z \textbf{z}^Q, 
\textbf{W}\_R \cdot \textbf{a}\_R \rangle +
\langle z \textbf{z}^Q, 
\textbf{W}\_O \cdot \textbf{a}\_O \rangle + \delta(y, z)
\end{aligned}
\\]

Proving that \\(t_2\\) is correct
---------------------------------

The prover first forms a commitment to the coefficients of \\(t(x)\\), then convinces the verifier that these commit to the correct \\(t(x)\\) by evaluating the polynomial at a challenge point \\(x\\). This proves that \\(t(x)\\) is correct and follows the following equation:

\\[
\begin{aligned}
t(x) &= \sum\_{i=1}^{6} x^i t\_{i} \\\\
t_2 &= \langle z \textbf{z}^Q,
\textbf{c} + \textbf{W}\_V \cdot \textbf{v} \rangle + \delta(y, z) \\\\
\end{aligned}
\\]

We define \\(\textbf{V}\\) as the vector of commitments to \\(\textbf{v}\\), and \\(T_i\\) as the commitment to \\(t_i\\) for \\(i \in [1, 3, 4, 5, 6]\\):

\\[
\begin{aligned}
V_j &= B \cdot v_j + \widetilde{B} \cdot \tilde{v}\_j \quad \forall j \in [1, m] \\\\
T_i &= B \cdot t_i + \widetilde{B} \cdot \tilde{t}\_i \quad \forall i \in [1, 3, 4, 5, 6] \\\\
\end{aligned}
\\]

The prover forms these commitments, and sends them to the verifier. These commitments are related to each other and to \\(t(x)\\) by the following diagram:

\\[
\begin{aligned}
  t(x) B                     &\quad &= \quad & x^2 \langle z \textbf{z}^Q , \textbf{W}\_v \cdot \textbf{v} \rangle \cdot B      & \quad &+ \quad & x^2 \big(\langle  z \textbf{z}^Q , \textbf{c} \rangle + \delta(y,z)\big) B  & \quad &+ \quad& x t\_{1} B                     &\quad &+\quad & \sum\_{i=3}^{6} x^i t\_{i} B \\\\
    +                        &\quad &  \quad &  +                          & \quad &  \quad &  +             & \quad &  \quad& +                             &\quad & \quad & +   \\\\
  {\tilde{t}}(x) {\widetilde{B}} &\quad &= \quad & x^2 \langle z \textbf{z}^Q , \textbf{W}\_v \cdot \tilde{\textbf{v}} \rangle \cdot \widetilde{B}  & \quad &+ \quad & 0 {\widetilde{B}}  & \quad &+ \quad& x {\tilde{t}}\_{1} {\widetilde{B}} &\quad &+\quad & \sum\_{i=3}^{6} x^i \tilde{t\_{i}} {\widetilde{B}} \\\\
    \shortparallel           &\quad &  \quad & \shortparallel              & \quad &  \quad & \shortparallel & \quad &  \quad& \shortparallel                &\quad & \quad & \shortparallel   \\\\
                 &\quad &= \quad & x^2 \langle z \textbf{z}^Q , \textbf{W}\_v \cdot \textbf{V} \rangle                         & \quad &+ \quad & x^2 \big(\langle  z \textbf{z}^Q , \textbf{c} \rangle + \delta(y,z)\big) B  & \quad &+ \quad& x T\_{1}                       &\quad &+\quad & \sum\_{i=3}^{6} x^i T\_{i}
\end{aligned}
\\]

Notice that the sum of each column is a commitment to the variable in the top row using the blinding factor in the second row. The sum of all of the columns is
\\(t(x) B + {\tilde{t}}(x) {\widetilde{B}}\\), a commitment to the value
of \\(t\\) at the point \\(x\\), using the synthetic blinding factor[^5]:
\\[
  {\tilde{t}}(x) = x^2 \langle z \textbf{z}^Q , \textbf{W}\_v \cdot \tilde{\textbf{v}} \rangle + x {\tilde{t}}\_{1} + \sum\_{i=3}^{6} x^i \tilde{t\_{i}} 
\\]

To convince the verifier that
\\(t(x) = \delta(y,z) + \sum\_{i=1}^{6} x^i t\_{i}\\), the prover sends
the opening \\(t(x), {\tilde{t}}(x)\\) to the verifier, who uses the
bottom row of the diagram to check consistency:
\\[
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} x^2 \langle z \textbf{z}^Q , \textbf{W}\_v \cdot \textbf{V} \rangle + x^2 \big(\langle  z \textbf{z}^Q , \textbf{c} \rangle + \delta(y,z)\big) B + x T\_{1} + \sum\_{i=3}^{6} x^i T\_{i}
\\]

[^5]: The blinding factor is synthetic in the sense that it is
    synthesized from the blinding factors of the other commitments.

Proving that \\(\textbf{l}(x)\\), \\(\textbf{r}(x)\\) are correct
-----------------------------------------------------------------

We want to relate \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) to commitments
to \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\), \\({\mathbf{s}}\_{L}\\), and
\\({\mathbf{s}}\_{R}\\). Since \\[
{\mathbf{r}}(x) = \textbf{y}^n \circ \textbf{a}\_R \cdot x + \textbf{y}^n \circ \textbf{s}\_R \cdot x^3 + z \textbf{z}^Q \cdot \textbf{W}\_L \cdot x - \textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O
\\]
we need commitments to \\({\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}\\) and
\\({\mathbf{y}}^{n} \circ {\mathbf{s}}\_{R}\\). However, since the prover
must form commitments before receiving the verifier’s challenge \\(y\\), the
prover can only commit to \\({\mathbf{a}}\_{R}\\) and \\({\mathbf{s}}\_{R}\\). Since the prover’s
commitments are to \\({\mathbf{a}}\_{R}\\) and \\({\mathbf{s}}\_{R}\\), the verifier needs to transmute
the prover’s commitment over
\\(
({\mathbf{a}}\_{L},{\mathbf{a}}\_{R}, {\widetilde{a}})
\\)
into a commitment over
\\(
({\mathbf{a}}\_{L}, {\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}, {\widetilde{a}})
\\)
(and similarly for \\({\mathbf{s}}\_{R}\\)).
To do this, notice that
\\[
\begin{aligned}
  \text{commitment over }({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}, {\widetilde{a}})
  &=
  {\langle {\mathbf{a}}\_{L}, {\mathbf{G}} \rangle} + {\langle {\mathbf{a}}\_{R}, {\mathbf{H}} \rangle} + {\widetilde{a}} {\widetilde{B}} \\\\
  &=
  {\langle {\mathbf{a}}\_{L}, {\mathbf{G}} \rangle} + {\langle {\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}, {\mathbf{y}}^{-n} \circ {\mathbf{H}} \rangle} + {\widetilde{a}} {\widetilde{B}},
\end{aligned}
\\]
so that by changing generators to
\\({\mathbf{H}}' = {\mathbf{y}}^{-n} \circ {\mathbf{H}}\\), the point which
is a commitment to
\\(({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}, {\widetilde{a}})\\) with respect to
\\(({\mathbf{G}}, {\mathbf{H}}, {\widetilde{a}})\\) is transmuted into a
commitment to
\\(({\mathbf{a}}\_{L}, {\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}, {\widetilde{a}})\\)
with respect to \\(({\mathbf{G}}, {\mathbf{H}}', {\widetilde{a}})\\).

We define the following commitments over the components of \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\):

\\[
\begin{aligned}
A_I &= \widetilde{B} \cdot \tilde{a} + \langle \textbf{G} , \textbf{a}\_L \rangle + \langle \textbf{H}, \textbf{a}\_R \rangle \\\\
A_O &= \widetilde{B} \cdot \tilde{o} + \langle \textbf{G} , \textbf{a}\_O \rangle \\\\
W_L &= \langle z \textbf{z}^Q \cdot \textbf{W}\_L , \textbf{H}' \rangle \\\\
W_R &= \textbf{y}^{-n} \circ (\langle z \textbf{z}^Q \cdot \textbf{W}\_R) , \textbf{G} \rangle \\\\
W_O &= \langle z \textbf{z}^Q \cdot \textbf{W}\_O , \textbf{H}' \rangle \\\\
S &= \widetilde{B} \cdot \tilde{s} + \langle \textbf{G} , \textbf{s}\_L \rangle + \langle \textbf{H}, \textbf{s}\_R \rangle
\end{aligned}
\\]

The prover forms these commitments, and sends them to the verifier.

For reference, here are the equations for \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\):

\\[
\begin{aligned}
  {\mathbf{l}}(x)  &= \textbf{a}\_L \cdot x + \textbf{s}\_L \cdot x^3 + \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \cdot x + \textbf{a}\_O \cdot x^2 \\\\
  {\mathbf{r}}(x)  &= \textbf{y}^n \circ \textbf{a}\_R \cdot x + \textbf{y}^n \circ \textbf{s}\_R \cdot x^3 + z \textbf{z}^Q \cdot \textbf{W}\_L \cdot x - \textbf{y}^n + z \textbf{z}^Q \cdot \textbf{W}\_O
\end{aligned}
\\]

To relate the prover’s commitments to
\\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\), we use the following diagram:

\\[
\begin{aligned}
  {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle}         &\quad &= \quad & {\langle {\mathbf{a}}\_L \cdot x, {\mathbf{G}} \rangle}      & \quad &+ \quad & {\langle {\mathbf{a}}\_O \cdot x^2, {\mathbf{G}} \rangle}  & \quad &+ \quad& \langle \textbf{y}^{-n} \circ (z \textbf{z}^Q \cdot \textbf{W}\_R) \cdot x , \textbf{G} \rangle      &\quad &+\quad & \langle \textbf{s}\_L \cdot x^3 , \textbf{G} \rangle \\\\
    +                        &\quad &  \quad &  +                          & \quad &  \quad &  +             & \quad &  \quad& +                             &\quad & \quad & +   \\\\
  {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}  &\quad &= \quad & \langle \textbf{a}\_R \cdot x, {\mathbf{H}} \rangle & \quad &+ \quad & - \langle \textbf{1}, \textbf{H} \rangle  & \quad &+ \quad& \langle z \textbf{z}^Q \cdot (\textbf{W}\_L \cdot x + \textbf{W}\_O), \textbf{H}' \rangle &\quad &+\quad & \langle \textbf{s}\_R \cdot x^3 , \textbf{H} \rangle \\\\
    +                        &\quad &  \quad &  +                          & \quad &  \quad &  +             & \quad &  \quad& +                             &\quad & \quad & +   \\\\
  \tilde{e} \cdot \widetilde{B}  &\quad &= \quad & \tilde{a} \cdot x \cdot \widetilde{B} & \quad &+ \quad & \tilde{o} \cdot x^2 \cdot \widetilde{B}  & \quad &+ \quad& 0 &\quad &+\quad & \tilde{s} \cdot x^3 \cdot \widetilde{B} \\\\
    \shortparallel           &\quad &  \quad & \shortparallel              & \quad &  \quad & \shortparallel & \quad &  \quad& \shortparallel                &\quad & \quad & \shortparallel   \\\\
                 &\quad &= \quad & x \cdot A_I                         & \quad &+ \quad & x^2 \cdot A_O - \langle \textbf{1}, \textbf{H} \rangle & \quad &+ \quad& W_L \cdot x + W_R \cdot x + W_O                       &\quad &+\quad & x^3 \cdot S
\end{aligned}
\\]

We can interpret the rows and columns similarly to the previous diagram:
the sum of each column is a vector Pedersen commitment with left and right halves from the first and second rows respectively
and blinding factor from the third row.
The sum of all of the columns is a vector
Pedersen commitment to \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) with
synthetic blinding factor \\({\widetilde{e}}\\).

To convince the verifier that
\\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\), the prover
sends \\({\widetilde{e}}\\) to the verifier, who uses the bottom row
to compute
\\[
\begin{aligned}
  P &= -{\widetilde{e}} {\widetilde{B}} + x \cdot A_I + x^2 \cdot A_O - \langle \textbf{1}, \textbf{H} \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot S \\\\
\end{aligned}
\\]
if the prover is honest, this is
\\(P = {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}\\),
so the verifier uses \\(P\\) and \\(t(x)\\) as inputs to the inner-product protocol
to prove that
\\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\).