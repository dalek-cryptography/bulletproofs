This module contains notes on how and why Bulletproofs work.

The documentation is laid out roughly as follows.  General notes on
the range proof and inner-product proofs are here.  The description of
each protocol is contained in the respective `range_proof` and
`inner_product_proof` modules.  Finally, structs from those modules
are publicly re-exported from the crate root, so that the external
documentation describes how to use the API, while the internal
documentation describes how it works.

Notation
========

We change notation from the original Bulletproofs paper. The primary
motivation is that our implementation uses additive notation, and we
would like our description of the protocol to use the same notation as
the implementation.

In general, we use lower-case letters
\\(a, b, c\\)
for scalars in
\\({\mathbb Z\_p}\\)
and upper-case letters
\\(G,H,P,Q\\)
for group elements in
\\({\mathbb G}\\).
Vectors are denoted as \\({\mathbf{a}}\\) and \\({\mathbf{G}}\\),
and the inner product of two vectors is denoted by
\\({\langle -, - \rangle}\\). Notice that
\\({\langle {\mathbf{a}}, {\mathbf{b}} \rangle} \in {\mathbb Z\_p}\\)
produces a scalar, while
\\({\langle {\mathbf{a}}, {\mathbf{G}} \rangle} \in {\mathbb G}\\)
is a multiscalar multiplication. The vectors of all \\(0\\) and all \\(1\\) are
denoted by \\({\mathbf{0}}\\), \\({\mathbf{1}}\\) respectively.

Vectors are indexed starting from \\(0\\), unlike the paper, which indexes
from \\(1\\). For a scalar \\(y\\), we write
\\[
\begin{aligned}
  {\mathbf{y}}^{n} &= (1,y,y^{2},\ldots,y^{n-1})
\end{aligned}
\\]
for the vector whose \\(i\\)-th entry is \\(y^{i}\\). For vectors
\\({\mathbf{v}}\\) of even
length \\(2k\\), we define \\({\mathbf{v}}\_{\operatorname{lo}}\\) and
\\({\mathbf{v}}\_{\operatorname{hi}}\\) to be the low and high halves of
\\({\mathbf{v}}\\):
\\[
\begin{aligned}
    {\mathbf{v}}\_{\operatorname{lo}} &= (v\_0,   \ldots, v\_{k-1})\\\\
    {\mathbf{v}}\_{\operatorname{hi}} &= (v\_{k}, \ldots, v\_{2k-1})
\end{aligned}
\\]
Pedersen commitments are written as
\\[
\begin{aligned}
    \operatorname{Com}(v) &= \operatorname{Com}(v, {\widetilde{v}}) = v \cdot B + {\widetilde{v}} \cdot {\widetilde{B}},
\end{aligned}
\\]
where \\(B\\) and \\({\widetilde{B}}\\) are the generators used for the values
and blinding factors, respectively. We denote the blinding factor for
the value \\(v\\) by \\({\widetilde{v}}\\), so that it is clear which blinding
factor corresponds to which value, and write \\(\operatorname{Com}(v)\\)
instead of \\(\operatorname{Com}(v, {\widetilde{v}})\\) for brevity.

We also make use of *vector Pedersen commitments*, which we define for
pairs of vectors as \\[
\begin{aligned}
    \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}) 
 &= \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}, {\widetilde{a}})
  = {\langle {\mathbf{a}}\_{L}, {\mathbf{G}} \rangle} + {\langle {\mathbf{a}}\_{R}, {\mathbf{H}} \rangle} + {\widetilde{a}} {\widetilde{B}},\end{aligned}
\\]
where \\({\mathbf{G}}\\) and \\({\mathbf{H}}\\) are vectors of generators.
Notice that this is exactly the same as taking a commitment to the
vector of values \\({\mathbf{a}}\_{L} \Vert {\mathbf{a}}\_{R}\\) with the
vector of bases \\({\mathbf{G}} \Vert {\mathbf{H}}\\), but defining the
commitment on pairs of vectors is a more convenient notation.

Decoder Ring
------------

Mapping from paper notation to this notation:
\\[
\begin{aligned}
    g^a             &\xrightarrow{} a \cdot G\\\\
    g \cdot h       &\xrightarrow{} G + H\\\\
    g^a \cdot h^y   &\xrightarrow{} a \cdot G + y \cdot H\\\\
    {\mathbf{g}}^{{\mathbf{a}}}  &\xrightarrow{} {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} = {\textstyle\sum a\_i \cdot G\_i}\end{aligned}
\\]
Variables:
\\[
\begin{aligned}
    g        &\xrightarrow{} B               & \gamma   &\xrightarrow{} \tilde{v}      \\\\
    h        &\xrightarrow{} \tilde{B}       & \alpha   &\xrightarrow{} \tilde{a}      \\\\
    {\mathbf{g}}   &\xrightarrow{} {\mathbf{G}}          & \rho     &\xrightarrow{} \tilde{s}      \\\\
    {\mathbf{h}}   &\xrightarrow{} {\mathbf{H}}          & \tau\_i   &\xrightarrow{} \tilde{t}\_i    \\\\
             &                               & \mu      &\xrightarrow{} \tilde{e}      \\\\
\end{aligned}
\\]

Range Proofs from Inner Products
================================

The goal of a *range proof* is for a *prover* to convince a *verifier*
that a particular value \\(v\\) lies within a valid range, without revealing
any additional information about the value \\(v\\).

The prover begins with a secret value \\(v\\) and commitment
\\(V = \operatorname{Com}(v)\\), which it sends to the verifier. The prover
wishes to convince the verifier that
\\[
\begin{aligned}
  v &\in [0, 2^{n}) 
\end{aligned}
\\]
without revealing \\(v\\).

Since the prover will eventually use an inner product proof to do this,
we want to work towards expressing this condition
in terms of a single inner product. In this section, we construct
successive statements which imply \\(v \in [0,2^{n})\\)
until we arrive at the ones the prover will use to convince
the verifier.

Proving range statements with bit vectors
-----------------------------------------

Write the bits of \\(v\\) as \\({\mathbf{a}}\\). If \\({\mathbf{2}}^{n}\\) is the
vector \\((1,2,4,\ldots,2^{n-1})\\) of powers of \\(2\\), then
\\[
\begin{aligned}
  {\langle {\mathbf{a}}, {\mathbf{2}}^{n} \rangle} &= v,  \\\\
  {\mathbf{a}} \circ ({\mathbf{a}} - {\mathbf{1}}) &= {\mathbf{0}}^{n} .
\end{aligned}
\\]
Here \\({\mathbf{x}} \circ {\mathbf{y}}\\) denotes the entry-wise
multiplication of two vectors.
Together, these conditions imply the range condition.
We will
eventually need to make separate commitments to the vectors
\\({\mathbf{a}}\\) and \\({\mathbf{a}} - {\mathbf{1}}\\), so we set
\\({\mathbf{a}}\_{L} = {\mathbf{a}}\\),
\\({\mathbf{a}}\_{R} = {\mathbf{a}} - {\mathbf{1}}\\) to obtain
\\[
\begin{aligned}
  {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^{n} \rangle} &= v, \\\\
  {\mathbf{a}}\_{L} \circ {\mathbf{a}}\_{R} &= {\mathbf{0}}, \\\\
  ({\mathbf{a}}\_{L} - {\mathbf{1}}) - {\mathbf{a}}\_{R} &= {\mathbf{0}}.
\end{aligned}
\\]

Proving vectors of statements with a single statement
-----------------------------------------------------

The statements above are statements about vectors, or equivalently, a
vector of statements about each entry. Now, we want to combine these
into a single statement. Since \\({\mathbf{b}} = {\mathbf{0}}\\) if and only
if \\({\langle {\mathbf{b}}, {\mathbf{y}}^{n} \rangle} = 0\\) for every \\(y\\),
the statements above are implied by
\\[
\begin{aligned}
  {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^{n} \rangle} &= v, \\\\
  {\langle {\mathbf{a}}\_{L} - {\mathbf{1}} - {\mathbf{a}}\_{R}, {\mathbf{y}}^{n} \rangle} &= 0, \\\\
  {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle} &= 0
\end{aligned}
\\]
for the verifier’s choice of a challenge value \\(y\\). These statements can
then be combined in the same way, using the verifier’s choice of \\(z\\):
\\[
\begin{aligned}
z^{2} v 
&= 
   z^{2} {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^{n} \rangle} 
     + z {\langle {\mathbf{a}}\_{L} - {\mathbf{1}} - {\mathbf{a}}\_{R}, {\mathbf{y}}^{n} \rangle} 
         +   {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle} 
\end{aligned}
\\]

Combining inner-products
------------------------

Finally, we want to combine these terms into a single inner product. Our
goal is to rearrange the inner product above so that terms
involving \\({\mathbf{a}}\_{L}\\) appear only on the left-hand side, terms
involving \\({\mathbf{a}}\_{R}\\) appear only on the right-hand side, and
non-secret terms (which the verifier can compute on its own) are
factored out into a new term \\(\delta\\).

First, break the statement into simpler terms, then rearrange:
\\[
\begin{aligned}
z^2 v
&= 
z^2 {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^n \rangle}
\+ z {\langle {\mathbf{a}}\_{L}, {\mathbf{y}}^n \rangle}
\- z {\langle {\mathbf{a}}\_{R}, {\mathbf{y}}^n \rangle}
\- z {\langle {\mathbf{1}}, {\mathbf{y}}^n \rangle}
\+ {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\\\\
z^{2} v 
\+ z {\langle {\mathbf{1}}, {\mathbf{y}}^{n} \rangle}
&= 
z^2 {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^n \rangle}
\+ z {\langle {\mathbf{a}}\_{L}, {\mathbf{y}}^n \rangle}
\- z {\langle {\mathbf{1}} , {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\+ {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\\\\
z^{2} v 
\+ z {\langle {\mathbf{1}}, {\mathbf{y}}^{n} \rangle}
&= 
{\langle {\mathbf{a}}\_{L}, z^{2} {\mathbf{2}}^n \rangle}
\+ {\langle {\mathbf{a}}\_{L}, z {\mathbf{y}}^n \rangle}
\+ {\langle -z {\mathbf{1}} , {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\+ {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\\\\
z^{2} v 
\+ z {\langle {\mathbf{1}}, {\mathbf{y}}^{n} \rangle}
&= 
{\langle {\mathbf{a}}\_{L}, z^{2} {\mathbf{2}}^n + z {\mathbf{y}}^{n} + {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle}
\+ {\langle -z {\mathbf{1}} , {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n \rangle}
\end{aligned}
\\]
To combine the terms on the right-hand side, add
\\({\langle -z {\mathbf{1}}, z^2 {\mathbf{2}}^n + z {\mathbf{y}}^n \rangle}\\)
to each side, then simplify:
\\[
\begin{aligned}
z^{2} v 
\+ z {\langle {\mathbf{1}}, {\mathbf{y}}^{n} \rangle}
\- {\langle z {\mathbf{1}}, z^2 {\mathbf{2}}^n + z {\mathbf{y}}^n \rangle}
&= 
{\langle {\mathbf{a}}\_{L}, z^{2} {\mathbf{2}}^n + z {\mathbf{y}}^{n} + {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle} 
\\\\
&+ {\langle -z {\mathbf{1}} , z^2 {\mathbf{2}}^n + z {\mathbf{y}}^n + {\mathbf{a}}\_{R} \circ {\mathbf{y}}^n  \rangle}
\\\\
z^2 v 
\+ (z - z^2) {\langle {\mathbf{1}}, {\mathbf{y}}^n \rangle} 
\- z^3 {\langle {\mathbf{1}}, {\mathbf{2}}^n \rangle}
&= 
{\langle {\mathbf{a}}\_{L} - z{\mathbf{1}}, z^{2} {\mathbf{2}}^n + z {\mathbf{y}}^{n} + {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle}
\end{aligned}
\\]
Writing
\\[
 \delta(y,z) = (z - z^{2}) {\langle {\mathbf{1}}, {\mathbf{y}}^{n} \rangle} - z^{3} {\langle {\mathbf{1}}, {\mathbf{2}}^{n} \rangle},
\\]
we finally obtain
\\[
 z^{2}v + \delta(y,z) = {\langle {\mathbf{a}}\_{L} - z {\mathbf{1}}, {\mathbf{y}}^{n} \circ ({\mathbf{a}}\_{R} + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} \rangle}. 
\\]
This is equivalent to the original inner-product equation, but has a single
inner product with \\({\mathbf{a}}\_{L}\\) on the left, \\({\mathbf{a}}\_{R}\\) on
the right, and non-secret terms factored out.

Blinding the inner product
--------------------------

The prover cannot send the left and right vectors in
the single inner-product equation to the verifier without revealing information
about the value \\(v\\), and since the inner-product argument is not
zero-knowledge, they cannot be used there either.

Instead, the prover chooses vectors of blinding factors
\\[
{\mathbf{s}}\_{L}, {\mathbf{s}}\_{R} \\;{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n},
\\]
and uses them to construct vector polynomials
\\[
\begin{aligned}
  {\mathbf{l}}(x) &= {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1} x = ({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x) - z {\mathbf{1}} & \in {\mathbb Z\_p}[x]^{n}  \\\\
  {\mathbf{r}}(x) &= {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} x = {\mathbf{y}}^{n} \circ \left( ({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\right)  + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} &\in {\mathbb Z\_p}[x]^{n} 
\end{aligned}
\\]
These are the left and right sides of the inner product
(\[eqn:single\\_inner\]), with \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\)
replaced by blinded terms \\({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x\\),
\\({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\\). Notice that since only the
blinding factors \\({\mathbf{s}}\_{L}\\), \\({\mathbf{s}}\_{R}\\) are multiplied
by \\(x\\), the vectors \\({\mathbf{l}}\_{0}\\) and \\({\mathbf{r}}\_{0}\\) are
exactly the left and right sides of the unblinded single inner-product.

Setting
\\[
  t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} = t\_{0} + t\_{1} x + t\_{2} x^{2}, 
\\]
we can express the coefficients of \\(t(x)\\) using Karatsuba’s method:
\\[
\begin{aligned}
  t\_{0} &= {\langle {\mathbf{l}}\_{0}, {\mathbf{r}}\_{0} \rangle},  \\\\
  t\_{2} &= {\langle {\mathbf{l}}\_{1}, {\mathbf{r}}\_{1} \rangle},  \\\\
  t\_{1} &= {\langle {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1}, {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} \rangle} - t\_{0} - t\_{2} 
\end{aligned}
\\]
Since \\[
\begin{aligned}
  t\_{0} &= {\langle {\mathbf{a}}\_{L} - z {\mathbf{1}}, {\mathbf{y}}^{n} \circ ({\mathbf{a}}\_{R} + z {\mathbf{1}}) + z^{2} 2^{n} \rangle},\end{aligned}
\\]
for the prover to convince the verifier that the unblinded single inner-product equation
holds, it’s enough to prove that the constant term \\(t\_{0}\\) of \\(t(x)\\) is
\\(z^{2} v + \delta(y,z)\\), and that
this \\(t(x)\\) is the correct polynomial.
Proving that \\(t(x)\\) is correct means proving that
\\({\mathbf{l}}(x)\\), \\({\mathbf{r}}(x)\\) are correctly formed, and that
\\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\).

Proving that \\(t\_{0}\\) is correct
------------------------------------

In order to prove that the constant term of \\(t(x)\\) is
\\(z^{2} v + \delta(y,z)\\), the prover first forms a commitment to the
coefficients of \\(t(x)\\), then convinces the verifier that these commit to
the correct \\(t(x)\\) by evaluating the polynomial at a challenge point
\\(x\\).

The prover has already used \\(V = \operatorname{Com}(v)\\) to commit to \\(v\\)
(and hence to \\(t\_{0}\\)), so the prover forms commitments
\\(T\_{1} = \operatorname{Com}(t\_{1})\\) and
\\(T\_{2} = \operatorname{Com}(t\_{2})\\), then sends these to the verifier.
The commitments \\(V\\), \\(T\_{1}\\), \\(T\_{2}\\) are related to each other and to
\\(t(x)\\) by the following diagram:
\\[
\begin{aligned}
  t(x) B                     &\quad &= \quad & z^{2}vB                     & \quad &+ \quad & \delta(y,z) B  & \quad &+ \quad& x t\_{1} B                     &\quad &+\quad & x^2 t\_{2} B \\\\
    +                        &\quad &  \quad &  +                          & \quad &  \quad &  +             & \quad &  \quad& +                             &\quad & \quad & +   \\\\
  {\widetilde{t}}(x) {\widetilde{B}} &\quad &= \quad & z^2 {\widetilde{v}} {\widetilde{B}} & \quad &+ \quad & 0 {\widetilde{B}}  & \quad &+ \quad& x {\widetilde{t}}\_{1} {\widetilde{B}} &\quad &+\quad & x^{2} {\widetilde{t}}\_{2} {\widetilde{B}} \\\\
    \shortparallel           &\quad &  \quad & \shortparallel              & \quad &  \quad & \shortparallel & \quad &  \quad& \shortparallel                &\quad & \quad & \shortparallel   \\\\
                 &\quad &= \quad & z V                         & \quad &+ \quad & \delta(y,z) B  & \quad &+ \quad& x T\_{1}                       &\quad &+\quad & x^{2} T\_{2}
\end{aligned}
\\]
Notice that the sum of each column is a commitment to the variable in the top
row using the blinding factor in the second row.
The sum of all of the columns is
\\(t(x) B + {\widetilde{t}}(x) {\widetilde{B}}\\), a commitment to the value
of \\(t\\) at the point \\(x\\), using the synthetic blinding factor[^1]
\\[
  {\widetilde{t}}(x) = z^{2} {\widetilde{v}} + x {\widetilde{t}}\_{1} + x^{2} {\widetilde{t}}\_{2}.
\\]
To convince the verifier that
\\(t(x) = z^2v + \delta(y,z) + t\_{1} x + t\_{2} x^{2}\\), the prover sends
the opening \\(t(x), {\widetilde{t}}(x)\\) to the verifier, who uses the
bottom row of the diagram to check consistency:
\\[
  t(x) B + {\widetilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} z V + \delta(y,z) B + x T\_{1} + x^{2} T\_{2}. 
\\]

[^1]: The blinding factor is synthetic in the sense that it is
    synthesized from the blinding factors of the other commitments.

Proving that \\({\mathbf{l}}(x)\\), \\({\mathbf{r}}(x)\\) are correct
---------------------------------------------------------------------

We want to relate \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) to commitments
to \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\), \\({\mathbf{s}}\_{L}\\), and
\\({\mathbf{s}}\_{R}\\). However, since \\[
\begin{aligned}
  {\mathbf{r}}(x) &= {\mathbf{y}}^{n} \circ \left( ({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\right)  + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n},\end{aligned}
\\]
we need commitments to \\({\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}\\) and
\\({\mathbf{y}}^{n} \circ {\mathbf{s}}\_{R}\\). However, since the prover
must form commitments before receiving the verifier’s challenge \\(y\\), the
prover can only commit to \\(a\_{R}\\) and \\(s\_{R}\\). Since the prover’s
commitments are to \\(a\_{R}\\) and \\(s\_{R}\\), the verifier needs to transmute
the prover’s commitment
\\(
\operatorname{Com}({\mathbf{a}}\_{L},{\mathbf{a}}\_{R}, {\widetilde{a}})
\\)
into a commitment
\\(
\operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}, {\widetilde{a}})
\\)
(and similarly for \\({\mathbf{s}}\_{R}\\)).
To do this, notice that
\\[
\begin{aligned}
  \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}, {\widetilde{a}})
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

To relate the prover’s commitments
\\(A = \operatorname{Com}({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R})\\) and
\\(S = \operatorname{Com}({\mathbf{s}}\_{L}, {\mathbf{s}}\_{R})\\) to
\\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\), we use the following diagram:
\\[
\begin{aligned}
  {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle}    &\quad &= \quad & {\langle {\mathbf{a}}\_L, {\mathbf{G}} \rangle}   & \quad &+ \quad & x {\langle {\mathbf{s}}\_L, {\mathbf{G}} \rangle} &\quad &+\quad & {\langle -z{\mathbf{1}}, {\mathbf{G}} \rangle} \\\\
    +                        &\quad &  \quad &  +                      & \quad &  \quad & +                       &\quad & \quad & +   \\\\
  {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}   &\quad &= \quad & {\langle {\mathbf{a}}\_R, {\mathbf{H}} \rangle}   & \quad &+ \quad & x {\langle {\mathbf{s}}\_R, {\mathbf{H}} \rangle} &\quad &+\quad & {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{H}}' \rangle} \\\\
    +                        &\quad &  \quad &  +                      & \quad &  \quad & +                       &\quad & \quad &     \\\\
  {\widetilde{e}} {\widetilde{B}}    &\quad &= \quad & {\widetilde{a}} {\widetilde{B}} & \quad &+ \quad & x {\widetilde{s}} {\widetilde{B}} &\quad & \quad &               \\\\
    \shortparallel           &\quad &  \quad & \shortparallel          & \quad &  \quad & \shortparallel          &\quad & \quad & \shortparallel   \\\\
                             &\quad &= \quad & A                       & \quad &+ \quad & x S                     &\quad &+\quad & {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{H}}' \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle}
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
  P = -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{H}}' \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle}; 
\\]
if the prover is honest, this is
\\(P = {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}\\),
so the verifier uses \\(P\\), \\(t(x)\\) as inputs to the inner-product protocol
to prove that
\\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\).

Inner-Product Proof
===================

First, let’s observe that the prover can simply send vectors
\\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) and the verifier can check
directly that the inner product \\(t(x)\\) and commitment \\(P\\) provided in
the protocols 1 and 2 are correct. This will not leak information (the
secret bits in these vectors are blinded), but will require us to
transfer \\(2n\\) scalars between a prover and a verifier.

To minimize the bandwidth cost we will use the inner-product argument
protocol which enables us to prove *indirectly* and with \\(O(log(n))\\)
communication cost, that a given inner product \\(t(x)\\) and a commitment
\\(P\\) are related as:
\\[
\begin{aligned}
t(x) &= {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} \\\\
P    &= {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}
\end{aligned}
\\]
To make the presentation
cleaner, we will change the notation to one used specifically in the
inner product argument which is not to be confused with the notation in
the rangeproof protocol:
\\[
\begin{split}
{\mathbf{a}}, {\mathbf{b}}  &\in {\mathbb Z\_{p}^{n}}\\\\
{\mathbf{G}}, {\mathbf{H}}  &\in {\mathbb G^{n}}\\\\
c  &= {\langle {\mathbf{a}}, {\mathbf{b}} \rangle}\\\\
P  &= {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle}
\end{split}
\\]
Within the above definitions we need a proof of knowledge
for the following relation:
\\[
\begin{aligned}
    P &{}={}&& {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} \hspace{0.2cm} \wedge\\\\
    c &{}={}&& {\langle {\mathbf{a}}, {\mathbf{b}} \rangle}
\end{aligned}
\\]
let’s compress these two statements into one equation using an
indeterminate variable \\(w \in {\mathbb Z\_{p}^{\times}}\\) and multiplying the
second equation by an additional orthogonal generator
\\(Q \in {\mathbb G}\\):
\\[
\begin{aligned}
    P &{}={}&& {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle}\\\\
      &{}+{}&&\\\\
    c \cdot w \cdot Q &{}={}&&  {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} \cdot w \cdot Q
\end{aligned}
\\]
let’s simplify the resulting equation using the following definitions:
\\[
\begin{aligned}
    k &= \lg n \\\\
    P\_k &= P + c \cdot w \cdot Q \\\\
    \hat{Q} &= w \cdot Q
\end{aligned}
\\]
The equation becomes:
\\[
    P\_k = {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} + {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} \cdot \hat{Q} 
\\]
If the prover can demonstrate that the above \\(P\_k\\) has such structure
over generators \\({\mathbf{G}}\\), \\({\mathbf{H}}\\) and \\(\hat Q\\) for all
\\(w \in {\mathbb Z\_{p}^{*}}\\), then the original \\(P\\) and \\(c\\) must satisfy
the original relation (\[eqn:ip\\_cp\\_def\]).

The equation (\[eqn:ip\\_inner\\_eq\]) is useful because it will allow us
to compress each vector in half and arrive to the same form. By doing
such compression \\(\lg n\\) times we will end up with an equation where
both vectors are one-element long and we can simply transmit them to
check the final equality directly.

let’s introduce an indeterminate variable \\(u\_k \in {\mathbb Z\_{p}^{\times}}\\)
and compress the vectors by adding the left and the right halves
separated by the variable \\(u\_k\\):
\\[
\begin{aligned}
  {\mathbf{a}}^{(k-1)} &= {\mathbf{a}}\_L \cdot u\_k        + u^{-1}\_k \cdot {\mathbf{a}}\_R \\\\
  {\mathbf{b}}^{(k-1)} &= {\mathbf{b}}\_L \cdot u^{-1}\_k   + u\_k \cdot {\mathbf{b}}\_R \\\\
  {\mathbf{G}}^{(k-1)} &= {\mathbf{G}}\_L \cdot u^{-1}\_k   + u\_k \cdot {\mathbf{G}}\_R \\\\
  {\mathbf{H}}^{(k-1)} &= {\mathbf{H}}\_L \cdot u\_k        + u^{-1}\_k \cdot {\mathbf{H}}\_R 
\end{aligned}
\\]
The powers of \\(u\_k\\) are chosen so they cancel out in the
inner products of interest as will be shown below.

let’s now form the equation (\[eqn:ip\\_inner\\_eq\]) with these
compressed vectors:
\\[
    P\_{k-1} = {\langle {\mathbf{a}}^{(k-1)}, {\mathbf{G}}^{(k-1)} \rangle} + {\langle {\mathbf{b}}^{(k-1)}, {\mathbf{H}}^{(k-1)} \rangle} + {\langle {\mathbf{a}}^{(k-1)}, {\mathbf{b}}^{(k-1)} \rangle} \cdot \hat{Q} 
\\]
Expanding it in terms of the original \\({\mathbf{a}}\\), \\({\mathbf{b}}\\),
\\({\mathbf{G}}\\) and \\({\mathbf{H}}\\) gives:
\\[
\begin{aligned}
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_L \cdot u\_k   + u\_k^{-1} \cdot {\mathbf{a}}\_R, {\mathbf{G}}\_L \cdot u^{-1}\_k + u\_k \cdot {\mathbf{G}}\_R      \rangle} + \\\\
             &&  &{\langle {\mathbf{b}}\_L \cdot u^{-1}\_k  + u\_k \cdot {\mathbf{b}}\_R,      {\mathbf{H}}\_L \cdot u\_k      + u^{-1}\_k \cdot {\mathbf{H}}\_R \rangle} + \\\\
             &&  &{\langle {\mathbf{a}}\_L \cdot u\_k       + u^{-1}\_k \cdot {\mathbf{a}}\_R,      {\mathbf{b}}\_L \cdot u^{-1}\_k + u\_k \cdot {\mathbf{b}}\_R      \rangle} \cdot \hat{Q}
\end{aligned}
\\]
Breaking down in simpler products:
\\[
\begin{aligned}
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_L, {\mathbf{G}}\_L \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_R \rangle} &{}+{}& u\_k^2 {\langle {\mathbf{a}}\_L, {\mathbf{G}}\_R \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_L \rangle} + \\\\
       &&      &{\langle {\mathbf{b}}\_L, {\mathbf{H}}\_L \rangle} + {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_R \rangle} &{}+{}& u^2\_k {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_L \rangle} + u^{-2}\_k {\langle {\mathbf{b}}\_L, {\mathbf{H}}\_R \rangle} + \\\\
       &&      &({\langle {\mathbf{a}}\_L, {\mathbf{b}}\_L \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_R \rangle})\cdot \hat{Q} &{}+{}& (u^2\_k {\langle {\mathbf{a}}\_L, {\mathbf{b}}\_R \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_L \rangle}) \cdot \hat{Q}
\end{aligned}
\\]
We now see that the left two columns in the above equation is the
definition of \\(P\_k\\), while various cross terms on the right are
separated from \\(P\_k\\) by an indeterminate variable \\(u\_k\\). let’s group all
terms with \\(u^2\_k\\) as \\(L\_k\\) and all terms with \\(u^{-2}\_k\\) as \\(R\_k\\):
\\[
\begin{aligned}
    P\_{k-1} &= P\_k + u^2\_k \cdot L\_k + u^{-2}\_k \cdot R\_k\\\\
    L\_k  &= {\langle {\mathbf{a}}\_L, {\mathbf{G}}\_R \rangle} + {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_L \rangle} + {\langle {\mathbf{a}}\_L, {\mathbf{b}}\_R \rangle} \cdot \hat{Q}\\\\
    R\_k  &= {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_L \rangle} + {\langle {\mathbf{b}}\_L, {\mathbf{H}}\_R \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_L \rangle} \cdot \hat{Q}
\end{aligned}
\\]
If the prover commits to \\(L\_k\\) and \\(R\_k\\) before \\(u\_k\\) is randomly
sampled, then if the (\[eqn:ip\\_inner\\_eq\\_compressed\]) is proven to be
true, it will follow that (\[eqn:ip\\_inner\\_eq\]) is also true with an
overwhelming probability.

We can compress the resulting statement
(\[eqn:ip\\_inner\\_eq\\_compressed\]) using one more indeterminate
variable \\(u\_{k-1}\\) as specified in (\[eqn:ip\\_compression\]) and arrive
to even shorter vectors. We will continue doing so until we end up with
vectors
\\({\mathbf{a}}^{(0)}, {\mathbf{b}}^{(0)}, {\mathbf{G}}^{(0)}, {\mathbf{H}}^{(0)}\\),
each containing one item:
\\[
    P\_0 = a^{(0)}\_0 \cdot G^{(0)}\_0 + b^{(0)}\_0 \cdot H^{(0)}\_0 + a^{(0)}\_0 \cdot b^{(0)}\_0 \cdot \hat{Q} 
\\]
At this point the prover can transmit two scalars \\(a^{(0)}\_0\\) and
\\(b^{(0)}\_0\\) to the verifier, so they check
(\[eqn:ip\\_inner\\_eq\\_final\]) directly by computing both sides of the
equation.

The resulting protocol has \\(\lg n\\) steps of compression where the prover
sends a pair \\((L\_j,R\_j)\\) of points at each step \\(j = k\dots1\\). An
additional and final step involves sending a pair of scalars
\\((a^{(0)}\_0,b^{(0)}\_0)\\) and checking the relation
(\[eqn:ip\\_inner\\_eq\\_final\]).