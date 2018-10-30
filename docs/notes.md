This module contains notes on how and why Bulletproofs work.

* [Notation](#notation)
* [Range proof from inner product](#range-proof-from-inner-product)
* [Inner product proof](#inner-product-proof)
* [Constraint system](#constraint-system)
* [Constraint system proof](#constraint-system-proof)
* [Aggregated range proof](#aggregated-range-proof)
* [Aggregated constraint system proof](#aggregated-constraint-system-proof)

For the detailed description of the actual protocols, see the internal documentation in the following modules:

* [`range_proof`](../range_proof/index.html): aggregated range proof protocol.
* [`range_proof_mpc`](../range_proof_mpc/index.html): multi-party API for range proof aggregation.
* [`inner_product_proof`](../inner_product_proof/index.html): inner product argument protocol.
* [`circuit_proof`](../circuit_proof/index.html): constraint system proof protocol.

The types from the above modules are publicly re-exported from the crate root,
so that the external documentation describes how to use the API, while the internal
documentation describes how it works.


Notation
========

We change notation from the original [Bulletproofs paper][bulletproofs_paper].
The primary motivation is that our implementation uses additive notation, and
we would like our description of the protocol to use the same notation as the
implementation.


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

The variable renaming is as follows:
\\[
\begin{aligned}
          g        &\xrightarrow{} B                     & \gamma   &\xrightarrow{} \tilde{v}    \\\\
          h        &\xrightarrow{} \widetilde{B}         & \alpha   &\xrightarrow{} \tilde{a}    \\\\
    {\mathbf{g}}   &\xrightarrow{} {\mathbf{G}}          & \rho     &\xrightarrow{} \tilde{s}    \\\\
    {\mathbf{h}}   &\xrightarrow{} {\mathbf{H}}          & \tau\_i  &\xrightarrow{} \tilde{t}\_i \\\\
                   &                                     & \mu      &\xrightarrow{} \tilde{e}    \\\\
\end{aligned}
\\]


[bulletproofs_paper]: https://eprint.iacr.org/2017/1066.pdf
[bp_website]: https://crypto.stanford.edu/bulletproofs/









Range proof from inner product
==============================

The goal of a *range proof* is for a prover to convince a verifier
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

Let \\({\mathbf{a}}\\) be the vector of bits of \\(v\\).
Then \\(v\\) can be represented as an inner product of bits \\({\mathbf{a}}\\)
and powers of two \\({\mathbf{2}}^{n} = (1,2,4,\ldots,2^{n-1})\\):
\\[
\begin{aligned}
  v &= {\langle {\mathbf{a}}, {\mathbf{2}}^{n} \rangle}  \\\\
    &= a_{0}\cdot 2^0 + \dots + a_{n-1}\cdot 2^{n-1}.
\end{aligned}
\\]
We need \\({\mathbf{a}}\\) to be a vector of integers \\(\\{0,1\\}\\).
This can be expressed with an additional condition
\\[
{\mathbf{a}} \circ ({\mathbf{a}} - {\mathbf{1}}) = {\mathbf{0}},
\\]
where \\({\mathbf{x}} \circ {\mathbf{y}}\\) denotes the entry-wise multiplication of two vectors.
The result of multiplication can be all-zero if and only if every bit is actually \\(0\\) or[^1] \\(1\\).

As a result of representing value in binary, the range condition \\(v \in [0, 2^{n})\\)
is equivalent to the pair of conditions
\\[
\begin{aligned}
  {\langle {\mathbf{a}}, {\mathbf{2}}^{n} \rangle} &= v,  \\\\
  {\mathbf{a}} \circ ({\mathbf{a}} - {\mathbf{1}}) &= {\mathbf{0}}.
\end{aligned}
\\]
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

[^1]: Generally, condition \\(x=0 \vee y=0\\) can be expressed as \\(x \cdot y = 0\\),
as the product can be zero if and only if at least one of the terms is zero.
This trick allows implementing logical `OR` with any number of terms.


Proving vectors of statements with a single statement
-----------------------------------------------------

The statements above are statements about vectors, or equivalently, a
vector of statements about each entry. We want to combine all of these
into a single statement.

First, we will combine each of the two vector-statements into a single statement.
Since \\({\mathbf{b}} = {\mathbf{0}}\\) if and only
if[^2] \\({\langle {\mathbf{b}}, {\mathbf{y}}^{n} \rangle} = 0\\) for every \\(y\\),
the statements above are implied by
\\[
\begin{aligned}
  {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^{n} \rangle} &= v, \\\\
  {\langle {\mathbf{a}}\_{L} - {\mathbf{1}} - {\mathbf{a}}\_{R}, {\mathbf{y}}^{n} \rangle} &= 0, \\\\
  {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle} &= 0
\end{aligned}
\\]
for the verifier’s choice of a challenge value \\(y\\).

The three resulting statements can then be combined in the same way,
using the verifier’s choice of \\(z\\):
\\[
\begin{aligned}
z^{2} v 
&= 
   z^{2} {\langle {\mathbf{a}}\_{L}, {\mathbf{2}}^{n} \rangle} 
     + z {\langle {\mathbf{a}}\_{L} - {\mathbf{1}} - {\mathbf{a}}\_{R}, {\mathbf{y}}^{n} \rangle} 
         +   {\langle {\mathbf{a}}\_{L}, {\mathbf{a}}\_{R} \circ {\mathbf{y}}^{n} \rangle} 
\end{aligned}
\\]

[^2]: This is because the polynomial in terms of \\(y\\) is zero at every point
if and only if every term of it is zero. The verifier is going to sample
a random \\(y\\) after the prover commits to all the values forming the terms of
that polynomial, making the probability that the prover cheated negligible.
This trick allows implementing logical `AND` with any number of terms.


Combining inner products
------------------------

Finally, we want to combine these terms into a single inner product. Our
goal is to rearrange the inner product above so that terms
involving \\({\mathbf{a}}\_{L}\\) appear only on the left-hand side, terms
involving \\({\mathbf{a}}\_{R}\\) appear only on the right-hand side, and
non-secret terms (which the verifier can compute on its own) are
factored out into a new term \\(\delta(y, z) \\).

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
Combining all non-secret terms outside the inner product
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
  {\mathbf{l}}(x) &= {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1} x = ({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x) - z {\mathbf{1}} & \in {\mathbb Z\_p}\[x\]^{n}  \\\\
  {\mathbf{r}}(x) &= {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} x = {\mathbf{y}}^{n} \circ \left( ({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\right)  + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} &\in {\mathbb Z\_p}\[x\]^{n} 
\end{aligned}
\\]
These are the left and right sides of the combined inner product with \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\)
replaced by blinded terms \\({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x\\),
\\({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\\). Notice that since only the
blinding factors \\({\mathbf{s}}\_{L}\\), \\({\mathbf{s}}\_{R}\\) are multiplied
by \\(x\\), the vectors \\({\mathbf{l}}\_{0}\\) and \\({\mathbf{r}}\_{0}\\) are
exactly the left and right sides of the unblinded single inner-product:
\\[
 {\langle {\mathbf{l}}\_{0}, {\mathbf{r}}\_{0} \rangle} = z^{2}v + \delta(y,z)
\\]

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
  {\tilde{t}}(x) {\widetilde{B}} &\quad &= \quad & z^2 {\widetilde{v}} {\widetilde{B}} & \quad &+ \quad & 0 {\widetilde{B}}  & \quad &+ \quad& x {\tilde{t}}\_{1} {\widetilde{B}} &\quad &+\quad & x^{2} {\tilde{t}}\_{2} {\widetilde{B}} \\\\
    \shortparallel           &\quad &  \quad & \shortparallel              & \quad &  \quad & \shortparallel & \quad &  \quad& \shortparallel                &\quad & \quad & \shortparallel   \\\\
                 &\quad &= \quad & z^2 V                         & \quad &+ \quad & \delta(y,z) B  & \quad &+ \quad& x T\_{1}                       &\quad &+\quad & x^{2} T\_{2}
\end{aligned}
\\]
Notice that the sum of each column is a commitment to the variable in the top
row using the blinding factor in the second row.
The sum of all of the columns is
\\(t(x) B + {\tilde{t}}(x) {\widetilde{B}}\\), a commitment to the value
of \\(t\\) at the point \\(x\\), using the synthetic blinding factor[^3]
\\[
  {\tilde{t}}(x) = z^{2} {\tilde{v}} + x {\tilde{t}}\_{1} + x^{2} {\tilde{t}}\_{2}.
\\]
To convince the verifier that
\\(t(x) = z^2v + \delta(y,z) + t\_{1} x + t\_{2} x^{2}\\), the prover sends
the opening \\(t(x), {\tilde{t}}(x)\\) to the verifier, who uses the
bottom row of the diagram to check consistency:
\\[
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} z^2 V + \delta(y,z) B + x T\_{1} + x^{2} T\_{2}.
\\]

[^3]: The blinding factor is synthetic in the sense that it is
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
\begin{aligned}
  P &= -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{y}}^n + z^2 {\mathbf{2}}^n, {\mathbf{H}}' \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle}\\\\
    &= -{\widetilde{e}} {\widetilde{B}} + A + x S + {\langle z {\mathbf{1}} + z^2 {\mathbf{y}^{-n}} \circ {\mathbf{2}}^n, {\mathbf{H}} \rangle} - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle};
\end{aligned}
\\]
if the prover is honest, this is
\\(P = {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), {\mathbf{H}}' \rangle}\\),
so the verifier uses \\(P\\), \\(t(x)\\) as inputs to the inner-product protocol
to prove that
\\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\).

























Inner product proof
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
\begin{aligned}
{\mathbf{a}}, {\mathbf{b}}  &\in {\mathbb Z\_{p}^{n}}\\\\
{\mathbf{G}}, {\mathbf{H}}  &\in {\mathbb G^{n}}\\\\
c  &= {\langle {\mathbf{a}}, {\mathbf{b}} \rangle}\\\\
P  &= {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle}
\end{aligned}
\\]
Within the above definitions we need a proof of knowledge
for the following relation:
\\[
\begin{aligned}
    P &{}={}&& {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} \hspace{0.2cm} \wedge\\\\
    c &{}={}&& {\langle {\mathbf{a}}, {\mathbf{b}} \rangle}
\end{aligned}
\\]
Let’s combine these two statements into one equation using an
indeterminate variable \\(w \in {\mathbb Z\_{p}^{\times}}\\) and multiplying the
second equation by an orthogonal generator
\\(B \in {\mathbb G}\\):
\\[
\begin{aligned}
    P &{}={}&& {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle}\\\\
      &{}+{}&&\\\\
    c w B &{}={}&&  {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} w B
\end{aligned}
\\]
Let’s simplify the resulting equation using the following definitions:
\\[
\begin{aligned}
    k &= \lg n \\\\
    P' &= P + cwB \\\\
    Q &= wB
\end{aligned}
\\]
The equation becomes:
\\[
    P' = {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle} + {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} Q 
\\]
The combined equation is useful because it will allow us
to compress each vector in half and arrive to the same form. By doing
such compression \\(\lg n\\) times we will end up with an equation where
both vectors are one-element long and we can simply transmit them to
check the final equality directly.

If the prover can demonstrate that the above \\(P'\\) has such structure
over generators \\({\mathbf{G}}\\), \\({\mathbf{H}}\\) and \\(Q\\) for all
\\(w \in {\mathbb Z\_{p}^{\*}}\\), then the original \\(P\\) and \\(c\\) must satisfy
the original relation
\\((P = {\langle {\mathbf{a}}, {\mathbf{G}} \rangle} + {\langle {\mathbf{b}}, {\mathbf{H}} \rangle}
\wedge c = {\langle {\mathbf{a}}, {\mathbf{b}} \rangle})\\).

Let’s introduce an indeterminate variable \\(u\_k \in {\mathbb Z\_{p}^{\times}}\\)
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

Let \\(P\_k = P'\\) and define \\(P\_{k-1}\\) using the same equation as for \\(P\_k\\), but using the compressed vectors:
\\[
    P\_{k-1} = {\langle {\mathbf{a}}^{(k-1)}, {\mathbf{G}}^{(k-1)} \rangle} + {\langle {\mathbf{b}}^{(k-1)}, {\mathbf{H}}^{(k-1)} \rangle} + {\langle {\mathbf{a}}^{(k-1)}, {\mathbf{b}}^{(k-1)} \rangle} \cdot Q
\\]
Expanding it in terms of the original \\({\mathbf{a}}\\), \\({\mathbf{b}}\\),
\\({\mathbf{G}}\\) and \\({\mathbf{H}}\\) gives:
\\[
\begin{aligned}
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_L \cdot u\_k   + u\_k^{-1} \cdot {\mathbf{a}}\_R, {\mathbf{G}}\_L \cdot u^{-1}\_k + u\_k \cdot {\mathbf{G}}\_R      \rangle} + \\\\
             &&  &{\langle {\mathbf{b}}\_L \cdot u^{-1}\_k  + u\_k \cdot {\mathbf{b}}\_R,      {\mathbf{H}}\_L \cdot u\_k      + u^{-1}\_k \cdot {\mathbf{H}}\_R \rangle} + \\\\
             &&  &{\langle {\mathbf{a}}\_L \cdot u\_k       + u^{-1}\_k \cdot {\mathbf{a}}\_R,      {\mathbf{b}}\_L \cdot u^{-1}\_k + u\_k \cdot {\mathbf{b}}\_R      \rangle} \cdot Q
\end{aligned}
\\]
Breaking down in simpler products:
\\[
\begin{aligned}
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_L, {\mathbf{G}}\_L \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_R \rangle} &{}+{}& u\_k^2 {\langle {\mathbf{a}}\_L, {\mathbf{G}}\_R \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_L \rangle} + \\\\
       &&      &{\langle {\mathbf{b}}\_L, {\mathbf{H}}\_L \rangle} + {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_R \rangle} &{}+{}& u^2\_k {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_L \rangle} + u^{-2}\_k {\langle {\mathbf{b}}\_L, {\mathbf{H}}\_R \rangle} + \\\\
       &&      &({\langle {\mathbf{a}}\_L, {\mathbf{b}}\_L \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_R \rangle})\cdot Q &{}+{}& (u^2\_k {\langle {\mathbf{a}}\_L, {\mathbf{b}}\_R \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_L \rangle}) \cdot Q
\end{aligned}
\\]
We now see that the left two columns in the above equation is the
definition of \\(P\_k\\), while various cross terms on the right are
separated from \\(P\_k\\) by an indeterminate variable \\(u\_k\\). Let’s group all
terms with \\(u^2\_k\\) as \\(L\_k\\) and all terms with \\(u^{-2}\_k\\) as \\(R\_k\\):
\\[
\begin{aligned}
    P\_{k-1} &= P\_k + u^2\_k \cdot L\_k + u^{-2}\_k \cdot R\_k\\\\
    L\_k  &= {\langle {\mathbf{a}}\_L, {\mathbf{G}}\_R \rangle} + {\langle {\mathbf{b}}\_R, {\mathbf{H}}\_L \rangle} + {\langle {\mathbf{a}}\_L, {\mathbf{b}}\_R \rangle} \cdot Q\\\\
    R\_k  &= {\langle {\mathbf{a}}\_R, {\mathbf{G}}\_L \rangle} + {\langle {\mathbf{b}}\_L, {\mathbf{H}}\_R \rangle} + {\langle {\mathbf{a}}\_R, {\mathbf{b}}\_L \rangle} \cdot Q
\end{aligned}
\\]
If the prover commits to \\(L\_k\\) and \\(R\_k\\) before \\(u\_k\\) is randomly
sampled, then if the statement about compressed vectors is proven to be
true, it will follow that the original statement about uncompressed vectors
is also true with an overwhelming probability.

We can compress the resulting statement about \\(P\_{k-1}\\) using one more indeterminate
variable \\(u\_{k-1}\\) in the same way as we used \\(u\_k\\) and arrive
to even shorter vectors. We will continue doing so until we end up with
vectors
\\({\mathbf{a}}^{(0)}, {\mathbf{b}}^{(0)}, {\mathbf{G}}^{(0)}, {\mathbf{H}}^{(0)}\\),
each containing one item, and \\(P\_0\\) containing all accumulated cross-terms at each step:
\\[
\begin{aligned}
    P\_0 &= a^{(0)}\_0 G^{(0)}\_0 + b^{(0)}\_0 H^{(0)}\_0 + a^{(0)}\_0 b^{(0)}\_0 Q\\\\
    P\_0 &= P\_k + \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right)
\end{aligned}
\\]

Rewriting the above with the definitions \\(P\_k = P' = P + cwB\\) and \\(Q = wB\\) gives the
final statement:
\\[
    P + c w B = a^{(0)}\_0 G^{(0)}\_0 + b^{(0)}\_0 H^{(0)}\_0 + a^{(0)}\_0 b^{(0)}\_0 wB - \sum\_{j=1}^{k} \left( L\_{j} u\_{j}^{2} + u\_{j}^{-2} R\_{j} \right)
\\]

At this point the prover can transmit two scalars \\(a^{(0)}\_0\\) and
\\(b^{(0)}\_0\\) to the verifier, so they check the final statement directly
by computing both sides of the equation.

The resulting protocol has \\(\lg n\\) steps of compression where the prover
sends a pair \\((L\_j,R\_j)\\) of points at each step \\(j = k\dots1\\). An
additional and final step involves sending a pair of scalars
\\((a^{(0)}\_0,b^{(0)}\_0)\\) and checking the final relation directly.





Constraint system
=================

A **constraint system** is a collection of arithmetic constraints over a set of variables.

The constraint system we use is specifically a **rank-1 quadratic constraint system** or **R1CS**.
Such system consists of two sets of constraints: [multiplication gates](#multiplication-gates) and [linear constraints](#linear-constraints) in terms of the [variables](#variables).

## Variables

There are two kinds of variables in the constraint system:

1. \\(m\\) **high-level** variables, the input secrets \\(\mathbf{v}\\),
2. \\(n\\) **low-level** variables, the internal inputs and outputs of the [multiplication gates](#multiplication-gates): \\(\mathbf{a}\_L, \mathbf{a}\_R, \mathbf{a}\_O\\).

## Multiplication gates

Each multiplication gate takes two input variables and multiplies them to get an output.
That relation for all multiplication gates is represented by \\(n\\) constraints:

\\[
\mathbf{a}\_L \circ \mathbf{a}\_R = \mathbf{a}\_O,
\\]
where:
* \\(\mathbf{a}\_L\\) is the vector of the first input to each gate,
* \\(\mathbf{a}\_R\\) is the vector of the second input to each gate,
* \\(\mathbf{a}\_O\\) is the vector of multiplication results.

## Linear constraints

Linear constraints are expressed using a vector of \\(q\\) equations that use linear combinations of the [variables](#variables):

\\[
\mathbf{W}\_L \cdot \mathbf{a}\_L +
\mathbf{W}\_R \cdot \mathbf{a}\_R +
\mathbf{W}\_O \cdot \mathbf{a}\_O =
\mathbf{W}\_V \cdot \mathbf{v} +
\mathbf{c},
\\]
where:

* \\(\mathbf{W}\_L, \mathbf{W}\_R, \mathbf{W}\_O\\) are weights applied to the respective inputs and outputs of the [multiplication gates](#multiplication-gates) (low-level [variables](#variables)),
* \\(\mathbf{W}\_V\\) are weights applied to the high-level [variables](#variables) \\(\mathbf{v}\\),
* \\(\mathbf{c}\\) is a vector of constant terms used in the linear constraints.


## Building constraints

Bulletproofs framework allows building constraint systems _on the fly_, without a trusted setup.
This allows instantiating constraints from a _family of constraint systems_ parametrized by
public values and commitments to the secret inputs.
As a result, the instantiation can be thought of as a _challenge_ generated by a verifier to a prover.

The prover starts out by committing to its secret inputs \\(\mathbf{v}\\)
and obtaining \\(m\\) _variables_ representing these inputs.

Then, the prover performs a combination of the following operations to generate the constraints:

1. **Allocate a multiplier:** a new [multiplication gate](#multiplication-gates) is added, represented by three [low-level variables](#variables) \\(a_L, a_R, a_O\\), for left input, right input and output value respectively.
2. **Add a constraint:** a [linear combination](#linear-constraints) of any number of [variables](#variables) is encoded into appropriate positions in matrices \\(\mathbf{W}\_L, \mathbf{W}\_R, \mathbf{W}\_O, \mathbf{W}\_V\\) and a vector of constants \\(\mathbf{c}\\).
3. **Request a challenge scalar:** a random scalar returned in response to committed [high-level variables](#variables).


## Gadgets

Gadgets are buildings blocks of a constraint system that map to some functions in a higher-level protocol.
Gadgets receive some [variables](#variables) as inputs, may [allocate more variables](#building-constraints) for internal use,
and produce constrains involving all these variables.

Examples:
* a **shuffle gadget** creates constraints that prove that two sets of variables are equal up to a permutation;
* a **range proof gadget** checks that a given value is composed of a specific number of bits.


## Low-level variables

Often a [gadget](#gadgets) needs a variable to connect with another gadget,
or to implement its internal logic, without requiring a distinct [high-level variable](#variables) commitment \\(V\_i\\) for it.
Such **low-level variables** are created from left and right variables \\(a\_L, a\_R\\) of additional multiplication gates.
Output variables \\(a\_O\\) are not used for this purpose because
they are implicitly constrained by a [multiplication gate](#multiplication-gates)
and cannot be used as independent uncommitted variables.

## Gadget as a challenge

Intermediate challenge scalars can be used to construct [gadgets](#gadgets) more efficiently.

For example, a shuffle gadgets (“proof of permutation”) can be done by proving equality of
two polynomials sampled at a challenge point, where roots of each polynomial
represent secret values of the corresponding side of a permutation:

\\[
 \\{a,b\\} = \\{c,d\\}  \iff  (a-x)\cdot(b-x) = (c-x)\cdot(d-x),
\\] where \\(x\\) is a random challenge, sampled after all values \\(a,b,c,d\\) are committed.

Making a proof of permutation using a static gadget (without challenge values) may require
building a [sorting network][sorting_network] that would use significantly more multiplication gates.

**Important:** challenges are bound to the [high-level variables](#variables) and the
committed portion of [low-level variables](#low-level-variables).
The remaining [low-level variables](#low-level-variables) are uncommitted and must be uniquely determined
by the committed variables and the challenge scalars in order for gadgets to be _locally sound_.
To facilitate this, the [constraint system API](../r1cs/index.html) prevents use of challenges
before all freely chosen variables are committed, and the raw challenge scalars are never exposed to the user.


[sorting_network]: https://en.wikipedia.org/wiki/Sorting_network


## Representation of constraints

The matrices \\(\mathbf{W}\_L, \mathbf{W}\_R, \mathbf{W}\_O, \mathbf{W}\_V\\) are typically very sparse
because most constraints apply only to a few variables. As a result, constraints are represented as short lists
of pairs \\((i, w)\\) where \\(i\\) is an index of a variable, and \\(w\\) is its (non-zero) weight.

Multiplication of a matrix by a vector is implemented via multiplication of each weight \\(w\\) by 
a scalar in the vector at a corresponding index \\(i\\). This way, all zero-weight terms are automatically skipped.











Constraint system proof
=======================

Constraint system proof allows a **verifier** to specify the constraints, for which a **prover** is asked to generate a valid proof.
The resulting proof is zero-knowledge: the constraints are known to both the prover and the verifier, but the variables remain secret.

The proving system uses efficient [inner product protocol](../inner_product_proof/index.html)
by expressing all the constraints in terms of a single inner product.
The following notes describe in detail how this is accomplished.

Constraint system notation
--------------------------

Dimensions of vectors:

* \\(m\\) — number of secret values \\({\mathbf{v}}\\),
* \\(n\\) — number of variable multiplication gates represented by \\(\mathbf{a}\_L, \mathbf{a}\_R, \mathbf{a}\_O\\),
* \\(q\\) — number of linear constraints represented by \\(\mathbf{W}\_L, \mathbf{W}\_R, \mathbf{W}\_O, \mathbf{W}\_V\\).

In the [Bulletproofs paper][bp_website], matrices are labeled as \\(\mathbf{W}\_L, \mathbf{W}\_R, \mathbf{W}\_O, \mathbf{W}\_V\\). We will keep this notation, but will note to readers not to confuse the \\(\mathbf{W}\_{L,R,O,V}\\) notation for being a vector of points.

We will use the general [notation](#notation) described above and, for consistency, rename two more variables from the paper:
\\[
\begin{aligned}
    \beta         &\xrightarrow{} \tilde{o} \\\\
    Q             &\xrightarrow{} q \\\\
\end{aligned}
\\]


[bp_website]: https://crypto.stanford.edu/bulletproofs/



Combining statements using challenge variables
----------------------------------------------

We can rewrite the statement about multiplication gates into an inner product equation, using the challenge variable \\(y\\).
We can do this for a random challenge \\(y\\) because \\({\mathbf{b}} = {\mathbf{0}}\\) if and only
if[^1] \\({\langle {\mathbf{b}}, {\mathbf{y}}^{n} \rangle} = 0\\). The equation \\(\mathbf{a}\_L \circ \mathbf{a}\_R = \mathbf{a}\_O\\) becomes:

\\[
\langle \mathbf{a}\_L \circ \mathbf{a}\_R - \mathbf{a}\_O ,
\mathbf{y}^n \rangle = 0
\\]

We can rewrite the statement about the linear constraints into an inner product equation, using the challenge variable \\(z\\).
We can do this for a random challenge \\(z\\), for the same reason as above. The equation
\\(
\mathbf{W}\_L \cdot \mathbf{a}\_L +
\mathbf{W}\_R \cdot \mathbf{a}\_R +
\mathbf{W}\_O \cdot \mathbf{a}\_O =
\mathbf{W}\_V \cdot \mathbf{v} +
\mathbf{c}
\\) 
becomes:

\\[
\langle z \mathbf{z}^q,
\mathbf{W}\_L \cdot \mathbf{a}\_L +
\mathbf{W}\_R \cdot \mathbf{a}\_R +
\mathbf{W}\_O \cdot \mathbf{a}\_O -
\mathbf{W}\_V \cdot \mathbf{v} -
\mathbf{c}
\rangle = 0
\\]

We can combine these two inner product equations, since they are offset by different multiples of challenge variable \\(z\\).
The statement about multiplication gates is multiplied by \\(z^0\\), while the statements about addition and scalar multiplication gates
are multiplied by a powers of \\(z\\) between \\(z^1\\) and \\(z^q\\). Combining the two equations gives us:

\\[
\langle \mathbf{a}\_L \circ \mathbf{a}\_R - \mathbf{a}\_O ,
\mathbf{y}^n \rangle +
\langle z \mathbf{z}^q, 
\mathbf{W}\_L \cdot \mathbf{a}\_L +
\mathbf{W}\_R \cdot \mathbf{a}\_R +
\mathbf{W}\_O \cdot \mathbf{a}\_O -
\mathbf{W}\_V \cdot \mathbf{v} -
\mathbf{c}
\rangle = 0
\\]

Before we proceed, we factor out “flattened constraints” from the terms that involve weight matrices:

\\[
\langle \mathbf{a}\_L \circ \mathbf{a}\_R - \mathbf{a}\_O ,
\mathbf{y}^n \rangle +
\langle \mathbf{w}\_L, \mathbf{a}\_L \rangle +
\langle \mathbf{w}\_R, \mathbf{a}\_R \rangle +
\langle \mathbf{w}\_O, \mathbf{a}\_O \rangle -
\langle \mathbf{w}\_V, \mathbf{v}    \rangle - w\_c = 0
\\]
\\[
\begin{aligned}
\mathbf{w}\_L &= z \mathbf{z}^q \cdot \mathbf{W}\_L, \\\\
\mathbf{w}\_R &= z \mathbf{z}^q \cdot \mathbf{W}\_R, \\\\
\mathbf{w}\_O &= z \mathbf{z}^q \cdot \mathbf{W}\_O, \\\\
\mathbf{w}\_V &= z \mathbf{z}^q \cdot \mathbf{W}\_V, \\\\
w\_c          &= \langle z \mathbf{z}^q, \mathbf{c} \rangle, \\\\
\end{aligned}
\\]
where each of \\(\mathbf{w}\_L, \mathbf{w}\_R, \mathbf{w}\_O\\) has length \\(n\\) and \\(\mathbf{w}\_V\\) has length \\(m\\).

[^1]: This is because the polynomial in terms of \\(y\\) is zero at every point
if and only if every term of it is zero. The verifier is going to sample
a random \\(y\\) after the prover commits to all the values forming the terms of
that polynomial, making the probability that the prover cheated negligible.
This trick allows implementing logical `AND` with any number of terms.

Rearranging into a single inner product statement
-------------------------------------------------

We want to work towards expressing the constraints in terms of a single inner product,
so that we can use the [inner product argument](../notes/index.html#inner-product-proof)
to represent it in a more compact and efficient-to-verify form. 
To do that we will rearrange the above equation so that terms
involving \\({\mathbf{a}}\_{L}\\) and \\({\mathbf{a}}\_{O}\\) appear only on the left-hand side, terms
involving \\({\mathbf{a}}\_{R}\\) appear only on the right-hand side, and
non-secret terms (which the verifier can compute on its own) are
factored out into a new term \\(\delta(y, z) \\).

This arrangement will allow us to verify relations between the resulting inner product,
its vectors and the commitments to high-level and low-level [variables](#variables).

The choice of placing \\({\mathbf{a}}\_{O}\\) on the same side with \\({\mathbf{a}}\_{L}\\) is arbitrary:
the proof would still work if \\({\mathbf{a}}\_{O}\\) was rearranged on the right-hand side instead.

If we reorder terms, we get:

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle
=
\langle \mathbf{a}\_L \circ \mathbf{a}\_R, \mathbf{y}^n \rangle -
\langle \mathbf{a}\_O, \mathbf{y}^n \rangle +
\langle \mathbf{w}\_L, \mathbf{a}\_L \rangle +
\langle \mathbf{w}\_R, \mathbf{a}\_R \rangle +
\langle \mathbf{w}\_O, \mathbf{a}\_O \rangle
\\]

Merge the statements containing \\(\mathbf{a}\_O \\):

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle
=
\langle \mathbf{a}\_L \circ \mathbf{a}\_R, \mathbf{y}^n \rangle +
\langle \mathbf{a}\_L, \mathbf{w}\_L                    \rangle +
\langle \mathbf{a}\_O, -\mathbf{y}^n + \mathbf{w}\_O    \rangle +
\langle \mathbf{a}\_R, \mathbf{w}\_R                    \rangle
\\]

Rearrange \\(\langle \mathbf{a}\_L \circ \mathbf{a}\_R, \mathbf{y}^n \rangle\\) into
\\(\langle \mathbf{a}\_L, \mathbf{y}^n \circ \mathbf{a}\_R \rangle\\):

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle
=
\langle \mathbf{a}\_L \circ \mathbf{a}\_R, \mathbf{y}^n \rangle +
\langle \mathbf{a}\_L, \mathbf{w}\_L                    \rangle +
\langle \mathbf{a}\_O, -\mathbf{y}^n + \mathbf{w}\_O    \rangle +
\langle \mathbf{a}\_R, \mathbf{w}\_R                    \rangle
\\]

Multiply the \\( \langle \mathbf{a}\_R, 
\mathbf{w}\_R \rangle \\) term by \\(\mathbf{y}^n\\) one one side of the inner product and by \\(\mathbf{y}^{-n}\\) on the other side:

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle
=
\langle \mathbf{a}\_L,                    \mathbf{y}^n \circ \mathbf{a}\_R    \rangle + 
\langle \mathbf{a}\_L,                    \mathbf{w}\_L                       \rangle +
\langle \mathbf{a}\_O,                   -\mathbf{y}^n + \mathbf{w}\_O        \rangle +
\langle \mathbf{y}^n \circ \mathbf{a}\_R, \mathbf{y}^{-n} \circ \mathbf{w}\_R \rangle
\\]

Merge the statements containing \\(\mathbf{y}^n \circ \mathbf{a}\_R\\):

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle
=
\langle \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{y}^n \circ \mathbf{a}\_R \rangle + 
\langle \mathbf{a}\_L,                                       \mathbf{w}\_L                    \rangle +
\langle \mathbf{a}\_O,                                      -\mathbf{y}^n + \mathbf{w}\_O     \rangle
\\]

Add \\(\delta(y, z) = \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{w}\_L \rangle \\) to both sides:

\\[
\begin{aligned}
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle +
\delta(y, z)
&=
\langle \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{y}^n \circ \mathbf{a}\_R \rangle + 
\langle \mathbf{a}\_L,                       \mathbf{w}\_L                \rangle \\\\ 
&+
\langle \mathbf{a}\_O,                      -\mathbf{y}^n + \mathbf{w}\_O \rangle + 
\langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{w}\_L                \rangle
\end{aligned}
\\]

Merge the terms containing \\(\mathbf{w}\_L\\):

\\[
\begin{aligned}
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z)
&= \langle \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R, 
\mathbf{y}^n \circ \mathbf{a}\_R \rangle + 
\langle \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R,
\mathbf{w}\_L \rangle +
\langle \mathbf{a}\_O, 
-\mathbf{y}^n + \mathbf{w}\_O \rangle
\end{aligned}
\\]

Merge the terms containing \\(\mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R\\):

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z) =
\langle \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R, 
\mathbf{y}^n \circ \mathbf{a}\_R +
\mathbf{w}\_L \rangle +
\langle \mathbf{a}\_O, 
-\mathbf{y}^n + \mathbf{w}\_O \rangle
\\]

We want to combine a sum of two inner products \\(\langle a, b \rangle + \langle c, d \rangle\\) into one inner product.
To do that, we will take a term of a polynomial formed by a linear combination of these products with respect to a challenge scalar \\(x\\). Specifically, the 2nd degree term of \\(\langle a \cdot x + c \cdot x^2, b \cdot x + d \cdot x^0 \rangle\\) is equal to
\\( \langle a, b \rangle + \langle c, d \rangle\\).

To apply this technique to the above equation we assign \\(a, b, c, d\\) the following values:

\\[
\begin{aligned}
a &= \mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R \\\\
b &= \mathbf{y}^n \circ \mathbf{a}\_R +
\mathbf{w}\_L\\\\
c &= \mathbf{a}\_O \\\\
d &= -\mathbf{y}^n + \mathbf{w}\_O
\end{aligned}
\\]

Next, we combine \\(a, b, c, d\\) using the equation \\( \langle a \cdot x + c \cdot x^2, b \cdot x + d \cdot x^0 \rangle \\). When we take its second degree, we recover a single inner product, which was our original goal:

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z) = 
\text{2nd degree of }
\langle (\mathbf{a}\_L + \mathbf{y}^{-n} \circ \mathbf{w}\_R) \cdot x + 
\mathbf{a}\_O \cdot x^2,
(\mathbf{y}^n \circ \mathbf{a}\_R +
\mathbf{w}\_L) \cdot x +
(-\mathbf{y}^n + \mathbf{w}\_O) \cdot x^0 \rangle 
\\]

Distribute the \\(x\\) values: 

\\[
w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z) = 
\text{2nd degree of }
\langle \mathbf{a}\_L \cdot x + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + 
\mathbf{a}\_O \cdot x^2,
\mathbf{y}^n \circ \mathbf{a}\_R \cdot x +
\mathbf{w}\_L \cdot x -
\mathbf{y}^n + \mathbf{w}\_O \rangle
\\]

This is equivalent to the equation we started with, but has a single
inner product with \\({\mathbf{a}}\_{L}\\) and \\({\mathbf{a}}\_{O}\\) on the left, \\({\mathbf{a}}\_{R}\\) on
the right, and non-secret terms factored out.

Blinding the inner product
--------------------------

In the current form, the vectors in the inner-product reveal information about the values
\\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\) and \\({\mathbf{a}}\_{O}\\), which in turn reveal the values \\(\mathbf{v}\\).
And since the inner-product argument is not zero-knowledge, the vectors cannot be used in the inner-product argument either.
To solve this problem, the prover chooses two vectors of blinding factors

\\[
{\mathbf{s}}\_{L}, {\mathbf{s}}\_{R} \\;{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n},
\\]

and uses them to blind \\(\mathbf{a}\_L\\) and \\(\mathbf{a}\_R\\) within left and right sides of the inner product respectively.

\\[
\begin{aligned}
\mathbf{a}\_{L} &\leftarrow \mathbf{a}\_{L} + \mathbf{s}\_{L} \cdot x^2 \\\\
\mathbf{a}\_{R} &\leftarrow \mathbf{a}\_{R} + \mathbf{s}\_{R} \cdot x^2
\end{aligned}
\\]

The blinding factors are multiplied by \\(x^2\\) so that when the substitution is made into the \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\) equations, \\({\mathbf{s}}\_{L}\\) will be in the 3rd degree of \\(x\\) in \\(\mathbf{l}(x)\\), and \\({\mathbf{s}}\_{L}\\) will be in the 3rd degree of \\(x\\) in \\(\mathbf{r}(x)\\). As a result, the blinding factors will not interfere with the value \\(t_2\\), which is the 2nd degree of \\(\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle\\).

Note: multiplication outputs \\(\mathbf{a}\_O\\) do not need their own blinding factors:
they are automatically blinded by \\(\mathbf{s}\_{L}\\) since both \\(\mathbf{a}\_L\\)
and \\(\mathbf{a}\_O\\) are terms in the same (left) side of the inner product.

We now construct vector polynomials \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\),
which represent the left and right sides of the input to the inner-product equation, with these new definitions:
\\[
\begin{aligned}
  {\mathbf{l}}(x) &= (\mathbf{a}\_L + \mathbf{s}\_L \cdot x^2) \cdot x + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + \mathbf{a}\_O \cdot x^2 \\\\
                  &= \mathbf{a}\_L \cdot x + \mathbf{s}\_L \cdot x^3 + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + \mathbf{a}\_O \cdot x^2 \\\\
  {\mathbf{r}}(x) &= \mathbf{y}^n \circ (\mathbf{a}\_R + \mathbf{s}\_R \cdot x^2) \cdot x + \mathbf{w}\_L \cdot x - \mathbf{y}^n + \mathbf{w}\_O \\\\
                  &= \mathbf{y}^n \circ \mathbf{a}\_R \cdot x + \mathbf{y}^n \circ \mathbf{s}\_R \cdot x^3 + \mathbf{w}\_L \cdot x - \mathbf{y}^n + \mathbf{w}\_O
\end{aligned}
\\]

When we take the inner product of \\({\mathbf{l}}(x)\\) and \\({\mathbf{l}}(x)\\), we get:

\\[
\begin{aligned}
  t(x) &= {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} \\\\
       &= t\_{1} x + t\_{2} x^{2} + t\_{3} x^{3} + t\_{4} x^{4} + t\_{5} x^{5} + t\_{6} x^{6} \\\\
       &= \sum_{i=1}^{6} t_i x^i
\end{aligned}
\\]

Notice that the second degree of \\(t(x)\\) does not include any blinding factors (because the blinding factors end up in the third or greater degrees of \\(t(x)\\)) and only contains the inner product forms of the initial arithmetic gate statements that we are trying to prove:

\\[
\begin{aligned}
t_2 &= \text{2nd degree of } \langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle
\\\\
&= w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z) \\\\
&=
\langle \mathbf{a}\_L \circ \mathbf{a}\_R, \mathbf{y}^n \rangle -
\langle \mathbf{a}\_O, \mathbf{y}^n \rangle + 
\langle \mathbf{w}\_L, \mathbf{a}\_L \rangle +
\langle \mathbf{w}\_R, \mathbf{a}\_R \rangle +
\langle \mathbf{w}\_O, \mathbf{a}\_O \rangle +
\delta(y, z)
\end{aligned}
\\]

Proving that \\(t_2\\) is correct
---------------------------------

The prover first forms a commitment to the coefficients of \\(t(x)\\), then convinces the verifier that these commit to the correct \\(t(x)\\) by evaluating the polynomial at a challenge point \\(x\\). This proves that \\(t(x)\\) is correct and follows the following equation:

\\[
\begin{aligned}
t(x) &= \sum\_{i=1}^{6} x^i t\_{i} \\\\
t_2 &= w\_c + \langle \mathbf{w}\_V, \mathbf{v} \rangle + \delta(y, z) \\\\
\end{aligned}
\\]

We define \\(\mathbf{V}\\) as the vector of Pedersen commitments to \\(\mathbf{v}\\), and \\(T_i\\) as the Pedersen commitment to \\(t_i\\) for \\(i \in [1, 3, 4, 5, 6]\\):

\\[
\begin{aligned}
V_j &= B \cdot v_j + \widetilde{B} \cdot \tilde{v}\_j \quad \forall j \in [1, m] \\\\
T_i &= B \cdot t_i + \widetilde{B} \cdot \tilde{t}\_i \quad \forall i \in [1, 3, 4, 5, 6] \\\\
\end{aligned}
\\]

The prover forms these commitments, and sends them to the verifier. These commitments are related to each other and to \\(t(x)\\) by the following diagram:

\\[
\begin{aligned}
  t(x) B                         &\quad &= \quad & x^2 \langle \mathbf{w}\_V, \mathbf{v} \rangle \cdot B                      & \quad &+ \quad & x^2 \big(w\_c + \delta(y,z)\big) B   &\quad &+\quad & \sum\_{i = 1,3,4,5,6} &x^i t\_{i} B                       \\\\
    +                            &\quad &  \quad &  +                                                                         & \quad &  \quad &  +                                   &\quad & \quad &                                     &         +           \\\\
  {\tilde{t}}(x) {\widetilde{B}} &\quad &= \quad & x^2 \langle \mathbf{w}\_V, \tilde{\mathbf{v}} \rangle \cdot \widetilde{B}  & \quad &+ \quad & 0 {\widetilde{B}}                    &\quad &+\quad & \sum\_{i = 1,3,4,5,6} &x^i \tilde{t\_{i}} {\widetilde{B}} \\\\
  \shortparallel                 &\quad &  \quad & \shortparallel                                                             & \quad &  \quad & \shortparallel                       &\quad & \quad &                                     &    \shortparallel   \\\\
                                 &\quad &= \quad & x^2 \langle \mathbf{w}\_V, \mathbf{V} \rangle                              & \quad &+ \quad & x^2 \big(w\_c + \delta(y,z)\big) B   &\quad &+\quad & \sum\_{i = 1,3,4,5,6} &x^i T\_{i}
\end{aligned}
\\]

Notice that the sum of each column is a commitment to the variable in the top row using the blinding factor in the second row. The sum of all of the columns is
\\(t(x) B + {\tilde{t}}(x) {\widetilde{B}}\\), a commitment to the value
of \\(t\\) at the point \\(x\\), using the synthetic blinding factor[^2]:
\\[
  {\tilde{t}}(x) = x^2 \langle \mathbf{w}\_V, \tilde{\mathbf{v}} \rangle + \sum\_{i = 1,3,4,5,6} x^i \tilde{t}\_{i}
\\]

To convince the verifier that
\\(t(x) = \delta(y,z) + \sum\_{i=1}^{6} x^i t\_{i}\\), the prover sends
the opening \\(t(x), {\tilde{t}}(x)\\) to the verifier, who uses the
bottom row of the diagram to check consistency:
\\[
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} x^2 \langle \mathbf{w}\_V, \mathbf{V} \rangle + x^2 \big(w\_c + \delta(y,z)\big) B + \sum\_{i = 1,3,4,5,6} x^i T\_{i}
\\]

[^2]: The blinding factor is synthetic in the sense that it is
    synthesized from the blinding factors of the other commitments.

Proving that \\(\mathbf{l}(x)\\), \\(\mathbf{r}(x)\\) are correct
-----------------------------------------------------------------

We want to relate \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) to commitments
to \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\), \\({\mathbf{s}}\_{L}\\), and
\\({\mathbf{s}}\_{R}\\). Since
\\[
{\mathbf{r}}(x) = \mathbf{y}^n \circ \mathbf{a}\_R \cdot x + \mathbf{y}^n \circ \mathbf{s}\_R \cdot x^3 + \mathbf{w}\_L \cdot x - \mathbf{y}^n + \mathbf{w}\_O
\\]
we need commitments to \\({\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}\\) and
\\({\mathbf{y}}^{n} \circ {\mathbf{s}}\_{R}\\). However, the prover
must form commitments before receiving the verifier’s challenge \\(y\\),
so they can only commit to \\({\mathbf{a}}\_{R}\\) and \\({\mathbf{s}}\_{R}\\),
requiring the verifier to transmute the prover’s commitment over
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
\\(\hat{\mathbf{H}} = {\mathbf{y}}^{-n} \circ {\mathbf{H}}\\), the point which
is a commitment to
\\(({\mathbf{a}}\_{L}, {\mathbf{a}}\_{R}, {\widetilde{a}})\\) with respect to
\\(({\mathbf{G}}, {\mathbf{H}}, {\widetilde{a}})\\) is transmuted into a
commitment to
\\(({\mathbf{a}}\_{L}, {\mathbf{y}}^{n} \circ {\mathbf{a}}\_{R}, {\widetilde{a}})\\)
with respect to \\(({\mathbf{G}}, \hat{\mathbf{H}}, {\widetilde{a}})\\).

We define the following commitments over the components of \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\):

\\[
\begin{aligned}
A_I &= \widetilde{B} \cdot \tilde{a} + \langle \mathbf{G} , \mathbf{a}\_L \rangle + \langle \mathbf{H}, \mathbf{a}\_R \rangle \\\\
A_O &= \widetilde{B} \cdot \tilde{o} + \langle \mathbf{G} , \mathbf{a}\_O \rangle \\\\
W_L &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_L, \mathbf{H} \rangle \\\\
W_R &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{G} \rangle \\\\
W_O &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_O, \mathbf{H} \rangle \\\\
S   &= \widetilde{B} \cdot \tilde{s} + \langle \mathbf{G} , \mathbf{s}\_L \rangle + \langle \mathbf{H}, \mathbf{s}\_R \rangle
\end{aligned}
\\]

The prover forms these commitments, and sends them to the verifier.

For reference, here are the equations for \\({\mathbf{l}}(x)\\), and \\({\mathbf{r}}(x)\\) multiplied by \\(\mathbf{y}^{-n}\\):

\\[
\begin{aligned}
                        \mathbf{l}(x)  &= \mathbf{a}\_L \cdot x + \mathbf{s}\_L \cdot x^3 + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + \mathbf{a}\_O \cdot x^2 \\\\
  \mathbf{y}^{-n} \circ \mathbf{r}(x)  &= \mathbf{a}\_R \cdot x + \mathbf{s}\_R \cdot x^3 + \mathbf{y}^{-n} \circ \mathbf{w}\_L \cdot x - \mathbf{1}^n + \mathbf{y}^{-n} \circ \mathbf{w}\_O
\end{aligned}
\\]

To relate the prover’s commitments to
\\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\), we use the following diagram:

\\[
\begin{aligned}
  {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle}      &\quad &= \quad & {\langle {\mathbf{a}}\_L \cdot x, {\mathbf{G}} \rangle}      & \quad &+ \quad & {\langle {\mathbf{a}}\_O \cdot x^2, {\mathbf{G}} \rangle}  & \quad &+ \quad& x \cdot \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{G} \rangle                      &\quad &+\quad & \langle \mathbf{s}\_L \cdot x^3 , \mathbf{G} \rangle \\\\
                                                +      &\quad &  \quad &  +                                                           & \quad &  \quad &  +                                                         & \quad &  \quad& +                                                                                            &\quad & \quad & +   \\\\
  {\langle {\mathbf{r}}(x), \hat{\mathbf{H}} \rangle}  &\quad &= \quad & \langle \mathbf{a}\_R \cdot x, {\mathbf{H}} \rangle          & \quad &+ \quad & - \langle \mathbf{1}, \mathbf{H} \rangle                   & \quad &+ \quad& \langle \mathbf{y}^{-n} \circ (x \cdot \mathbf{w}\_L + \mathbf{w}\_O), \mathbf{H} \rangle    &\quad &+\quad & \langle \mathbf{s}\_R \cdot x^3 , \mathbf{H} \rangle \\\\
                                                +      &\quad &  \quad &  +                                                           & \quad &  \quad &  +                                                         & \quad &  \quad& +                                                                                            &\quad & \quad & +   \\\\
  \tilde{e} \cdot \widetilde{B}                        &\quad &= \quad & \tilde{a} \cdot x \cdot \widetilde{B}                        & \quad &+ \quad & \tilde{o} \cdot x^2 \cdot \widetilde{B}                    & \quad &+ \quad& 0                                                                                            &\quad &+\quad & \tilde{s} \cdot x^3 \cdot \widetilde{B} \\\\
                                    \shortparallel     &\quad &  \quad & \shortparallel                                               & \quad &  \quad & \shortparallel                                             & \quad &  \quad& \shortparallel                                                                               &\quad & \quad & \shortparallel   \\\\
                                                       &\quad &= \quad & x \cdot A_I                                                  & \quad &+ \quad & x^2 \cdot A_O - \langle \mathbf{1}, \mathbf{H} \rangle     & \quad &+ \quad& x \cdot W_L + x \cdot W_R + W_O                                                              &\quad &+\quad & x^3 \cdot S
\end{aligned}
\\]

We can interpret the rows and columns similarly to the previous diagram:
the sum of each column is a vector Pedersen commitment with left and right halves from the first and second rows respectively
and blinding factor from the third row.
The sum of all of the columns is a vector
Pedersen commitment to \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) with
synthetic blinding factor \\(\widetilde{e} = \tilde{a} \cdot x+ \tilde{o} \cdot x^2 + \tilde{s} \cdot x^3\\).

To convince the verifier that \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\) are computed correctly,
the prover can send the evaluations \\(\mathbf{l}(x), \mathbf{r}(x)\\) along with \\(\tilde{e}\\) to the verifier,
who uses the bottom row of the diagram to check the following statement:
\\[
\begin{aligned}
   {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), \hat{\mathbf{H}} \rangle} \stackrel{?}{=}
   -{\widetilde{e}} {\widetilde{B}} + x \cdot A_I + x^2 \cdot A_O - \langle \mathbf{1}, \mathbf{H} \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot S \\\\
\end{aligned}
\\]


Verifying challenge-based constraints
-------------------------------------

Some [gadgets](#gadgets) can be made more efficient if they can [sample random challenges](#gadget-as-a-challenge) when building
a constraint system, provided certain variables are committed. For instance, a shuffle gadget
can use just \\(2(k-1)\\) multipliers for \\(k\\) inputs and \\(k\\) outputs to implement the check 
that two polynomials are equal up to a permutation of their roots, but it is only sound as long
as the roots of the polynomials (the inputs/outputs to the shuffle) are fixed before the evaluation point is chosen.

To faciliate this, we split the vectors of multipliers and their blinding factors in two subvectors of lengths \\(n'\\) and \\(n''\\): 

\\[
\begin{aligned}
    n                &= n' + n''                              \\\\
    {\mathbf{a}}\_L  &= {\mathbf{a}}\_L' || {\mathbf{a}}\_L'' \\\\
    {\mathbf{a}}\_R  &= {\mathbf{a}}\_R' || {\mathbf{a}}\_R'' \\\\
    {\mathbf{a}}\_O  &= {\mathbf{a}}\_O' || {\mathbf{a}}\_O'' \\\\
    {\mathbf{s}}\_L  &= {\mathbf{s}}\_L' || {\mathbf{s}}\_L'' \\\\
    {\mathbf{s}}\_R  &= {\mathbf{s}}\_R' || {\mathbf{s}}\_R'' \\\\
\end{aligned}
\\]

The vectors of flattened weights are split accordingly:

\\[
\begin{aligned}
    \mathbf{w}\_L  &= {\mathbf{w}}\_L' || {\mathbf{w}}\_L'' \\\\
    \mathbf{w}\_R  &= {\mathbf{w}}\_R' || {\mathbf{w}}\_R'' \\\\
    \mathbf{w}\_O  &= {\mathbf{w}}\_O' || {\mathbf{w}}\_O'' \\\\
\end{aligned}
\\]

The statements of each slice of the vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\) become:

\\[
\begin{aligned}
                                   \mathbf{l}'(x) &= \mathbf{a}'\_L \cdot x  + \mathbf{s}\_L' \cdot x^3  +        \mathbf{y}^{-n'}  \circ \mathbf{w}\_R'  \cdot x + \mathbf{a}\_O' \cdot x^2\\\\
                                  \mathbf{l}''(x) &= \mathbf{a}''\_L \cdot x + \mathbf{s}\_L'' \cdot x^3 + y^{-n'}\mathbf{y}^{-n''} \circ \mathbf{w}\_R'' \cdot x + \mathbf{a}\_O'' \cdot x^2\\\\
            \mathbf{y}^{-n'} \circ \mathbf{r}'(x) &= \mathbf{a}'\_R \cdot x  + \mathbf{s}\_R' \cdot x^3  +        \mathbf{y}^{-n'}  \circ \mathbf{w}\_L' \cdot x  - \mathbf{1}^{n'}  +        \mathbf{y}^{-n'}  \circ \mathbf{w}\_O'\\\\
  y^{-n'} \mathbf{y}^{-n''} \circ \mathbf{r}''(x) &= \mathbf{a}''\_R \cdot x + \mathbf{s}\_R'' \cdot x^3 + y^{-n'}\mathbf{y}^{-n''} \circ \mathbf{w}\_L'' \cdot x - \mathbf{1}^{n''} + y^{-n'}\mathbf{y}^{-n''} \circ \mathbf{w}\_O''\\\\
\end{aligned}
\\]

Now we need to express the statements above using independent commitments to the subvectors \\(\mathbf{a}'\_{L,R,O}\\) and \\(\mathbf{a}''\_{L,R,O}\\).
Commitments must be independent because second subvectors are computed with the use of challenges generated _after_ the first subvectors are determined and committed.

To do that, we split vectors of generators and combine the statements in two:
the first one in terms of the commitments to the first subvectors,
and the second one in terms of the commitments to the second subvectors.

\\[
\begin{aligned}
\mathbf{G} &= \mathbf{G}' || \mathbf{G}'' \\\\
\mathbf{H} &= \mathbf{H}' || \mathbf{H}'' \\\\
\end{aligned}
\\]

\\[
\begin{aligned}
  {\langle \mathbf{l}'(x), {\mathbf{G}'} \rangle}                                   &\quad &= \quad & x \cdot {\langle \mathbf{a}'\_L, \mathbf{G}' \rangle}       & \quad &+ \quad x^2 \cdot {\langle \mathbf{a}'\_O, \mathbf{G}' \rangle}    & \quad &+ \quad \langle x \cdot \mathbf{y}^{-n'} \circ \mathbf{w}\_R', \mathbf{G}' \rangle                                 &\quad &+\quad  x^3 \cdot \langle \mathbf{s}'\_L , \mathbf{G}' \rangle \\\\
                                                                        +           &\quad &  \quad &  +                                                          & \quad &  \quad \quad  +                                                   & \quad &  \quad \quad +                                                                                                    &\quad & \quad  \quad +   \\\\
  {\langle  \mathbf{y}^{-n'} \circ \mathbf{r}'(x), {\mathbf{H}'} \rangle}           &\quad &= \quad & x \cdot {\langle \mathbf{a}'\_R, \mathbf{H}' \rangle}       & \quad &- \quad \langle \mathbf{1}, \mathbf{H}' \rangle                    & \quad &+ \quad \langle \mathbf{y}^{-n'} \circ (x \cdot \mathbf{w}\_L'  + \mathbf{w}\_O'), \mathbf{H}' \rangle             &\quad &+\quad  x^3 \cdot \langle \mathbf{s}'\_R , \mathbf{H}' \rangle \\\\
                                                                                    &\quad &  \quad &                                                             & \quad &  \quad \quad                                                      & \quad &  \quad \quad                                                                                                      &\quad & \quad  \quad     \\\\
  {\langle \mathbf{l}''(x), {\mathbf{G}''} \rangle}                                 &\quad &= \quad & x \cdot {\langle \mathbf{a}''\_L, \mathbf{G}'' \rangle}     & \quad &+ \quad x^2 \cdot {\langle \mathbf{a}''\_O, \mathbf{G}'' \rangle}  & \quad &+ \quad \langle x \cdot y^{-n'} \mathbf{y}^{-n''} \circ \mathbf{w}\_R'', \mathbf{G}'' \rangle                      &\quad &+\quad  x^3 \cdot \langle \mathbf{s}''\_L , \mathbf{G}'' \rangle \\\\
                                                                              +     &\quad &  \quad &  +                                                          & \quad &  \quad \quad  +                                                   & \quad &  \quad \quad +                                                                                                    &\quad & \quad  \quad +   \\\\
  {\langle  y^{n'} \mathbf{y}^{-n''} \circ \mathbf{r}''(x), {\mathbf{H}''} \rangle} &\quad &= \quad & x \cdot {\langle \mathbf{a}''\_R, \mathbf{H}'' \rangle}     & \quad &- \quad \langle \mathbf{1}, \mathbf{H}'' \rangle                   & \quad &+ \quad \langle y^{-n'} \mathbf{y}^{-n''} \circ (x \cdot \mathbf{w}\_L''  + \mathbf{w}\_O''), \mathbf{H}'' \rangle &\quad &+\quad  x^3 \cdot \langle \mathbf{s}''\_R , \mathbf{H}'' \rangle \\\\
\end{aligned}
\\]

We need to combine the above statements in one in order to have an expression for the complete vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\).
For that we will multiply the second statement by a random challenge \\(e \in {\mathbb Z\_{p}^{\times}}\\), and add it to the first statement.

\\[
\begin{aligned}
  {\langle \mathbf{l}'(x), {\mathbf{G}'} \rangle}                                           &\quad &= \quad & x \cdot {\langle \mathbf{a}'\_L, \mathbf{G}' \rangle}               & \quad &+ \quad x^2 \cdot {\langle \mathbf{a}'\_O, \mathbf{G}' \rangle}            & \quad &+ \quad \langle x \cdot \mathbf{y}^{-n'} \circ \mathbf{w}\_R', \mathbf{G}' \rangle                                         &\quad &+\quad  x^3 \cdot \langle \mathbf{s}'\_L , \mathbf{G}' \rangle \\\\
                                                                        +                   &\quad &  \quad &  +                                                                  & \quad &  \quad \quad  +                                                           & \quad &  \quad \quad +                                                                                                            &\quad & \quad  \quad +   \\\\
  {\langle  \mathbf{y}^{-n'} \circ \mathbf{r}'(x), {\mathbf{H}'} \rangle}                   &\quad &= \quad & x \cdot {\langle \mathbf{a}'\_R, \mathbf{H}' \rangle}               & \quad &- \quad \langle \mathbf{1}, \mathbf{H}' \rangle                            & \quad &+ \quad \langle \mathbf{y}^{-n'} \circ (x \cdot \mathbf{w}\_L'  + \mathbf{w}\_O'), \mathbf{H}' \rangle                     &\quad &+\quad  x^3 \cdot \langle \mathbf{s}'\_R , \mathbf{H}' \rangle \\\\
                                                                        +                   &\quad &  \quad &  +                                                                  & \quad &  \quad \quad  +                                                           & \quad &  \quad \quad +                                                                                                            &\quad & \quad  \quad     \\\\
  {\langle e \cdot \mathbf{l}''(x), {\mathbf{G}''} \rangle}                                 &\quad &= \quad & e \cdot x \cdot {\langle \mathbf{a}''\_L, \mathbf{G}'' \rangle}     & \quad &+ \quad e \cdot x^2 \cdot {\langle \mathbf{a}''\_O, \mathbf{G}'' \rangle}  & \quad &+ \quad e \cdot \langle x \cdot y^{-n'} \mathbf{y}^{-n''} \circ \mathbf{w}\_R'', \mathbf{G}'' \rangle                      &\quad &+\quad  e \cdot x^3 \cdot \langle \mathbf{s}''\_L , \mathbf{G}'' \rangle \\\\
                                                                        +                   &\quad &  \quad &  +                                                                  & \quad &  \quad \quad  +                                                           & \quad &  \quad \quad +                                                                                                            &\quad & \quad  \quad +   \\\\
  {\langle e \cdot  y^{n'} \mathbf{y}^{-n''} \circ \mathbf{r}''(x), {\mathbf{H}''} \rangle} &\quad &= \quad & e \cdot x \cdot {\langle \mathbf{a}''\_R, \mathbf{H}'' \rangle}     & \quad &- \quad e \cdot \langle \mathbf{1}, \mathbf{H}'' \rangle                   & \quad &+ \quad e \cdot \langle y^{-n'} \mathbf{y}^{-n''} \circ (x \cdot \mathbf{w}\_L''  + \mathbf{w}\_O''), \mathbf{H}'' \rangle &\quad &+\quad  e \cdot x^3 \cdot \langle \mathbf{s}''\_R , \mathbf{H}'' \rangle \\\\
\end{aligned}
\\]


Low-level variables are committed before challenges \\(y\\) and \\(e\\) are known, so we change the generators for the \\(\mathbf{l}(x), \mathbf{r}(x)\\):

\\[
\begin{aligned}
    \hat{\mathbf{G}} &= \mathbf{G}' || (e \cdot \mathbf{G}'') \\\\
    \hat{\mathbf{H}} &= \mathbf{y}^{-n} \circ \big( \mathbf{H}' || (e \cdot \mathbf{H}'') \big) \\\\
\end{aligned}
\\]

Lets now define the commitments over the components of \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\):

\\[
\begin{aligned}
     A_I'  &= \langle \mathbf{G}'  , \mathbf{a}\_L'  \rangle + \langle \mathbf{H}', \mathbf{a}\_R' \rangle + \widetilde{B} \cdot \tilde{a}'  \\\\
     A_I'' &= \langle \mathbf{G}'' , \mathbf{a}\_L'' \rangle + \langle \mathbf{H}'', \mathbf{a}\_R'' \rangle + \widetilde{B} \cdot \tilde{a}'' \\\\
     A_O'  &= \langle \mathbf{G}'  , \mathbf{a}\_O'  \rangle + \widetilde{B} \cdot \tilde{o}'  \\\\
     A_O'' &= \langle \mathbf{G}'' , \mathbf{a}\_O'' \rangle + \widetilde{B} \cdot \tilde{o}'' \\\\
     S'    &= \langle \mathbf{G}'  , \mathbf{s}\_L'  \rangle + \langle \mathbf{H}', \mathbf{s}\_R' \rangle + \widetilde{B} \cdot \tilde{s}'  \\\\
     S''   &= \langle \mathbf{G}'' , \mathbf{s}\_L'' \rangle + \langle \mathbf{H}'', \mathbf{s}\_R'' \rangle + \widetilde{B} \cdot \tilde{s}'' \\\\
\end{aligned}
\\]

We can now relate the above commitments to \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) using the new diagram:

\\[
\begin{aligned}
  {\langle {\mathbf{l}}(x), \hat{\mathbf{G}} \rangle}      &\quad &= \quad & x \cdot \big( {\langle \mathbf{a}'\_L, \mathbf{G}' \rangle} + e \cdot {\langle \mathbf{a}''\_L, \mathbf{G}'' \rangle} \big)      & \quad &+ \quad x^2 \cdot \big( {\langle \mathbf{a}'\_O, \mathbf{G}' \rangle}  +  e \cdot {\langle \mathbf{a}''\_O, \mathbf{G}'' \rangle} \big)         & \quad &+ \quad \langle \mathbf{y}^{-n} \circ (\mathbf{w}\_R' || e \cdot \mathbf{w}\_R'') \cdot x , \mathbf{G} \rangle                                                   &\quad &+\quad  x^3 \cdot \big( \langle \mathbf{s}'\_L , \mathbf{G}' \rangle + e \cdot \langle \mathbf{s}''\_L , \mathbf{G}'' \rangle \big) \\\\
                                                    +      &\quad &  \quad &  +                                                                                                                               & \quad &  \quad \quad  +                                                                                                                                & \quad &  \quad \quad +                                                                                                                                                  &\quad & \quad  \quad +   \\\\
  {\langle {\mathbf{r}}(x), \hat{\mathbf{H}} \rangle}      &\quad &= \quad & x \cdot \big( {\langle \mathbf{a}'\_R, \mathbf{H}' \rangle} + e \cdot {\langle \mathbf{a}''\_R, \mathbf{H}'' \rangle} \big)      & \quad &- \quad \langle \mathbf{1}, \mathbf{H}' \rangle -  e \cdot \langle \mathbf{1}, \mathbf{H}'' \rangle                                             & \quad &+ \quad \langle \mathbf{y}^{-n} \circ (\mathbf{w}\_L' || e \cdot \mathbf{w}\_L'') \cdot x + (\mathbf{w}\_O' || e \cdot \mathbf{w}\_O''), \mathbf{H} \rangle      &\quad &+\quad  x^3 \cdot \big( \langle \mathbf{s}'\_R , \mathbf{H}' \rangle + e \cdot \langle \mathbf{s}''\_R , \mathbf{H}'' \rangle \big) \\\\
                                                    +      &\quad &  \quad &  +                                                                                                                               & \quad &  \quad \quad +                                                                                                                                 & \quad &  \quad \quad +                                                                                                                                                  &\quad & \quad  \quad +   \\\\
                        \tilde{e} \cdot \widetilde{B}      &\quad &= \quad & x \cdot \big( \tilde{a}' \cdot \widetilde{B} + e \tilde{a}'' \cdot \widetilde{B} \big)                                           & \quad &+ \quad x^2 \cdot \big( \tilde{o}' \cdot \widetilde{B} + e \cdot \tilde{o}'' \cdot \widetilde{B} \big)                                          & \quad &+ \quad 0                                                                                                                                                        &\quad &+\quad  x^3 \cdot \big( \tilde{s}' \cdot \widetilde{B} + e \tilde{s}'' \cdot \widetilde{B} \big) \\\\
                                        \shortparallel     &\quad &  \quad & \shortparallel                                                                                                                   & \quad &  \quad \quad \shortparallel                                                                                                                    & \quad &  \quad \quad \shortparallel                                                                                                                                           &\quad & \quad  \quad \shortparallel   \\\\
                                                           &\quad &= \quad & x \cdot \big(A_I' + e \cdot A_I'')                                                                                               & \quad &+ \quad x^2 \cdot \big(A_O' + e \cdot A_O'' \big) - \langle \mathbf{1}, \mathbf{H}' \rangle - e \cdot \langle \mathbf{1}, \mathbf{H}'' \rangle  & \quad &+ \quad W_L \cdot x + W_R \cdot x + W_O                                                                                                                          &\quad &+\quad  x^3 \cdot (S' + e \cdot S'')
\end{aligned}
\\]
where
\\[
\begin{aligned}
W_L &= \langle \mathbf{y}^{-n} \circ (\mathbf{w}'\_L || e \cdot \mathbf{w}''\_L), \mathbf{H} \rangle, \\\\
W_R &= \langle \mathbf{y}^{-n} \circ (\mathbf{w}'\_R || e \cdot \mathbf{w}''\_R), \mathbf{G} \rangle, \\\\
W_O &= \langle \mathbf{y}^{-n} \circ (\mathbf{w}'\_O || e \cdot \mathbf{w}''\_O), \mathbf{H} \rangle. \\\\
\end{aligned}
\\]

The sum of each column is a vector Pedersen commitment with left and right halves from the first and second rows respectively
and blinding factor from the third row.
The sum of all of the columns is a vector
Pedersen commitment to \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) with
synthetic blinding factor \\(\widetilde{e} = (\tilde{a}' + e \tilde{a}'') \cdot x + (\tilde{o}' + e \tilde{o}'') \cdot x^2 + (\tilde{s}' + e \tilde{s}'') \cdot x^3\\).

To convince the verifier that \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\) are computed correctly,
the prover can send the evaluations \\(\mathbf{l}(x), \mathbf{r}(x)\\) along with \\(\tilde{e}\\) to the verifier,
who uses the bottom row of the diagram to check the following statement:

\\[
\begin{aligned}
   {\langle {\mathbf{l}}(x), \hat{\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), \hat{\mathbf{H}} \rangle} \stackrel{?}{=}
   -{\widetilde{e}} {\widetilde{B}} + x \cdot (A_I' + e \cdot A_I'') + x^2 \cdot (A_O' + e \cdot A_O'') - \langle \mathbf{1}, \mathbf{H}' \rangle - e \cdot \langle \mathbf{1}, \mathbf{H}'' \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot (S' + e \cdot S'') \\\\
\end{aligned}
\\]



Compressing vectors \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\) with an inner product argument
----------------------------------------------------------------------------------------------

Once the verifier has checked correctness of \\(t(x)\\), \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\),
they can directly compute the inner product to verify whether \\(t(x) \stackrel{?}{=} {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\).
This, however, would require transmitting \\(2n\\) 32-byte elements representing the vectors.

To make the proof smaller, the prover will use the [inner product argument](../notes/index.html#inner-product-proof)
to indirectly prove the inner product relation using \\(t(x)\\) and the vectors represented
by a commitment \\(P = {\langle {\mathbf{l}}(x), \hat{\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), \hat{\mathbf{H}} \rangle}\\).

The verifier checks the inner product proof with \\(P\\) computed using the bottom row of the diagram,
which proves that the vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\) are computed correctly:
\\[
\begin{aligned}
  P &= -{\widetilde{e}} {\widetilde{B}} + x \cdot (A_I' + e \cdot A_I'') + x^2 \cdot (A_O' + e \cdot A_O'') - \langle \mathbf{1}, \mathbf{H}' \rangle - e \cdot \langle \mathbf{1}, \mathbf{H}'' \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot (S' + e \cdot S'') \\\\
\end{aligned}
\\]

If the inner product proof with such \\(P\\) is correct, the verifier is convinced of two facts:
that \\(t(x) = {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}\\), and
\\(\mathbf{l}(x), \mathbf{r}(x)\\) are correct.



Padding \\(\mathbf{l}(x)\\) and \\(\mathbf{r}(x)\\) for the inner product proof
-------------------------------------------------------------------------------

The above discussion did not have restrictions on the value \\(n\\).
However, the [inner product argument](../notes/index.html#inner-product-proof)
requires the input vectors to have power-of-two elements: \\(n^{+} = 2^k\\).
To resolve this mismatch, we need to specify how to pad vectors \\(\mathbf{l}(x), \mathbf{r}(x)\\)
and related commitments before we can use the inner product argument.

Our goal is to translate the _padding of the constraint system_ into the _padding of proof data_,
so we can keep the constraint system small and perform less computations in proving and verification.

We will use the following notation for the padding:

\\[
\begin{aligned}
                           n^{+} &= 2^{\lceil \log_2 n \rceil} \\\\
                      \mathbf{0} &= [0,...,0]
\end{aligned}
\\]

We start by padding the entire constraint system:
multipliers are padded with all-zero assignments \\(a\_{L,j}, a\_{R,j}, a\_{O,j}\\),
all-zero blinding factors \\(s\_{L,j}, s\_{R,j}\\),
and all-zero weights \\(W\_{R,i,j}, W\_{L,i,j}, W\_{O,i,j}\\),
for all constraints \\(i \in [0, q)\\) and all additional multipliers \\(j \in [n,n^{+})\\):

\\[
\begin{aligned}
\mathbf{a}\_L^{+} &= \mathbf{a}\_L \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{a}\_R^{+} &= \mathbf{a}\_R \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{a}\_O^{+} &= \mathbf{a}\_O \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{s}\_L^{+} &= \mathbf{s}\_L \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{s}\_R^{+} &= \mathbf{s}\_R \hspace{0.1cm} || \hspace{0.1cm} \mathbf{0} \\\\
\mathbf{W}\_L^{+} &= \mathbf{W}\_L \hspace{0.1cm} || \hspace{0.1cm} [\mathbf{0}, ..., \mathbf{0}] \\\\
\mathbf{W}\_R^{+} &= \mathbf{W}\_R \hspace{0.1cm} || \hspace{0.1cm} [\mathbf{0}, ..., \mathbf{0}] \\\\
\mathbf{W}\_O^{+} &= \mathbf{W}\_O \hspace{0.1cm} || \hspace{0.1cm} [\mathbf{0}, ..., \mathbf{0}] \\\\
\end{aligned}
\\]

As a result, we have to take larger slices of the vectors of generators \\(\mathbf{G},\mathbf{H}\\) and more powers of the challenge \\(y\\):

\\[
\begin{aligned}
\mathbf{G}^{+}     &= \mathbf{G}   \hspace{0.1cm} || \hspace{0.1cm} [G_n,...,G_{n^{+}-1}] \\\\
\mathbf{H}^{+}     &= \mathbf{H}   \hspace{0.1cm} || \hspace{0.1cm} [H_n,...,H_{n^{+}-1}] \\\\
\mathbf{y}^{n^{+}} &= \mathbf{y}^n \hspace{0.1cm} || \hspace{0.1cm} [y^n,...,y^{n^{+}-1}] \\\\
\end{aligned}
\\]

The low-level variables are padded with zeroes, so their commitments remain unchanged:

\\[
\begin{aligned}
A_I^{+} &= \widetilde{B} \cdot \tilde{a} + \langle \mathbf{G}^{+}, \mathbf{a}\_L^{+} \rangle + \langle \mathbf{H}^{+}, \mathbf{a}\_R^{+} \rangle \\\\
        &= \widetilde{B} \cdot \tilde{a} + \langle \mathbf{G}, \mathbf{a}\_L \rangle + \langle \mathbf{H}, \mathbf{a}\_R \rangle +
           \langle [G_n, ..., G_{n^{+}-1}], \mathbf{0} \rangle + \langle [H_n, ..., H_{n^{+}-1}], \mathbf{0} \rangle \\\\
    &= \widetilde{B} \cdot \tilde{a} + \langle \mathbf{G}, \mathbf{a}\_L \rangle + \langle \mathbf{H}, \mathbf{a}\_R \rangle + 
       0 \\\\
        &= A_I \\\\
\end{aligned}
\\]

Similarly, \\(A_O\\) and \\(S\\) are unchanged:

\\[
\begin{aligned}
A_O^{+} &= A_O \\\\
S^{+}   &= S
\end{aligned}
\\]

The flattened weight vectors \\(\mathbf{w}\_{L,R,O}\\) are padded with zeroes
because the corresponding weights are padded with zeroes:
\\[
\begin{aligned}
\mathbf{w}\_L^{+} &= z \mathbf{z}^q \cdot \mathbf{W}\_L^{+}  &{}={}& (z \mathbf{z}^q \cdot \mathbf{W}\_L) || (z \mathbf{z}^q \cdot \mathbf{0}) &{}={}& \mathbf{w}\_L || \mathbf{0}, \\\\
\mathbf{w}\_R^{+} &= z \mathbf{z}^q \cdot \mathbf{W}\_R^{+}  &{}={}& (z \mathbf{z}^q \cdot \mathbf{W}\_R) || (z \mathbf{z}^q \cdot \mathbf{0}) &{}={}& \mathbf{w}\_R || \mathbf{0}, \\\\
\mathbf{w}\_O^{+} &= z \mathbf{z}^q \cdot \mathbf{W}\_O^{+}  &{}={}& (z \mathbf{z}^q \cdot \mathbf{W}\_O) || (z \mathbf{z}^q \cdot \mathbf{0}) &{}={}& \mathbf{w}\_O || \mathbf{0}. \\\\
\end{aligned}
\\]

The \\(\delta(y,z)\\) remains unchanged because the padding weights are zeroes:

\\[
\begin{aligned}
\delta(y, z)^{+} &= \langle \mathbf{y}^{-n^{+}} \circ \mathbf{w}\_R^{+}, \mathbf{w}\_L^{+} \rangle \\\\
                 &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{w}\_L \rangle      +     \langle [y^n,...,y^{n^{+}-1}] \circ \mathbf{0}, \mathbf{0} \rangle \\\\
                 &= \langle \mathbf{y}^{-n} \circ \mathbf{w}\_R, \mathbf{w}\_L \rangle      +     0 \\\\
                 &= \delta(y, z)
\end{aligned}
\\]

Vector polynomial \\(\mathbf{l}(x)\\) is padded with zeroes:

\\[
\begin{aligned}
\mathbf{l}(x)^{+} &= \mathbf{a}\_L^{+} \cdot x + \mathbf{s}\_L^{+} \cdot x^3 + \mathbf{y}^{-n^{+}} \circ \mathbf{w}\_R^{+} \cdot x + \mathbf{a}\_O^{+} \cdot x^2 \\\\
                  &= \mathbf{a}\_L \cdot x + \mathbf{s}\_L \cdot x^3 + \mathbf{y}^{-n} \circ \mathbf{w}\_R \cdot x + \mathbf{a}\_O \cdot x^2 \\\\
                  &  \hspace{0.5cm} || \hspace{0.1cm} \mathbf{0} \cdot x + \mathbf{0} \cdot x^3 + [y^n,...,y^{n^{+}-1}] \circ \mathbf{0} \cdot x + \mathbf{0} \cdot x^2 \\\\
                  &= \mathbf{l}(x) || \mathbf{0} \\\\
\end{aligned}
\\]

Vector polynomial \\(\mathbf{r}(x)\\) is padded with additional (negated) powers of \\(y\\):

\\[
\begin{aligned}
\mathbf{r}(x)^{+} &= \mathbf{y}^{n^{+}} \circ \mathbf{a}\_R^{+} \cdot x + \mathbf{y}^{n^{+}} \circ \mathbf{s}\_R^{+} \cdot x^3 + \mathbf{w}\_L^{+} \cdot x - \mathbf{y}^{n^{+}} + \mathbf{w}\_O^{+} \\\\
                  &= \mathbf{y}^n \circ \mathbf{a}\_R \cdot x + \mathbf{y}^n \circ \mathbf{s}\_R \cdot x^3 + \mathbf{w}\_L \cdot x - \mathbf{y}^n + \mathbf{w}\_O \\\\
                  &  \hspace{0.5cm} || \hspace{0.1cm} [y^n,...,y^{n^{+}-1}] \circ \mathbf{0} \cdot x + [y^n,...,y^{n^{+}-1}] \circ \mathbf{0} \cdot x^3 + \mathbf{0} \cdot x - [y^n,...,y^{n^{+}-1}] + \mathbf{0} \\\\
                  &= \mathbf{r}(x) || [-y^n,...,-y^{n^{+}-1}]
\end{aligned}
\\]


The commitments to these vector polynomials are also padded (\\(W\_{L,R,O}\\) remain unchanged because the weights are padded with zeroes):

\\[
\begin{aligned}
  P^{+} &= -{\widetilde{e}} {\widetilde{B}} + x \cdot A_I + x^2 \cdot A_O - \langle \mathbf{1}, \mathbf{H}^{+} \rangle + W_L \cdot x + W_R \cdot x + W_O + x^3 \cdot S \\\\
        &= P - \langle \mathbf{1}, [H_n,...,H_{n^{+}-1}] \rangle
\end{aligned}
\\]

The inner product \\(t(x)\\) remains unchanged because the non-zero padding in the right vector gets multiplied with the zero padding in the left vector:

\\[
\begin{aligned}
t(x)^{+} &= {\langle {\mathbf{l}}(x)^{+}, {\mathbf{r}}(x)^{+} \rangle} \\\\
         &= {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} + {\langle \mathbf{0}, [y^n,...,y^{n^{+}-1}] \rangle} \\\\
         &= {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle} + 0 \\\\
         &= t(x)
\end{aligned}
\\]

This implies that the terms \\(t\_{0, 1, 2, 3, 4, 5, 6}\\) also remain unchanged.











Aggregated Range Proof
======================

The goal of an _aggregated range proof_ is to enable a group of parties to produce proofs of their individual statements
(individual range proofs for the corresponding value commitments), that can be aggregated in a more compact proof.
This is made efficient due to a logarithmic size of the inner-product protocol: an aggregated range proof for \\(m\\)
values is smaller than \\(m\\) individual range proofs.

The aggregation protocol is a multi-party computation protocol, involving \\(m\\) parties (one party per value) and one dealer, where the parties don't reveal their secrets to each other. The parties share their commitments with the dealer, and the dealer generates and returns challenge variables. The parties then share their proof shares with the dealer, and the dealer combines their shares to create an aggregated proof. 

The Bulletproofs paper outlines two versions of multi-party computation aggregation. In the first approach, the inner-product proof is performed by the dealer, which requires sending the vectors used for the inner-product to the dealer. In the second approach, the inner-product proof is performed using multi-party computation, which sends less data but requires one round for each iteration of the inner-product protocol. We chose to implement the first approach because it requires fewer round trips between parties, which outweighed the slight message size savings of the second approach. 

For more information on how the aggregation protocol works and is implemented, see the [protocol notes](../range_proof/index.html). 

The aggregated range proof has the same form as the individual range proof, in that the provers (the parties) still perform the same calculations to prove that \\(t(x) = \langle \mathbf{l}(x), \mathbf{r}(x) \rangle \\) and that \\(t_0, \mathbf{l}(x), \mathbf{r}(x)\\) are correct. The difference is that the challenge values are obtained from the dealer, which generates them by combining commitments from all the parties, and that the calculations of different parties are separated by different powers of the challenge scalars \\(y\\) and \\(z\\).

We will explain how one piece of the aggregated proof is generated for party \\(j\\), and then will show how all of the pieces for all of the \\(m\\) parties can be combined into one aggregated proof.

New notation for aggregated proofs
----------------------------------

The subscript \\({(j)}\\) denotes the \\(j\\)th party's share. For instance, \\(v_{(j)}\\) is the \\(v\\) value of the \\(j\\)th party; \\( \mathbf{a}\_{L, (j)}\\) is the \\( \mathbf{a}\_L \\) vector of the \\(j\\)th party; \\(\mathbf{l}\_{(0)}(x)\\) is the \\(\mathbf{l}(x)\\) polynomial of party \\(0\\). 

We use pythonic notation to denote slices of vectors, such that \\(\mathbf{G}\_{\[a:b\]} = [\mathbf{G}\_{a}, \mathbf{G}\_{a+1}, \dots, \mathbf{G}\_{b-1} ]\\).

\\({\mathbf{G}\_{(j)}}\\) is party \\(j\\)'s share of the generators \\({\mathbf{G}}\\), or \\({\mathbf{G}\_{[j\cdot n : (j+1)n]}}\\), and \\({\mathbf{H}'\_{(j)}}\\) is party \\(j\\)'s share of the generators \\({\mathbf{H}'}\\), or \\({\mathbf{H}'\_{[j\cdot n : (j+1)n]}}\\).

\\(z_{(j)}\\) is a scalar offset that is unique to each party \\(j\\), and is defined by \\(z_{(j)} = z^j\\). \\(\mathbf{y}^n\_{(j)}\\) is a length \\(n\\) vector offset that is unique to each party \\(j\\). It is a slice into vector \\(\mathbf{y}^{n \cdot m}\\), and is defined by \\(\mathbf{y}^n\_{(j)} = \mathbf{y}^{n \cdot m}\_{[j \cdot n : (j+1) \cdot n]} \\)



Proving range statements with bit vectors
-----------------------------------------

Party \\(j\\) begins with a secret value \\(v_{(j)}\\), and wishes to convince the verifier that \\(v_{(j)} \in [0, 2^n)\\) without revealing \\(v_{(j)}\\). 

We want to make statements about \\(v_{(j)}\\) using its bit vector representation, where the statements will be true if and only if \\(v_{(j)}\\) is actually in the expected range. We will not reproduce the steps or explanation here since it is the same as in the [proving range statements with bit vectors](index.html#proving-range-statements-with-bit-vectors) step of the single-value range proof. Here are the final statements for party \\(j\\):

\\[
\begin{aligned}
  {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{2}}^{n} \rangle} &= v_{(j)} \\\\
  {\mathbf{a}}\_{L, (j)} \circ {\mathbf{a}}\_{R, (j)} &= {\mathbf{0}} \\\\
  ({\mathbf{a}}\_{L, (j)} - {\mathbf{1}}) - {\mathbf{a}}\_{R, (j)} &= {\mathbf{0}}
\end{aligned}
\\]

Proving vectors of statements with a single statement
-----------------------------------------------------

We want to combine the above three statements into a single statement for party \\(j\\), as in the [proving vectors of statements](index.html#proving-vectors-of-statements-with-a-single-statement) step of the single-value range proof. We will additionally use offsets \\(\mathbf{y}^n\_{(j)}\\) and \\(z_{(j)}\\) that are unique to each party \\(j\\). Since these challenge values are independent for each party, we can later merge the per-party combined statements into one statement for all \\(m\\) parties.

First, we will combine each of the two vector-statements into a single statement using the verifier's choice of challenge value \\(y\\) that is shared across all parties, and offset by vector \\(\mathbf{y}^n\_{(j)}\\):

\\[
\begin{aligned}
  {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{2}}^{n} \rangle} &= v_{(j)} \\\\
  {\langle {\mathbf{a}}\_{L, (j)} - {\mathbf{1}} - {\mathbf{a}}\_{R, (j)}, {\mathbf{y}}^{n}\_{(j)} \rangle} &= 0 \\\\
  {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{a}}\_{R, (j)} \circ {\mathbf{y}}^{n}\_{(j)} \rangle} &= 0
\end{aligned}
\\]

The three resulting statements can then be combined in the same way,
using the verifier’s choice of challenge value \\(z\\) that is shared across all parties, and offset by scalar \\(z\_{(j)} \\) :
\\[
\begin{aligned}
z^{2} z\_{(j)}  \cdot v_{(j)} 
&= 
   z^{2} z\_{(j)}  \cdot {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{2}}^{n} \rangle} \\\\
     &+ z \cdot {\langle {\mathbf{a}}\_{L, (j)} - {\mathbf{1}} - {\mathbf{a}}\_{R, (j)}, {\mathbf{y}}^{n}\_{(j)}  \rangle} \\\\
         &+   {\langle {\mathbf{a}}\_{L, (j)}, {\mathbf{a}}\_{R, (j)} \circ {\mathbf{y}}^{n}\_{(j)} \rangle} 
\end{aligned}
\\]

Combining inner products
------------------------

We combine the terms in the preceding statement into a single inner product, using the same technique as in the single-value range proof. We will not reproduce the math here since it is the same as in the [combining inner products](index.html#combining-inner-products) step of the single-value proof. Here is the end result:

\\[
\begin{aligned}
 \delta_{(j)}(y,z) &= (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n}\_{(j)} \rangle} - z^{3} z_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n} \rangle}\\\\
 z^{2}z_{(j)} \cdot v_{(j)} + \delta_{(j)}(y,z) &= {\langle {\mathbf{a}}\_{L, (j)} - z {\mathbf{1}}, {\mathbf{y}}^{n}\_{(j)} \circ ({\mathbf{a}}\_{R, (j)} + z {\mathbf{1}}) + z^{2} z_{(j)} \cdot {\mathbf{2}}^{n} \rangle}
\end{aligned} 
\\]

Blinding the inner product
--------------------------

The prover chooses vectors of blinding factors \\( \mathbf{s}\_{L, (j)}, {\mathbf{s}}\_{R, (j)} \\), and uses them to construct the blinded vector polynomials \\(\mathbf{l}\_{(j)}(x), \mathbf{r}\_{(j)}(x)\\). We will not reproduce the steps or the explanation here since it is the same as in the [blinding the inner product](index.html#blinding-the-inner-product) step of the single-value proof. Here are the final equations for the vector polynomials:

\\[
\begin{aligned}
  {\mathbf{l}}\_{(j)}(x) &= ({\mathbf{a}}\_{L, (j)} + {\mathbf{s}}\_{L, (j)} x) - z {\mathbf{1}} & \in {\mathbb Z\_p}\[x\]^{n}  \\\\
  {\mathbf{r}}\_{(j)}(x) &= {\mathbf{y}}^{n}\_{(j)} \circ \left( ({\mathbf{a}}\_{R, (j)} + {\mathbf{s}}\_{R, (j)} x\right)  + z {\mathbf{1}}) + z^{2} z_{(j)} {\mathbf{2}}^{n} &\in {\mathbb Z\_p}\[x\]^{n} 
\end{aligned}
\\]

Proving that \\(t(x)\\) is correct
----------------------------------

Proving that \\(t\_{(j)}(x)\\) is correct means proving that
\\({\mathbf{l}}\_{(j)}(x)\\), \\({\mathbf{r}}\_{(j)}(x)\\) are correctly formed, and that
\\(t\_{(j)}(x) = {\langle {\mathbf{l}}\_{(j)}(x), {\mathbf{r}}\_{(j)}(x) \rangle}\\).

We can combine the statements about \\(t\_{(j)}(x)\\), \\({\mathbf{l}}\_{(j)}(x)\\), and \\({\mathbf{r}}\_{(j)}(x)\\) from all \\(m\\) parties in the following manner:

\\[
\begin{aligned}
  t(x) &= \sum_{j=0}^{m-1} t\_{(j)}(x)\\\\
  {\mathbf{l}}(x) &= {\mathbf{l}}\_{(0)}(x) || {\mathbf{l}}\_{(1)}(x) || \dots || {\mathbf{l}}\_{(m-1)}(x) \\\\
  {\mathbf{r}}(x) &= {\mathbf{r}}\_{(0)}(x) || {\mathbf{r}}\_{(1)}(x) || \dots || {\mathbf{r}}\_{(m-1)}(x) \\\\
\end{aligned}
\\]

We can add the \\(t_{(j)}(x)\\) values together to create \\(t(x)\\) instead of taking a random linear combination of \\(t_{(j)}(x)\\) values, because each \\(t_{(j)}(x)\\) is calculated with the \\(\mathbf{y}^n\_{(j)}\\) and \\(z_{(j)}\\) challenge variables that are unique to that party \\(j\\), so all of the \\(t_{(j)}(x)\\) values will be offset from one another.

Now instead of having to do \\(m\\) individual checks to prove that \\(t_{(j)}(x)\\), \\({\mathbf{l}}\_{(j)}(x)\\), and \\({\mathbf{r}}\_{(j)}(x)\\) for all parties \\(j\\) are correct, we can do the verification with one check:

\\[
\begin{aligned}
  t(x) \stackrel{?}{=} {\langle {\mathbf{l}}(x), {\mathbf{r}}(x) \rangle}
\end{aligned}
\\]

We can do this check using the [inner product proof](index.html#inner-product-proof), in the same way the single-value range proof uses the inner product proof.

Proving that \\(t_0\\) is correct
---------------------------------

Proving that \\(t\_{0, (j)}\\) is correct requires first creating commitments to the variables, and then proving a relation over the commitments. For an explanation of how the commitments are created and how the relation is derived, see the [proving that \\(t_0\\) is correct](index.html#proving-that-t_0-is-correct) step of the single-value range proof. The statement each party wants to prove is:

\\[
\begin{aligned}
  t\_{(j)}(x) B + {\tilde{t}}\_{(j)}(x) {\widetilde{B}} \stackrel{?}{=} z^2 z\_{(j)} V_{(j)} + \delta\_{(j)}(y,z) B + x T\_{1, (j)} + x^{2} T\_{2, (j)}\\\\
  \delta\_{(j)}(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n}\_{(j)} \rangle} - z^{3} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n} \rangle}
\end{aligned}
\\]

If we combine all of the statements about \\(t\_{0, (j)}\\) from all of the \\(j\\) parties by adding them together, then we get:

\\[
\begin{aligned}
  \sum_{j=0}^{m-1}t_{(j)}(x) B + \sum_{j=0}^{m-1}{\tilde{t}}\_{(j)}(x) {\widetilde{B}} \stackrel{?}{=} z^2 \sum_{j=0}^{m-1} z_{(j)} V_{(j)} + \sum_{j=0}^{m-1} \delta_{(j)}(y,z) B + x \sum_{j=0}^{m-1} T\_{1, (j)} + x^{2} \sum_{j=0}^{m-1} T\_{2, (j)}
\end{aligned}
\\]

We can combine the values and commitments by summing them directly. We can do this instead of having to take a random linear combination, because each party's values and commitments are already offset by the values \\(\mathbf{y}^n\_{(j)}\\) and \\(z_{(j)}\\) that are unique to that party.

\\[
\begin{aligned}
  t(x) &= \sum_{j=0}^{m-1} t\_{(j)}(x)\\\\
  {\tilde{t}}(x) &= \sum_{j=0}^{m-1}{\tilde{t}}\_{(j)}(x)\\\\
  T_1 &= \sum_{j=0}^{m-1} T_{1, (j)}\\\\
  T_2 &= \sum_{j=0}^{m-1} T_{2, (j)}\\\\
  \delta(y,z) &= \sum_{j=0}^{m-1} \delta\_{(j)}(y,z)\\\\
\end{aligned}
\\]

We can plug the equation for \\(\delta_{(j)}(y,z)\\) into the calculation for \\(\delta(y,z)\\):

\\[
\begin{aligned}
  \delta(y, z) &= (z - z^{2}) \cdot \sum_{j=0}^{m-1} {\langle {\mathbf{1}}, {\mathbf{y}}^{n}\_{(j)} \rangle} - z^{3} \sum_{j=0}^{m-1} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle}\\\\
\end{aligned}
\\]

Since we know that \\(\mathbf{y}^n\_{(j)} = \mathbf{y}^{n \cdot m}\_{[j \cdot n : (j+1) \cdot n]} \\), we can simplify \\(\delta(y, z)\\):

\\[
\begin{aligned}
  \delta(y, z) &= (z - z^{2}) \cdot (
    {\langle {\mathbf{1}}, \mathbf{y}^{n \cdot m}\_{[0 : n]} \rangle + 
    \langle {\mathbf{1}}, \mathbf{y}^{n \cdot m}\_{[n : 2 \cdot n]} \rangle + 
    \dots +
    \langle {\mathbf{1}}, \mathbf{y}^{n \cdot m}\_{[(m-1) \cdot n : m \cdot n]} \rangle}) -
  z^{3} \sum_{j=0}^{m-1} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle} \\\\
  &= (z - z^{2}) \cdot {\langle {\mathbf{1}}, \mathbf{y}^{n \cdot m} \rangle} - z^{3} \sum_{j=0}^{m-1} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle} \\\\
\end{aligned}
\\]


Now instead of having to do \\(m\\) individual checks to prove that \\(t\_{0, (j)}\\) for all parties \\(j\\) are correct, we can do the verification with one check using the combined values:

\\[
\begin{aligned}
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} z^2 \sum_{j=0}^{m-1} z\_{(j)} V_{(j)} + \delta(y,z) B + x T\_{1} + x^{2} T\_{2},\\\\
  \delta(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n \cdot m} \rangle} - z^{3} \sum_{j=0}^{m-1} z\_{(j)} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle}\\\\
\end{aligned}
\\]

Since we know that \\(z\_{(j)} = z^j\\), we can rewrite the equation as follows:

\\[
\begin{aligned}
  t(x) B + {\tilde{t}}(x) {\widetilde{B}} \stackrel{?}{=} \sum_{j=0}^{m-1} z^{j+2} V_{(j)} + \delta(y,z) B + x T\_{1} + x^{2} T\_{2},\\\\
  \delta(y,z) = (z - z^{2}) \cdot {\langle {\mathbf{1}}, {\mathbf{y}}^{n \cdot m} \rangle} - \sum_{j=0}^{m-1} z^{j+3} \cdot {\langle {\mathbf{1}}, {\mathbf{2}}^{n \cdot m} \rangle}\\\\
\end{aligned}
\\]

Proving that \\({\mathbf{l}}(x)\\), \\({\mathbf{r}}(x)\\) are correct
---------------------------------------------------------------------

Proving that \\({\mathbf{l}}\_{(j)}(x)\\), \\({\mathbf{r}}\_{(j)}(x)\\) are correct requires first creating commitments to the variables, and then proving a relation over the commitments. For an explanation of how the commitments are created and how the relation is derived, see the [proving that \\({\mathbf{l}}(x)\\), \\({\mathbf{r}}(x)\\) are correct](index.html#proving-that-mathbflx-mathbfrx-are-correct) step of the single-value range proof. The statement that each party wants to prove is:

\\[
\begin{aligned}
  {\langle {\mathbf{l}}\_{(j)}(x), {\mathbf{G}\_{(j)}} \rangle} + {\langle {\mathbf{r}}\_{(j)}(x), {\mathbf{H}'}\_{(j)} \rangle} \stackrel{?}{=} -{\widetilde{e}\_{(j)}} {\widetilde{B}} + A_{(j)} + x S_{(j)} - z{\langle {\mathbf{1}}, {\mathbf{G}\_{(j)}} \rangle} + {\langle z \mathbf{y}^{n}\_{(j)}  + z^2 z_{(j)} {\mathbf{2}}^n, {\mathbf{H}'}\_{(j)} \rangle} 
\end{aligned}
\\]

If we combine all of the statements about \\({\mathbf{l}}(x)\\), \\({\mathbf{r}}(x)\\) from all the \\(j\\) parties by adding them together, then we get:

\\[
\begin{aligned}
  \sum_{j=0}^{m-1}{\langle {\mathbf{l}}\_{(j)}(x), {\mathbf{G}\_{(j)}} \rangle} + 
  \sum_{j=0}^{m-1}{\langle {\mathbf{r}}\_{(j)}(x), {\mathbf{H}'}\_{(j)} \rangle} \stackrel{?}{=} 
  -\sum_{j=0}^{m-1}{\widetilde{e}\_{(j)}} {\widetilde{B}} + 
  \sum_{j=0}^{m-1}A_{(j)} + x \sum_{j=0}^{m-1}S_{(j)} - 
  z \sum_{j=0}^{m-1}{\langle {\mathbf{1}}, {\mathbf{G}\_{(j)}} \rangle} + 
  \sum_{j=0}^{m-1}{\langle z {\mathbf{y}^n_{(j)}} + z^2 z_{(j)} {\mathbf{2}}^n, {\mathbf{H}'\_{(j)}} \rangle}
\end{aligned}
\\]

We can simplify this expression by making a few observations. We know that:

\\[
\begin{aligned}
  &{\mathbf{l}}(x)     &{}&=&{}& {\mathbf{l}}\_{(0)}(x) & {} &||& {} & {\mathbf{l}}\_{(1)}(x) & {} &||& {} & \dots & {} &||& {} & {\mathbf{l}}\_{(m-1)}(x) \\\\
  &{\mathbf{r}}(x)     &{}&=&{}& {\mathbf{r}}\_{(0)}(x) & {} &||& {} & {\mathbf{r}}\_{(1)}(x) & {} &||& {} & \dots & {} &||& {} & {\mathbf{r}}\_{(m-1)}(x) \\\\
  &{\mathbf{G}}        &{}&=&{}& {\mathbf{G}}\_{(0)}    & {} &||& {} & {\mathbf{G}}\_{(1)}    & {} &||& {} & \dots & {} &||& {} & {\mathbf{G}}\_{(m-1)} \\\\
  &{\mathbf{H}'}       &{}&=&{}& {\mathbf{H}'}\_{(0)}   & {} &||& {} & {\mathbf{H}'}\_{(1)}   & {} &||& {} & \dots & {} &||& {} & {\mathbf{H}'}\_{(m-1)} 
\end{aligned}
\\]
\\[
\begin{aligned}
  \mathbf{y}^n\_{(j)} &= \mathbf{y}^{n \cdot m}\_{[j \cdot n : (j+1) \cdot n]} \\\\
  z_{(j)}             &= z^j
\end{aligned}
\\]

Therefore, we can simplify the following statements:

\\[
\begin{aligned}
  \sum_{j=0}^{m-1}{\langle {\mathbf{l}}\_{(j)}(x), {\mathbf{G}\_{(j)}} \rangle} &= {\langle {\mathbf{l}}\_{(0)}(x), {\mathbf{G}}\_{(0)} \rangle} + 
    {\langle {\mathbf{l}}\_{(1)}(x), {\mathbf{G}}\_{(1)} \rangle} + 
    \dots + 
    {\langle {\mathbf{l}}\_{(m-1)}(x), {\mathbf{G}}\_{(m-1)} \rangle}\\\\
  &= {\langle {\mathbf{l}}\_{(0)}(x) || {\mathbf{l}}\_{(1)}(x) || \dots || {\mathbf{l}}\_{(m-1)}(x), {\mathbf{G}}\_{(0)} || {\mathbf{G}}\_{(1)} || \dots || {\mathbf{G}}\_{(m-1)} \rangle} \\\\
  &= {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} \\\\
  \sum_{j=0}^{m-1}{\langle {\mathbf{r}}\_{(j)}(x), {\mathbf{H}'}\_{(j)} \rangle} 
  &= {\langle {\mathbf{r}}\_{(0)}(x), {\mathbf{H}'}\_{(0)} \rangle} + 
    {\langle {\mathbf{r}}\_{(1)}(x), {\mathbf{H}'}\_{(1)} \rangle} + 
    \dots + 
    {\langle {\mathbf{r}}\_{(m-1)}(x), {\mathbf{H}'}\_{(m-1)} \rangle} \\\\
  &= {\langle {\mathbf{r}}\_{(0)}(x) || {\mathbf{r}}\_{(1)}(x) || \dots || {\mathbf{r}}\_{(m-1)}(x), {\mathbf{H}'}\_{(0)} || {\mathbf{H}'}\_{(1)} || \dots || {\mathbf{H}'}\_{(m-1)}  \rangle}\\\\
  &= {\langle  {\mathbf{r}}(x), {\mathbf{H}'} \rangle}
\end{aligned}
\\]

We can combine the values and commitments from all the \\(m\\) parties by summing them directly:

\\[
\begin{aligned}
  {\widetilde{e}} &= \sum_{j=0}^{m-1} {\widetilde{e}\_{(j)}} \\\\
  A &= \sum_{j=0}^{m-1} A_{(j)} \\\\
  S &= \sum_{j=0}^{m-1} S_{(j)} \\\\
\end{aligned}
\\]

With these observations, we can simplify the combined \\(m\\)-party statement about \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) into:

\\[
\begin{aligned}
  {\langle {\mathbf{l}}(x), {\mathbf{G}} \rangle} + {\langle {\mathbf{r}}(x), {\mathbf{H}'} \rangle} \stackrel{?}{=} -{\widetilde{e}} {\widetilde{B}} + A + x S - z{\langle {\mathbf{1}}, {\mathbf{G}} \rangle} + z{\langle {\mathbf{y}^{n \cdot m}}, {\mathbf{H}'} \rangle} + \sum_{j=0}^{m-1} {\langle z^{j+2} \cdot {\mathbf{2}}^n, {\mathbf{H}'}\_{[j \cdot n : (j+1) \cdot n]} \rangle} 
\end{aligned}
\\]






Aggregated Constraint System Proof
==================================

(Under development.)

Range proofs can be naturally aggregated keeping each statement independent.
For constraint systems proofs, two options exist:

1. each party can prove satisfiability of **their own constraint system** (systems can be distinct);
2. parties can collaborate to prove satisfiability of a **single constraint system** without having to reveal secrets to each other.

The aggregation of distinct proofs can be done in a very similar way
to the aggregation of range proofs and is useful purely for the space savings (just like with the range proofs).

The collaborative construction of a proof of a single constraint system requires a different framework,
but is very useful for computations that increase privacy for each party, e.g. by allowing them to mix their inputs,
while not making them share secrets between each other.

