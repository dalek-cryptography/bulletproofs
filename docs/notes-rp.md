This module contains notes on how and why range proofs work.

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
the right, and non-secret terms factored out. Let's call the left-hand side of the single inner product equation "unblinded" \\({\mathbf{l}(x)}\\) and the right-hand side "unblinded" \\({\mathbf{r}(x)}\\), such that 
\\[
\begin{aligned}
\text{unblinded } \mathbf{l}(x) &= {\mathbf{a}}\_{L} - z {\mathbf{1}} \\\\
\text{unblinded } \mathbf{r}(x) &= {\mathbf{y}}^{n} \circ ({\mathbf{a}}\_{R} + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} \\\\
z^{2}v + \delta(y,z) &= {\langle \text{unblinded } \mathbf{l}(x), \text{unblinded } \mathbf{r}(x) \rangle}
\end{aligned}
\\]

Blinding the inner product
--------------------------

The prover cannot send the left and right vectors in
the single inner-product equation (unblinded \\({\mathbf{l}(x)}\\) and \\({\mathbf{r}(x)}\\)) to the verifier without revealing information
about the value \\(v\\), and since the inner-product argument is not
zero-knowledge, they cannot be used there either.

Instead, the prover chooses vectors of blinding factors
\\[
{\mathbf{s}}\_{L}, {\mathbf{s}}\_{R} \\;{\xleftarrow{\\$}}\\; {\mathbb Z\_p}^{n},
\\]
and uses them to construct blinded vector polynomials from the unblinded vector polynomials \\({\mathbf{l}(x)}\\) and \\({\mathbf{r}(x)}\\):
\\[
\begin{aligned}
  {\mathbf{l}}(x) &= {\mathbf{l}}\_{0} + {\mathbf{l}}\_{1} x = ({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x) - z {\mathbf{1}} & \in {\mathbb Z\_p}\[x\]^{n}  \\\\
  {\mathbf{r}}(x) &= {\mathbf{r}}\_{0} + {\mathbf{r}}\_{1} x = {\mathbf{y}}^{n} \circ \left( ({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\right)  + z {\mathbf{1}}) + z^{2} {\mathbf{2}}^{n} &\in {\mathbb Z\_p}\[x\]^{n} 
\end{aligned}
\\]
The "blinded" \\({\mathbf{l}}(x)\\) and \\({\mathbf{r}}(x)\\) have \\({\mathbf{a}}\_{L}\\), \\({\mathbf{a}}\_{R}\\) replaced by blinded terms \\({\mathbf{a}}\_{L} + {\mathbf{s}}\_{L} x\\),
\\({\mathbf{a}}\_{R} + {\mathbf{s}}\_{R} x\\). The \\({\mathbf{l}}\_{0}\\) and \\({\mathbf{r}}\_{0}\\) terms represent the degree-zero terms of the polynomial with respect to \\(x\\), and the \\({\mathbf{l}}\_{1}\\) and \\({\mathbf{r}}\_{1}\\) terms represent the degree-one terms. Notice that since only the
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

Aggregated Range Proof
======================

The goal of an _aggregated range proof_ is to enable a group of parties to produce proofs of their individual statements
(individual range proofs for the corresponding value commitments), that can be aggregated in a more compact proof.
This is made efficient due to a logarithmic size of the inner-product protocol: an aggregated range proof for \\(m\\)
values is smaller than \\(m\\) individual range proofs.

The aggregation protocol is a multi-party computation protocol, involving \\(m\\) parties (one party per value) and one dealer, where the parties don't reveal their secrets to each other. The parties share their commitments with the dealer, and the dealer generates and returns challenge variables. The parties then share their proof shares with the dealer, and the dealer combines their shares to create an aggregated proof. 

The Bulletproofs paper outlines two versions of multi-party computation aggregation. In the first approach, the inner-product proof is performed by the dealer, which requires sending the vectors used for the inner-product to the dealer. In the second approach, the inner-product proof is performed using multi-party computation, which sends less data but requires one round for each iteration of the inner-product protocol. We chose to implement the first approach because it requires fewer round trips between parties, which outweighed the slight message size savings of the second approach. 

For more information on how the aggregation protocol works and is implemented, see the [protocol notes](::range_proof). 

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
