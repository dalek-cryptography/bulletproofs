This module contains notes on how and why the inner product proof protocol works.

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
  {\mathbf{a}}^{(k-1)} &= {\mathbf{a}}\_{\operatorname{lo}} \cdot u\_k        + u^{-1}\_k \cdot {\mathbf{a}}\_{\operatorname{hi}} \\\\
  {\mathbf{b}}^{(k-1)} &= {\mathbf{b}}\_{\operatorname{lo}} \cdot u^{-1}\_k   + u\_k \cdot {\mathbf{b}}\_{\operatorname{hi}} \\\\
  {\mathbf{G}}^{(k-1)} &= {\mathbf{G}}\_{\operatorname{lo}} \cdot u^{-1}\_k   + u\_k \cdot {\mathbf{G}}\_{\operatorname{hi}} \\\\
  {\mathbf{H}}^{(k-1)} &= {\mathbf{H}}\_{\operatorname{lo}} \cdot u\_k        + u^{-1}\_k \cdot {\mathbf{H}}\_{\operatorname{hi}}
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
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_{\operatorname{lo}} \cdot u\_k   + u\_k^{-1} \cdot {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{G}}\_{\operatorname{lo}} \cdot u^{-1}\_k + u\_k \cdot {\mathbf{G}}\_{\operatorname{hi}}      \rangle} + \\\\
             &&  &{\langle {\mathbf{b}}\_{\operatorname{lo}} \cdot u^{-1}\_k  + u\_k \cdot {\mathbf{b}}\_{\operatorname{hi}},      {\mathbf{H}}\_{\operatorname{lo}} \cdot u\_k      + u^{-1}\_k \cdot {\mathbf{H}}\_{\operatorname{hi}} \rangle} + \\\\
             &&  &{\langle {\mathbf{a}}\_{\operatorname{lo}} \cdot u\_k       + u^{-1}\_k \cdot {\mathbf{a}}\_{\operatorname{hi}},      {\mathbf{b}}\_{\operatorname{lo}} \cdot u^{-1}\_k + u\_k \cdot {\mathbf{b}}\_{\operatorname{hi}}      \rangle} \cdot Q
\end{aligned}
\\]
Breaking down in simpler products:
\\[
\begin{aligned}
    P\_{k-1} &{}={}& &{\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{G}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{G}}\_{\operatorname{hi}} \rangle} &{}+{}& u\_k^2 {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{G}}\_{\operatorname{hi}} \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{G}}\_{\operatorname{lo}} \rangle} + \\\\
       &&      &{\langle {\mathbf{b}}\_{\operatorname{lo}}, {\mathbf{H}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{b}}\_{\operatorname{hi}}, {\mathbf{H}}\_{\operatorname{hi}} \rangle} &{}+{}& u^2\_k {\langle {\mathbf{b}}\_{\operatorname{hi}}, {\mathbf{H}}\_{\operatorname{lo}} \rangle} + u^{-2}\_k {\langle {\mathbf{b}}\_{\operatorname{lo}}, {\mathbf{H}}\_{\operatorname{hi}} \rangle} + \\\\
       &&      &({\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{b}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{b}}\_{\operatorname{hi}} \rangle})\cdot Q &{}+{}& (u^2\_k {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{b}}\_{\operatorname{hi}} \rangle} + u^{-2}\_k {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{b}}\_{\operatorname{lo}} \rangle}) \cdot Q
\end{aligned}
\\]
We now see that the left two columns in the above equation is the
definition of \\(P\_k\\), while various cross terms on the right are
separated from \\(P\_k\\) by an indeterminate variable \\(u\_k\\). Let’s group all
terms with \\(u^2\_k\\) as \\(L\_k\\) and all terms with \\(u^{-2}\_k\\) as \\(R\_k\\):
\\[
\begin{aligned}
    P\_{k-1} &= P\_k + u^2\_k \cdot L\_k + u^{-2}\_k \cdot R\_k\\\\
    L\_k  &= {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{G}}\_{\operatorname{hi}} \rangle} + {\langle {\mathbf{b}}\_{\operatorname{hi}}, {\mathbf{H}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{lo}}, {\mathbf{b}}\_{\operatorname{hi}} \rangle} \cdot Q\\\\
    R\_k  &= {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{G}}\_{\operatorname{lo}} \rangle} + {\langle {\mathbf{b}}\_{\operatorname{lo}}, {\mathbf{H}}\_{\operatorname{hi}} \rangle} + {\langle {\mathbf{a}}\_{\operatorname{hi}}, {\mathbf{b}}\_{\operatorname{lo}} \rangle} \cdot Q
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
