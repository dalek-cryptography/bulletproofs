This module contains notes on how and why Bulletproofs work.

These notes are organized as follows:

Table of Contents
=================

These notes explain how and why the proofs work:

* [Inner product proof](::notes::inner_product_proof)
* [Range proof](::notes::range_proof)
* [Rank-1 constraint system proof](::notes::r1cs_proof)

The description of what the protocols actually do is contained in these notes:

* [`range_proof`](::range_proof): aggregated range proof protocol.
* [`range_proof_mpc`](::range_proof_mpc): multi-party API for range proof aggregation.
* [`inner_product_proof`](::inner_product_proof): inner product argument protocol.
* [`r1cs`](::r1cs::notes): constraint system proof protocol.

The types from the above modules are publicly re-exported from the crate root,
so that the external documentation describes how to use the API, while the internal
documentation describes how it works.

(FIXME Streamline module structure?)

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
