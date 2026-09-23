# Mathematical synopsis, part I: foundations, simplex measure, one complex variable

This document and its two companions describe the mathematical content of the project for
mathematicians. Lean-specific matters (module layout, namespaces, tactic proofs) are kept in the
background; the emphasis is on definitions, theorems and hypotheses as a mathematician would
state them, and on what is new relative to Mathlib.

* Part I (this file): the general support libraries, the measure theory of the standard simplex,
  and single-variable complex analysis.
* [Part II](SYNOPSIS_SCV.md): several complex variables.
* [Part III](SYNOPSIS_CARLSON.md): Dirichlet integrals, Dirichlet averages, and Carlson's special
  functions.

The order of presentation follows the dependency order of the code: every library is described
after the libraries it imports. The nine libraries and their dependencies are

| Library | Depends on | Size |
| --- | --- | --- |
| `Algebra` | Mathlib | 1 file |
| `Topology` | Mathlib | 7 files |
| `Analysis` | Mathlib | 19 files |
| `Pochhammer` | Mathlib | 10 files |
| `StdSimplexMeasure` | `Pochhammer` | 32 files |
| `ComplexAnalysis` | `Analysis`, `Topology` | 60 files |
| `SeveralComplexVariables` | `Analysis`, `Topology`, `ComplexAnalysis` | 133 files |
| `Dirichlet` | all of the above except `Algebra` | 50 files |
| `Carlson` | all of the above | 97 files |

The whole project is written against a pinned Mathlib (the Lean 4 mathematical library, release
v4.34.0). "New" below always means: not available in that Mathlib release, as far as the authors
could determine. Where the project reproves a Mathlib result in a more general form (typically
Banach-valued instead of scalar-valued, or with fewer hypotheses), this is said explicitly.
Conversely, wherever a Mathlib theorem is used as a black box, this is also indicated; the
project is meant to be read as an extension of Mathlib, not as a replacement for it.

All results are fully proved: the project contains no unproved statements outside a separate
statement file, and no additional axioms.

## Conventions

Throughout, $\mathbb C^n$ and more generally $\mathbb C^{I}$, for a finite index set $I$, carry
the supremum norm $\|z\|_\infty = \max_i |z_i|$ unless stated otherwise; in particular
"balls" in coordinate spaces are polydiscs. The index set may be empty; the code is careful about
the degenerate cases $|I| = 0$ and $|I| = 1$, and the synopsis mentions them where they matter.

"Holomorphic" means complex Fréchet-differentiable on an open set; "analytic" means locally given
by a convergent power series. In finite dimension the two notions coincide (this is itself one of
the theorems, see Part II). Target spaces $F$ are complex Banach spaces unless stated
otherwise.

The principal branch of $w^t$, of $\log w$ and of related functions is always used; the *slit
plane* is $\mathbb C \setminus (-\infty, 0]$.

The *standard simplex* on a finite index set $I$ is
$$E_I = \Bigl\{u \in \mathbb R^{I} : u_i \ge 0,\ \sum_i u_i = 1\Bigr\},$$
its (relative) interior is the set with all $u_i > 0$, and the *solid simplex* of radius $r$ is
$\{x \in \mathbb R^I : x_i \ge 0, \sum_i x_i \le r\}$.

---

## I.1 General algebra

**Denominator closure.** Let $A$ be an integral domain and $M$ an $A$-module. For a submodule
$P \subseteq M$ the *denominator closure* is
$$\overline P = \{\,v \in M : d v \in P \text{ for some } d \in A \setminus \{0\}\,\}.$$
It is a submodule, contains $P$, and is closed under cancelling nonzero scalars. If a finite
linear relation $\sum_{j \in s} c_j v_j = 0$ has $c_i \neq 0$ and all $v_j$ with $j \ne i$ in
$\overline P$, then $v_i \in \overline P$. Finally, a vector in the denominator closure of a
finitely generated submodule satisfies a linear relation over $A$ with a nonzero coefficient.

This small module packages the "clear denominators" step that turns Carlson's rational-coefficient
relations between associated R-functions into polynomial relations valid everywhere (Part III).
It is not in Mathlib.

## I.2 General topology

Small additions to Mathlib's topology library, all with elementary statements:

* **Gluing with locally constant differences.** On a simply connected, locally path connected
  space, given an open cover and functions $f_i$ on the members with values in an additive
  group, such that each difference $f_i - f_j$ is locally constant on overlaps, there is a global
  function agreeing with each $f_i$ up to a constant on its member. (The proof builds the discrete
  covering bundle defined by the differences and uses simple connectedness.) This is the
  topological core of the existence of global primitives and logarithms in Part I.3 below.
* Compact exhaustions of open subsets of locally compact second countable spaces.
* Frontier and complement lemmas: a frontier point of an open set is not in the set; an open
  preconnected set is a component of the complement of its frontier; connectedness of the
  complement of a closed set from connectedness of an exterior neighborhood.
* Graphs defined by equations: uniqueness of solution maps and the projection homeomorphism from
  a zero set to the parameter domain, without differentiability.
* First exit time of a path from an open set.
* Baire-category boundedness: a separately continuous function on a product with compact second
  factor is uniformly bounded on some open cylinder.
* Nonnegative multiples of upper semicontinuous functions are upper semicontinuous.

## I.3 General analysis

This library contains real and functional analysis extracted from the complex-analytic
developments, all depending only on Mathlib.

**Integration.**

* Tonelli for finite products: $\int \prod_i g_i(x_i)\,d\mu = \prod_i \int g_i\,d\mu_i$ for
  nonnegative measurable $g_i$ on a finite dependent product of measure spaces (possibly empty
  index).
* Differentiation of compactly weighted parametric integrals: if $K$ is compact, $w$ is
  integrable on $K$ (possibly singular), and $(x, a) \mapsto H(x, a)$ is jointly continuous
  together with its Fréchet derivative in $x$, then $x \mapsto \int_K w(a) H(x, a)\,d\mu(a)$ is
  Fréchet differentiable with derivative obtained under the integral.
* Reciprocal substitution $x = u^{-1}$ between $(a, \infty)$ and $(0, a^{-1})$ for Bochner
  integrals and integrability, with the Jacobian $u^{-2}$.
* Uniform control of tails: a family dominated on a half-line by one integrable function has
  uniformly vanishing tails; for a power-decay majorant $C x^{-p}$, $p > 1$, the tail beyond
  $R$ is bounded by $C R^{1-p}/(p-1)$.

**Curve integrals.** For Mathlib's curve integral of a one-form $\omega$ along a path
$\gamma$ in a real or complex normed space:

* Fundamental theorem: if $\omega = dF$ for a Banach-valued potential $F$ along a
  differentiable path along which $\omega$ is integrable, then $\int_\gamma \omega =
  F(\gamma(1)) - F(\gamma(0))$; for continuous $\omega$ on a $C^1$ path integrability is
  automatic.
* Pullback: mapping a differentiable path through a differentiable map pulls back the one-form by
  composition with the derivative, as an identity of (totalized) curve integrals.
* Improper integrals of exact forms on half-lines and open intervals: the integral equals the
  difference of the limiting potential values; limits of finite curve integrals require only
  convergence of the endpoint potentials.
* Norm bounds $\bigl\|\int_\gamma \omega\bigr\| \le \sup\|\omega\| \cdot \int \|\gamma'\|$, and
  vanishing of integrals along families of connecting paths when the product of the form bound
  and the speed tends to zero; in particular power decay with exponent greater than one suffices
  when speeds grow at most linearly in the radius.

**The Gamma integral with a complex rate.** For $\operatorname{Re} a > 0$ and
$\operatorname{Re} w > 0$,
$$\int_0^\infty y^{a-1} e^{-yw}\,dy = w^{-a}\,\Gamma(a)$$
with the principal power. Mathlib has this for real $w > 0$; the project supplies the kernel
bounds, integrability, differentiation under the integral in $w$, holomorphy in $w$ on the right
half-plane, and the evaluation by analytic continuation from the real ray.

**Function spaces of holomorphic maps.** For an open subset $U$ of a complex normed space $E$
and a Banach space $F$, the holomorphic maps $U \to F$ form a subspace $\mathcal O(U, F)$ of the
continuous maps with the compact-open topology; convergence in this space is locally uniform
convergence and point evaluation is continuous. The Montel and Vitali arguments are proved once
here, taking closedness of $\mathcal O(U, F)$ and a "uniqueness set" as inputs, so that the
one-variable and several-variable theories can both use them:

* a family bounded on each compact subset is equicontinuous (Schwarz estimate);
* if moreover $\mathcal O(U,F)$ is closed and $F$ is finite dimensional, the family has compact
  closure (Arzelà–Ascoli), hence every sequence has a locally uniformly convergent subsequence;
* a bounded-on-compacts sequence converging on a uniqueness set converges locally uniformly on
  $U$ (Vitali).

**Open mapping.** A surjective continuous linear map from a complete metrizable topological
vector space to a Hausdorff metrizable Baire vector space is open. Mathlib has the Banach-space
version; here the metrics need not come from norms. This is used for restriction isomorphisms of
holomorphic function spaces.

**Miscellaneous.** Connectedness of spherical shells and exteriors of balls in real dimension at
least two; path-connectedness of the set of configurations whose convex hull stays in a
path-connected set; the diagonal chain rule $\frac{d}{dt} g(t, t)$; a uniform second-order Taylor
bound for $C^2$ maps on real normed spaces; geometric majorant lemmas; facts about continuous
linear functionals (a nonzero functional takes the value $1$; inclusion of negative half-spaces
forces positive proportionality).

## I.4 Pochhammer symbols, Gamma, beta, and Mellin transforms

Notation: $(a)_n = a(a+1)\cdots(a+n-1)$ is the rising factorial, Mathlib's
`ascPochhammer`.

**Algebraic identities**, all division-free and valid at zeros of the symbols:
$(a)_{m+n} = (a)_m (a+m)_n$; $(a)_{2n} = 4^n (a/2)_n ((a+1)/2)_n$; reflection identities such
as $(-a-n+1)_n = (-1)^n (a)_n$; and the Chu–Vandermonde identities for rising factorials,
$(a+b)_n = \sum_k \binom nk (a)_k (b)_{n-k}$ and the multinomial form for finite sums. Mathlib
records Chu–Vandermonde only for falling factorials.

**Estimates.** $|(a)_n| \le (|a|)_n$; $|(a)_n| \le n!\,(1+|a|)^n$; $(a)_n \ne 0$ when
$\operatorname{Re} a > 0$; comparison of $(1/2)_n$ with factorials.

**Binomial series.** $\sum_{n \ge 0} \frac{(a)_n}{n!}\, t^n = (1-t)^{-a}$ for $|t| < 1$ and
complex $a$, with absolute convergence.

**Gamma identities.** $\frac{1}{\Gamma(w)} = \frac{(w)_n}{\Gamma(w+n)}$ for all complex $w$
(this is the pole-free form of $\Gamma(w+n) = (w)_n \Gamma(w)$); the predicate
"$w$ is not a nonpositive integer" (Carlson's Gamma-regularity) with its stability under
positive integer shifts and nonvanishing of $(w)_n$; and uniform bounds
$$\sup_{w \in K}\Bigl|\frac{1}{\Gamma(w+n)}\Bigr| \le \frac{C_K}{n!^{\,1-\varepsilon}}$$
type decay estimates on compact sets $K$, used to control R-polynomial series in Part III.

**The Pochhammer transform.** The linear automorphism of the polynomial ring $R[X]$ sending
$X^n \mapsto (X)_n$, its inverse in terms of Stirling numbers of the second kind, the
coefficient formula in terms of Stirling numbers of the first kind (DLMF 26.8.7, 26.8.10,
26.8.39, adapted to rising factorials), preservation of degree and leading coefficient, and the
interaction with multiplication by $X$.

**Beta integrals.** Supplements to Mathlib's beta function: integrability and evaluation of
$\int_0^c x^{a-1}(c-x)^{b-1}dx = c^{a+b-1} B(a,b)$ and of $\int_0^1 x^m (1-x)^n dx =
m!\,n!/(m+n+1)!$, plus norm estimates for the beta kernel. Measurability of $x \mapsto x^s$
($x > 0$, $s \in \mathbb C$), and the continuous, differentiable "positive power" functions
$x \mapsto x_+^{s}$ and $x \mapsto x_+^{s-1}/\Gamma(s)$ on the real line.

**Regularized incomplete Mellin transforms.** For $K$ on $[0, a]$ and $\operatorname{Re}\alpha
> 0$ put
$$\mathcal M_\alpha K = \frac{1}{\Gamma(\alpha)} \int_0^a t^{\alpha - 1} K(t)\,dt .$$
For $K \in C^N[0,a]$, subtracting the Taylor polynomial of order $N-1$ at $0$ gives the exact
identity
$$\mathcal M_\alpha K = \sum_{k<N} \frac{K^{(k)}(0)}{k!}\,\frac{a^{\alpha+k}(\alpha)_k}{\Gamma(\alpha+k+1)} + (\alpha)_N\, \mathcal M_{\alpha+N}\bigl(\text{Peano remainder}\bigr),$$
whose right-hand side is holomorphic in $\alpha$ on $\operatorname{Re}\alpha > -N$. Hence
$\alpha \mapsto \mathcal M_\alpha K$ continues holomorphically from $\operatorname{Re}\alpha >
0$ to $\operatorname{Re}\alpha > -N$. This is the one-dimensional engine behind the continuation
of Dirichlet integrals in Part III. Not in Mathlib.

## I.5 Measure and integration on the standard simplex

Mathlib provides the standard simplex as an abstract convex object (`Convexity.StdSimplex`),
but no measure theory on it. This library builds the coordinate description, the natural
measures, and the integration formulas that the Dirichlet theory needs.

**Coordinates.** For a finite index set $I$ and a chosen $i \in I$, the affine hyperplane
$H_I = \{u \in \mathbb R^I : \sum_j u_j = 1\}$ is parametrized by the $|I| - 1$ coordinates
$u_j$, $j \neq i$, with $u_i = 1 - \sum_{j \ne i} u_j$. The standard vertices form an affine
basis of $H_I$, whose barycentric coordinates are the ambient coordinates. These charts are
homeomorphisms onto $H_I$, are compatible with coordinate permutations, and identify the
abstract standard simplex with its coordinate realization $E_I \subseteq \mathbb R^I$ (a compact
set; empty when $I = \varnothing$).

**Aggregation.** For a map $f : I \to J$ of finite sets, aggregation
$\mathrm{Agg}_f : \mathbb R^I \to \mathbb R^J$, $(\mathrm{Agg}_f u)_k = \sum_{f(i) = k} u_i$,
maps $E_I$ to $E_J$ and is the coordinate form of the map of standard simplices induced by $f$.

**The hyperplane measure.** Lebesgue measure on any free-coordinate chart of $H_I$ pushes
forward to a measure $\sigma_I$ on the whole hyperplane $H_I$ (not only on the simplex) which is
independent of the omitted coordinate, invariant under coordinate permutations, $\sigma$-finite,
zero when $I = \varnothing$, and gives the simplex mass
$$\sigma_I(E_I) = \frac{1}{(|I| - 1)!} \qquad (I \ne \varnothing).$$
Its restriction to $E_I$, transported to the abstract simplex, is the *coordinate measure* of the
intrinsic simplex. No probability normalization is imposed. The coordinate hyperplanes are
null, and a point of $E_I$ almost surely has all coordinates positive.

**Solid simplices.** The solid simplex $\Delta_I(r)$ of radius $r$ has Lebesgue volume
$r^{|I|}/|I|!$, obtained by separating one coordinate. Integration by coordinate sum: for
nonnegative measurable $g$,
$$\int_{\Delta_I(r)} g\Bigl(\sum_i x_i\Bigr)dx = \int_0^r \frac{s^{n-1}}{(n-1)!}\, g(s)\,ds,
\qquad n = |I|.$$
Radial integration over the positive orthant: with $t = \sum_i x_i$ as radial coordinate and
the coordinate measure of $E_I$ as angular measure,
$$\int_{\mathbb R_+^I} F(x)\,dx = \int_0^\infty t^{\,n-1} \int_{E_I} F(t u)\,d\sigma_I(u)\,dt .$$

**Aggregation of measures.** For a surjection $f : I \to J$ the pushforward of the restricted
hyperplane measure along $\mathrm{Agg}_f$ is absolutely continuous with respect to $\sigma_J$
with density proportional to
$$\prod_{k \in J} y_k^{\,|f^{-1}(k)| - 1}.$$
The same computation is done for solid simplices by disintegration along the fibers.

**Slicing (Fubini) and monomials.** Separating one coordinate $u_i = t$ writes an integral over
$E_I$ as an iterated integral over $t \in [0, 1]$ and a scaled simplex $(1-t)E_{I \setminus
\{i\}}$; the Jacobian is $(1-t)^{|I|-2}$. Consequently
$$\int_{E_I} \prod_i u_i^{m_i}\,d\sigma_I(u) = \frac{\prod_i m_i!}{(|I| + \sum_i m_i - 1)!}$$
for natural exponents, and the corresponding formula for monomials of multivariate
polynomials. The two-coordinate simplex is identified with the unit interval.

**Simplex fundamental theorem of calculus.** Separating the last free coordinate gives the
one-dimensional slices used to integrate derivatives along edges; this is the ingredient of the
Hermite–Genocchi formulas below.

**Product slices.** Tonelli and Fubini formulas for integration over an arbitrary measurable
subset of a product (Mathlib only covers rectangles), specialized to regions between two graphs
in the closed-interval convention.

**Smooth functions near the simplex.** A function on $\mathbb R^I$ is $C^N$ *near the
simplex* if it is $C^N$ on some open neighborhood of $E_I$. The tangential derivative in the
direction $e_j - e_k$ consumes one order of differentiability; restriction to a face and
"slicing" $u \mapsto (1-t)v + t e_i$ preserve the property. These are the differential-operator
inputs for the tangential integration by parts of Part III.

**Moment determination.** Two finite measures supported on the compact simplex $E_I$ with the
same monomial moments $\int \prod_i x_i^{m_i}$ for all $m \in \mathbb N^I$ are equal
(polynomials are dense in continuous functions on a compact set, and continuous functions
determine finite measures).

**Temporary Mathlib-bound results.** Null weighted affine hyperplanes in finite products of
real lines; the measurable equivalence $\bigl(\prod_{i<n} \alpha_i\bigr) \times \alpha_n \simeq
\prod_{i \le n} \alpha_i$ given by appending a last coordinate and its measure preservation;
and the Hausdorff-measure slicing formula for a set inside a lower-dimensional affine subspace
(adapted from a Mathlib pull request).

**Divided differences and repeated integrals (complex kernels).** The library closes with
complex kernels integrated over simplices.

**Hermite–Genocchi divided differences.** For nodes $z_0, \dots, z_n$ in a convex domain of
holomorphy of $f$ (coincident nodes allowed),
$$f[z_0, \dots, z_n] = \int_{E_{n+1}} f^{(n)}\Bigl(\sum_i u_i z_i\Bigr)d\sigma(u)$$
(unnormalized simplex integral). Proved: permutation symmetry, the coalesced value
$f[z, \dots, z] = f^{(n)}(z)/n!$, the recurrence
$(z_0 - z_1) f[z_0, \dots] = f[z_0, z_2, \dots] - f[z_1, z_2, \dots]$, the Newton interpolation
formula with exact divided-difference remainder, its coalesced Taylor form, and the
identification of $n$-fold repeated segment integrals with simplex integrals with repeated base
nodes. These are not in Mathlib; they are placed here rather than in Part I.6 so that the complex
analysis libraries do not depend on the simplex measure.


## I.6 Single-variable complex analysis

This library extends Mathlib's complex analysis in the direction needed for contour
representations and analytic continuation. Unless stated otherwise, functions take values in an
arbitrary complex Banach space $F$; Mathlib's corresponding results are often scalar-valued or
restricted to discs, annuli or convex sets.

### Primitives, Cauchy's theorem, and the curve index

**Primitives on simply connected domains (new).** Let $U \subseteq \mathbb C$ be open and
simply connected and $f : U \to F$ holomorphic. Then $f$ has a holomorphic primitive on $U$,
unique up to a constant and normalizable at a point. More precisely, exactness is local-to-global
on simply connected open sets: a function with local primitives has a global one, by the gluing
lemma of Part I.2 applied to locally constant differences. Consequently, for Mathlib's notions
of exact and conservative one-forms on planar domains, "exact" equals "locally exact" equals
"conservative" on simply connected open sets, and Morera's theorem yields global primitives.

**Cauchy's integral theorem.** For a closed differentiable curve $\gamma$ in a simply
connected open set $U$ and $f : U \to F$ holomorphic, $\int_\gamma f(z)\,dz = 0$, and integrals
along two curves with the same endpoints agree. Mathlib has this for convex sets; the simply
connected version is new.

**Cauchy's formula with an explicit kernel integral.** For a closed $C^1$ curve $\gamma$ in a
simply connected open $U$, $a \in U \setminus \gamma$, and $f$ holomorphic,
$$\int_\gamma \frac{f(z)}{z - a}\,dz = \Bigl(\int_\gamma \frac{dz}{z - a}\Bigr)\, f(a).$$
No winding-number theory or Jordan interior is assumed; the usual formula follows when the
kernel integral is $2\pi i$.

**The analytic index.** For a closed $C^1$ curve $\gamma$ avoiding $a$ the *index* is
$\operatorname{ind}_\gamma(a) = \frac{1}{2\pi i}\int_\gamma \frac{dz}{z-a}$. It is an integer
(proved by the exponential endpoint identity $\exp\int \frac{g'}{g} = \frac{g(1)}{g(0)}$ along
the curve), it respects reversal and concatenation, vanishes for curves in a simply connected
domain avoiding $a$, equals $1$ inside and $0$ outside a counterclockwise circle, and gives the
index-weighted Cauchy formula $\frac{1}{2\pi i}\int_\gamma \frac{f(z)}{z-a}dz =
\operatorname{ind}_\gamma(a) f(a)$. The index is continuous, hence locally constant, in $a$ off
the curve, constant on connected components of the complement, and zero on every unbounded
component. Mathlib has no curve index for general closed curves.

**Homotopy invariance.** Cauchy's theorem for $C^2$ homotopies on arbitrary open domains (from
Mathlib's closed-one-form deformation theorem), including moving endpoints. New: Cauchy's
theorem for merely *continuous* homotopies whose boundary paths are differentiable and
integrable, obtained by pulling local primitives back to the parameter square and gluing; the
integrals along the two endpoint tracks account for moving endpoints, and deformation preserves
limiting integrals of finite truncations when the endpoint-track integrals vanish. The index of
$C^1$ loops is invariant under continuous based homotopies avoiding the pole, and vanishes for
loops contractible in the punctured plane.

**Circles and polygons.** The counterclockwise circle as a $C^1$ path with curve integral equal
to Mathlib's circle integral (any radius, including zero); integration around polygons as the
sum over oriented edges, vanishing for exact functions and, on simply connected open sets, for
holomorphic functions.

**Logarithms.** A continuous logarithm of a holomorphic function is holomorphic with derivative
$g'/g$; on a simply connected open set every nonvanishing holomorphic $g$ has holomorphic
logarithms and $n$-th roots, normalizable at a point and then unique on connected domains. The
branch depends analytically on holomorphic parameters, also for parameters in a complex normed
space, and can be normalized along a zero section. A continuous homotopy of paths in the punctured
plane lifts to a continuous logarithm on the parameter square, so continuation of a logarithm
along homotopic paths gives the same terminal value.

**Univalent disc images (analytic Jordan contours).** Let $f$ be injective and holomorphic on
a neighborhood of the closed disc $\overline B(c, R)$. Then $f(B(c,R))$ is a bounded, open,
simply connected domain with closure $f(\overline B)$ and frontier the embedded circle
$f(\partial B)$; the complement of $f(\partial B)$ has exactly two components, the image disc
and the exterior of the image closed disc; the index of the image contour is $1$ in the image
disc and $0$ outside its closure (so positive orientation is a theorem); and the normalized
Banach-valued Cauchy formula holds on the image contour. Smaller concentric image discs exhaust
an injective holomorphic image of an open disc by relatively compact domains, each closure inside
the next, every compact subset inside some term. The disc parametrization is an explicit
hypothesis; the Riemann mapping theorem is not used.

**Exterior paths.** Compactified paths to infinity $u \mapsto t + \frac{1-u}{u} q(u)$,
$u \in (0, 1]$, with $q(0) \ne 0$; escape to infinity, regularity of the reversed Jacobian and
of the normalized node factors at $u = 0$; and endpoint formulas for integrals of exact
Banach-valued functions along them, with explicit integrability hypotheses.

### Derivatives, series, singularities

**Cauchy's derivative formula at any interior point.** If $f$ is holomorphic on $B(c, R)$ and
continuous on the closed disc, then for every $w \in B(c, R)$ and $k \ge 0$,
$$f^{(k)}(w) = \frac{k!}{2\pi i}\oint_{|\zeta - c| = R} \frac{f(\zeta)}{(\zeta - w)^{k+1}}\,d\zeta,$$
Banach-valued; Mathlib states this only at the center. Differentiating the contour kernel in $w$
raises its order. Uniform derivative bounds on closed thickenings of compact subsets, geometric
majorants for Taylor coefficients, and bounds for the Cauchy power series.

**Laurent series (new).** For $f$ holomorphic on an annulus $r_1 < |z - c| < r_2$ the circle
coefficients $a_k(r) = \frac{1}{2\pi i}\oint_{|z-c|=r} f(z)(z-c)^{-k-1}dz$ satisfy Cauchy bounds,
are independent of $r$ on any connected set of admissible radii, depend holomorphically on
holomorphic parameters, and give the two-sided expansion $f(z) = \sum_{k \in \mathbb Z} a_k
(z-c)^k$ on the annulus; negative coefficients vanish when $f$ extends over the disc. Cauchy's
formula on an annulus is proved by removing the singularity of the kernel and applying
Cauchy–Goursat. Mathlib has Laurent series only as algebraic objects.

**Residues (new).** For $f$ holomorphic on a punctured neighborhood of $c$ (essential
singularities allowed, Banach values allowed), the residue is the common value of
$\frac{1}{2\pi i}\oint_{|z-c|=\rho} f$ for small $\rho$; it equals the Laurent coefficient
$a_{-1}$, is a germ invariant, is linear, and has the usual computations for $f(z)/(z-c)^m$.
For a nonzero meromorphic germ $g$, $\operatorname{res}_c(g'/g) = \operatorname{ord}_c g$
(via Mathlib's local meromorphic factorization). A meromorphic germ is the sum of a finite
principal part and an analytic germ; the principal part's normalized circle integral is the
residue.

**Argument principle, Rouché, Hurwitz (new).** For $f$ meromorphic on a neighborhood of the
closed disc with no zeros or poles on the circle,
$$\frac{1}{2\pi i}\oint_{|z-c|=R}\frac{f'}{f} = \sum_{|a - c| < R} \operatorname{ord}_a f,$$
using Mathlib's divisors and meromorphic orders. Rouché: if $|g - f| < |f|$ on the circle, then
$f$ and $g$ have the same number of zeros inside, with multiplicity (the count is a continuous
integer-valued function along the segment from $f$ to $g$). Hurwitz: uniform approximation on a
closed disc with zero-free boundary eventually preserves the zero count; a locally uniform limit
of zero-free holomorphic functions on a connected open set is zero-free or identically zero;
limits of injective functions are constant or injective.

**Montel, Vitali (one variable).** A family of holomorphic maps bounded on each compact subset of
an open set, with finite-dimensional target, has compact closure in $\mathcal O(U, F)$, and
every such sequence has a locally uniformly convergent subsequence. A bounded-on-compacts
sequence converging pointwise on a set with an accumulation point inside a connected open domain
converges locally uniformly on the domain.

**Isolated singularities (new).** A function holomorphic on a punctured neighborhood of $c$ and
bounded near $c$ extends analytically (assigned value at $c$ irrelevant); a meromorphic germ is
exactly one with a finite limit or with $|f| \to \infty$; at a nonmeromorphic isolated
singularity the image of every punctured neighborhood is dense (Casorati–Weierstrass); the
three-way trichotomy removable/pole/essential.

**Injectivity and zeros.** An injective holomorphic function of one variable has nowhere
vanishing derivative. A zero inside a disc persists under small perturbations with no boundary
zeros, in particular along holomorphic families.

**Removability and reflection.** A continuous function analytic off a countable set, or off the
zero set of a nonzero analytic function, is analytic on the whole open set; a continuous
function holomorphic off the real axis is holomorphic throughout (Morera integrals split at the
axis); Schwarz reflection across the real axis for a function real-valued on the axis.

### Real-variable tools of complex analysis

**Subharmonic functions (new).** A real function on an open subset of $\mathbb C$ is
*subharmonic* if it is upper semicontinuous and satisfies the local submean inequality
$u(c) \le \frac{1}{2\pi}\int_0^{2\pi} u(c + \rho e^{i\theta})\,d\theta$ for all small $\rho$.
Proved: closure under sums, nonnegative multiples and maxima; real parts, positive powers of
norms and logarithms of nonvanishing moduli of holomorphic functions are subharmonic; the
maximum principle on preconnected open sets and on discs; harmonic polynomial majorants (real
parts of polynomials in $(z-a)/r$ approximate continuous functions on a circle uniformly);
hence the submean inequality on *every* closed disc for continuous subharmonic functions; continuous
convex functions are subharmonic; and the Laplacian criterion: a $C^2$ function is subharmonic
if and only if $\Delta u \ge 0$, through the second-order expansion of circle averages
$\frac{1}{2\pi}\int u(c + re^{i\theta})d\theta - u(c) = \frac{r^2}{4}\Delta u(c) + o(r^2)$.
Jensen's formula $\log|f(c)| \le$ circle average of $\log|f|$ and the submean inequality for
$|f|^p$, every $p > 0$ (needed for roots of Taylor coefficients in Hartogs' theorem, Part II).

**Cauchy–Pompeiu and the Cauchy transform (new).** For a compactly supported $C^1$ function
$\varphi : \mathbb C \to F$,
$$\int_{\mathbb C} \frac{1}{w}\,\frac{\partial \varphi}{\partial \bar z}(w)\,dA(w) = -\pi\,\varphi(0),$$
proved in polar coordinates without Green's theorem. The Cauchy transform in the first variable
of a compactly supported $C^1$ function $g$ on $\mathbb C \times G$,
$u(z, y) = \pi^{-1}\int w^{-1} g(z - w, y)\,dA(w)$, is $C^1$ with derivative obtained under the
integral, satisfies $\partial u/\partial\bar z = g$, and its parameter $\bar\partial$-derivatives
are the Cauchy transforms of those of $g$. These are the analytic inputs to Ehrenpreis' proof of
Hartogs' extension theorem in Part II.

### Miscellaneous

Right-half-plane geometry (products and quotients of right-half-plane numbers stay in the slit
plane; square roots of right-half-plane numbers lie in a sector; finitely many right-half-plane
points fit in a disc tangent to the imaginary axis); principal power multiplication formulas
$(xw)^s = x^s w^s$ for $x > 0$ and holomorphy of $w^s$ on discs centered on the positive axis;
uniqueness of analytic functions from agreement on a real germ or on the positive reals;
differentiation of compact weighted integrals in one complex parameter; convergence of iterated
derivatives under locally uniform convergence; circle integrability of maxima and reflection
invariance of circle averages.
