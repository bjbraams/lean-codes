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
| `ComplexAnalysis` | `Analysis`, `Topology` | 115 files |
| `SeveralComplexVariables` | `Analysis`, `Topology`, `ComplexAnalysis` | 133 files |
| `Dirichlet` | all of the above except `Algebra` | 50 files |
| `Carlson` | all of the above | 97 files |

The whole project is written against a pinned Mathlib (the Lean 4 mathematical library, release
v4.35.0-rc2). "New" below always means: not available in that Mathlib release, as far as the authors
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
Banach-valued; Mathlib states this only at the center, and supplies the derivative of the
contour kernel in $w$, from which the formula follows by induction. Uniform derivative bounds
on closed thickenings of compact subsets, geometric majorants for Taylor coefficients, and
bounds for the Cauchy power series.

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

**Cycles and the homology form of Cauchy's theorem (new).** A *cycle* $\Gamma$ is a finite
family of closed $C^1$ curves; its integral and its index $\operatorname{ind}_\Gamma(w)$ are the
sums over the family. The index is an integer off the cycle, locally constant there, and zero
far away; cycles can be concatenated and a closed curve can be taken with an integer
multiplicity. Let $U$ be open and $\Gamma$ a cycle in $U$ with $\operatorname{ind}_\Gamma(w) = 0$
for every $w \notin U$ (*homologous to zero in $U$*). Then for every Banach-valued $f$
holomorphic on $U$ and every $z \in U$ off the cycle,
$$\frac{1}{2\pi i}\int_\Gamma \frac{f(w)}{w - z}\,dw = \operatorname{ind}_\Gamma(z)\, f(z),
\qquad \int_\Gamma f = 0,$$
by Dixon's proof: the integral of the divided slope $(f(w) - f(z))/(w - z)$ over $\Gamma$ is
holomorphic in $z$ on $U$ (holomorphy of parametric integrals with jointly continuous
integrands, proved through Cauchy's formula on discs and Fubini), agrees off the cycle with
the Cauchy integral where the index vanishes, and the two pieces glue to a bounded entire
function vanishing at infinity. No simple connectivity is assumed. Consequences: the **residue
theorem for cycles**, $\int_\Gamma f = 2\pi i \sum_{a \in S} \operatorname{ind}_\Gamma(a)
\operatorname{res}_a f$ for $f$ holomorphic on $U$ minus a finite set $S$ of isolated
singularities of any type avoided by the cycle (proved by induction on $S$, subtracting
$\operatorname{ind}_\Gamma(a)$ copies of a small circle), and the **argument principle for
cycles**, $\frac{1}{2\pi i}\int_\Gamma f'/f = \sum_a \operatorname{ind}_\Gamma(a)
\operatorname{ord}_a f$ for $f$ meromorphic on $U$, analytic and nonvanishing on the cycle;
the sum is finite because the index vanishes outside a compact subset of $U$, on which the
divisor has finite support (a set in the codiscrete filter of $U$ has finite complement in every
compact subset). The index of merely continuous closed curves and the Jordan curve theorem are
not included.

**Runge's approximation theorem (new).** Let $K$ be compact and $f$ holomorphic on an open
neighborhood $U$ of $K$. First, $f$ is a uniform limit on $K$ of finite sums of simple poles
$\sum_i a_i/(c_i - z)$ with $c_i \in U \setminus K$: with a smooth cutoff $\varphi$ equal to $1$
near $K$ and compactly supported in $U$ (from Mathlib's smooth Urysohn lemma), the
Cauchy–Pompeiu identity gives $f(z) = -\pi^{-1}\int_\Omega \frac{f(w)\,\partial\varphi/\partial\bar
w}{w - z}\,dA(w)$ on $K$ with $\Omega = \operatorname{supp}\varphi \setminus \{\varphi = 1\}^\circ$
compact in $U \setminus K$, and a Cauchy-type integral with bounded density over a compact set
disjoint from $K$ is approximated uniformly on $K$ by finite pole sums (Riemann sums over a
disjoint refinement of a finite cover by small balls, controlled by the uniform continuity of
the kernel). Second, *pole pushing*: uniform approximability on $K$ by elements of a subalgebra
of functions is closed under sums, products and uniform limits; if $(a - z)^{-1}$ is
approximable then so is $(a' - z)^{-1}$ for $a'$ within a fixed fraction of the distance from
$a$ to $K$ (geometric series), hence for all $a'$ in the connected component of $a$ in the
complement of $K$; and poles outside a disc containing $K$ are approximable by polynomials.
**Runge's theorem**: if $A \subseteq \mathbb C \setminus K$ meets every bounded component of
$\mathbb C \setminus K$, then $f$ is uniformly approximable on $K$ by the algebra generated by
$z$ and the poles $(a - z)^{-1}$, $a \in A$; if $\mathbb C \setminus K$ is connected, by
polynomials.

**Runge on open sets and Mittag-Leffler (new).** For an open set $U$ let $K_n$ be the
points of $U$ within distance $n$ of the origin and at distance at least $1/(n+1)$ from
$\mathbb C \setminus U$. These compact sets exhaust $U$, $K_n \subseteq K_{n+1}^\circ$, and every
bounded component of $\mathbb C \setminus K_n$ meets $\mathbb C \setminus U$; so Runge's theorem
gives, for $f$ holomorphic on $U$ and $A$ meeting every component of $\mathbb C \setminus U$ (the
complement of $U$ itself when nothing better is known), a sequence in the algebra generated by
$z$ and the poles $(a - z)^{-1}$, $a \in A$, converging to $f$ locally uniformly on $U$;
polynomials suffice when $\mathbb C \setminus U$ has no bounded component. **Mittag-Leffler**:
for a set $S$ discrete in $U$ and functions $P_a$ holomorphic on $\mathbb C \setminus \{a\}$,
$a \in S$, there is $f$ holomorphic on $U \setminus S$ with $f - P_a$ holomorphic near each
$a$; the sum $\sum_a (P_a - r_a)$ converges after subtracting, for the finitely many $a$ in
each $K_n \setminus K_{n-1}$, a Runge correction $r_a$ with poles off $U$ that approximates
$P_a$ on $K_{n-1}$ to within $2^{-n}$.

**Infinite products and Weierstrass factorization (new).** If the $f_n$ are holomorphic on
$U$ and $\sum_n \sup_K |f_n| < \infty$ for every compact $K \subseteq U$, then $\prod_n (1 +
f_n)$ converges locally uniformly (Mathlib), is holomorphic, vanishes exactly where some
factor vanishes, and its order of vanishing at a point is the sum of the orders of the
finitely many factors vanishing there. The elementary factors $E_p(z) = (1 - z)\exp(z + z^2/2
+ \dots + z^p/p)$ satisfy $|1 - E_p(z)| \le 4|z|^{p+1}$ for $|z| \le 1/2$, from $E_p(z) =
\exp(-\sum_{k > p} z^k/k)$; hence for $a_n \ne 0$ with $|a_n| \to \infty$ the product $P(z) =
\prod_n E_n(z/a_n)$ is entire with zeros exactly the $a_n$, the order at $w$ being the number
of $n$ with $a_n = w$. **Factorization**: an entire $f$ with $f(0) \ne 0$ whose orders of
vanishing are those of $P$ is $e^g P$ with $g$ entire, since $f/P$ extends to a nonvanishing
entire function (removal across the zero set, by the local normal forms $f = (z - w)^m f_1$,
$P = (z - w)^m P_1$), which is an exponential because $H'/H$ has an entire primitive.

**Möbius transformations, the Riemann mapping theorem (new).** The disc Möbius map
$\varphi_a(z) = (z - a)/(1 - \bar a z)$, $|a| < 1$, preserves the open disc and the unit circle,
has inverse $\varphi_{-a}$, and has derivative $(1 - |a|^2)/(1 - \bar a z)^2$, from the identity
$|1 - \bar a z|^2 - |z - a|^2 = (1 - |a|^2)(1 - |z|^2)$. An injective holomorphic function on
an open set is an open map with holomorphic inverse (open mapping theorem and nonvanishing
derivative). **Automorphisms of the disc**: a holomorphic bijection of the disc with
holomorphic inverse (equivalently, an injective holomorphic map of the disc onto itself) is
$z \mapsto c\,\varphi_a(z)$ with $|c| = 1$, by the Schwarz lemma and its equality case
(Mathlib) applied at a fixed point after conjugating by $\varphi_a$; the automorphisms of the
upper half-plane are the conjugates by the Cayley transform $z \mapsto (z - i)/(z + i)$.
**Riemann mapping theorem**: for $U \ne \mathbb C$ open and simply connected and $z_0 \in U$
there is an injective holomorphic $f$ with $f(U)$ the unit disc, $f(z_0) = 0$ and $f'(z_0) >
0$, and it is unique. The family of injective holomorphic maps $U \to \mathbb D$ with $z_0
\mapsto 0$ is nonempty (a holomorphic square root $h$ of $z - a$, $a \notin U$, has open
image disjoint from $-h(U)$, and $(\varepsilon/2)/(h + h(z_0))$ maps into the disc); $|f'(z_0)|$
is bounded by the Cauchy estimate; a maximizing sequence has a locally uniform limit $g$ by
Montel, injective by Hurwitz, into the open disc by the open mapping theorem; and if $g$
omitted $w \in \mathbb D$, then with $h^2 = \varphi_w \circ g$ and $c = h(z_0)$ the map
$\varphi_c \circ h$ would have $|(\varphi_c \circ h)'(z_0)| = |g'(z_0)|\,(1 + |w|)/(2\sqrt{|w|}) >
|g'(z_0)|$. Uniqueness follows from the classification of disc automorphisms fixing $0$.

**Harnack's inequality and the Dirichlet problem on a disc (new).** Mathlib's Poisson kernel
$P_w(\zeta) = (R^2 - |w - c|^2)/|\zeta - w|^2$ on the circle $|\zeta - c| = R$ is nonnegative,
continuous, has circle average $1$, and satisfies $(R - r)/(R + r) \le P_w \le (R + r)/(R - r)$
with $r = |w - c|$. For $u \ge 0$ harmonic on the disc and continuous on its closure, Mathlib's
Poisson representation $u(w) = \operatorname{avg}(P_w u)$ and the mean value $u(c) =
\operatorname{avg} u$ give **Harnack's inequality** $\frac{R - r}{R + r} u(c) \le u(w) \le
\frac{R + r}{R - r} u(c)$. For continuous boundary data $g$ the Poisson integral $w \mapsto
\operatorname{avg}(P_w g)$ is harmonic on the disc (the real part of the Herglotz–Riesz integral,
analytic in $w$ by Mathlib) and tends to $g(\zeta_0)$ as $w \to \zeta_0$ from inside: split the
circle at distance $\delta$ from $\zeta_0$, use the modulus of continuity of $g$ on the near
arc and the bound $P_w \le (R^2 - |w - c|^2)/(\delta/2)^2 \le 2R|w - \zeta_0|/(\delta/2)^2$ on
the far arc. Hence the **Dirichlet problem** on a disc has a solution continuous on the closed
disc, unique by the maximum principle for subharmonic functions (harmonic functions are
subharmonic by the mean value property).

**Local mapping and the residue at infinity (new).** If $f - f(a)$ vanishes to finite order
$m$ at $a$, then $f - f(a)$ and $f'$ do not vanish on a punctured neighborhood of $a$ (the order
of $f'$ at $a$ is $m - 1$). For small $\varepsilon$ and $\delta$ the minimum of $|f - f(a)|$ on
the circle $|z - a| = \varepsilon$, every $w$ with $0 < |w - f(a)| < \delta$ is taken exactly $m$
times in the disc, each time with $f' \ne 0$: Rouché gives the divisor degrees of $f - w$ and
$f - f(a)$ on the closed disc to be equal, the latter is $m$, and the zeros of $f - w$ are
simple. The **residue at infinity** is $\operatorname{res}_\infty f = -\operatorname{res}_0
\bigl(w^{-2} f(1/w)\bigr)$; the substitution $z = 1/w$ turns the circle integral of $f$ over
$|z| = R$ into that of $w^{-2} f(1/w)$ over $|w| = 1/R$ (reparametrize $\varphi \mapsto
-\varphi$ and use periodicity), so the integral over a large circle equals $-2\pi i
\operatorname{res}_\infty f$, and the residue theorem for the circle as a cycle gives the
**total residue theorem** $\sum_{a \in S} \operatorname{res}_a f + \operatorname{res}_\infty f
= 0$ for $f$ holomorphic off a finite set $S$.

**Analytic continuation along paths and a natural boundary (new).** A continuation along a
continuous path $\gamma\colon [0,1] \to \mathbb C$ is a family of function elements
$(f_t, D(\gamma(t), r_t))$ with $f_t$ analytic on the disc, such that for $s$ near $t$ the point
$\gamma(s)$ lies in the disc of $t$ and $f_s = f_t$ near $\gamma(s)$. Two continuations along
the same path with the same germ at $\gamma(0)$ have the same germ at every $\gamma(t)$: the
set of parameters where the germs agree is open and closed by the identity theorem on the
discs, and $[0,1]$ is connected. The lacunary series $f(z) = \sum_n z^{2^n}$ is holomorphic on
the unit disc; for a $2^k$-th root of unity $\zeta$ and $0 \le r < 1$ one has $\operatorname{Re}
f(r\zeta) \ge N r^{2^{N+k}} - k$ for every $N$, since the terms with $n \ge k$ are the positive
reals $r^{2^n}$; as these roots of unity are dense in the circle, $f$ is unbounded near every
boundary point, and no continuous extension across any point of the circle exists (a
**natural boundary**).

**Entire functions of finite order and Hadamard's factorization (new).** An entire function
$f$ has order at most $\rho$ if $|f(z)| \le A e^{B|z|^\rho}$. For $f(0) \ne 0$, Mathlib's Jensen
inequality bounds the number of zeros in $|z| \le r$ by $(\log(A e^{B(2r)^\rho}) -
\log|f(0)|)/\log 2 \le C r^\rho$; if $a_i$ ($i$ in a countable index set) lists the zeros with
multiplicity, this counting function equals the divisor degree on the closed disc, and
grouping the zeros in dyadic shells $2^j \le |a_i| < 2^{j+1}$ gives $\sum_i |a_i|^{-s} < \infty$ for
every $s > \rho$. The canonical product of genus $k$, $P(z) = \prod_i E_k(z/a_i)$, converges for
$\sum_i |a_i|^{-(k+1)} < \infty$, is entire with zeros exactly the $a_i$ (orders equal to
multiplicities), and satisfies, from the elementary bounds $|E_k(w)| \ge e^{-2|w|^{k+1}}$ for
$|w| \le 1/2$ and $|E_k(w)| \ge |1 - w| e^{-2^k k |w|^k}$ for $|w| \ge 1/2$, the lower bound
$|P(z)| \ge e^{-c|z|^s}$ for $|z| \ge 1$ outside the discs $|z - a_i| < |a_i|^{-(k+1)}$, when
$k \le s < k+1$ and $\sum |a_i|^{-\rho'} < \infty$ for some $\rho' < s$. Since the radii met by
those discs have finite total length, there are arbitrarily large circles $|z| = r$ avoiding
them all. **Hadamard's theorem**: if $f$ has order at most $\rho < k+1$, a zero of order $m$ at
$0$ and nonzero zeros $a_i$, then $\sum |a_i|^{-(k+1)} < \infty$ and $f(z) = e^{Q(z)} z^m P(z)$
with $Q$ a polynomial of degree at most $k$: the quotient $f/(z^m P)$ is $e^{G}$ with $G$
entire; on good circles $|z| = r$ the two bounds give $\operatorname{Re} G(z) \le C r^s$, which
extends to the disc by the maximum principle; the Borel–Carathéodory theorem (Mathlib) then
bounds $|G|$ on $|z| = r/2$, and
the Cauchy estimates force the Taylor coefficients of $G$ of index above $s$ to vanish along
$r \to \infty$. The intrinsic form constructs the enumeration of the zeros over the countable
index type $\sum_{w} \{1, \dots, \operatorname{ord}_w f\}$.

**Blaschke products and the Blaschke condition (new).** For $0 < |a| < 1$ the Blaschke factor
$b_a(z) = \frac{|a|}{a}\,\frac{a - z}{1 - \bar a z}$ is a disc Möbius map with $b_a(0) = |a|$,
$|b_a| \le 1$ on the closed disc, a simple zero at $a$, and $|1 - b_a(z)| \le \frac{1 + |z|}{1 -
|z|}(1 - |a|)$ from the identity $1 - b_a(z) = (1 - |a|)(a + |a| z)/(a(1 - \bar a z))$. For a
family $a_i$ of nonzero points of the disc with $\sum (1 - |a_i|) < \infty$ the Blaschke product
$\prod_i b_{a_i}$ therefore converges locally uniformly on the disc (the general product theory
of Part I.6), is holomorphic with $|B| \le 1$, and vanishes exactly at the $a_i$ with the
multiplicities of the family. Conversely (**F. Riesz**), if $f$ is bounded and holomorphic on
the disc with $f(0) \ne 0$, Jensen's formula on $|z| \le R < 1$ gives $\sum_{|w| \le R}
\operatorname{ord}_w f \cdot \log(R/|w|) \le \log M - \log|f(0)|$; letting $R \to 1$ and using
$1 - |w| \le \log(1/|w|)$ shows $\sum_w (1 - |w|) < \infty$ over the zeros. Dividing out $z^m$
handles $f(0) = 0$, and a bounded holomorphic function vanishing on a family with $\sum (1 -
|a_i|) = \infty$ is identically zero.

**Harnack's principle and Perron's method (new).** A locally uniform limit of harmonic
functions is harmonic: on each closed disc the Poisson representation passes to the limit by
uniform convergence of circle averages. A monotone sequence of harmonic functions on a connected
open set that is bounded at one point converges locally uniformly to a harmonic function
(**Harnack's principle**): Harnack's inequality on each disc transfers the bound and the
Cauchy property from the center to the disc, and the set of points where the sequence is
bounded is clopen. For a bounded open set $U$ and bounded boundary data $g$ on $\partial U$,
the **Perron family** consists of the continuous subharmonic $v$ on $U$ with
$\limsup_{z \to \zeta} v(z) \le g(\zeta)$ at every boundary point, and the **Perron function** is
$u = \sup v$. The maximum principle for subharmonic functions with boundary upper limits bounds
every member by $\sup g$. The family is closed under maxima and under **Poisson modification**
(replacing $v$ on a closed disc in $U$ by the Poisson extension of its boundary values,
which is subharmonic and dominates $v$). Fixing a disc, a sequence of members tending to $u$
at the center is made increasing and Poisson-modified; Harnack's principle gives a harmonic
limit $h \le u$ with $h = u$ at the center, and comparison with a second sequence (built from
any point of the disc) shows $h = u$ on the disc, so $u$ is harmonic (**Perron's theorem**).
A **barrier** at $\zeta \in \partial U$ is a continuous subharmonic $\beta < 0$ on $U$ with
$\beta \to 0$ at $\zeta$ and $\beta \le -\eta(\delta) < 0$ outside each $\delta$-neighbourhood of
$\zeta$. If $g$ is continuous at $\zeta$, then $g(\zeta) - \varepsilon + K \beta$ belongs to
the family for a suitable $K$ while every member is at most $g(\zeta) + \varepsilon - K \beta$,
so $u(z) \to g(\zeta)$. When a closed disc $\bar D(c, R)$ meets $\bar U$ only in $\zeta$
(**exterior disc condition**), $\log(R / |z - c|)$ is a barrier; hence on a bounded open set
all of whose boundary points satisfy this condition the Dirichlet problem is solvable for
every continuous boundary function.

**The Schwarz–Pick lemma (new).** For a holomorphic self-map $f$ of the disc and $a$ in the
disc, the map $h(z) = \varphi_{f(a)}(f(\varphi_{-a}(z)))$ (with $\varphi_b(z) = (z-b)/(1-\bar b
z)$ the disc Möbius involution) sends the disc into itself with $h(0)=0$, so the classical
Schwarz lemma gives $|h(z)| \le |z|$ and $|h'(0)| \le 1$. Substituting $z = \varphi_a(w)$ and
using $\varphi_{-a}(\varphi_a(w)) = w$ turns the first bound into
$|\varphi_{f(a)}(f(w))| \le |\varphi_a(w)|$: a holomorphic self-map of the disc contracts the
pseudo-hyperbolic distance. The chain rule on $h'(0) = \varphi_{f(a)}'(f(a)) \cdot f'(a) \cdot
\varphi_{-a}'(0)$, with $\varphi_b'(b) = (1-|b|^2)^{-1}$ and $\varphi_b'(0) = 1-|b|^2$, turns the
second bound into $|f'(a)| / (1-|f(a)|^2) \le 1/(1-|a|^2)$: the infinitesimal form contracting
the hyperbolic metric of the disc.

**The Riesz factorization theorem (new).** For a bounded holomorphic $f$ on the disc, not
identically zero, the zeros with multiplicity give a countable index $\iota = \sum_{w} \{1,
\dots, \operatorname{ord}_w f\}$ over the nonzero zeros $w$; the multiplicity-weighted Blaschke
condition $\sum \operatorname{ord}_w f \cdot (1 - |w|) < \infty$ strengthens the plain Blaschke
condition of the previous section by carrying the divisor weight through Jensen's inequality
instead of dropping it to one. The matching Blaschke product $B(z) = z^m \prod_i b_{a_i}(z)$
then has the same order as $f$ at every point of the disc, so the quotient $f / B$ extends
holomorphically and without zeros across the disc by the general removable-singularity
extension theorem (`RemovableSingularity`), applied with the open preconnected set taken to be
the disc rather than the whole plane. This gives $f = z^m B g$ with $g$ nonvanishing. The
further fact that $g$ is bounded by the same constant $M$ as $f$ (new, 2026-09-23) is proved
classically: a finite Blaschke prefix $B_S(z) = \prod_{i \in S} b_{a_i}(z)$ has modulus exactly
$1$ on the unit circle, and by uniform continuity of $B_S$ on the closed disc, modulus at least
$1 - \varepsilon$ on circles of radius $r$ close enough to $1$. The quotient $f / (z^m B_S)$
extends holomorphically across $B_S$'s finitely many zeros to $B_S^c \cdot g$, where $B_S^c$ is
the Blaschke product over the complementary (still countable, still summable) index set — the
identity $B = B_S \cdot B_S^c$ splits the infinite product exactly via
`Multipliable.tprod_mul_tprod_compl`, so no removable-singularity argument is needed for this
step. The maximum modulus principle on circles of radius $r \to 1$ then bounds this quotient by
$M / (r^m(1-\varepsilon))$, giving $\|g(z_0)\| \le M$ in the limit for any $z_0$ with $B(z_0)
\ne 0$; a finite prefix $B_{S_N}$ along an exhaustion of the (countable) index set converges to
$B$ itself, transporting the bound to $g(z_0)$ directly. The remaining case, $z_0$ itself a
zero of $B$, follows from continuity of $g$ at $z_0$, since $B$'s zeros are isolated (it is a
nonzero analytic function) and the bound holds on the punctured neighborhood.

**Parseval, the area theorem, Bieberbach and Koebe (new).** For $f$ holomorphic on $|z| < R$
with Taylor coefficients $c_n$ and $r < R$, the restriction to $|z| = r$ has the uniformly
convergent Fourier expansion $f(re^{i\theta}) = \sum c_n r^n e^{in\theta}$; term-by-term
integration gives Cauchy's coefficient formula, the pairing formula
$\int_0^{2\pi} \overline{f(re^{i\theta})}\, G(\theta)\, d\theta = \sum \bar c_n r^n
\int_0^{2\pi} e^{-in\theta} G(\theta)\, d\theta$ for continuous $G$, hence **Parseval's identity**
$\int_0^{2\pi} |f(re^{i\theta})|^2 d\theta = 2\pi \sum |c_n|^2 r^{2n}$, **Gutzmer's inequality**
$\sum |c_n|^2 r^{2n} \le M^2$, and $\int_0^{2\pi} \overline{f}\,(z f')\, d\theta =
2\pi \sum n |c_n|^2 r^{2n}$. Separately, polar coordinates give the Cauchy transform of a disc,
$\int_{|w| < \rho} (z - w)^{-1}\, dA(w) = \pi \bar z$ for $|z| < \rho$. For $g(z) = z^{-1} + h(z)$
injective on the punctured disc (the class $\Sigma$, $h(z) = \sum b_n z^n$), the index of the
curve $g(re^{i\theta})$ about $w$ is $(2\pi i)^{-1}\oint g'/(g - w)$; it is $-1$ on the complement
$E_r$ of the image of the punctured disc of radius $r$ (off the null set $g(|z| = r)$) and $0$ on
the image, by the argument principle for $z(g(z) - w)$. Integrating the index over a large disc
with Fubini and the disc transform gives $-\operatorname{area}(E_r) = (2i)^{-1}\oint
\overline{g}\, g'\, dz$, which Parseval evaluates as $-\pi(r^{-2} - \sum n |b_n|^2 r^{2n})$.
Nonnegativity of the area and $r \to 1$ give **Gronwall's area theorem** $\sum n |b_n|^2 \le 1$.
For $f$ in the class $S$ (injective on the disc, $f(0) = 0$, $f'(0) = 1$, $f = z + a_2 z^2 +
\cdots$), the odd square-root transform $F(z) = z\sqrt{f(z^2)/z^2}$ is injective, and $1/F$ is of
class $\Sigma$ with $b_1 = -a_2/2$, so **Bieberbach's theorem** $|a_2| \le 2$ follows. If $w$ is
omitted by $f$, then $f/(1 - f/w)$ is again of class $S$ with second coefficient $a_2 + 1/w$, so
$|1/w| \le 4$: this is the **Koebe one-quarter theorem**, $f(\mathbb D) \supseteq \{|w| < 1/4\}$.

**Hadamard's three-circle theorem (new).** For $f$ holomorphic and nonvanishing on
$0 < |z| < R$, let $M(r) = \max_{|z|=r} |f(z)|$. Choosing $a$ so that the affine function
$a \log |z| + C$ agrees with $\log M(r_1)$ and $\log M(r_2)$ at $|z| = r_1$ and $|z| = r_2$, the
harmonic function $\varphi(z) = \log |f(z)| - a \log |z|$ (harmonic because $\log |f|$ and
$\log |z|$ both are, away from zeros of $f$ and of $z$) satisfies $\varphi \le C$ on both
bounding circles, hence on the whole open annulus $r_1 < |z| < r_2$ by the maximum principle
for subharmonic functions on bounded open sets (`Perron.SubharmonicOn.le_of_frontier`, whose
frontier is exactly the two circles). This gives $\log M(r) \le t \log M(r_1) +
(1-t) \log M(r_2)$ for $t = (\log r_2 - \log r)/(\log r_2 - \log r_1)$: **$\log M(r)$ is a
convex function of $\log r$**. No branch of $\log f$ is needed on the (not simply connected)
annulus, only $\log |f|$.

**The Green function (new).** For a bounded open set $U$ with the exterior disc property and
$w \in U$, solving the Dirichlet problem with boundary data $\zeta \mapsto \log|\zeta - w|$
gives a harmonic $h$ on $U$ agreeing with $\log|\zeta - w|$ on $\partial U$. The Green function
$G(z) = h(z) - \log|z - w|$ is then harmonic on $U \setminus \{w\}$, has $G(z) + \log|z-w|$
extending harmonically across $w$ (equal to $h$), vanishes at $\partial U$, and blows up to
$+\infty$ at $w$. Nonnegativity of $G$ on $U \setminus \{w\}$ follows from the maximum
principle applied to $-G$, a subharmonic function on the punctured domain whose frontier is
$\partial U \cup \{w\}$: $-G \to 0$ at $\partial U$ and $-G \to -\infty$ at $w$, giving
$-G \le 0$ throughout. The sharper strict positivity, and the symmetry $G(z,w) = G(w,z)$, are
not proved; both need the strong maximum principle for harmonic functions on the (preconnected)
punctured domain.

**The pre-Schwarzian bound (new).** For $f$ holomorphic and injective on the disc and
$z_0$ in the disc, the Koebe transform $\varphi(w) = f(\psi(w))$ with $\psi = $ the disc
Möbius map sending $0$ to $z_0$, normalized as $F(w) = (\varphi(w) - \varphi(0))/\varphi'(0)$,
lies in the class $S$. Its second Taylor coefficient unwinds by the chain rule (using
$\psi'(0) = 1 - |z_0|^2$ and $\psi''(0) = -2\bar z_0(1-|z_0|^2)$, both computed from the
explicit rational formula for the disc Möbius map) to
$\tfrac12\big[(1-|z_0|^2) f''(z_0)/f'(z_0) - 2\bar z_0\big]$, so Bieberbach's bound
$|a_2(F)| \le 2$ gives $|(1-|z_0|^2) f''(z_0)/f'(z_0) - 2\bar z_0| \le 4$: the
**pre-Schwarzian bound**. No normalization of $f$ itself at $0$ is needed, since the bound is
invariant under post-composition of $f$ with an affine map; the full Koebe distortion and
growth theorems, obtained by integrating this pointwise bound along a ray from $0$ to $z$, are
not derived.

**The Koebe distortion theorem and the growth theorem's upper bound (new).** Fix $z_0 = r
e^{i\theta}$ in the disc. Since $f'$ is nonvanishing and the disc is simply connected, $f'$ has
a holomorphic logarithm $L$ with $L(0) = 0$; $\operatorname{Re} L(z) = \log|f'(z)|$. Along the
ray $t \mapsto tu$ ($u = e^{i\theta}$), the pre-Schwarzian bound, multiplied through by $u$ and
using $\bar u u = 1$, gives $|(1-t^2)L'(tu)u - 2t| \le 4$, so
$(2t-4)/(1-t^2) \le \operatorname{Re}(L'(tu)u) \le (2t+4)/(1-t^2)$. Since
$\tfrac{d}{dt}\operatorname{Re} L(tu) = \operatorname{Re}(L'(tu)u)$, integrating from $0$ to
$r$ (the fundamental theorem of calculus for the real part of a path) and evaluating the
explicit antiderivatives $\log(1+t) - 3\log(1-t)$ and $\log(1-t) - 3\log(1+t)$ gives
$\log[(1-r)/(1+r)^3] \le \log|f'(z_0)| \le \log[(1+r)/(1-r)^3]$: the **Koebe distortion
theorem**. The **growth theorem's upper bound** follows from $f(z_0) = \int_0^r f'(tu)u\,dt$,
the triangle inequality for the integral, and the antiderivative $t/(1-t)^2$ of the distortion
upper bound $(1+t)/(1-t)^3$. The growth theorem's lower bound is not derived: it needs a
separate argument bounding the rotation of $f'$ along the ray, not a direct integration of the
distortion theorem.

**Möbius geometry: cross ratio and generalized circles (new).** For the Möbius transformation
$M(z) = (az+b)/(cz+d)$ with $ad-bc \ne 0$, a direct computation gives $M(z_i) - M(z_j) =
(ad-bc)(z_i-z_j) / [(cz_i+d)(cz_j+d)]$ for each pair, and substituting into the cross ratio
$(z_1-z_3)(z_2-z_4)/[(z_1-z_4)(z_2-z_3)]$ cancels the $(ad-bc)^2$ factor and the four
denominators symmetrically, giving invariance of the cross ratio. A **generalized circle** (a
circle, or in the limit a line) is the zero set of $A|z|^2 + 2\operatorname{Re}(\bar B z) + C$
for real $A, C$ and complex $B$. Direct substitution shows translations and nonzero scalings
preserve this form, and the inversion $z \mapsto 1/z$ sends the circle $(A, B, C)$ to
$(C, \bar B, A)$ (clearing denominators in the substituted equation and using
$\operatorname{Re}(\bar B/w) = \operatorname{Re}(Bw)/|w|^2$). Since every Möbius transformation
with $c \ne 0$ decomposes as $z \mapsto a/c - \big[(ad-bc)/c^2\big] \cdot (z + d/c)^{-1}$ — a
translation, an inversion, a scaling, and a further translation — and the $c = 0$ case is
already an affine map, every Möbius transformation sends generalized circles to generalized
circles. A point $z^*$ is **symmetric** to $z$ with respect to the generalized circle through
three distinct points $z_1, z_2, z_3$ when the cross ratio of $z^*, z_1, z_2, z_3$ is the
complex conjugate of the cross ratio of $z, z_1, z_2, z_3$; applying cross-ratio invariance to
both cross ratios shows this relation is itself preserved by every Möbius transformation.

**Liouville's first theorem for elliptic functions (new).** A function $f$ doubly periodic
with respect to a lattice, given as Mathlib's `PeriodPair` (periods $\omega_1, \omega_2$
linearly independent over $\mathbb{R}$), is bounded on all of $\mathbb{C}$ once it is
continuous: the compact closed fundamental parallelogram $\{x\omega_1 + y\omega_2 : x, y \in
[0,1]\}$ has a uniform bound $M$ by compactness, and any $z$, written as $x\omega_1 +
y\omega_2$ in the $\mathbb{R}$-basis given by the periods, is congruent modulo the lattice
(subtracting $\lfloor x\rfloor$ and $\lfloor y \rfloor$ integer periods) to a point of the
parallelogram, so $|f(z)|\le M$ everywhere. If $f$ is in addition entire, boundedness on
$\mathbb{C}$ forces it to be constant by the classical Liouville theorem for bounded entire
functions — this is **Liouville's first theorem**. Liouville's second theorem (the sum of
residues of an elliptic function over a period parallelogram vanishes) and third theorem
(the numbers of zeros and poles, counted with multiplicity, agree) still are not proved as
theorems — but, unlike before, both of their prerequisite building blocks now are, described
in the next two entries; only the final assembly is missing.

**The parallelogram boundary as a smooth cycle, with its index proved on both sides (new).**
The boundary of the parallelogram with vertices $c, c+\omega_1, c+\omega_1+\omega_2,
c+\omega_2$ is realized as a single $C^\infty$ closed curve rather than four separate line
segments: each edge is reparametrized by `Real.smoothTransition`, a function equal to $0$ up
to its left endpoint and $1$ from its right endpoint on, with every derivative vanishing
exactly at those two endpoints. Summing the four edge terms with this reparametrization glues
them into a single globally $C^\infty$ closed curve, with no case analysis on differentiability
at the corners, since each term is locally constant to all orders exactly where it hands off
to the next. For a point $w$ outside the closed parallelogram, the index of this loop about
$w$ vanishes, by a straight-line homotopy coning the loop toward the vertex $c$: since $c$ and
every point of the loop lie in the closed convex parallelogram, so does the entire homotopy, so
it automatically avoids $w$. The harder half — that the index equals $1$ at every point of the
open interior, for $\omega_1, \omega_2$ positively oriented — is now also proved, by a route
different from the one originally attempted (and shelved) here: rather than tracking a
continuously varying branch of $\log$ or $\arg$ around the whole boundary (delicate to glue
consistently across all four corners), each edge's contribution to the real "turning" integral
$\int \mathrm{Im}[\gamma'/(\gamma-w)]$ is computed as an explicit $\arctan$ antiderivative — the
Lagrange identity $(1+|z|^2)(1+|w|^2)-|1+\bar zw|^2=|z-w|^2$-style computation makes the
relevant quadratic denominator positive-definite, and $\arctan$'s range bound $(-\pi/2,\pi/2)$
then gives, for free, that each edge's contribution lies in $(0,\pi)$, hence the total lies in
$(0,4\pi)$. Since the index is already known to be an integer, this pins it to exactly $1$
without ever computing the total directly or gluing branches across corners at all.

**The boundary integral of a doubly periodic function vanishes (new).** The other classical
ingredient for Liouville 2/3 is that $\oint_{\partial P} f\,dz = 0$ for $f$ doubly periodic:
opposite edges cancel exactly, since one is the periodic translate of the other, traversed in
the opposite direction. Made precise: after a linear reparametrization bringing each edge's
integral to the form $\int_0^1 h(v)\,dv$, the reversal substitution $u=1-v$ relates edge $k$'s
integral to the opposite edge $k+2$'s, using one algebraic fact about the gluing function not
recorded where `Real.smoothTransition` is defined —
$\mathrm{smoothTransition}(1-x)=1-\mathrm{smoothTransition}(x)$, immediate from its own
defining formula as a ratio of two `expNegInvGlue` translates — to simplify the shifted
argument down to exactly "the original point translated by the other period", at which point
periodicity of $f$ finishes it. **Not done**: combining this with the index fact above into
Liouville 2/3 proper. The obstacle is a hypothesis mismatch, not further mathematics: this
lemma needs $f$ *globally* continuous, but a genuinely non-constant elliptic function always
has poles (an entire doubly periodic function is constant, by Liouville 1) and so is never
globally continuous — weakening the hypothesis to continuity near the boundary only (needed to
touch several internal continuity/integrability steps in the proof) remains for future work,
after which the residue theorem and argument principle for cycles (already general enough,
proved independently of this work) apply directly.

**The Pringsheim–Vivanti theorem (new).** A power series $\sum a_n z^n$ with nonnegative real
coefficients and finite radius of convergence $R$ cannot be continued holomorphically across a
neighborhood of the boundary point $R$; equivalently (the contrapositive form proved here), if
$F$ agrees with the series on $\{|z|<R\}$ and extends holomorphically to
$\{|z|<R\}\cup\{|z-R|<\rho\}$ for some $\rho>0$, the series itself already converges at some
real $z_0 > R$. Fix $x_0$ close enough to $R$ (specifically $x_0 = R-\delta$ for
$\delta=\min(\rho,R)/4$) that a genuine disc $\{|w-x_0|<s'\}$, $s'=\rho/2$, sits inside the
extended domain — a short triangle-inequality computation, since the extended domain already
contains $\{|z|<R\}$ and only needs to reach a bit further near $R$. On a *small* circle
$\{|w|=r\}$, $r<R-x_0$, entirely inside the original disc, the Taylor coefficients of the
translate $G(w)=F(x_0+w)$ at $0$ (Mathlib's `circleLaurentCoeff`, a Cauchy-kernel circle
integral) are computed *explicitly*: substituting the series for $F$, moving the sum outside
the integral (justified by uniform convergence of the partial sums on the circle, Weierstrass's
$M$-test — no delicate interchange machinery needed), expanding $(x_0+w)^k$ by the finite
binomial theorem, and evaluating $\oint w^m\,dw$ around the origin (zero unless $m=-1$, when it
is $2\pi i$) picks out a single term from each finite expansion, giving the $n$-th coefficient
as $\sum_k a_k\binom{k}{n}x_0^{k-n}$ — manifestly nonnegative. Since $G$ is in fact holomorphic
on the larger disc $\{|w|<s'\}$ (reaching past $R$), Mathlib's Laurent expansion on an annulus
gives convergence of this same Taylor series at every point out to radius $s'$, in particular at
$z_0-x_0$ for a suitable real $z_0>R$; taking real parts (the coefficients are real) gives an
ordinary real convergent series $\sum_n (z_0-x_0)^n\sum_k[\text{if }n\le k\text{ then }
a_k\binom{k}{n}x_0^{k-n}\text{ else }0]$. Finally, for any finite set $S$ of indices, bounding
$\sum_{k\in S}a_k z_0^k$ by a partial sum over $\{0,\dots,K\}$ ($K=\max S$), expanding
$z_0^k=(x_0+(z_0-x_0))^k$ by the binomial theorem, swapping the two finite sums (an ordinary
`Finset.sum_comm`, since both range over the same rectangle once padded with an
if-then-zero guard — no genuine reindexing needed), and comparing each resulting finite
inner sum to the corresponding infinite tail, bounds $\sum_{k\in S}a_k z_0^k$ by the total of
the already-known-convergent real series, giving $\sum a_k z_0^k$ convergent by comparison.

**The Sokhotski–Plemelj jump relation (new).** For a density $\varphi$ on a circle $\{|w|=R\}$,
the Cauchy-type contour integral $C\varphi(z)=(2\pi i)^{-1}\oint\varphi(w)/(w-z)\,dw$ is
holomorphic off the circle, and classically its boundary values from inside and outside a point
$t$ of the circle differ by the density itself: $C_+(t)-C_-(t)=\varphi(t)$. This is proved for
densities given by an *absolutely summable* two-sided Laurent series
$\varphi(w)=\sum_k c_k w^k$ ($k\in\mathbb Z$, $\sum_k\|c_k\|R^k$ summable). Splitting $c$ into
its nonnegative- and negative-index parts, the two one-sided series $c_+(z)=\sum_n c_n z^n$ and
$c_-(z)=-\sum_n c_{-(n+1)}z^{-(n+1)}$ ($n\in\mathbb N$) are shown to equal $C\varphi(z)$ for
$\|z\|<R$ and $\|z\|>R$ respectively, by first identifying $c$ with the actual Laurent
coefficients of $\varphi$ on its own circle — a term-by-term circle integration (the same
Weierstrass-$M$-test technique and the elementary evaluation of $\oint w^m\,dw$ reused from
`PringsheimVivanti`) picks out $c_n$ regardless of the sign of $n$, since exactly one of the two
one-sided sums contributes the surviving residue — and then invoking Mathlib's Laurent expansion
`hasSum_circleLaurentCoeff_nat` / `hasSum_circleLaurentCoeff_negSucc` to recognize each one-sided
series as the genuine Cauchy-type integral on its side (the latter with a reversed kernel
$(z-w)^{-1}$, whose sign is tracked explicitly). Since $c$ is summable at radius $R$ itself, both
series converge absolutely at any boundary point $t$, giving natural continuations of $C\varphi$
to the boundary from each side; their difference is then $\sum_n c_n t^n+\sum_n
c_{-(n+1)}t^{-(n+1)}=\varphi(t)$ by construction — the jump relation. Not proved: the companion
"sum" identity with a Cauchy principal-value integral, and an explicit $\mathrm{Tendsto}$
statement that these power-series values are literal one-sided limits as $z\to t$ (their
agreement with the actual contour integral on each *open* side is what is proved).

**Paley–Wiener, holomorphic-extension half (new).** The full Paley–Wiener theorem identifies the
entire functions of exponential type with square-integrable restriction to $\mathbb R$ exactly
with the Fourier-type transforms of functions supported on a bounded interval. This is the
classical *preliminary* half (Stein–Shakarchi's own split, SS 4.1): for $f$ integrable on
$[-\tau,\tau]$, the transform $F(z)=\int_{-\tau}^{\tau}f(t)e^{izt}\,dt$ — the (unnormalized-kernel)
Fourier-type transform of $f$ extended by zero outside $[-\tau,\tau]$ — extends holomorphically to
an entire function of exponential type at most $\tau$. Entire-ness is obtained by differentiating
under the integral sign in the *complex* parameter $z$, using Mathlib's parametric-derivative
machinery (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) instantiated with parameter space
$H=\mathbb C$, so the resulting `HasDerivAt` literally is complex differentiability; the needed
locally uniform bound on the derivative of the kernel $e^{izt}$ comes from $t$ ranging over the
fixed compact interval $[-\tau,\tau]$. The exponential type bound is the elementary estimate
$|e^{izt}|=e^{-t\cdot\mathrm{Im}\,z}\le e^{\tau\|z\|}$ for $t\in[-\tau,\tau]$. Not proved: that
$F$ restricted to $\mathbb R$ lies in $L^2(\mathbb R)$ when $f$ does (Plancherel for this
transform — bridging it to Mathlib's abstract $L^2$ Fourier isometry, built by continuous
extension from Schwartz functions with a $2\pi$-normalized kernel, would need a currently-missing
lemma identifying that isometry with the concrete integral on $L^1\cap L^2$ functions), and the
converse ("hard") direction, that every entire function of exponential type $\tau$ with $L^2$
restriction to $\mathbb R$ arises this way (the classical proof needs a mean-square bound on
$\int\|F(x+iy)\|^2\,dx$ uniform in $y$, from the sub-mean-value property of the subharmonic
function $\|F\|^2$ together with the growth bound — a substantial argument, not attempted here).

**Reflection across a circle (new).** The Schwarz reflection principle proved earlier is
specific to the real axis; this is the next classical instance of reflection across an
*analytic arc* — the first genuinely curved case, reflection across a circle $\|z\|=r$. The
proof reduces to the real-axis case via a Cayley-type Möbius map
$\varphi(z) = i(r-z)/(r+z)$,
which sends the circle to the real axis and the disc to the upper half-plane. Every geometric
fact about $\varphi$ needed — which of the three regions a point lands in on which side of the
real axis — follows from a single closed-form identity for its imaginary part,
$\varphi(z).\mathrm{im} = (r^2-\|z\|^2)/\|z+r\|^2$,
obtained directly from $\mathrm{Complex.div\_im}$ and real/imaginary-part algebra. Crucially,
$\varphi$ conjugates circle inversion $z\mapsto r^2/\bar z$ to complex conjugation:
$\varphi(r^2/\bar z) = \overline{\varphi(z)}$,
verified by direct field algebra (clearing denominators via the nonvanishing facts already in
hand). Consequently, for $f$ holomorphic inside the circle, continuous up to it, and
real-valued on it, the function $g := f\circ\varphi^{-1}$ is holomorphic in the upper
half-plane, continuous up to $\mathbb R$, and real-valued there, so the earlier Schwarz
reflection theorem gives an entire extension of $g$ on the transported (inversion-invariant
becomes conjugation-invariant, via the intertwining identity) domain; pulling back along
$\varphi$ — itself holomorphic away from its pole $-r$ — shows the reflected extension of $f$
across the circle, defined directly as $f(z)$ for $\|z\|\le r$ and $\overline{f(r^2/\bar z)}$
for $\|z\|>r$, equals $\mathrm{schwarzReflection}\ g\circ\varphi$ and hence is holomorphic on
the original domain. The domain hypotheses mirror the real-axis case exactly: open and
inversion-invariant, only now also avoiding the inversion pole $0$ and the Möbius pole $-r$.
Not treated: reflection across a general analytic arc (only the circle, not an arbitrary curve
via local conformal straightening) and the Carleman extension principle.

**The chordal metric and spherical derivative (new).** Normal families of *meromorphic*
functions need a metric on the extended plane $\mathbb C\cup\{\infty\}$ (Mathlib's `OnePoint
ℂ`) under which a pole is just an ordinary point — the chordal (spherical) metric. Rather than
verifying the classical closed-form formula
$\chi(z,w) = 2|z-w|/\sqrt{(1+|z|^2)(1+|w|^2)}$
satisfies the triangle inequality directly (a considerably messier computation), `chordalDist`
is *defined* as the Euclidean distance between the images of two points under inverse
stereographic projection `stereographicInv`,
$z \mapsto (2\operatorname{Re}z,\, 2\operatorname{Im}z,\, |z|^2-1)/(|z|^2+1) \in \mathbb R^3,
\qquad \infty \mapsto (0,0,1)$,
landing on the unit sphere in $\mathbb R^3$ (`EuclideanSpace ℝ (Fin 3)`, via the `!₂[\cdot]`
literal notation). Every metric-space axiom — symmetry, the triangle inequality, nonnegativity —
is then inherited for free from the ambient Euclidean metric on $\mathbb R^3$, and definiteness
(distance zero only between a point and itself) follows from proving `stereographicInv`
injective directly: equal third coordinates force equal $|z|^2$, and then equal first/second
coordinates force $z=w$. The classical closed-form formula is recovered afterward as a genuine
*theorem* about this definition — the key algebraic content of that recovery is the identity
$(1+|z|^2)(1+|w|^2) - |1+\bar zw|^2 = |z-w|^2$ underlying the sum of the three squared Euclidean
coordinate differences, verified directly by `field_simp`/`ring` on the real and imaginary parts.
The **spherical derivative** $f^\#(z) = |f'(z)|/(1+|f(z)|^2)$ of a holomorphic function measures
the local chordal-metric distortion of $f$; the one structural fact proved here is its
invariance under post-composition with the inversion $w\mapsto 1/w$, reflecting that inversion
is a chordal isometry of the sphere — a short computation via the quotient rule for `deriv` and
`norm_inv`. Not treated: Marty's criterion for normality (spherical derivatives locally bounded
$\iff$ the family is normal) and Zalcman's rescaling lemma, both of which need a genuine
normal-families compactness theory for sphere-valued function families — allowing degenerate
limits identically equal to $\infty$ — that does not exist anywhere in the project; the
project's existing Montel compactness machinery (`Analysis.Holomorphic.NormalFamily`, shared
with `SeveralComplexVariables`) is built for finite-dimensional vector space targets and does
not transfer directly to the sphere.

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
