# Synopsis: measure and integration on the standard simplex (`StdSimplexMeasure`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library depends on
Mathlib, the pinned TauCeti library and [Pochhammer](SYNOPSIS_POCHHAMMER.md). Mathlib provides
the standard simplex as an abstract convex object (`Convexity.StdSimplex`) but no measure theory
on it; this library supplies coordinates, measures, integration formulas, smooth functions near
the simplex, moment theory, and divided differences.

For a finite index set $I$ (possibly empty) the *standard simplex* is
$E_I = \{u \in \mathbb R^{I} : u_i \ge 0, \sum_i u_i = 1\}$, its *interior* is the set with all
$u_i > 0$, and the *solid simplex* of radius $r$ is
$\Delta_I(r) = \{x \in \mathbb R^{I} : x_i \ge 0, \sum_i x_i \le r\}$.

## Coordinates

For $i \in I$ the affine hyperplane $H_I = \{\sum_j u_j = 1\}$ is parametrized by the
$|I| - 1$ free coordinates $u_j$, $j \ne i$, with $u_i = 1 - \sum_{j \ne i}u_j$. The standard
vertices form an affine basis of $H_I$ whose barycentric coordinates are the ambient
coordinates. These charts are homeomorphisms onto $H_I$, compatible with coordinate
permutations, and identify Mathlib's intrinsic simplex with its coordinate realization $E_I$
through a closed, measurable topological embedding. Normalization by the coordinate sum is
measurable (defined also at sum zero) and recovers a simplex point and its scale.

**Aggregation.** For a map $f : I \to J$ of finite sets, $(\operatorname{Agg}_f u)_k =
\sum_{f(i) = k} u_i$ maps $E_I$ to $E_J$ and realizes Mathlib's map of simplices induced by $f$;
fibre cardinalities give the exponents in the aggregation densities below.

## The hyperplane measure

Lebesgue measure on any free-coordinate chart pushes forward to a measure $\sigma_I$ on all of
$H_I$, independent of the omitted coordinate, invariant under permutations, $\sigma$-finite,
zero for $I = \varnothing$, with
$$\sigma_I(E_I) = \frac{1}{(|I| - 1)!}\qquad(I \ne \varnothing).$$
No probability normalization is imposed. Its restriction to $E_I$, transported to the intrinsic
simplex, is the *coordinate measure*; integrals agree under the transport. Weighted coordinate
hyperplanes in finite products are null, so almost every simplex point has all coordinates
positive; the interior is open in the intrinsic simplex and measurable.

**Aggregation of measures.** For surjective $f : I \to J$, the pushforward of
$\sigma_I|_{E_I}$ under $\operatorname{Agg}_f$ has density proportional to
$\prod_{k \in J} y_k^{|f^{-1}(k)| - 1}$ with respect to $\sigma_J$; the analogous formula for solid
simplices is obtained by disintegration along the fibres.

## Integration formulas

* Integrals over $E_I$ are computed in any chart; continuous functions are integrable; the
  two-coordinate simplex is the unit interval with Lebesgue measure.
* **Solid simplices.** $\operatorname{vol}\Delta_I(r) = r^{|I|}/|I|!$, and for nonnegative
  measurable $g$, $\int_{\Delta_I(r)} g(\sum_i x_i)\,dx = \int_0^r\frac{s^{n-1}}{(n-1)!}g(s)\,ds$,
  $n = |I|$; slices of solid simplices are solid simplices of reduced radius.
* **Slicing.** Separating $u_i = t$ writes an integral over $E_I$ as an iterated integral over
  $t \in [0, 1]$ and the scaled simplex $(1 - t)E_{I \setminus\{i\}}$, with Jacobian
  $(1 - t)^{|I| - 2}$; dilation of solid simplices.
* **Monomials.**
  $\int_{E_I}\prod_i u_i^{m_i}d\sigma_I = \frac{\prod_i m_i!}{(|I| + \sum_i m_i - 1)!}$ for natural
  exponents, and the integrals of monomials of multivariate polynomials.
* **Radial integration.** In simplicial polar coordinates $x = t u$ ($t = \sum x_i$, $u \in E_I$),
  Lebesgue measure on the closed orthant is the image of $t^{|I|-1}dt \otimes d\sigma_I(u)$; hence
  $\int_{\mathbb R_+^{I}}F = \int_0^\infty t^{|I|-1}\int_{E_I}F(tu)\,d\sigma_I(u)\,dt$ for
  nonnegative measurable and for integrable Banach-valued $F$, with transfer of integrability.
* **General product slices.** Tonelli and Fubini for integrals over an arbitrary measurable
  subset of a product (inner integrals over sections), specialized to regions between two
  graphs; the measurable splitting of the last coordinate in finite products and its measure
  preservation; the Hausdorff-measure slicing formula for a set inside a lower-dimensional
  affine subspace.
* **Simplex fundamental theorem of calculus.** Separating the last free coordinate gives the
  one-dimensional slices along edges used to integrate derivatives.

## Smooth functions near the simplex

A function on $\mathbb R^{I}$ is $C^N$ *near the simplex* if it is $C^N$ on a neighbourhood of
$E_I$. Tangential derivatives in directions $e_j - e_i$ consume one order; restriction to faces,
affine slices $u \mapsto (1 - t)v + te_i$ and division by the nonvanishing "power partition"
denominator preserve the class. These are the differential-operator inputs for tangential
integration by parts in the Dirichlet theory.

## Moments

* **Moment determination.** Finite Borel measures supported on $E_I$ with the same monomial
  moments $\int\prod_i u_i^{m_i}$ are equal; a complex function whose monomial moments all vanish
  vanishes almost everywhere, and everywhere on $E_I$ if continuous.
* **The moment problem on the simplex.** A sequence $a : \mathbb N^{I} \to \mathbb R$ is the
  moment sequence of a finite measure supported on $E_I$ if and only if $a \ge 0$ and $a$
  satisfies the *sum-shift equation* $a(n) = \sum_i a(n + e_i)$; the measure is unique. For two
  coordinates this is Hausdorff's moment problem on $[0, 1]$. Sufficiency uses discrete measures
  with multinomial weights on the lattice points $k/N$, the falling-factorial identity, the
  Stone–Weierstrass theorem and the Riesz–Markov–Kakutani theorem.

## Divided differences and repeated integrals

**Complex kernels.** For nodes $z_0, \dots, z_n$ in a convex domain where $f$ is holomorphic
(coincident nodes allowed), the Hermite–Genocchi divided difference is
$$f[z_0, \dots, z_n] = \int_{E_{n+1}} f^{(n)}\Bigl(\sum_i u_i z_i\Bigr)d\sigma(u).$$
Proved: permutation symmetry; the coalesced value $f[z, \dots, z] = f^{(n)}(z)/n!$; the recurrence
$(z_0 - z_1)f[z_0, \dots] = f[z_0, z_2, \dots] - f[z_1, z_2, \dots]$; the simplex fundamental
theorem of calculus; Newton's interpolation formula with exact divided-difference remainder and
its coalesced Taylor form; and the identification of $n$-fold repeated segment integrals (which
agree with Mathlib's curve integrals) with simplex integrals with coalesced base nodes, for
continuous kernels on convex domains.

**Real nodes.** The same theory for real nodes and kernels $f : \mathbb R \to \mathbb C$ that are
only $C^p$ on an open interval: the simplex fundamental theorem for $C^1$ kernels, the
recurrence (Carlson's Lemma 5.5-1), Newton's formula with exact remainder (Theorem 5.5-2) and
Taylor's formula with Carlson's remainder (5.5-8).
