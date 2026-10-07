# Synopsis: one complex variable (`ComplexAnalysis`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. The modules in
`ComplexAnalysis/` are the part of the separate one-variable library `lean-CA` that the
Dirichlet and Carlson developments use, directly or through the several-variable modules; each
is an exact copy of the `lean-CA` module of the same name, where the full one-variable theory
is documented. The library depends on Mathlib, the pinned TauCeti library and `ToMathlib`.

Unless stated otherwise, functions take values in an arbitrary complex Banach space $F$.
Mathlib's corresponding statements are often scalar-valued or restricted to discs, annuli or
convex sets. Curves are integrated with Mathlib's curve integral, the integrand $f$ being the
one-form $v \mapsto v\, f(z)$.

## Primitives and Cauchy's theorem on simply connected domains

* **Primitives.** On a simply connected open $U \subseteq \mathbb C$, local primitives glue to a
  global primitive (their differences are locally constant; see
  [topology](SYNOPSIS_TOPOLOGY.md)). Hence every holomorphic $f : U \to F$ has a holomorphic
  primitive, with any prescribed value at a base point; holomorphy on $U$ is equivalent to having
  a primitive; and Morera's rectangle condition with continuity gives a global primitive.
* **Cauchy's integral theorem.** For a closed differentiable curve in a simply connected open
  $U$ and $f$ holomorphic on $U$, $\int_\gamma f = 0$; integrals along curves with the same
  endpoints agree. A continuous $f$ is integrable along any $C^1$ path in its domain.
* **Cauchy's formula with an explicit kernel integral.** For a closed $C^1$ curve $\gamma$ in a
  convex or simply connected open $U$ and $a \in U$ off the curve,
  $\int_\gamma \frac{f(z)}{z - a}\,dz = \bigl(\int_\gamma \frac{dz}{z - a}\bigr) f(a)$; no
  orientation, simplicity or Jordan interior is assumed.
* **Logarithmic derivatives.** Integrating $g'/g$ along a curve gives the endpoint difference of
  any continuous logarithm of $g$, and the integral vanishes along closed curves in a simply
  connected domain where $g$ has no zeros.

## Logarithms and roots

A continuous logarithm of a holomorphic (analytic) function is holomorphic (analytic), with
derivative $g'/g$, also when the source is a complex normed space carrying auxiliary
parameters. On a simply connected open set every nonvanishing holomorphic function has a
holomorphic logarithm and holomorphic $n$-th roots; a branch can be prescribed at one point and
is then unique on connected domains. Families equal to one on a zero section admit logarithms
vanishing there.

## The curve index and cycles

* For a closed piecewise $C^1$ curve $\gamma$ avoiding $a$, the index
  $\operatorname{ind}_\gamma(a) = \frac{1}{2\pi i}\int_\gamma \frac{dz}{z - a}$ is an integer
  (via $\exp\int g'/g = g(1)/g(0)$), equals the winding number of the TauCeti contour library,
  respects reversal and concatenation, vanishes in simply connected domains avoiding $a$, equals
  $1$ inside and $0$ outside a counterclockwise circle (radius zero included), and gives the
  index-weighted formula $\frac{1}{2\pi i}\int_\gamma \frac{f(z)}{z - a}dz =
  \operatorname{ind}_\gamma(a) f(a)$. It is locally constant off the curve, constant on
  components of the complement, and zero on every unbounded component.
* A *cycle* is a finite family of closed curves (integer combinations are realized by
  repetition and reversal); its integral and index are sums over the family. The index is an
  integer off the cycle, locally constant, zero far away, and additive under concatenation.
* **Homology form of Cauchy's theorem.** If a $C^1$ cycle $\Gamma$ in an open $U$ has index zero
  at every point outside $U$, then for every holomorphic $f : U \to F$ and $z \in U$ off the cycle,
  $\frac{1}{2\pi i}\int_\Gamma \frac{f(w)}{w - z}dw = \operatorname{ind}_\Gamma(z) f(z)$ and
  $\int_\Gamma f = 0$ (Dixon's proof). No simple connectivity is assumed.
* Counterclockwise circles are $C^1$ paths whose curve integrals are Mathlib's circle integrals.

## Derivatives, estimates and parametric integrals

* **Cauchy's derivative formula at any interior point.** If $f$ is holomorphic on $B(c, R)$
  and continuous on its closure, then for every $w \in B(c, R)$ and $k \ge 0$,
  $f^{(k)}(w) = \frac{k!}{2\pi i}\oint_{|\zeta - c| = R}\frac{f(\zeta)}{(\zeta - w)^{k+1}}d\zeta$.
* Uniform derivative bounds on closed thickenings of compact subsets of a domain; geometric
  majorants for Taylor coefficients at radii below the disc radius; Cauchy estimates for the
  coefficients of the Cauchy power series, which represents a function analytic on a closed disc
  throughout the open disc.
* **Holomorphic parametric integrals.** Interval integrals of jointly continuous integrands
  holomorphic in a complex parameter are holomorphic; Fubini for continuous integrands on
  rectangles; differentiation under integrals over compact sets with fixed integrable,
  possibly singular, weights; joint continuity of the divided slope
  $(f(y) - f(x))/(y - x)$, including the diagonal.
* **Submean inequality.** For $f$ holomorphic near a closed disc and every $p > 0$, $|f(c)|^p$ is
  at most the circle average of $|f|^p$ (Jensen's formula and the tangent-line inequality); this
  includes exponents below one.

## Injective holomorphic maps

An injective holomorphic function on an open set has nonvanishing derivative, is an open map,
and its inverse on the open image is holomorphic with derivative $1/f'$; any left inverse is
holomorphic on the image. The circle integral of $f'/(f - f(w))$ is $2\pi i$ for a value taken
only at $w$ and zero for an omitted value.

## Geometry, powers and uniqueness

* **Right half-plane.** Products and quotients of numbers with positive real part avoid the
  cut $(-\infty, 0]$; squares of such numbers lie in the slit plane; they have square roots in
  the sector $|\operatorname{Im} x| < \operatorname{Re} x$; finitely many lie in a disc centred on
  the positive axis and contained in the half-plane.
* **Principal powers.** $(xw)^s = x^s w^s$ for $x > 0$, and for two factors in the right
  half-plane; $w^s$ is holomorphic on discs centred at $r > 0$ of radius $r$.
* **Exterior paths.** The compactified paths $u \mapsto t + \frac{1 - u}{u} q(u)$,
  $u \in (0, 1]$, with $q(0) \ne 0$, tend to infinity at $u = 0$, with regular reversed Jacobian
  and normalized node factors.
* **Uniqueness from real data.** Analytic functions on a preconnected domain agreeing on a real
  germ agree; entire functions agreeing on the positive reals are equal.
