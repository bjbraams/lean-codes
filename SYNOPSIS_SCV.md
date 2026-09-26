# Mathematical synopsis, part II: several complex variables

This is the second part of the mathematical synopsis; see [Part I](SYNOPSIS.md) for conventions
and for the libraries this one builds on, and [Part III](SYNOPSIS_CARLSON.md) for the Dirichlet
and Carlson theory that uses it.

The several-variable library in this repository is the part of a separate project,
`lean-SCV`, that the Dirichlet and Carlson developments use: polydisc Cauchy theory, analyticity
of holomorphic maps, separate analyticity, locally uniform convergence, and holomorphic
parameter integrals. Its files are exact copies of the corresponding `lean-SCV` modules; the
full several-variable theory (extension theorems, domains of holomorphy, pseudoconvexity,
analytic germs and analytic sets) is described there.

Mathlib, at the pinned version, contains the general theory of analytic functions on normed
spaces (power series, the identity principle, Cauchy estimates on discs) but no polydisc Cauchy
formula and no Osgood or Hartogs theorem. Everything in this part is new relative to Mathlib
unless stated otherwise. The library uses finite index sets $I$ for the coordinates of
$\mathbb C^I$ throughout, with the supremum norm; "finite-dimensional complex normed space"
means an arbitrary such space, and results proved in coordinates are transported along
continuous linear equivalences when stated in coordinate-free form.

Standard references followed by the code are Hörmander (1973), Range (1986), Scheidemann
(2005) and Boas (2013); the module documentation cites the precise theorem numbers.

## II.1 Polydiscs, Cauchy's formula, Cauchy series

For $c \in \mathbb C^n$ and radii $R_j > 0$ let $P(c,R)$ be the open polydisc,
$\overline P(c, R)$ the closed one and $T(c, R)$ the distinguished boundary (torus). Equal-radius
polydiscs are the balls of the supremum norm, and the closure of an open polydisc is the closed
one. A set is Reinhardt if it is invariant under independent coordinate rotations and complete
Reinhardt if it is also invariant under decreasing the coordinate moduli; complete Reinhardt sets
are exactly the unions of closed polydiscs centred at the origin, are path connected, and have
complete Reinhardt interiors, and logarithmic convexity passes to interiors.

**Cauchy's formula on a polydisc.** If $f : \mathbb C^n \to F$ is continuous on
$\overline P(c, R)$ and analytic in each coordinate separately at every point of the closed
polydisc, then for $w \in P(c, R)$
$$f(w) = \frac{1}{(2\pi i)^n}\int_{T(c,R)} \frac{f(\zeta)}{\prod_j (\zeta_j - w_j)}\,d\zeta,$$
with separate radii, proved by iterating the one-variable formula; no joint holomorphy is
assumed. The formula is independent of the enumeration of the coordinates.

**Cauchy series.** The multi-index Cauchy coefficients
$a_\alpha = \frac{1}{(2\pi i)^n}\int_{T(c,R)} f(\zeta)\prod_j (\zeta_j - c_j)^{-\alpha_j - 1}
d\zeta$, grouped by total degree, form a formal multilinear series. For $f$ continuous on a
closed polydisc and separately analytic there, this series converges to $f$ at every point of the
open polydisc and represents $f$ as a power series on the whole open equal-radius polydisc; on
the diagonal its terms are the iterated Fréchet derivatives, so it is the usual Taylor series.

## II.2 Holomorphy, analyticity, separate analyticity

**Holomorphy equals analyticity in finite dimension.** For $U$ open in a finite-dimensional
complex normed space $E$ and $f : U \to F$, $f$ is complex Fréchet-differentiable on $U$ if and
only if $f$ is analytic on $U$. (Mathlib has the one-variable case.) The proof passes through
Osgood's theorem below.

**Osgood.** Jointly continuous and separately holomorphic on an open subset of $\mathbb C^I$
implies jointly analytic.

**Locally bounded separate holomorphy.** Separately holomorphic and locally bounded implies
locally Lipschitz (with the quantitative bound $\|f(y) - f(x)\| \le \frac{nM}{r}\|y - x\|_\infty$
on $\overline P(c, r)$ when $\|f\| \le M$ on $\overline P(c, 2r)$) and hence jointly analytic.

**Hartogs' theorem on separate analyticity.** Let $U \subseteq \mathbb C^I$ be open and $f : U
\to F$. If for every $z \in U$ and every coordinate $i$ the slice $w \mapsto f(z \text{ with }
z_i := w)$ is analytic at $z_i$, then $f$ is analytic on $U$. No continuity or boundedness is
assumed. The proof follows Hörmander and Boas: induction on the number of coordinates; Baire's
theorem gives a thin cylinder of joint analyticity; Hartogs' lemma on the roots of the fiber
Taylor coefficients (a uniform version of pointwise eventual bounds for $|g_k|^{1/k}$, proved
via the volume submean inequality on balls) extends the local bound to the full cylinder; the
locally bounded Osgood theorem closes the induction.

**Coordinate derivatives.** The coordinate derivative $\partial_j f$ is defined by slices and
equals $Df(z)[e_j]$; iterated coordinate derivatives commute, and mixed derivatives are indexed
by lists or multi-indices. The complex Jacobian gives the chain rule
$\partial_i(g \circ f) = \sum_j \partial_i f_j \cdot \partial_j g \circ f$. Formal partial
derivatives of multivariate polynomials agree with analytic ones.

**Cauchy estimates.** $\|\partial_j f(z)\| \le M/r$ when $\|f\| \le M$ on the closed sup-norm
ball of radius $r$; a one-variable slice version needs only the bound on the boundary circle.

## II.3 Convergence and parametric integrals

**Weierstrass convergence.** A locally uniform limit of holomorphic maps on an open subset of a
finite-dimensional complex normed space is holomorphic, and all iterated Fréchet derivatives
(equivalently all mixed coordinate derivatives) converge locally uniformly. Locally uniformly
summable families of holomorphic maps have holomorphic sums with termwise mixed derivatives; a
compactwise summable majorant suffices.

**Parametric integrals.** Holomorphy of $x \mapsto \int H(x, a)\,d\mu(a)$ on an open subset
of a finite-dimensional complex space, under a local dominated-derivative criterion, or under a
local integrable majorant of $H$ itself (the derivative is then dominated by the Schwarz
estimate); holomorphic dependence of compact contour integrals $\int_K g(a) H(x, \gamma(a))
d\mu(a)$ with a fixed integrable weight $g$ and a jointly analytic kernel, and of circle integrals
$\oint H(x, \zeta) f(\zeta)\,d\zeta$ with merely continuous boundary data $f$.

**Uniqueness from real parameters.** Entire functions of finitely many variables agreeing on
the positive real orthant agree everywhere.
