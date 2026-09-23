# Mathematical synopsis, part II: several complex variables

This is the second part of the mathematical synopsis; see [Part I](SYNOPSIS.md) for conventions
and for the libraries this one builds on, and [Part III](SYNOPSIS_CARLSON.md) for the Dirichlet
and Carlson theory that uses it.

Mathlib, at the pinned version, contains the general theory of analytic functions on normed
spaces (power series, the identity principle, Cauchy estimates on discs, the inverse and
implicit function theorems) but essentially no theory of several complex variables as such: no
polydisc Cauchy formula, no Osgood or Hartogs theorem, no Hartogs extension, no domains of
holomorphy, pseudoconvexity or Levi form, no analytic Weierstrass theorems, no analytic sets.
Everything in this part is new relative to Mathlib unless stated otherwise. The library uses
finite index sets $I$ for the coordinates of $\mathbb C^I$ throughout, with the supremum norm;
"finite-dimensional complex normed space" means an arbitrary such space, and results proved in
coordinates are transported along continuous linear equivalences when stated in coordinate-free
form.

Standard references followed by the code are Hörmander (1973), Range (1986), Fritzsche–Grauert
(2002), Scheidemann (2005), Jakóbczak–Jarnicki (2021), Korevaar–Wiegerinck (2017), Boas
(2013), Shabat (1991) and Suwa (2024); the module documentation cites the precise theorem
numbers.

## II.1 Polydiscs, Cauchy's formula, Taylor expansion

For $c \in \mathbb C^n$ and radii $R_j > 0$ let $P(c,R)$ be the open polydisc,
$\overline P(c, R)$ the closed one and $T(c, R)$ the distinguished boundary (torus). Equal-radius
polydiscs are the balls of the supremum norm. Polydiscs are open, closed polydiscs are compact,
and the closure of an open polydisc is the closed one. Origin-centred polydiscs are complete
Reinhardt and logarithmically convex.

**Cauchy's formula on a polydisc.** If $f : \mathbb C^n \to F$ is continuous on
$\overline P(c, R)$ and analytic in each coordinate separately at every point of the closed
polydisc, then for $w \in P(c, R)$
$$f(w) = \frac{1}{(2\pi i)^n}\int_{T(c,R)} \frac{f(\zeta)}{\prod_j (\zeta_j - w_j)}\,d\zeta,$$
with separate radii, proved by iterating the one-variable formula; no joint holomorphy is
assumed. The formula is independent of the enumeration of the coordinates.

**Cauchy coefficients and estimates.** With
$a_\alpha = \frac{1}{(2\pi i)^n}\int_{T(c,R)} f(\zeta)\prod_j (\zeta_j - c_j)^{-\alpha_j - 1} d\zeta$,
one has $a_\alpha = \partial^\alpha f(c)/\alpha!$ (the mixed derivative computed in any order),
independence of the radii, and the sharp Cauchy estimate
$\|\partial^\alpha f(c)\| \le \alpha!\, M \prod_j R_j^{-\alpha_j}$ when $\|f\| \le M$ on the
closed polydisc. Differentiating the higher Cauchy transform in the evaluation point raises the
corresponding kernel exponent.

**Taylor expansion.** Under the same hypotheses $f(c + h) = \sum_\alpha a_\alpha h^\alpha$ for
$|h_j| < R_j$, absolutely, uniformly on smaller closed polydiscs and locally uniformly on the open
polydisc, with the explicit remainder bound $M \sum_{\alpha \notin A}\prod_j (s_j/R_j)^{\alpha_j}$
for $|h_j| \le s_j < R_j$ and any finite set $A$ of multi-indices; mixed derivatives may be taken
termwise. Grouping by total degree gives a convergent formal multilinear series representing $f$
on the whole open equal-radius polydisc, whose diagonal terms are the iterated Fréchet
derivatives. The scalar Taylor coefficients define a multivariate formal power series.

**Mean values.** The torus average of a holomorphic function over any admissible radius is its
value at the center; averaging over rotations gives the volume mean-value formula on equal-radius
polydiscs.

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

**Coordinate derivatives and Cauchy–Riemann.** The coordinate derivative $\partial_j f$ is
defined by slices and equals $Df(z)[e_j]$; $Df(z)[v] = \sum_j v_j\,\partial_j f(z)$; iterated
coordinate derivatives of holomorphic maps are holomorphic and commute; mixed derivatives are
indexed by lists or multi-indices; the chain rule $\partial_i(g \circ f) = \sum_j \partial_i f_j
\cdot \partial_j g \circ f$ and the Jacobian product rule. Holomorphy on an open subset of
$\mathbb C^I$ is equivalent to real differentiability plus the coordinate Cauchy–Riemann
equations $D_{\mathbb R}f(z)[ie_j] = i\,D_{\mathbb R}f(z)[e_j]$; the Wirtinger derivatives
$\partial/\partial z_j$, $\partial/\partial\bar z_j$ are defined from the real derivative, and for
holomorphic $f$ the antiholomorphic ones vanish while the holomorphic ones are the coordinate
derivatives. Formal partial derivatives of multivariate polynomials agree with analytic ones.
Coordinate derivatives commute with relabelling of coordinates.

**Cauchy estimates.** $\|\partial_j f(z)\| \le M/r$ when $\|f\| \le M$ on the closed sup-norm
ball of radius $r$; a one-variable slice version needs only the bound on the boundary circle.

## II.3 Convergence, function spaces, normal families

**Weierstrass convergence.** A locally uniform limit of holomorphic maps on an open subset of a
finite-dimensional complex normed space is holomorphic, and all iterated Fréchet derivatives
(equivalently all mixed coordinate derivatives) converge locally uniformly. Locally uniformly
summable families of holomorphic maps have holomorphic sums with termwise mixed derivatives; a
compactwise summable majorant suffices.

**The space $\mathcal O(U, F)$.** For open $U$ in a finite-dimensional complex space, the
holomorphic maps form a closed subspace of $C(U, F)$ in the compact-open topology, hence a
complete space; evaluation, restriction to open subsets and coordinate differentiation are
continuous. Restriction $\mathcal O(V, F) \to \mathcal O(U, F)$ for $U \subseteq V$ is a
continuous linear map, injective when $V$ is connected and $U \ne \varnothing$, and when it is
bijective its inverse is continuous (open mapping theorem for complete metrizable spaces, Part
I.3); correspondingly the scalar holomorphic algebras of a common extension pair are isomorphic.

**Holomorphic $L^p$ spaces.** The classes in $L^p(U)$ with a holomorphic representative form a
closed subspace ($1 \le p \le \infty$), by the local estimate $|f(z)| \le C_K \|f\|_{L^p}$ on
compact $K \subseteq U$ derived from the volume mean-value formula and Hölder; for $p = 2$ and a
Hilbert target this is a Hilbert space.

**Montel and Vitali.** A family in $\mathcal O(U, F)$ bounded on every compact subset is
equicontinuous; with finite-dimensional $F$ it has compact closure and every sequence has a
locally uniformly convergent subsequence. A bounded-on-compacts sequence converging pointwise on
a nonempty open subset of a connected open $U$ converges locally uniformly on $U$.

**Parametric integrals.** Holomorphy of $x \mapsto \int H(x, a)\,d\mu(a)$ on an open subset
of a finite-dimensional complex space, under a local dominated-derivative criterion, or under a
local integrable majorant of $H$ itself (the derivative is then dominated by the Schwarz
estimate); holomorphic dependence of compact contour integrals $\int_K g(a) H(x, \gamma(a))
d\mu(a)$ with a fixed integrable weight $g$ and a jointly analytic kernel, and of circle integrals
$\oint H(x, \zeta) f(\zeta)\,d\zeta$ with merely continuous boundary data $f$.

**Uniqueness from real parameters.** Entire functions of finitely many variables agreeing on
the positive real orthant agree everywhere.

## II.4 Identity principle, maximum modulus, mappings

**Identity theorem.** Holomorphic maps on a connected open subset of a finite-dimensional complex
normed space that agree on a nonempty open subset agree everywhere (agreement on a set with an
accumulation point does not suffice in several variables).

**Maximum modulus.** If the norm of a holomorphic map into a strictly convex Banach space
(in particular a scalar function) has a local maximum at an interior point of a connected open
set, the map is constant.

**Biholomorphic maps.** An equivalence of open sets whose two maps are holomorphic; derivative
identities; equality of dimensions; the holomorphic inverse mapping theorem (invertible
derivative gives a local biholomorphism) and local injectivity from an injective derivative;
affine maps and shears as examples; Jacobian formulation in coordinates.

**Implicit mapping theorem.** For holomorphic $f : P \times Q \to R$ with invertible partial
derivative in $Q$ at $(a, b)$, the level set $f(x, y) = f(a, b)$ is, on an open product
neighborhood, exactly the graph of a holomorphic map $y = g(x)$, with uniqueness and the formula
for $g'$; the corresponding homeomorphism from the local zero set to the parameter neighborhood.

**Injective holomorphic maps.** An injective holomorphic map between equal-dimensional
finite-dimensional complex spaces has invertible derivative everywhere and is biholomorphic onto
its open image (Fritzsche–Grauert I.8.5–8.6). The proof excludes critical points through regular
hypersurface points of the critical set, immersion points after restriction to level
hyperplanes, and the one-variable nonsingularity theorem.

**Cartan's uniqueness theorem.** A holomorphic self-map of a bounded domain in a
finite-dimensional space that fixes a point with identity derivative there is the identity on
the component of that point (Montel plus averaging of iterates). Consequences: rigidity from
equal 1-jets, and linearity of biholomorphisms between circular domains fixing the origin.

**Ball automorphisms.** The standard involution of the Euclidean unit ball exchanging an interior
point with the origin: holomorphy, the metric identity, involutivity, transitivity of the
automorphism group on the ball; and the theorem that the Euclidean ball and the polydisc are not
biholomorphic in dimension at least two (Schwarz bounds and the parallelogram identity).

## II.5 Extension theorems

**Hartogs continuation over a connected base.** A function holomorphic on an annular cylinder
$B \times \{r < |w| < R\}$ and on full discs $B' \times \{|w| < R\}$ over a nonempty open part
$B'$ of the connected base $B$ extends holomorphically to $B \times \{|w| < R\}$; no local
boundedness near the missing part is assumed (fixed circle integral plus the identity principle in
the base).

**Hartogs figures and compact holes.** A Banach-valued holomorphic function on a standard
Hartogs figure extends to the full unit polydisc. Hartogs' extension theorem: for an open $D$ in
a finite-dimensional complex space of dimension at least two and a compact $K \subseteq D$ with
$D \setminus K$ connected, every holomorphic $f$ on $D \setminus K$ extends holomorphically to
$D$. The proof is Ehrenpreis' $\bar\partial$ argument: a cutoff $\varphi$ equal to $1$ near $K$,
the compactly supported $\bar\partial$-data of $(1-\varphi) f$, its Cauchy transform in one
variable (Part I.6), and the identity principle. Corollaries: removal of isolated singularities
(no boundedness), punctured polydiscs, spherical shells and exteriors of closed balls in
dimension at least two; in particular a scalar holomorphic function of at least two variables
has no isolated zeros.

**Circular domains and homogeneous expansions.** On a circular open set (invariant under
$z \mapsto e^{i\theta}z$) a holomorphic function is the locally uniformly convergent sum of the
homogeneous polynomials $P_k$ given by the diagonals of its multilinear Taylor coefficients, and
extends to the balanced hull (Scheidemann 2.1.8).

**Reinhardt domains, Laurent series, hulls.** A set is *Reinhardt* if invariant under
independent coordinate rotations, *complete Reinhardt* if also under independent shrinking of
moduli; the logarithmic image and *logarithmic convexity*; geometric convexity of radii
including zero coordinates, the geometric convex hull, and its openness; the complete Reinhardt
hull and the logarithmic Reinhardt hull as minimal hulls. On a connected open Reinhardt domain
$D$ every holomorphic $f$ has a multivariable Laurent expansion
$$f(z) = \sum_{m \in \mathbb Z^n} a_m z^m,\qquad a_m = \frac{1}{(2\pi i)^n}\int_{T(0,r)} f(\zeta)\,\zeta^{-m-1}d\zeta,$$
with coefficients independent of the torus, absolute and locally uniform convergence, uniqueness
of the coefficients of any locally uniformly convergent Laurent series, and vanishing of $a_m$
when $m_j < 0$ and $D$ meets the hyperplane $z_j = 0$ (this keeps the statement meaningful for
Lean's totalized integer powers). Coefficient functionals are continuous on $\mathcal O(D)$ and
finite Laurent sums approximate $f$ uniformly on compact sets. Extension theorems: from a
complete Reinhardt domain to the convergence domain of its Taylor series; from a connected
Reinhardt domain meeting every coordinate hyperplane to its logarithmic hull; to the complete
Reinhardt hull; and completion in a selected set of coordinates.

**Hartogs sets and Hartogs series.** For sets in $E \times \mathbb C$ with rotational symmetry
in the fiber coordinate (and contraction to zero for *complete* Hartogs sets): on an open complete
Hartogs set a holomorphic function has a Hartogs–Taylor expansion $\sum_k a_k(x) w^k$ with
coefficients holomorphic on the base and locally uniform convergence; on a Hartogs set with
preconnected nonempty fibers a Hartogs–Laurent expansion $\sum_{k \in \mathbb Z} a_k(x) w^k$
with single-valued holomorphic coefficients on the projected base (the fiber hypothesis is shown
to be the one needed for global coefficients) and vanishing negative coefficients over fibers
containing zero.

**Power-series convergence domains.** The absolute-convergence set of a multivariable power
series and its interior, the *convergence domain*, are complete Reinhardt and logarithmically
convex; a nonempty convergence domain is path connected; on it the series converges locally
uniformly to an analytic sum. Conversely every nonempty open complete logarithmically convex
Reinhardt set is the convergence domain of some scalar power series (via holomorphic convexity
and Cartan–Thullen below), which characterizes logarithmic convexity among open complete
Reinhardt sets.

**Tube domains and Bochner's theorem.** The tube $T_\Omega = \{z \in \mathbb C^n : \operatorname{Re} z
\in \Omega\}$ over an open connected $\Omega \subseteq \mathbb R^n$. Every Banach-valued
holomorphic function on $T_\Omega$ extends to the tube over the convex hull of $\Omega$
(Hörmander 2.5.10). The proof constructs the maximal star-convex extension base and shows it
is convex using parabolic analytic discs in tubes, the maximum principle, and Thullen's Taylor
continuation lemma, then a path argument for connected bases. Uniqueness of the extension and the
characterization "the tube over $\Omega$ is a domain of holomorphy iff $\Omega$ is convex"
follow.

**Common extension domains.** $U \subseteq V$ is a common analytic extension pair if every
scalar analytic function on $U$ extends to $V$; such extension cannot create new values, and a
common extension domain lies in the real convex hull of the original.

## II.6 Removable singularities and analytic sets

**Riemann extension.** A continuous function analytic off a countable set is analytic. A
locally bounded Banach-valued holomorphic map on the complement of the zero set of a nonzero
scalar holomorphic function extends holomorphically across it (first Riemann extension theorem);
the zero set may be singular and no Weierstrass theory is used (circles avoiding the zero set,
parameter-dependent Cauchy integrals, gluing from a dense subset). The same holds across
relatively closed sets locally contained in proper analytic zero sets ("thin" sets), with a
unique extension, and such complements are connected.

**Analytic subsets.** $A \subseteq U$ is an *analytic subset* of the open set $U$ if it is
locally the common zero set of finitely many scalar analytic functions. Proved: relative
closedness, finite intersections and unions, holomorphic preimages, products, local nature,
biholomorphic transport; a proper analytic subset of a preconnected domain has empty interior;
*regular points* of codimension $q$ (local biholomorphic flattening to the kernel of a surjective
linear map), characterized by full-rank defining equations, relative openness of the regular
locus, and existence of regular hypersurface points of a nonempty proper scalar zero set.

**Codimension two.** Complex codimension at least $q$ is expressed through isolated
intersections with affine complex $q$-planes. Across an analytic subset of codimension at least
two every holomorphic function is automatically locally bounded (Hartogs figures around the
isolated two-dimensional slices) and hence extends (second Riemann extension theorem); restriction
is an isomorphism of holomorphic algebras $\mathcal O(U) \to \mathcal O(U \setminus A)$. The
model case of a coordinate subspace of codimension two is proved independently with Banach
values.

**Local structure of zero sets.** The nonvanishing locus of a nonzero analytic function is dense
and, on connected domains, connected; a product vanishes near a point only if a factor does; a
zero set of a nontrivial germ is contained in the zero set of an analytic function with nonzero
derivative, which straightens it locally to a hyperplane.

## II.7 Domains of holomorphy, holomorphic convexity, pseudoconvexity

**Definitions.** $U$ is a *domain of holomorphy* if no nonempty open overlap admits a common
analytic continuation of all scalar holomorphic functions on $U$ to a point outside $U$; a
*domain of existence* of one function is defined analogously. Every planar open set, every
product of planar open sets, and every convex open set in a finite-dimensional complex space is a
domain of holomorphy; the property is invariant under linear equivalences. The *holomorphic
hull* of $K \subseteq U$ is $\hat K_U = \{z \in U : |f(z)| \le \sup_K|f| \text{ for all } f \in
\mathcal O(U)\}$, and $U$ is *holomorphically convex* if compact subsets have compact hulls.
Products and biholomorphic images of holomorphically convex sets are holomorphically convex.

**Thullen's lemma and the boundary distance.** Cauchy bounds on compact families of balls
control Taylor coefficients weighted by powers of a scalar holomorphic radius function; these
bounds transfer to the hull and give Taylor continuation on the corresponding polydisc.
Consequently, on a domain of holomorphy, the (extended) boundary distance is preserved by hulls:
$\operatorname{dist}(\hat K_U, \partial U) = \operatorname{dist}(K, \partial U)$.

**Cartan–Thullen.** For an open subset $U$ of a finite-dimensional complex normed space the
following are equivalent: $U$ is a domain of holomorphy; $U$ is holomorphically convex; $U$ is
the domain of existence of a single scalar holomorphic function; hulls preserve boundary
distance; hulls preserve polydisc radii. Connectedness is not required and the empty set and the
whole space are included. The direction "holomorphically convex implies domain of existence"
constructs, from a countable family of escaping sequences detecting all local continuation
patches, one function unbounded along all of them by Baire's theorem in $\mathcal O(U)$;
holomorphically convex sets have compact exhaustions by hull-fixed compacts and are characterized
by unboundedness of some holomorphic function on every escaping sequence. Complete
logarithmically convex Reinhardt domains are holomorphically convex (monomial separation).

**Runge domains.** Runge pairs (locally uniform approximation of holomorphic functions on $U$
by those on $V$), Runge domains (approximation by polynomials), the polynomial hull, its
agreement with the entire-function hull, the hull identity $\widehat K_{\text{pol}} \cap U =
\hat K_U$ for Runge domains $U$, compactness of that set for Runge domains of holomorphy, and
examples: complete Reinhardt and circular domains containing the origin are Runge, and Runge
domains are transported by holomorphic maps with polynomial inverses. The Oka–Weil converse is
not included.

**Plurisubharmonic functions and the Levi form.** A real function on an open subset of a
complex normed space is plurisubharmonic if upper semicontinuous with subharmonic restrictions
to complex lines; closure properties, convex functions, real parts, $|f|^p$ and $\log|f|$ of
holomorphic $f$. The *Levi form* of a $C^2$ function $u$ at $a$ in direction $w$ is
$$\operatorname{Lev} u(a; w) = \tfrac14\bigl(D^2u(a)[w,w] + D^2u(a)[iw, iw]\bigr),$$
one quarter of the Laplacian of the slice $t \mapsto u(a + tw)$; a $C^2$ function is
plurisubharmonic iff its Levi form is positive semidefinite; the chain rule
$\operatorname{Lev}(g \circ \Phi)(a; w) = \operatorname{Lev} g(\Phi(a); \Phi'(a) w)$ for
holomorphic $\Phi$.

**Pseudoconvexity.** On a domain of holomorphy in $\mathbb C^n$ the function $-\log
\operatorname{dist}(z, \partial U)$ is plurisubharmonic (Hörmander 2.6.5, via harmonic
majorants on discs and Thullen's radius bound); hence domains of holomorphy are *pseudoconvex*
(carry a continuous plurisubharmonic exhaustion function). Pseudoconvex sets satisfy the
continuity principle for affine analytic discs, domains of holomorphy satisfy it for holomorphic
discs (Kontinuitätssatz), and the continuity principle implies Hartogs convexity (filled
cylinders). The converse direction, the Levi problem, is not treated.

**Levi convexity.** Local $C^2$ defining functions $\rho$ of an open set at a boundary point,
the complex tangent space $\{w : \partial\rho(p)(w) = 0\}$, and the *Levi condition* (Levi form
of every defining function positive semidefinite on the complex tangent space). Independence of
the defining function: derivatives of two defining functions are positively proportional and
their second derivatives agree on tangent vectors up to the same factor, so the condition can be
checked on one defining function; invariance under holomorphic maps with invertible derivative;
convex open sets are Levi pseudoconvex. **Levi's theorem:** a domain of holomorphy with $C^2$
boundary in a finite-dimensional complex normed space is Levi pseudoconvex. The proof uses the
Levi polynomial to build a small analytic disc tangent to the boundary from inside whose boundary
circle lies much deeper in the domain than its center, contradicting the preservation of boundary
distance by hulls. At a *strictly* Levi pseudoconvex boundary point there is a local holomorphic
peak function (value $1$ at $p$, modulus $< 1$ nearby on the closed side) and a local
holomorphic function with modulus tending to infinity at $p$.

## II.8 Local algebra of analytic germs

**The ring of germs.** For a normed space over a nontrivially normed field $k$, the germs at a
point with an analytic representative form a $k$-algebra $\mathcal O_x$; evaluation at $x$ is a
surjective ring homomorphism whose kernel is the unique maximal ideal, a germ is a unit iff its
value is nonzero, analytic maps act by pullback, and over $\mathbb R$ or $\mathbb C$ the ring is
an integral domain. On finite-dimensional complex spaces: the Taylor series of a germ is a
multivariate formal power series determining the germ; the *total order* (least total degree of a
nonzero coefficient) is additive, invariant under analytic coordinate changes, zero exactly for
units, and can be made equal to the order along the last coordinate by a linear shear (Suwa,
Lemma 1.2); an intrinsic, coordinate-independent order.

**Weierstrass division and preparation (analytic).** Let $f$ be holomorphic near $0$ in
$\mathbb C^{n} \times \mathbb C$ with $f(0, w)$ of finite order $d$ in $w$. Every holomorphic
$g$ near $0$ can be written uniquely as $g = q f + r$ with $q$ holomorphic and $r$ a polynomial
of degree $< d$ in $w$ with holomorphic coefficients (division; uniform version for bounded
numerators on a fixed polydisc, via Cauchy division by $w^d$ and a Picard iteration with a
geometric contraction estimate), and $f = e \cdot (w^d + c_{d-1}(z) w^{d-1} + \dots + c_0(z))$
with $e$ nonvanishing and $c_j(0) = 0$ (preparation), uniquely. Both are stated for germs on
arbitrary finite-dimensional parameter spaces. Mathlib's Weierstrass preparation is formal
(adic power series) and does not give these analytic statements.

**Consequences in the germ ring.** In the ring of germs at $0 \in \mathbb C^n$: Weierstrass
division and preparation for polynomials over parameter germs with Mathlib's distinguished
polynomials; a distinguished polynomial is irreducible iff its germ is; the ring is Noetherian
(Jakóbczak–Jarnicki 1.8.6) and a unique factorization domain (irreducible germs are prime,
1.8.4); relative primality of two germs persists at nearby points (via resultants and elimination
of the scalar variable), so the locus where two functions have relatively prime germs is open;
every unit germ has analytic roots of every order; finite families of nonzero germs can be made
simultaneously regular by one linear coordinate change.
