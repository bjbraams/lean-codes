# Synopsis: Dirichlet measures, integrals, transforms and averages (`Dirichlet`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library is the common
basis of [SimplexMellin](SYNOPSIS_SIMPLEXMELLIN.md) and [Carlson](SYNOPSIS_CARLSON.md). It
depends on all the support libraries: [ToMathlib](SYNOPSIS_ANALYSIS.md),
[Pochhammer](SYNOPSIS_POCHHAMMER.md), [StdSimplexMeasure](SYNOPSIS_STDSIMPLEX.md),
[ComplexAnalysis](SYNOPSIS_CA.md) and [SeveralComplexVariables](SYNOPSIS_SCV.md).

Throughout, $I$ is a finite index set (possibly empty), $E_I$ the standard simplex with the
hyperplane measure $\sigma$, and $b \in \mathbb C^{I}$ the *Dirichlet parameters*. The
*convergence region* is $\{b : \operatorname{Re} b_i > 0\ \forall i\}$, and
$b + e_i$ denotes $b$ with its $i$-th coordinate raised by one. Mathlib has the one-variable
beta and gamma distributions; the multivariate beta function, the Dirichlet distribution and
everything below are formalized here (the TauCeti library has a Dirichlet law, identified with
the one here).

## Multivariate beta functions

$B(b) = \prod_i\Gamma(b_i)/\Gamma(\sum_i b_i)$ for complex $b$, and separately for positive
real $b$; symmetry, nonvanishing on the convergence region, behaviour under integer translates
of parameters. Integral representations: the solid-simplex integrals (DLMF 5.14.1, 5.14.2)
$$\int_{\Delta_n}\prod_{i=1}^n x_i^{b_i - 1}\Bigl(1 - \sum x_i\Bigr)^{b_0 - 1}dx = B(b_0, \dots, b_n),
\qquad \int_{\Delta_n}\prod_{i=1}^n x_i^{b_i - 1}dx = \frac{\prod_i\Gamma(b_i)}{\Gamma(1 + \sum_i b_i)},$$
and, on the hyperplane, $\int_{E_I}\prod_i u_i^{b_i - 1}d\sigma = B(b)$ for real and complex
parameters in the convergence region, with logarithmic-moment majorants.

## The Dirichlet distribution

For $b_i > 0$ the density $B(b)^{-1}\prod_i u_i^{b_i - 1}$ on the interior of $E_I$ defines a
probability measure $\operatorname{Dir}(b)$ on $\mathbb R^{I}$ carried by the simplex (uniform for
$b = \mathbf 1$), invariant under simultaneous permutation of coordinates and parameters.

* **Moments.** $\mathbb E\prod_i u_i^{m_i} = \prod_i(b_i)_{m_i}/(\Sigma)_{|m|}$ with
  $\Sigma = \sum_i b_i$, also for real power products; $\mathbb E u_i = b_i/\Sigma$,
  $\operatorname{Var} u_i = b_i(\Sigma - b_i)/(\Sigma^2(\Sigma + 1))$,
  $\operatorname{Cov}(u_i, u_j) = -b_ib_j/(\Sigma^2(\Sigma + 1))$.
* **Aggregation.** For surjective $f : I \to K$ the pushforward under block sums is
  $\operatorname{Dir}((\sum_{f(i) = k}b_i)_k)$; coordinate marginals are beta laws, and for two
  coordinates the first coordinate has Mathlib's $\operatorname{Beta}(b_0, b_1)$.
* **Gamma construction.** If $X_i$ are independent $\Gamma(b_i, r)$ with a common rate and $I$
  nonempty, then $\sum X_i \sim \Gamma(\Sigma, r)$, $(X_i/\sum_j X_j)_i \sim \operatorname{Dir}(b)$,
  and the two are independent (from radial integration, without analytic continuation). Through
  this, the Dirichlet measure here is identified with TauCeti's Dirichlet law, with transfer of
  integrals.
* **Merging (stick-breaking).** For $a \ne a'$, writing $u_a = v_0 s$, $u_{a'} = v_1 s$, the
  proportions $v$ have the two-point law $\operatorname{Dir}(b_a, b_{a'})$, independent of the
  merged vector, which is Dirichlet with parameter $b_a + b_{a'}$ at the merged coordinate;
  equivalently $\operatorname{Dir}(b)$ is the image of the product law under the merging map
  (proved by moment determination).
* **Averages of affine combinations.** For continuous $f$ and nodes $x \in \mathbb R^{I}$,
  $u \mapsto f(\sum u_i x_i)$ is integrable; Jensen bounds place its average between $f$ at the
  weighted barycentre and the weighted node values for convex $f$ (reversed for concave $f$),
  needing only convexity of the domain. Almost-sure equality of two affine combinations is
  equivalent to equality of the node vectors, so nonconstant nodes give strict Jensen
  inequalities; positive Dirichlet laws have the same null sets as $\sigma$, giving exact
  essential bounds.
* **Concentration.** For normalized weights $w$ and concentration $c$, the second moment of an
  affine combination is $A^2 + V/(c + 1)$ ($A$, $V$ the weighted mean and variance of the
  nodes); two-node averages are beta averages, strictly decreasing in $c$ for strictly convex
  kernels and distinct nodes; as $c \to \infty$, $\operatorname{Dir}(cw)$ concentrates at $w$,
  with explicit bounds for Lipschitz kernels and convergence for $C^1$ kernels.

## Complex Dirichlet integrals

The *regularized Dirichlet density*
$\rho_b(u) = \mathbf 1_{E_I}(u)\prod_i u_i^{b_i - 1}/\Gamma(b_i)$ is entire in $b$ pointwise; the
*regularized Dirichlet integral* of $f$ is $T_b[f] = \int_{E_I}\rho_b f\,d\sigma$, and the
*normalized* integral is $\Gamma(\sum_i b_i)T_b[f]$. On positive real parameters the normalized
integral is the $\operatorname{Dir}(b)$-expectation and $T_b[f]$ is that expectation divided by
$\Gamma(\Sigma)$, for arbitrary integrands. On the convergence region $\rho_b$ is integrable,
$T_b[1] = 1/\Gamma(\Sigma)$, and $b \mapsto T_b[f]$ is analytic for $f$ continuous on the
simplex, jointly analytic with auxiliary parameters for kernels holomorphic on a complex
neighbourhood of the simplex.

* **Parameter shifts.** $u_i\rho_b = b_i\rho_{b + e_i}$, hence $T_b[u_if] = b_iT_{b+e_i}[f]$ and
  $T_b[f] = \sum_i b_iT_{b + e_i}[f]$.
* **Tangential integration by parts.** For $f$ differentiable near the simplex and
  $\operatorname{Re} b_k > 2$,
  $T_b[\partial_{e_j - e_i}f] = T_{b - e_i}[f] - T_{b - e_j}[f]$, without boundary terms (via the
  derivative of $x_+^{a-1}/\Gamma(a)$).
* **Polynomials.** $T_b[u^m] = \prod_i(b_i)_{m_i}/\Gamma(\sum_i(b_i + m_i))$, entire in $b$, and
  the corresponding transforms of multivariate polynomials.

## The regularized Dirichlet transform

An *entire regularized Dirichlet transform* of a kernel $g$ on the simplex is an entire function
of $b \in \mathbb C^{I}$ agreeing with $T_b[g]$ on the convergence region. It is unique when it
exists (identity theorem on the connected convergence region), recognized by its values at
positive real parameters, insensitive to changes of $g$ off the simplex, and linear in $g$.

**Existence.** If $g$ is $C^{(|I| - 1)N}$ near the simplex, $b \mapsto T_b[g]$ continues
analytically to $\{\operatorname{Re} b_i > -N\ \forall i\}$, by an explicit finite formula
(iterating the parameter shift backwards and integrating by parts tangentially); if $g$ is
$C^\infty$ near the simplex the continuation is entire. A parametric version keeps auxiliary
holomorphic parameters throughout (by complexifying the simplex coordinates) and gives joint
analyticity in Dirichlet and auxiliary parameters, with auxiliary differentiation commuting with
the continued transform.

**Structural laws of the continued transform**, for all complex $b$: coordinate
multiplication $T_b[u_ig] = b_iT_{b + e_i}[g]$; the sum rule $T_b[g] = \sum_i b_iT_{b + e_i}[g]$;
tangential differentiation $T_b[\partial_{e_j - e_i}g] = T_{b - e_i}[g] - T_{b - e_j}[g]$;
permutation; monomial multiplication; vanishing at $b_i = 0$ for kernels divisible by $u_i$;
aggregation (the transform of $g \circ \operatorname{Agg}_q$ at $b$ is the transform of $g$ at
the block-summed parameters, for surjective $q$); termwise transformation of uniformly summable
series, and recognition of locally uniformly convergent series of continued transforms.

**Euler integrals.** The doubly Gamma-regularized Euler integral
$\mathcal E_{a, a'}[f] = \frac{1}{\Gamma(a)\Gamma(a')}\int_0^1 u^{a-1}(1 - u)^{a'-1}f(u)\,du$ is
the two-coordinate transform; for a kernel holomorphic near $U \times [0, 1]$ it has a
continuation entire in $(a, a')$ and holomorphic in the auxiliary parameter, stable under
analytic substitution of the exponents.

**Merging identity.** For $a \ne a'$, with $b'$ the merged parameters,
$$\Gamma(b_a + b_{a'})^{-1}\,T_b[g] = \mathcal E_{b_a, b_{a'}}\bigl[v \mapsto T_{b'}[y \mapsto
g(\operatorname{merge}(v, y))]\bigr]$$
natively for continuous kernels and positive parameters, and as an identity of entire functions
whenever the inner transform depends holomorphically on $v$ (as it does for kernels holomorphic
near the simplex). Iterating represents $T_b[g]$ as an iterated Euler integral.

**Gamma poles.** If $G$ is analytic, $\Gamma(c)G$ has at $c = -m$ a local analytic numerator over
$c + m$, with residue $(-1)^m/m!$ times $G$; the singularity is removable on a transverse line
exactly when $G$ vanishes there. If $G$ vanishes along every exceptional hyperplane, the product
extends jointly analytically (Hartogs).

## Carlson's Dirichlet averages

For nodes $z \in \mathbb C^{I}$ and a scalar function $f$, the *regularized Dirichlet average*
is $\mathcal R_b(z; f) = T_b[u \mapsto f(\sum_i u_iz_i)]$; Carlson's average is
$\Gamma(\Sigma)\mathcal R_b(z; f)$, the $\operatorname{Dir}(b)$-expectation of
$f(\langle u, z\rangle)$ for positive parameters. The affine form maps the simplex onto the convex
hull of the nodes.

* **Elementary properties.** Symmetry under simultaneous permutation of parameters and nodes,
  the constant-node value $f(c)/\Gamma(\Sigma)$, affine substitution, linearity, termwise
  averaging of uniformly dominated series (Representation 5.7-2), and equal-node aggregation
  (Theorem 5.2-4) for all complex parameters.
* **Analyticity (Theorem 5.3-3).** For $f$ holomorphic on a convex open $\Omega$ and $b$ in the
  convergence region, $\mathcal R_b(z; f)$ is holomorphic in $z \in \Omega^{I}$ and jointly in
  $(b, z)$.
* **Derivatives.** $\partial_{z_i}\mathcal R_b(z; f) = b_i\mathcal R_{b+e_i}(z; f')$ with
  iterated versions; Carlson's operator identity (5.3-4): with
  $\delta = \alpha + \beta\frac{d}{dx} + \gamma x\frac{d}{dx}$ and
  $\Delta = \alpha + \beta\sum_i\partial_i + \gamma\sum_iz_i\partial_i$, the average of
  $\delta^nf$ is $\Delta^n$ of the average of $f$.
* **Euler–Poisson system (5.4-1).** With
  $\mathcal P_{ij}G = (z_i - z_j)\partial_i\partial_jG + b_i\partial_jG - b_j\partial_iG$,
  $\mathcal P_{ij}\mathcal R_b(\cdot; f) = 0$.
* **Real nodes, finite smoothness.** For real nodes and $f \in C^n$ on an open interval: $C^n$
  regularity of the average, (5.3-2)–(5.3-4), the tangential relation and, for $f \in C^2$, the
  Euler–Poisson system.
* **Divided differences (§5.5).** The unweighted average of $f^{(n)}$ is $n!\,f[z_0, \dots, z_n]$;
  Carlson's Lemma 5.5-1, Newton–Taylor formula (5.5-2), Taylor remainder and the repeated-integral
  representation (5.5-10).
* **Associated relations (§5.6)**, for all complex parameters after continuation: the sum rule,
  the tangential relation
  $(z_i - z_j)\mathcal R_b(z; f') = \mathcal R_{b - e_j}(z; f) - \mathcal R_{b - e_i}(z; f)$, the
  three-node relation
  $(z_i - z_j)G(b - e_k) + (z_j - z_k)G(b - e_i) + (z_k - z_i)G(b - e_j) = 0$, multiplication by
  the argument, and relation 5.6-4.

### Cauchy representations

* **Circles (5.11-2).** For $f$ holomorphic on $B(c, R)$ containing the nodes and continuous on
  its closure, and every $n$,
  $\mathcal R_b(z; f^{(n)}) = \frac{n!}{2\pi i}\oint_{|s - c| = R}\mathcal R_b(z; (s - \cdot)^{-n-1})
  f(s)\,ds$; the regularized resolvent $\mathcal R_b(z; (s - \cdot)^{-n-1})$ continues to a function
  jointly holomorphic in all Dirichlet parameters, the nodes and $s$ off the convex hull of the
  nodes, with affine covariance, normalization at infinity and derivatives in $s$ for all
  parameters. The contour expression is the unique entire continuation of the average of
  $f^{(n)}$ and is independent of the enclosing circle.
* **Cycles.** Cauchy's formula for derivatives on $C^1$ cycles homologous to zero; the same
  representation on any $C^1$ cycle in the holomorphy domain, homologous to zero there and
  avoiding the convex hull of the nodes, weighted by its index on the hull, for all complex
  parameters (the contour form of Theorem 6.3-6).

### Analytic continuation

* **Joint continuation (Theorem 6.3-6).** For $f$ holomorphic on a convex open $\Omega$ there is
  $G(b, z)$, holomorphic on $\mathbb C^{I} \times \Omega^{I}$, which for every $z$ is the
  regularized continuation of $\mathcal R_\cdot(z; f)$; likewise for every derivative of $f$.
  All relations above persist on the whole parameter space.
* **Domain-aware continuation.** On an open $D \subseteq \mathbb C$ the node tuples whose convex
  hull lies in $D$ form an open set, connected if $D$ is; a joint continuation on $D$ is required
  to agree with the native average only on such tuples. Such continuations are unique on
  connected $D$, exist on the native node domain of any open $D$, and glue along increasing
  unions of connected domains.
* **Simply connected domains (Carlson 1969, Theorem 8).** If $f$ is holomorphic on a simply
  connected open $D \subseteq \mathbb C$, the regularized average has a continuation entire in
  the Dirichlet parameters and holomorphic in all node tuples in $D^{I}$, coincident nodes
  included; this answers the question at the foot of p. 156 of Carlson (1977). The proof takes
  a convex chart $\varphi : V \to D$ (Riemann mapping), pulls a two-node average back to an
  Euler integral of a holomorphic kernel over a straight segment in $V$ (agreement by endpoint
  deformation), and reduces $k$ nodes to two by the merging identity
  $\mathcal R_b(z; f) = \Gamma(b_a + b_{a'})\,\mathcal R_{(b_a, b_{a'})}\bigl((z_a, z_{a'}); w \mapsto
  \mathcal R_{b'}(z'(w); f)\bigr)$ (Carlson 1969, (4.21)), with removable Gamma poles.
* **Moving simply connected fibres.** For $g(t, p)$ holomorphic on an open
  $\mathcal W \subseteq \mathbb C \times P$ with simply connected fibres $D_p$, the two-node
  average and the Euler integral with endpoints $0, 1$ continue holomorphically in the Dirichlet
  parameters, the nodes and $p$ wherever the nodes lie in $D_p$.
* **Several variables.** For $h$ holomorphic on an open $D \subseteq \mathbb C^n$ whose sections
  by complex lines through two of its points are simply connected (convex and $\mathbb C$-convex
  domains), the average $\mathcal R_b(Z; h) = T_b[u \mapsto h(\sum_iu_iZ_i)]$ with vector nodes
  continues to all node tuples in $D^{I}$, entire in the parameters; for $n = 1$ this recovers
  Theorem 8.
