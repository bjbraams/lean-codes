# Synopsis: Carlson's special functions (`Carlson`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library formalizes the
theory of special functions as Dirichlet averages, following

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapters 5–9 (cited by section, theorem and equation number, e.g. Theorem 6.8-1, (9.2-10));
* [Carl87] B. C. Carlson, *Dirichlet averages of $x^t\log x$*, SIAM J. Math. Anal. 18 (1987);
* [Carl69] B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969);
* the articles of Carlson (1965, 1966, 1970) and Carlson–Tobey (1968) on hypergeometric means
  and sequences satisfying a binomial theorem.

It builds on [Dirichlet](SYNOPSIS_DIRICHLET.md), whose notation is used: $I$ is a finite index
set, $b \in \mathbb C^{I}$ the Dirichlet parameters with $\Sigma = \sum_ib_i$, $z \in \mathbb C^{I}$
the nodes, and regularized functions are ordinary ones divided by $\Gamma(\Sigma)$. The
*product slit plane* is the set of $z$ with every $z_i \notin (-\infty, 0]$. Statements in
regularized form hold for all complex parameters, including the Gamma poles of the ordinary
normalization. Printed statements of [Carl77] found to be false or in need of qualification are
collected in [CARLSON_ERRATA.md](CARLSON_ERRATA.md).

## 1. R-polynomials (Sections 5.7, 6.1–6.6)

For $n \in \mathbb N$ the regularized polynomial $\mathcal R_n(b, z) = T_b[\langle u, z\rangle^n]$ is
entire in $b$ and polynomial in $z$:
$$\Gamma(n + \Sigma)\,\mathcal R_n(b, z) = N_n(b, z) = \sum_{|m| = n}\binom nm\prod_i(b_i)_{m_i}z_i^{m_i}.$$

* **Algebra.** Homogeneity, the diagonal value, termination and deletion when a parameter
  vanishes (Corollary 6.3-2), equal-node aggregation, the binomial theorem
  $\mathcal R_n(b, z + a\mathbf 1) = \sum_m\binom nm a^{n-m}\mathcal R_m(b, z)$ for all $b$ (so the
  R-polynomials lie in Carlson's class $A_k$ and satisfy (6.4-4); see
  [analysis](SYNOPSIS_ANALYSIS.md)), the linear transformation 6.5-1 (replacing $b_i$ by
  $1 - \Sigma - n$ and $z_j$ by $z_i - z_j$ gives the sign $(-1)^n$), node derivatives, and
  R-polynomials as diagonal derivatives of $\prod_jz_j^{-b_j}$.
* **Generating function (6.6-1).** $\sum_nN_n(b, z)t^n/n! = \prod_i(1 - tz_i)^{-b_i}$ near $t = 0$,
  with its consequences: juxtaposition and addition of parameters, squared nodes, Tobey's
  relation, roots of unity as nodes and averages over regular polygons (as
  ${}_0F_{k-1}$ and ${}_kF_{k-1}$, via Gauss's multiplication formula for Pochhammer symbols).
* **Estimates and growth.** $|N_n(b, z)| \le (\sum_i|b_i|)_n\max_i|z_i|^n$ (6.2-7), bounds for equal
  parameters, small-parameter asymptotics, and the concentration limits of Theorem 6.2-5.
  **Theorem 6.6-2, corrected:** $\|\mathcal R_n\| \le (r + \varepsilon)^n$ eventually and
  $\|\mathcal R_n\| \ge (r - \varepsilon)^n$ infinitely often, $r = \max_i|z_i|$, provided the summed
  parameter at the nodes of maximal modulus is not a nonpositive integer (in particular for
  distinct nodes); as printed the statement fails, with counterexample
  $b = (\tfrac12, -\tfrac12, 1)$, $z = (2, 2, 1)$, for which $R_n = 1$ for all $n$.
* **Continued Taylor representation (Theorem 6.3-1).** If $f$ is holomorphic on $B(A, R)$ and
  $\max_i|z_i - A| < R$, then $\sum_n\frac{f^{(n)}(A)}{n!}\mathcal R_n(b, z - A\mathbf 1)$ converges
  absolutely and locally uniformly in $(b, z)$ to the regularized continuation of the average of
  $f$; zero parameters may be deleted from such averages.
* **Polynomial averages.** The regularized R-polynomials are the moments of a linear functional
  on univariate polynomials, which is the unique entire continuation of the polynomial average
  and commutes with affine substitutions.

## 2. The R-function (Sections 5.9, 6.8, 8.1–8.5)

**Definition.** The regularized $R$-function $\mathcal R_t(b, z) = R_t(b, z)/\Gamma(\Sigma)$ is
defined for every exponent $t \in \mathbb C$, $b \in \mathbb C^{I}$ and $z$ in the product slit plane.
In the strip $\operatorname{Re} t < 0 < \operatorname{Re}(\Sigma + t)$ it is the doubly regularized
Euler integral
$$\mathcal R_t(b, z) = \frac{1}{\Gamma(-t)\Gamma(\Sigma + t)}\int_0^1u^{-t-1}(1 - u)^{\Sigma + t - 1}
\prod_i(1 - u + uz_i)^{-b_i}\,du,$$
and outside the strip it is reached by the denominator-free relations
$\mathcal R_t(b, z) = \sum_ib_i\mathcal R_t(b + e_i, z)$ and
$\mathcal R_t(b, z) = \sum_ib_iz_i\mathcal R_{t-1}(b + e_i, z)$; independence of the number of steps
follows from the identity theorem in the joint variables. It is jointly holomorphic in
$(t, b, z)$ on $\mathbb C \times \mathbb C^{I} \times(\text{slit plane})^{I}$, agrees with the native
average $T_b[\langle u, z\rangle^t]$ whenever the convex hull of the nodes avoids the cut, is the
unique entire continuation of that average in the parameters, and at natural $t$ is the
R-polynomial. On positive data it has the positive-ray representation
$\Gamma(a)\Gamma(a')\mathcal R_{-a'}(b, z) = \int_0^\infty s^{a-1}\prod_i(z_i + s)^{-b_i}ds$,
$a + a' = \Sigma$.

**Functional identities**, all on the full slit domain and for all parameters:

* the third associated relation
  $\mathcal R_t(b, z) = (\Sigma + t)\mathcal R_t(b + e_i, z) - tz_i\mathcal R_{t-1}(b + e_i, z)$, parameter
  lowering, tangential relations
  $(z_i - z_j)\,t\,\mathcal R_{t-1}(b + e_i + e_j, z) = \mathcal R_t(b + e_i, z) - \mathcal R_t(b + e_j, z)$,
  Zill's relation and Carlson's Exercises 5.9-6 to 5.9-10, 5.9-13;
* node derivatives $\partial_{z_i}\mathcal R_t = t\,b_i\mathcal R_{t-1}(b + e_i, z)$, second derivatives,
  the translation and Euler identities $\sum_i\partial_i\mathcal R_t = t\mathcal R_{t-1}$,
  $\sum_iz_i\partial_i\mathcal R_t = t\mathcal R_t$, and the Euler–Poisson system (6.4-2);
* **Euler's transformation (Theorem 6.8-3)** $\mathcal R_t(b, z) = \prod_iz_i^{-b_i}\mathcal
  R_{-\Sigma - t}(b, z^{-1})$;
* homogeneity $\mathcal R_t(b, \mu z) = \mu^t\mathcal R_t(b, z)$ (5.9-3) when
  $\arg\mu + \arg z_i \in (-\pi, \pi)$, permutation symmetry, equal-node aggregation and deletion
  of a zero parameter;
* contour representations: formula (6.8-7) on $C^1$ cycles homologous to zero in the slit
  domain and avoiding the hull of the nodes, a logarithmic contour formula, and the continued
  circle-Cauchy representation.

**Representations and limits.**

* **Integral evaluations (§8.1).** Euler-type integrals along straight paths
  $\int_0^1u^{a-1}(1 - u)^{a'-1}\prod_i((1 - u)p_i + uq_i)^{-b_i}du$ (Formula 8.1-1, for all complex
  parameters when each affine factor stays in the slit plane) and along rays (8.1-2, 8.1-3, with
  the principal-phase condition explicit) are Gamma multiples of $R$-values; the Mellin
  transform of $\prod_i(z_i + s)^{-b_i}$ is an $R$-function; Exercises 8.1-1, 8.1-2, 8.1-3, 8.1-5,
  8.1-6 (the average of $(u\cdot x)^{-a}(u\cdot y)^{-a'}$).
* **Small-variable limit (Theorem 8.3-2).** With $a + a' = \Sigma$ and
  $\operatorname{Re}(a' - b_k) > 0$, as $z \to z_0$ with $(z_0)_k = 0$ through the right
  half-plane (the other nodes varying),
  $\mathcal R_{-a}(b, z) \to \frac{\Gamma(a' - b_k)}{\Gamma(a')}\mathcal R_{-a}(b^{\hat k}, z_0^{\hat k})$,
  the $k$-th coordinate deleted.
* **Confluence (Section 5.10).** $R_t(b, \mathbf 1 + z/t) \to S(b, z)$ as $t \to \infty$ in
  $\mathbb C$, with perturbed nodes $1 + \zeta(t)/t$, $\zeta(t) \to z$ (5.10-9); the Laplace
  representation $\mathcal R_{-a}(b, z) = \Gamma(a)^{-1}\int_0^\infty y^{a-1}\mathcal S(b, -yz)dy$
  (Theorem 5.10-2).
* **Recurrences and dependence (Section 8.4).** The homogeneity recurrence (Relation 8.4-1): with
  $a + a' = \Sigma$ and elementary symmetric polynomials $e_n(z)$,
  $\sum_{n=0}^{|I|}A_n(a, a', b, z)R_{-a-n}(b, z) = 0$, in a division-free polynomial form valid for
  all $t$, $b$ and slit-plane nodes, with a single coefficient family polynomial jointly in the
  exponent parameter, the Dirichlet parameters and the nodes; for equal parameters the
  coefficients are multiples of $e_n$ (Exercise 8.4-1). Lemma 8.4-2 (exponent reduction) and
  **Theorem 8.4-3**: for fixed $t, b$, any $|I| + 1$ associated functions
  $\mathcal R_{t + k_j}(b + m_j, z)$ satisfy a nontrivial linear relation with polynomial
  coefficients in the nodes, on the whole slit domain.
* **Integer parameters (Section 8.5).** A parameter $b_{i_0} = -N$ can be eliminated; terminating
  cases are explicit. **Theorem 8.5-1:** for integral $t$ and $b$, $R_t(b, z)$ is log-rational on
  the slit domain, $Q(z)R = P_0(z) + \sum_iP_i(z)\log z_i$ with polynomials $Q \ne 0$, $P_0$, $P_i$;
  $(z_i - z_j)R_{-1}(e_i + e_j; z) = \log z_i - \log z_j$; Table 8.5-1 (all seven rows) and
  Example 8.5-5. Exercise 8.5-1 gives $R_{-1}(\tfrac12, \tfrac12, 1; x, y, z)$ as a logarithm for
  positive nodes.
* **Equal parameters (Theorems 6.2-6, 6.8-4, Corollary 6.3-7).** $R_t(\beta, \dots, \beta; z)/\Gamma(k\beta)$
  vanishes at $\beta = 0, -1, -2, \dots$, and $\Gamma(\beta)R_t/\Gamma(k\beta)$ is holomorphic in
  $(t, \beta, z)$; the same for general averages and R-polynomials.
* **Ordinary normalization.** The ordinary $R$, $L$, $S$ and $T$ functions are jointly holomorphic
  away from nonpositive integral total parameters and meromorphic on analytic one-variable
  slices; on a transverse parameter line at total parameter $-m$ the residue is $(-1)^m/m!$ times
  the regularized value, and the singularity is removable exactly when that value vanishes.
* **Exterior-path kernels** (Carlson 1969, §5): the regularized exterior-path integrand of the
  integer resolvent is an Euler-type kernel with joint continuation for admissible paths and
  branches; the straight path recovers $\mathcal R$.

## 3. The L-function (Carlson 1987)

$\mathcal L_t(b, z) = \partial_t\mathcal R_t(b, z)$, jointly holomorphic on the domain of $\mathcal R$,
agrees with the native average $T_b[\langle u, z\rangle^t\log\langle u, z\rangle]$ whenever the node hull
avoids the cut, and is its unique entire continuation. Proved, on the slit domain for all
parameters: symmetry, aggregation, coincident-node and singleton values, zero-parameter deletion
((2.2)–(2.4)); positive scaling with the correction $\log\lambda\,\mathcal R_t$ (2.5); Euler
inversion (2.6); the Euler–Poisson system (2.7); the Euler and translation identities
(2.8)–(2.10) with their inhomogeneous $R$-terms; the node derivative (3.5)
$\partial_{z_i}\mathcal L_t = b_i(t\mathcal L_{t-1}(b + e_i, z) + \mathcal R_{t-1}(b + e_i, z))$; the
parameter-raising relations (3.1), (3.2), (3.4), the three-node relation (3.3), the backward shift
(3.7), (3.6), (3.8); the principle that a polynomial $R$-relation in a varying exponent
differentiates to an inhomogeneous $L$-relation whose correction coefficients are the formal
derivatives of the coefficients, applied to the homogeneity recurrence (Theorem 3.1 for that
recurrence); the expansion $\mathcal L_t(b, z) = \sum_n\ell_n(t)\mathcal R_n(b, z - \mathbf 1)$ on
$\max_i|z_i - 1| < 1$, $\ell_n(t) = \frac1{n!}\frac{d^n}{dw^n}(w^t\log w)|_{w=1}$, with the logarithmic
series (5.8) at $t = 0$; and the two-variable identities (2.11), (2.12), (3.9), (3.10), (6.4), (6.5),
(6.6), (6.7), (6.8) and (8.8) listed in §6 below.

## 4. The S- and T-functions

**$S$ (Sections 5.8, 6.3).** $\mathcal S(b, z) = T_b[\exp\langle u, z\rangle] = \sum_n\mathcal R_n(b, z)/n!$,
the series converging absolutely and locally uniformly for all $(b, z)$; it is the unique entire
continuation, jointly entire in parameters and nodes, with
$\partial_{z_i}\mathcal S = b_i\mathcal S(b + e_i, z)$ (Theorem 5.8-2), the translation law
$\mathcal S(b, z + a\mathbf 1) = e^a\mathcal S(b, z)$, symmetry, aggregation and zero-parameter
deletion.

**$T$ and ${}_2F_0$ (Section 5.12).** The average of $w \mapsto e^{1/w}$ continues jointly on the
node domain where the convex hull avoids $0$; a principal-branch continuation extends to all
slit-plane nodes, compatible when the hull lies in the slit plane. Carlson's ${}_2F_0(\alpha, \beta;
x)$: the double and single Euler integrals, continuation through the remainder representation
(5.12-10), symmetry (5.12-2), holomorphy (5.12-4), the error bound (5.12-15) and asymptotic
expansion (5.12-17), continuation to the sector $|\operatorname{ph}(-x)| < 3\pi/2$ (Theorem
5.12-6) with uniform bounds on closed subsectors and the simplified bound (5.12-16), the single
integral (5.12-7), the connection formulas (5.12-18) and (5.12-20) (Theorems 5.12-8, 5.12-9),
and the zero-node limit (5.12-2), (5.12-3).

## 5. Hypergeometric means (Carlson 1965, 1966; Carlson–Tobey 1968)

For positive nodes $x$ and positive parameters $b = cw$ ($w$ normalized weights, $c$ the
concentration), the mean of order $t$ is $M_t = R_t(b, x)^{1/t}$, with $M_0 = \exp
\mathbb E\log\langle u, x\rangle$; every real order is allowed. Complex means, ratio means and
power-transformed means are defined from the continued $R$ and $L$, with derivative-defined
weights equal to $b_i/\Sigma$ for complex parameters.

* **Order and nodes.** $M_t$ is nondecreasing in $t$ on $\mathbb R$, strictly increasing for
  nonconstant nodes, with equality between orders exactly for constant nodes; strictly
  increasing in each node; positively homogeneous; between the smallest and largest node, with
  these as limits at $t \to \mp\infty$; Euler inversion identifies $M_{-\Sigma}$ with the weighted
  geometric mean.
* **Inequalities.** Jensen-type comparisons with arithmetic and weighted power means;
  log-convexity of $t \mapsto \log R_t$ (strict for nonconstant nodes); Minkowski (subadditivity
  above order one, superadditivity below) and Hölder (for nonnegative orders, reversed below
  $-\Sigma$), with equality exactly for proportional vectors; Beckenbach–Dresher for
  $0 < s \le 1 \le t$; the five strict bound chains of Carlson (1966), Theorem 2, with
  exceptional values and refined minima.
* **Concentration.** Continuity in $c$; as $c \to 0$ the means tend to weighted power means
  (geometric at order zero), also for complex orders and slit-plane nodes for $R$ and $L$; as
  $c \to \infty$ to the weighted arithmetic mean. For two distinct nodes (Carlson–Tobey) $R_t$
  strictly decreases in $c$ for $t < 0$ and $t > 1$ and increases for $0 < t < 1$, and $M_t$
  increases for $t < 1$ and decreases for $t > 1$. At order two, $R_2(cw; x) = A^2 + V/(c + 1)$
  for arbitrary real nodes, strictly decreasing and strictly log-convex in $c$.

## 6. Two variables (Sections 6.2–6.11, 8.3)

For $I = \{0, 1\}$, nodes $(x, y)$ and parameters $(u, v)$ or $(\beta, \beta)$:

* **Polynomials.** The explicit numerator $\sum_k\binom nk(b_0)_k(b_1)_{n-k}x^ky^{n-k}$, parity
  (odd-degree equal-parameter polynomials vanish at opposite nodes), contiguous relations at every
  parameter; identification with terminating ${}_2F_1$ in Carlson's six forms (Exercises 6.2-5,
  6.5-2, 6.5-3), special values at $2, -1, \tfrac12$, and Fibonacci numbers.
* **Elementary values.** $(x - y)\mathcal R_{-1}((1, 1); (x, y)) = \log x - \log y$ and the
  squared-logarithm analogue for $L$, in undivided form including coincident nodes; the inverse
  circular and hyperbolic functions as $R_C(x, y) = R_{-1/2}(\tfrac12, 1; x, y)$ (6.9-16),
  trigonometric $R_C$ values (6.9-17), and the arccos/logarithm forms of $R_C$ (6.9-4).
* **Recurrences and inversion.** The three-term recurrence
  $(u + v + t)\mathcal R_{t+1} - ((u + t)x + (v + t)y)\mathcal R_t + txy\mathcal R_{t-1} = 0$, the mixed node
  derivative, the $L$-analogue (3.10); inversion
  $\mathcal R_t((u, v); (x, y)) = x^{t + v}y^{t + u}\mathcal R_{-u-v-t}((v, u); (x, y))$ with the
  $L$-version carrying $\log x + \log y$; the Gauss-series parameter–exponent interchange.
* **Quadratic transformations (6.9-3, 6.10-1).** For all complex $t, \beta$ and
  $\operatorname{Re} x, \operatorname{Re} y > 0$, with $A = ((x + y)/2)^2$, $G = xy$ and
  $q(\beta) = 2^{1-2\beta}\sqrt\pi/\Gamma(\beta)$,
  $$\mathcal R_{2t}(\beta, \beta; x, y) = q(\beta)\,\mathcal R_t(\beta + t, \tfrac12 - t; A, G),\qquad
  \mathcal R_t(\beta, \beta; x^2, y^2) = q(\beta)\,\mathcal R_t(2\beta + t, \tfrac12 - \beta - t; A, G),$$
  the transformed nodes lying in the slit plane; their polynomial forms (6.9-8)–(6.9-11), (6.10-3)
  in division-free form; the hybrid 6.10-4; and the equal-parameter normalization by
  $\Gamma(\beta + \tfrac12)$ (Remark to 6.8-4), jointly holomorphic on slit-plane nodes, for which both
  transformations and the differentiated $L$-identities (6.4), (6.5), (6.8) of [Carl87] hold
  including $\beta = 0, -1, \dots$. Also the ${}_2F_1$ quadratic transformation (Exercise 6.10-1).
* **Means and algorithms.** $R_K(x^2, y^2) = 1/M(x, y)$ for the arithmetic–geometric mean
  (Gauss), $R_K$ and $R_C$ invariance under the AGM and Borchardt steps, Borchardt's algorithm and
  its accelerations (6.10-27)–(6.10-30), and the expansion of $R_C$ near the diagonal and as one
  argument tends to zero (Exercise 6.9-18).
* **Confluent functions.** $S(a, b; x, 0) = {}_1F_1(a; a + b; x)$ (5.8-6), Theorem 6.9-2
  $S(\beta, \beta; x, y) = e^{(x+y)/2}{}_0F_1(\beta + \tfrac12; (x - y)^2/16)$, Kummer's second formula,
  Bessel functions $J_\mu$, $I_\mu$ and spherical Bessel functions as $S$-functions (6.9-18)–(6.9-25),
  three nodes in arithmetic progression ($S$ as ${}_1F_2$, $R$ as ${}_3F_2$).
* **Gauss hypergeometric function (§8.3).** ${}_2F_1$ as an $R$-function (8.3-7), Corollary
  8.3-3, Gauss's theorem $F(\alpha, \beta; \gamma; 1) = \Gamma(\gamma)\Gamma(\gamma - \alpha - \beta)/
  (\Gamma(\gamma - \alpha)\Gamma(\gamma - \beta))$ for $\operatorname{Re}(\gamma - \alpha - \beta) > 0$,
  Kummer's theorems at $-1$ and $\tfrac12$, ${}_3F_2$ as an average of ${}_2F_1$ and its
  transformations at unit argument (Exercises 8.3-1 to 8.3-5, 8.3-10 to 8.3-12).
* **Product formulas (§6.11).** The bilateral generating relation 6.11-1 and Meixner's formula
  6.11-2 for all complex parameters, Ossicini's formula 6.11-3 and Gegenbauer's product formula
  6.11-4 for complex angles, and (6.11-6).
* **Fractional integrals.** Carlson's fractional integral (5.5-14) and its Riemann–Liouville
  form; its continuation in the order with $I^{-n}f = f^{(n)}$ (5.5-16), entire for $f$ holomorphic
  on a convex set and on $\operatorname{Re}\nu > -n$ for $f \in C^n$ on a real interval.

## 7. Jacobi polynomials and series (Chapter 7)

Notation: $p_n$ is the monic Jacobi polynomial with foci $r, s$, $q_n$ Carlson's adjoint function
of the second kind (a Gamma-normalized continued Cauchy average), $\mu(x)$ the mean radius of the
confocal ellipse through $x$. Parameters are complex, with $\alpha + \beta + 2$ not a nonpositive
integer where a basis is needed; coincident foci $r = s$ give Taylor theory.

* **Polynomials.** Standard and shifted Jacobi polynomials over any commutative
  $\mathbb Q$-algebra, derivatives of all orders, the differential equation, exact degree and bases
  under explicit nonvanishing conditions, identification with Carlson's two-node numerator and
  with Mathlib's Legendre and Chebyshev $T, U$ polynomials, Gegenbauer polynomials at every
  parameter, three-term recurrences, the Christoffel–Darboux formula, Bateman's relation; with
  both parameters lowered by the degree they form an Appell sequence (Carlson 1970).
* **Orthogonality and Rodrigues.** Weighted orthogonality for real $\alpha, \beta > -1$ and bilinear
  orthogonality for $\operatorname{Re}\alpha, \operatorname{Re}\beta > -1$, squared norms as a
  Pochhammer factor times a beta function, Rodrigues' formula for real and (on the principal
  branch) complex parameters and at arbitrary complex endpoints, weighted coefficient integrals
  for $C^n$ functions, and orthogonality on complex segments (Theorem 7.8-3).
* **Biorthogonality and finite expansions.** $\oint p_mq_n$ is a multiple of $\delta_{mn}$ on any
  $C^1$ cycle avoiding the focal segment, with the index as factor (Theorem 7.2-1), with contour
  independence under the homology condition; finite expansions at arbitrary complex endpoints
  (Theorem 7.2-2) with coefficients given by continued averages of derivatives.
* **Second-kind functions.** Joint analyticity in parameters, foci and the exterior point;
  differentiation by an index increase and parameter decreases; the adjoint differential
  equation; normalization $x^{n+1}q_n \to 1$; Cauchy representations for
  $\operatorname{Re}\alpha, \operatorname{Re}\beta > -1$ with Plemelj boundary values and principal
  values; the jump (7.8-5) for all complex parameters (by Theorem 8 on rotated slit planes); the
  second-kind recurrence, Casoratian and Christoffel's second summation formula.
* **Growth and convergence (§§7.4–7.6).** $\|p_n(x)\| \le C(\rho + \varepsilon)^n$ on closed
  elliptic discs (recurrence and maximum modulus) and $\|q_n(y)\| \le C(1/\sigma + \varepsilon)^n$ on
  closed elliptic exteriors (deformation of the Euler integral onto Carlson's saddle curve);
  the root limits $\|p_n(x)\|^{1/n} \to \mu(x)$, $\|q_n(y)\|^{1/n} \to 1/\mu(y)$ (Theorem 7.5-1) and for
  maxima on confocal ellipses (7.5-2); convergence and divergence of series of both kinds
  (7.5-3); the Cauchy-kernel expansion $\sum_np_n(x)q_n(y) = (y - x)^{-1}$ on $\mu(x) < \mu(y)$
  (Lemma 7.6-1); **Theorem 7.6-2**: a function holomorphic on an open elliptic disc is the sum
  of its Jacobi series there, uniformly on closed subdiscs, with coefficients on any confocal
  ellipse given as continued averages of $f^{(n)}$ (7.6-8); entire functions have Jacobi
  expansions throughout the plane.
* **Asymptotics.** $q_n(z) \sim C(4/\Lambda(z))^n$ with $C \ne 0$, $\|\Lambda(z)\| = 4\mu(z)$, uniformly
  on compact sets off the segment, for all complex parameters (Laplace's method on the saddle
  curve with explicit error); Theorem 7.4-3 uniformly on compact subsets of Carlson's set $W$;
  Lemma 7.4-1; the exact Chebyshev two-saddle formula (7.4-1) with its dominant-term limit.
* **Applications.** Gegenbauer's and Legendre's addition theorems (7.3-1, (7.3-11)) and Unsöld's
  theorem; the plane-wave expansion with $S$-function coefficients (Example 7.7-1), the Fourier
  cosine expansion, the Jacobi–Anger expansions and Bessel generating functions, Gegenbauer's
  addition theorem for Bessel functions (Example 7.7-4), Sonine's formula, Neumann's series and
  Bessel's integral.
* **Laguerre and Hermite.** Monic Laguerre and Hermite polynomials as limits of Jacobi
  polynomials (Theorems 7.9-1, 7.10-1), Rodrigues formulas, weighted representations and
  orthogonality (7.9-3, 7.9-4, 7.10-3, 7.10-4), their functions of the second kind as confluent
  limits (7.9-4), (7.10-3), Theorem 7.9-5, generating functions and addition formulas.

## 8. Elliptic integrals and conformal maps (Chapters 8 and 9)

**Standard functions.** $R_F(x, y, z) = R_{-1/2}(\tfrac12, \tfrac12, \tfrac12; x, y, z)$,
$R_G$, $R_H$, the complete integrals $R_K$, $R_E$, $R_L$, and $R_C$, with their symmetries and
integral representations, $R_F(x, y, y) = R_C(x, y)$, and the zero-variable limits (8.3-17),
(9.2-3), (9.2-4) ($R_F(x, y, z) \to \frac\pi2R_K(x, y)$ as $z \to 0$, also for $x, y$ anywhere in
the slit plane). Legendre's integrals $F$, $E$, $\Pi$, $K$, $E(k)$ as $R$-functions (9.2-11),
(9.2-14), (9.3-2) whenever $k^2\sin^2\varphi < 1$, their reduction to the symmetric standard basis
((9.2-12)–(9.2-15), Example 9.3-1, Exercise 9.3-1), and the reciprocal-modulus transformation
(Exercise 9.2-2).

**The Schwarz–Christoffel map (§8.2).** $w(z) = R_{-a}(b; z - x)$ satisfies the differential
equation (8.2-1) and the integral formula (8.2-3); it extends continuously to the closed upper
half-plane with vertices $w(x_i)$ and $w(\infty) = 0$. **Theorem 8.2-1:** for distinct real $x_i$,
$0 < b_i < 1$ and $0 < a \le 1$ with $a + 1 = \sum b_i$, $w$ is a bijection of the upper half-plane
onto an open convex polygon, with holomorphic inverse (the proof: a minimum principle places the
image in the polygon, and a proper local homeomorphism onto a simply connected set is
injective). Examples 8.2-2 and 8.2-3: $R_F(z - x_1, z - x_2, z - x_3)$ and Carlson's $v$ map the
upper half-plane onto rectangles whose half-periods are complete integrals (8.2-8)–(8.2-10),
(8.2-20), (8.2-21); the inverses satisfy the Weierstrass equation (8.2-11), (8.2-12) and
$(\operatorname{sn}')^2 = (1 - \operatorname{sn}^2)(1 - k^2\operatorname{sn}^2)$. Also the lemniscate
(Exercise 8.3-7) and the equation $|dx/dt|^p + |x|^p = c^p$ (Exercise 8.3-8).

**Reduction (§9.3).** Carlson's Tables 9.3-1 to 9.3-4 (all rows), each row a polynomial
combination of contiguous relations, and Exercises 9.3-3, 9.3-4; the reduction of the incomplete
and complete third-kind integrals to $R_F, R_H$ and $R_K, R_L$.

**Landen and Gauss (§9.5).** **Theorem 9.5-1** for every complex $t$ in regularized form:
$R_t(\tfrac12, \tfrac12, -t; x^2, y^2, z^2) = R_t(t + 1, -t, -t; u^2, v^2, w^2)$, $u = (x + y)/2$, for
all positive $x, y, z$ (with $v^2, w^2$ complex conjugates when $z$ lies between $x$ and $y$);
Landen's transformations of $R_F$, $R_E$, $R_G$ and $K$; the ascending Landen and descending Gauss
algorithms with limits $(1/M)\operatorname{arcsinh}(M/S)$ and $(1/M)\arcsin(M/T)$, including the
endpoints $s_0 = 0$ and $t_0 = a_0$; $R_E(x^2, y^2) = B/M$ along the AGM (Exercises 9.5-3, 9.5-4).

**Duplication and addition (§§9.6, 9.7).** The duplication theorem
$R_F(x, y, z) = 2R_F(x + \lambda, y + \lambda, z + \lambda)$, $\lambda = \sqrt x\sqrt y + \sqrt x\sqrt z +
\sqrt y\sqrt z$, on the whole slit domain, with the zero-variable form
$\frac\pi2R_K(x, y) = 2R_F(x + \sqrt{xy}, y + \sqrt{xy}, \sqrt{xy})$; convergence of Algorithm 9.6-2 to
$R_F(x_0^2, y_0^2, z_0^2) = 1/L$ for positive initial values. The addition theorem 9.7-1 for
positive variables with Euler's algebraic solution, and (9.7-17)
$R_F(x + \lambda, y + \lambda, \lambda) + R_F(x + \mu, y + \mu, \mu) = \frac\pi2R_K(x, y)$ for $\lambda\mu = xy$.

**Quartic reduction (§9.8).** **Theorem 9.8-1:**
$R_{-1}(\tfrac12, \tfrac12, \tfrac12, \tfrac12; A^2, B^2, C^2, D^2) = 2R_F(X^2, Y^2, Z^2)$,
$X = AB + CD$, $Y = AC + BD$, $Z = AD + BC$, when all of $A, \dots, Z$ have positive real parts,
with the cases $D = 0$ and $X = 0$ (then the right side is $\pi R_K(Y^2, Z^2)$); the quartic-to-cubic
integral identity (9.8-3); for real $y < x$ with four positive linear factors,
$\int_y^x\bigl[\prod(a + \alpha t)\bigr]^{-1/2}dt = 2R_F(U^2, V^2, W^2)$ with Carlson's $U, V, W$ and the
differences $V^2 - U^2$ etc. as products of $2 \times 2$ determinants (9.8-10)–(9.8-13); Exercises
8.5-2, 9.8-3, 9.8-5 and 9.8-6 (the last for quartics with nonnegative coefficients).

**Asymptotics and independence.** $R_F(x, y, z) \sim \log(4\sqrt z/(\sqrt x + \sqrt y))/\sqrt z$ as
$z \to \infty$ (9.2-10) and $R_K(x, y) \sim \log(16x/y)/(\pi\sqrt x)$ as $y \to 0^+$ (8.3-16), for fixed
positive arguments; Exercise 9.2-1; $\sqrt\rho\,R_H(x, y, z, \rho)$ has a nonzero limit as
$\rho \to \infty$, so $R_H$ is linearly independent of $(xyz)^{-1/2}$, $R_F$, $R_G$ over
coefficients polynomial in $\rho$ (part of Theorem 9.2-1).

**Applications (§9.4).** The simple pendulum ((9.4-21), the separatrix (9.4-25) with
$R_C(x^{-2}, x^{-2} - 1) = \operatorname{artanh} x$, rotation (9.4-26)); the anharmonic
oscillator ((9.4-17), period $2\pi R_K(1, 1 + \sigma)$); the perimeter $2\pi R_E(\alpha^2, \beta^2)$
of an ellipse (9.4-5); the arc of a hyperbola (Exercise 9.4-1); the potential
$R_F(\lambda + \alpha^2, \lambda + \beta^2, \lambda + \gamma^2)$ of a charged conducting ellipsoid,
with $[(\lambda + \alpha^2)(\lambda + \beta^2)(\lambda + \gamma^2)]^{1/2}dV/d\lambda = -\tfrac12$ and
$\lambda^{1/2}V \to 1$ ((9.4-9), (9.4-10)); and the mutual inductance of coaxial circles as
$\pi ab\,R_{-3/2}(\tfrac32, \tfrac32; r_+^2, r_-^2)$ (Exercise 9.3-2).

Chapter 9 exercises also proved: 9.2-3 (the $R_F$ and $R_H$ integrals from $\lambda$), 9.5-2, 9.5-5,
9.6-2, 9.7-1 to 9.7-5 (9.7-2 and 9.7-5 with the branch condition of Theorem 9.7-1).
