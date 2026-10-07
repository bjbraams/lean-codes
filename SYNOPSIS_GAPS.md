# Gaps in the Dirichlet, SimplexMellin and Carlson developments

Companion to the [mathematical synopsis](SYNOPSIS.md). The other synopsis files describe what is
proved; this file lists what is not, for the three target libraries. A gap here means that no
corresponding Lean statement exists, or that the statement is proved under narrower hypotheses
than in the source. No gap is represented by an admitted proof: the libraries contain no `sorry`
and no additional axioms. Printed statements of Carlson (1977) found to be false or in need of
qualification are listed separately in [CARLSON_ERRATA.md](CARLSON_ERRATA.md); the corrected
versions are proved.

The detailed section-by-section inventory is `CarlsonCoverage.md`, with the exercise tables
`CarlsonChapter6Exercises.md` and `CarlsonChapter7Exercises.md`; see also `CARLSON_ARTICLES.md`
and `DirichletTransformProgram.md`.

## Dirichlet

* **Theorem 8 of Carlson (1969) beyond simply connected domains.** Continuation of Dirichlet
  averages when the domain of holomorphy is multiply connected, or a Riemann surface, with
  continuation along paths avoiding the collision diagonals. The simply connected method does not
  extend: a proof needs Euler integrals over arbitrary contours with continued branches and
  moving singular endpoints (the endpoint-deformation lemma covers convex domains only), or
  averages on immersed simply connected domains. The same applies to moving fibres that are not
  simply connected.
* **Carlson's contour route.** The contour-adapted resolvent branches of Carlson (1969),
  Theorems 4–5, and path independence of the exterior-path kernels.
* **Rectifiable contours.** The Cauchy representations (5.11-2), (6.3-6) and (6.8-7) are proved on
  $C^1$ cycles; rectifiable non-$C^1$ Jordan curves are not covered.
* **Euler–Poisson system for continued averages.** For a general average the system 5.4-1 is
  proved on the native convergence region; its continuation to all complex parameters is proved
  only for the $R$- and $L$-functions.
* **Several variables.** The continuation for vector nodes is proved for kernels
  $h(\sum_iu_iZ_i)$; general kernels $G(u, z)$ depending holomorphically on $u$ in other ways, with
  a fibre condition adapted to the kernel, are not treated, and $\mathbb C$-convexity is not
  formally defined.
* **Merging identity for smooth kernels.** As an identity of entire functions the merging
  identity needs holomorphic dependence of the inner transform on the proportions; smooth
  (non-holomorphic) parameter dependence of continued transforms is not developed.
* **Series of transforms.** Recognition of a series of continued transforms assumes local uniform
  convergence of the transformed series; it is not deduced from bounds on the kernels.

## SimplexMellin

* **The image for general kernels.** The Paley–Wiener description of the image is proved for
  kernels smooth near the simplex and vanishing near its faces; kernels smooth up to the faces
  are not characterized.
* **Inversion with the general integrability hypothesis.** The inversion formula is
  unconditional for smooth kernels vanishing near the faces; for other kernels the integrability
  of the transform on the vertical plane remains a hypothesis.
* **Decay of the simplex Mellin transform.** The stationary-phase decay
  $|\operatorname{Im} b|^{-(|I|-1)/2}$ of $S_g$ in directions where all $\operatorname{Im} b_i$
  have the same sign is not formalized.
* **Master theorems for genuinely multivariable series** $\sum c(n)\prod(-x_i)^{n_i}/n_i!$ (the
  method of brackets).
* **Further directions** of the programme: Euler–Mellin (A-hypergeometric) integrals and
  transforms on symmetric cones.

## Carlson

### Background chapters (Carlson 1977, Chapters 2–4)

These chapters are used through Mathlib's Gamma and beta theory and the project's support
libraries and are not formalized systematically. Items from Chapter 3 not available: the
packaged simple-pole and residue statements of $\Gamma$ at every nonpositive integer, the
ratio asymptotic for real arguments with fixed complex shifts, Weierstrass's product and the
partial-fraction expansions of the digamma function, strict log-convexity of $\Gamma$, the
logarithmic correction series and the sectorial Stirling theorem, the quantitative Gamma
inequalities of §3.10, and the normalized complex Euler integration functional with rotated rays
of §3.11 as a general theory. Many Chapter 3 exercises are open.

### Chapter 5

* The wave, Laplace and potential-theory substitutions (5.4-3)–(5.4-21).
* The Whittaker and other physical special functions of §5.8, and the Tricomi, Whittaker,
  parabolic-cylinder, Macdonald and Hankel identifications (5.12-21)–(5.12-28).
* The confluence limit (5.10-1) for the continued function at non-convergent parameters.
* The real-variable forms of (5.5-10)–(5.5-13) for merely continuous $f$ (covered through
  (5.5-15)).
* Arbitrary-order continued node derivatives of $R$ as a general theorem.

### Chapter 6

* Identifications with symmetric functions ($E_n$, $C_n$ of (6.2-11), (6.2-12); Exercises 6.2-3,
  6.6-11, 6.6-14), Stirling numbers (Exercises 6.6-2, 6.6-3) and Lucas numbers (Exercises 6.9-12,
  6.10-9).
* Legendre and Gegenbauer functions of complex degree (§6.8, Exercises 6.8-1 to 6.8-4); the direct
  Carlson-function forms of §6.7; the equality of the middle and last members of (6.10-18) for
  positive order.
* The transformation group of order six (§6.5) as a group action; the general-order form of
  (6.9-22), which needs a branch condition.
* Exercises 6.3-1 (holomorphy on the plane cut along the segment), 6.3-5 (Appell's $F_1$),
  6.7-6; partial: 6.2-7, 6.2-14 (the homogeneity step), 6.3-6 (joint holomorphy on
  $\mathbb C \setminus \operatorname{con}(z)$), 6.6-9 and 6.6-15 (Jordan-curve forms), 6.9-19 (joint
  entire dependence of ${}_0F_1$ on its parameter).
* The generating relations (2.14), (2.15) of Carlson (1970) in closed form.

### Chapter 7

* **Polynomial asymptotics.** Theorem 7.4-2 and the polynomial part of Corollary 7.4-4 at general
  parameters, which need a formulation accounting for the zeros of the polynomials (see the
  errata); the second-kind part and Theorem 7.4-3 are proved.
* The compact-uniform root limits asserted in Theorem 7.5-1 (the pointwise limits are proved);
  coefficient growth is expressed by explicit bounds rather than $\limsup$.
* **Boundary theory.** Separate boundary values and principal values outside
  $\operatorname{Re}\alpha, \operatorname{Re}\beta > -1$, endpoint finite parts, arbitrary approach
  paths, and branches along contours crossing the focal segment (the jump (7.8-5) itself is
  proved for all parameters).
* The second-kind recurrence at the exceptional values of $\alpha + \beta + 1$ for small degrees.
* **Confluent limits.** The Laguerre second-kind limit assumes $\operatorname{Re}(1 + \beta + n) > 0$;
  the weighted Laguerre and Hermite representations assume growth control also on $f^{(n)}$.
* The physical Examples 7.9-6, 7.9-7 and 7.10-5.
* Open exercises: 7.1-4, 7.1-13, 7.4-2 to 7.4-4, 7.6-1, 7.6-3, 7.6-4, 7.7-9 to 7.7-13, 7.8-2 to
  7.8-4, 7.8-9, 7.8-10, 7.9-3, 7.9-4, 7.9-7, 7.9-9, 7.10-3; partial: 7.5-2.

### Chapter 8

* **Logarithmic boundary behaviour.** The connection formula (8.3-10), the logarithmic series of
  $R_K$ (8.3-13)–(8.3-15), the complex-sector form of (8.3-16), and the remainder after the
  leading logarithm (only leading equivalents are proved).
* **Small-variable limits** through closed sectors avoiding the cut with the other nodes in the
  slit plane (proved through the right half-plane); Corollary 8.3-3 with approach to $1$ from
  outside the unit disc; the terminating cases of Gauss's theorem 8.3-4.
* **General reductions.** Theorems 8.5-3 and 8.5-4, which need formal definitions of the
  function classes, the branch-point splitting formula (8.5-5), and the linear independence of
  $R_C$ and $x^{-1/2}$ over rational functions.
* **Global elliptic functions.** Continuation of the inverses of §8.2 (Weierstrass and Jacobian
  functions) to doubly periodic meromorphic functions by reflection, with their poles and zeros.
* **Branches in §8.1.** Integrals with arbitrary continuously tracked phases beyond
  principal-compatible paths and rays.
* Exercises 8.1-4, 8.2-1 to 8.2-3, 8.3-6, 8.4-2; partial: 8.3-7 (double periodicity of the
  lemniscatic sine); 8.5-1 and 8.5-2 are proved for positive real nodes only.

### Chapter 9

* **Theorem 9.2-1** (linear independence of $(xyz)^{-1/2}$, $R_F$, $R_G$, $R_H$ over rational
  functions), except the $R_H$ part; the supporting formulas (9.2-5)–(9.2-9) and full logarithmic
  expansions.
* **Transformations.** The two-free-parameter transformation (9.5-1) beyond Theorem 9.5-1;
  formula (9.5-18); Carlson's remark extending Theorem 9.5-1 to complex $x, y, z$.
* **Duplication.** Convergence of Algorithm 9.6-2 for complex initial values (the iteration
  identity is proved on the whole slit domain, but convergence needs a uniform lower bound on the
  iterates); the iteration identities and error expansion (9.6-9)–(9.6-12) and Exercise 9.6-1.
* **Applications (§9.4).** The arc of an ellipse (9.4-3), (9.4-4); the surface area of an ellipsoid
  (Example 9.4-2, (9.4-6), (9.4-7)); the capacity of an ellipsoid in $\mathbb R^n$ (9.4-14,
  Exercise 9.8-2); the asymptotics (9.4-23), (9.4-24) beyond Exercise 9.2-1; Exercises 9.4-2 and
  9.4-3 (integrals over a sphere and over $\mathbb R^6$); the asymptotic half of Exercise 9.3-2.
* Other exercises: 9.8-3 with $x = \infty$; 9.8-4; 9.8-6 under its sharp hypothesis
  $b\sqrt e + d\sqrt a \ge 0$ (proved for nonnegative coefficients); the alternative derivations
  asked for in 9.8-1; the numerical Exercise 9.5-6.
* The later computational basis $R_D$, $R_J$ of Carlson's post-1977 papers is not defined.

### The R- and L-functions beyond the book

* **Joint polynomial relations.** Theorem 8.4-3 provides polynomial relations among associated
  $R$-functions for fixed exponent and parameters; their dependence on $(t, b)$ is not
  established (the joint polynomial form is proved for the homogeneity recurrence only), so
  Theorem 3.1 of Carlson (1987) is proved only for that recurrence.
* **Carlson (1987).** Section 4 (the zero-node boundary theory, which needs locally uniform
  control in the exponent) and the logarithmic integrals (2.13)–(2.15); the explicit
  Pochhammer–digamma coefficients (5.3)–(5.7), (5.9)–(5.17) of the $L$-series at general exponents;
  alternative forms of (6.6), (6.7) and the half-integral and Legendre cases of Section 6; the
  real-probability results of Section 7 (bounds and monotonicity of $L$ and $L/R$); the
  positive-integral reductions, three-node exceptional formulas, dilogarithm limit and special
  hypergeometric values of Section 8.
* The complete classification of integral and half-integral parameter configurations by
  elementary functions.

### Hypergeometric means and Carlson's articles

* **Carlson–Tobey (1968).** Concentration monotonicity for arbitrary finitely many nodes (proved
  for two nodes, and at order two for any number); strict derivative signs beyond order two;
  log-convexity in the concentration at negative orders and at integer orders above two;
  concavity for $0 < t < 1$ and convexity for $1 < t < 2$. (Log-convexity for all real orders
  above one is only a conjecture in the paper.)
* **Carlson–Gustafson (1983)** (total positivity) and the remaining articles reviewed in
  `CARLSON_ARTICLES.md` (Appell functions and multiple averages, mixed and logarithmic means,
  averaged integral transforms, the tables of elliptic integrals, the numerical algorithms,
  Jacobian elliptic and theta functions) are not formalized beyond what the book chapters use.

### Domain qualifications

* Functions of the book evaluated at boundary points of their domains (one vanishing variable, as
  in $R_F(x, y, 0)$, or a vanishing $X$ in Theorem 9.8-1) are represented by limits or by the
  limiting function ($\tfrac\pi2R_K$), not by values of the slit-domain function.
* Several theorems are proved for real or right-half-plane data where the book states complex
  slit-plane data; the coverage files list the hypotheses theorem by theorem (in particular
  §§8.1, 8.3 and 9.5–9.7).
