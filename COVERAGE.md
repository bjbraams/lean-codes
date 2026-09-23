# Coverage of `ComplexAnalysis` against standard references

This file records how far the single-variable library `ComplexAnalysis` covers the chapters of
the reference texts listed below, what is instead supplied by the pinned Mathlib release, and
what is missing. It is a working document for the owner and editors; the public description of
what is proved is in [STRUCTURE.md](STRUCTURE.md) and [SYNOPSIS.md](SYNOPSIS.md).

Status labels: **Project** (proved in `ComplexAnalysis`), **Mathlib** (available in the pinned
Mathlib and used as a black box), **Gap** (in neither).

References and requested chapters (PDFs in `ComplexAnalysis/References/`):

* [APP] Agarwal, Perera, Pinelas, *An Introduction to Complex Analysis* (2011), Lectures 25–44.
* [BN] Bak, Newman, *Complex Analysis*, 3rd ed. (2010), Chapters 4–18.
* [Bu] Burckel, *Classical Analysis in the Complex Plane* (2021), Chapters II–VIII.
* [C1] Conway, *Functions of One Complex Variable I* (1978), Chapters IV–XII.
* [C2] Conway, *Functions of One Complex Variable II* (1995), Chapters 13–15, 20, 21.
* [Ga] Gamelin, *Complex Analysis* (2001), Chapters II–VII.
* [He] Heins, *Complex Function Theory* (1968), Chapters IV–VIII.
* [Re] Remmert, *Theory of Complex Functions* (1991), Chapters 6–8.
* [Si] Simon, *A Comprehensive Course in Analysis*, Part 2A (2015), Chapters 2–4.
* [SS] Stein, Shakarchi, *Complex Analysis* (2003), Chapters 2–3.

## 1. What is covered

### 1.1 Cauchy theory

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Curve integrals, primitives, path independence | Project (Banach-valued) | `HasPrimitives`, `CauchyIntegral` | Re 6, Bu II.2, Ga IV.1–2, Si 2.2 |
| Goursat, Cauchy for star regions and discs | Mathlib | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` | Re 7.1–2, Bu V.1, Si 2.4–5, SS 2.1–2 |
| Cauchy's theorem and formula on simply connected open sets | Project (Banach-valued) | `CauchyIntegral`, `CauchyFormula`, `PolygonIntegral` | C1 IV.5, BN 8.1, Si 2.6, He V.4 |
| Homotopy version of Cauchy's theorem ($C^2$ and continuous homotopies, moving endpoints) | Project | `Integral.Homotopy`, `Integral.ContinuousHomotopy` | C1 IV.6, Bu IV.3, SS 3.5, He V.3 |
| Index of a closed $C^1$ curve: integer-valued, locally constant, zero on the unbounded component, circle values, homotopy invariance | Project | `CurveIndex`, `CurveIndex.Continuity`, `CurveIndex.Homotopy` | C1 IV.4, BN 10.1, Bu IV.2–3, Si 3.3 |
| Index-weighted Cauchy formula for one closed curve on a simply connected set | Project | `CurveIndex` | C1 IV.5 |
| Cycles: integrals, integer locally constant index, concatenation and integer multiples | Project | `Cycle` | C1 IV.5, Si 4.1 |
| Homology form of Cauchy's theorem and formula (Dixon), Banach-valued | Project | `Cycle.Cauchy` | C1 IV.5.4, Si 4.2, Bu IV.6 |
| Holomorphy of parametric interval integrals; Fubini for interval integrals; joint continuity of the divided slope | Project | `HolomorphicIntegral` | SS 2.5.3 |
| Continuous and holomorphic logarithms, roots; lifts over homotopies | Project + Mathlib (`Complex.BranchLogRoot`) | `BranchLog`, `BranchLog.Analytic`, `BranchLog.Homotopy` | Bu IV.4, IV.7, BN 8.2, Si 2.6, SS 3.6 |
| Cauchy derivative formulas and estimates on discs | Project (Banach-valued) + Mathlib (`cauchyPowerSeries`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) | `CauchyDerivatives`, `CauchyEstimates`, `CauchySeries` | Re 8.3, Si 3.1–2, BN 5.1 |
| Morera's theorem | Project (global primitive form) + Mathlib | `HasPrimitives` | BN 7.2, Ga IV.6, SS 2.5.1 |
| Holomorphy of parameter integrals | Project | `ParametricIntegral` | SS 2.5.3, Bu II.3 |
| Cauchy–Pompeiu formula and the Cauchy transform | Project | `CauchyPompeiu`, `CauchyTransform` | Ga IV.8 |
| Exterior paths and improper contour integrals | Project | `ExteriorPath`, `ExteriorPath.Integral` | (Carlson-specific) |
| Contours from univalent maps of a disc | Project | `UnivalentDisk.*` | (Carlson-specific) |

### 1.2 Local theory

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Power series, Taylor expansion, identity theorem, isolated zeros | Mathlib | `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` | Re 7.3, 8.1, C1 IV.2–3, Ga V, APP 26 |
| Liouville, fundamental theorem of algebra | Mathlib | `Differentiable.apply_eq_apply_of_bounded`, `Complex.exists_root` | BN 5.2, Ga IV.5 |
| Open mapping, maximum modulus, mean value | Mathlib | `AnalyticOnNhd.is_constant_or_isOpen`, `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, `Complex.circleAverage_eq`-style results | Re 8.5, C1 IV.7, VI.1, Ga III.4–5 |
| Hadamard three lines, Phragmén–Lindelöf | Mathlib | `Complex.norm_le_interp_of_mem_verticalClosedStrip`, `PhragmenLindelof.*` | C1 VI.3–4, BN 15.2 |
| Weierstrass convergence theorems | Mathlib | `TendstoLocallyUniformlyOn.differentiableOn`, `.deriv` | Re 8.4, Bu VII.1 |
| Convergence of iterated derivatives; closed and complete holomorphic function spaces | Project | `LocallyUniform`, `FunctionSpace` | C1 VII.1–2 |
| Montel, Vitali | Project | `Montel`, `Vitali` | C1 VII.2, Bu VII.1–2, Ga XII |
| Hurwitz | Project | `Hurwitz` | APP 37, Bu VII.1 |
| Nonvanishing derivative of injective functions; persistence of zeros | Project | `Injective`, `ZeroPersistence` | Bu V.7 (in part) |
| Riemann removable singularity theorem (discs) | Mathlib (Banach-valued) | `Complex.differentiableOn_update_limUnder_of_bddAbove` | BN 9.1, Ga VI.2 |
| Removal across countable sets and planar analytic zero sets under continuity; gluing across the real axis | Project | `RemovableSingularity`, `RemovableLine` | Bu V.6 (in part) |
| Schwarz reflection across the real axis | Project | `Reflection` | APP 28, SS 2.5.4, C1 IX.1, C2 13.4 (line case) |
| Uniqueness from real parameters | Project | `RealUniqueness` | – |

### 1.3 Singularities, Laurent series, residues

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Laurent expansion on annuli, coefficient estimates, radius independence | Project (Banach-valued) | `LaurentSeries.*` | C1 V.1, APP 25, Ga VI.1, Si 3.7, Bu XI.1 |
| Classification of isolated singularities, Casorati–Weierstrass | Project | `EssentialSingularity` | C1 V.1, Si 3.8, BN 9.1, Ga VI.2 |
| Meromorphic functions, orders, divisors | Mathlib | `MeromorphicAt`, `MeromorphicOn.divisor` | Si 3.9, He VI.4 |
| Residues: definition, Laurent identification, pole formulas, logarithmic derivative | Project | `Residue`, `Residue.LogDeriv`, `Residue.PrincipalPart` | C1 V.2, BN 10, He VI.3 |
| Residue theorem on discs (circle contours) | Project | `Residue` | APP 31, Ga VII.1 (disc case) |
| Argument principle and Rouché on discs | Project | `ArgumentPrinciple`, `Rouche` | C1 V.3, APP 37, SS 3.4, Si 3.3 |
| Residue theorem for cycles homologous to zero, singularities of any type | Project | `Cycle.Residue` | C1 V.2.2, Si 4.3, He VII.1 |
| Argument principle for cycles | Project | `Cycle.ArgumentPrinciple` | C1 V.3.4, Si 4.3 |
| Runge's theorem: poles in `U \ K`; poles in a set meeting every bounded component; polynomials when the complement is connected | Project | `Runge.*` | SS 2.5.5, C1 VIII.1, He V.8, Si 4.7, Bu VIII.1–2 |
| Runge's theorem on open sets: hole-free compact exhaustion, locally uniform rational and polynomial approximation | Project | `Runge.OpenSet` | C1 VIII.1.10–11, Si 4.7, Bu VIII.2 |
| Mittag-Leffler theorem on arbitrary open sets, principal parts of any type | Project | `MittagLeffler` | C1 VIII.3, SS 2.5.5, He VIII.1, Si 4.7, APP 44 |
| Infinite products of holomorphic functions: locally uniform convergence, holomorphy, zeros, orders | Project + Mathlib (`HasProdLocallyUniformlyOn`) | `InfiniteProduct` | C1 VII.5, APP 42, He VIII.2, Bu VII.3 |
| Elementary factors and the uniform estimate | Project | `WeierstrassFactor` | C1 VII.5.11, APP 43, BN 17.1 |
| Weierstrass product with prescribed zeros; factorization of entire functions | Project | `WeierstrassProduct` | C1 VII.5.12–14, APP 43, BN 17.1, He VIII.3 |
| Entire functions of finite order: Jensen's zero counting, summability of `‖a i‖ ^ (-s)` for `s > ρ` | Project + Mathlib (Jensen) | `FiniteOrder` | SS 5.1–5.2, La XIII.3, Si 9.10, C1 XI.2 |
| Canonical products of finite genus: convergence, zeros, lower bounds off small discs, good radii | Project | `CanonicalProduct.*` | SS 5.4, Lemmas 5.3–5.6 |
| Hadamard's factorization theorem (given enumeration of zeros, and intrinsic form) | Project + Mathlib (Borel–Carathéodory) | `Hadamard` | SS 5.5, La XIII.3, Si 9.10, C1 XI.3.4, BN 17.1 |
| Blaschke factors and products; Blaschke condition for bounded functions on the disc; uniqueness theorem | Project + Mathlib (Jensen) | `Blaschke` | Si 9.9, C2 20.2–20.3, Bu XII.1 |
| Multiplicity-weighted Blaschke condition; division by a matching-order function on the disc; Riesz factorization theorem | Project | `RieszFactorization` | Si 9.9, C2 20.2, C1 VII.5 (exercises) |
| Schwarz–Pick lemma (distance and derivative form); hyperbolic metric contraction | Project + Mathlib (Schwarz lemma) | `SchwarzPick` | Ga IX.3, Si 7.4, Bu VI.1 |
| Hadamard's three-circle theorem (log-convexity of the maximum modulus on an annulus) | Project | `ThreeCircles` | La XII.4, Si 5.2, Re 9.3.4 |
| Existence and nonnegativity of the Green function of a domain with the exterior disc property | Project | `GreenFunction` | Ga XV.2, C2 19.7–19.9, Bu IX.7 |
| Locally uniform limits of harmonic functions; Harnack's principle for monotone sequences | Project | `HarmonicLimit` | Ga X.2, C1 X.2, Bu V.5, C2 19.3 |
| Maximum principle with boundary upper limits; Perron families, Poisson modification, Perron's theorem | Project | `Perron` | Ga XV.2–3, C2 19.7, Bu IX.7, He XIII, La VIII.5 |
| Barriers; boundary behaviour of the Perron function; exterior disc criterion; Dirichlet problem on bounded open sets with the exterior disc property | Project | `Perron.Barrier` | Ga XV.4–5, C2 19.8–19.10, Bu IX.8, C1 X.4 |
| Parseval's identity and Gutzmer's inequality for Taylor coefficients on circles; Cauchy transform of a disc | Project | `Parseval`, `DiscCauchyTransform` | Re 8.3, C1 IV (exercises) |
| Area theorem for the class `Σ`; Bieberbach's `‖a₂‖ ≤ 2`; Koebe one-quarter theorem | Project | `AreaTheorem`, `Koebe` | C2 14.6–14.7, He XVII, Bu VI |
| The pre-Schwarzian bound `‖(1-‖z‖²) f''/f' - 2z̄‖ ≤ 4` for injective holomorphic maps of the disc | Project | `KoebeDistortion` | Du 2.6, C2 14.7 |
| The Koebe distortion theorem (both bounds on `‖f'‖`); the growth theorem's upper bound on `‖f‖` | Project | `KoebeGrowth` | Du 2.6, C2 14.7 |
| Cross ratio invariance, generalized circles mapping to generalized circles, and symmetric points under Möbius transformations | Project | `MobiusGeometry` | Si 7.3, He XV, La VII.5, Ga II.7 |
| Liouville's first theorem for elliptic functions: an entire doubly periodic function is constant | Project | `EllipticLiouville` | SS 9.1, La XIV.1, Si 10.3, He XIV.2 |
| The parallelogram boundary as a `C^∞` `Cycle`, with index `0` outside it (index `1` inside not proved) | Project in part | `Cycle.Parallelogram` | C1 IV.5 (chains) |
| Local mapping theorem: `f - f a` of order `m` is locally `m`-to-one with simple preimages | Project | `LocalMapping` | Si 3.4.1, C1 IV.7.4, Bu V.7 |
| Residue at infinity; inversion change of variables in circle integrals; total residue theorem | Project | `ResidueAtInfinity` | Si 3.8, Ga VII.3, APP 33 |
| Partial fractions of `π cot (π z)` | Mathlib | `cot_series_rep` | C1 VII.5, APP 42, Ga VII.4, Si 9.2 |
| Periodic holomorphic functions | Mathlib | `Complex.Periodic` | Si 3.10, Ga VI.5 |
| Jensen's formula | Mathlib | `Complex.JensenFormula` | C1 XI.1, He VIII.5 |
| Gamma and zeta functions | Mathlib | `Complex.Gamma`, `riemannZeta` | C1 VII.7–8, BN 18.3 |

### 1.4 Conformal mapping

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Disc Möbius transformations `(z - a) / (1 - conj a z)`: disc and circle preserved, inverse, derivative | Project | `DiscMobius` | C1 VI.2, Ga IX.2, Bu VI.1 |
| Inverse of an injective holomorphic function is holomorphic; image open | Project | `HolomorphicInverse` | C1 IV.7.6, Bu V.7 |
| Schwarz lemma | Mathlib | `Complex.norm_deriv_le_one_of_mapsTo_ball`, `Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'` | C1 VI.2, Re 9.2, Bu VI.1 |
| Automorphisms of the disc: rotations at a fixed point, `c φ_a` in general | Project | `DiscAutomorphism` | C1 VI.2.5, Ga IX.2, BN 7.2, Bu VI.1 |
| Cayley transform; automorphisms of the upper half-plane by conjugation | Project | `Cayley` | C1 III.3, Ga IX.2 |
| Riemann mapping theorem (existence, normalized) | Project | `RiemannMapping` | C1 VII.4, Ga XI.4, Si 8.1, BN 14.2, Bu IX.2, APP 41 |
| Uniqueness of the normalized Riemann map | Project | `DiscAutomorphism` | C1 VII.4.2, Ga XI.4 |

### 1.5 Harmonic and subharmonic functions

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Harmonic functions: mean value, Poisson formula, Liouville, analyticity, harmonic conjugates on discs | Mathlib | `Mathlib.Analysis.Complex.Harmonic.*`, `Mathlib.Analysis.Complex.Poisson` | C1 X.1–2 (in part), Ga III.3–4, BN 16, Bu V.3 (in part) |
| Subharmonic functions: submean property, maximum principle, majorants, Laplacian criterion, $\log|f|$, $|f|^p$ | Project | `Subharmonic.*` | C1 X.3, C2 19.4 |
| Poisson kernel: nonnegativity, total mass one, two-sided bounds; Harnack's inequality | Project + Mathlib (`re_herglotzRieszKernel_le`) | `Harnack` | C1 X.2.9, Ga X.1, Bu V.3, Si 5.3 |
| Dirichlet problem on a disc with continuous data: harmonicity of the Poisson integral, boundary values, existence and uniqueness | Project | `DirichletDisc` | C1 X.2.4, Ga X.1, Si 5.3, BN 16.1, Bu V.3 |
| Harmonic functions are subharmonic | Project | `DirichletDisc` | C1 X.3 |

### 1.6 Analytic continuation

| Topic | Status | Where | References |
| --- | --- | --- | --- |
| Function elements and continuation along a path; uniqueness of the continuation | Project | `AnalyticContinuation` | C1 IX.2, APP 27, Ga V.8 |
| The lacunary series `∑ z ^ (2 ^ n)`: holomorphy, unboundedness near every boundary point, no continuous extension (natural boundary) | Project | `NaturalBoundary` | C1 IX.1 (exercise), APP 27, BN 18.2 |
| Path lifting for covering maps | Mathlib | `IsCoveringMap.liftPath`, `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` | C1 IX.4 |

## 2. Gaps, ordered by value to this project

Each item lists the references that request it and the state of Mathlib.

1. **General Cauchy theorem, residue theorem and argument principle for cycles.** Done for
   cycles of closed $C^1$ curves (`Cycle`, `Cycle.Cauchy`, `Cycle.Residue`,
   `Cycle.ArgumentPrinciple`): Dixon's proof of the general Cauchy theorem and formula, the
   residue theorem with index weights for singularities of any type, and the argument
   principle. Still missing: chains with integer coefficients as a free abelian group (the
   present cycles use repetition and reversal), the index of continuous (not only $C^1$)
   closed curves, mesh-defined cycles around a compact set (Si 4.4, 4.6), the Jordan curve
   theorem (smooth or general), and the argument principle for functions with junk values at
   removable points of the cycle. References: C1 IV.4–5, Bu IV.2, IV.5–6, Si 4.1–4.6, 4.8,
   He V.3, BN 10.1. Mathlib: nothing.
2. **Runge's theorems and Mittag-Leffler.** Done (`Runge.*`, `MittagLeffler`): approximation
   on compact sets with poles in a prescribed set meeting every bounded component of the
   complement, and by polynomials when the complement is connected, by the Cauchy–Pompeiu
   representation and pole pushing; Runge's theorem on open sets through hole-free compact
   exhaustions, with locally uniformly convergent sequences of approximants; the Mittag-Leffler
   theorem on arbitrary open sets with principal parts of any type. Still missing: the
   characterizations of simple connectivity (Conway VIII.2, Burckel IV.8, Simon 4.5).
   References: SS 2.5.5, C1 VIII, He V.8, VIII.1, Si 4.7, Bu VIII.1–2, APP 44, Bu XI.5.
   Mathlib: nothing.
3. **Infinite products and factorization.** Done in part (`InfiniteProduct`,
   `WeierstrassFactor`, `WeierstrassProduct`): holomorphy, zeros and orders of locally
   uniformly convergent products `∏ (1 + f_n)`, the elementary factors with the uniform
   estimate `‖1 - E_p z‖ ≤ 4 ‖z‖^(p+1)` on `‖z‖ ≤ 1/2`, the Weierstrass product with
   prescribed zeros `a_n → ∞`, and the factorization `f = e^g ∏ E_n(z / a_n)` of an entire
   function with `f 0 ≠ 0`. Still missing: prescribed zeros on arbitrary domains
   (Weierstrass on open sets), order and genus, Hadamard factorization, Blaschke products,
   Bers' isomorphism theorem. References: C1 VII.5, XI.2–3, APP 42–43, BN 17.1, He VIII.2–4,
   VIII.6–7, Bu VII.3. Mathlib: `HasProd` API, locally uniform products
   (`Summable.hasProdUniformlyOn_one_add`), Euler sine product; no factorization theorem.
4. **Conformal mapping.** Done in part (`DiscMobius`, `HolomorphicInverse`,
   `DiscAutomorphism`, `Cayley`, `RiemannMapping`): disc Möbius transformations, holomorphic
   inverses, the classification of disc automorphisms as `c φ_a` and of half-plane
   automorphisms by Cayley conjugation, the Riemann mapping theorem with normalization, and
   uniqueness of the normalized map. Still missing: Möbius transformations on the Riemann
   sphere, cross ratio, circles to circles, symmetry; Schwarz–Christoffel; spaces of
   meromorphic functions with the chordal metric; boundary behavior (Carathéodory).
   References: Ga II.6–7, APP 39, 41, BN 13–14, C1 VII.3–4, Re 9.2, Bu VI, IX, Si 7–8.
   Mathlib: Schwarz lemma; upper half-plane Möbius action; Riemann mapping only as
   non-exported partial lemmas (`Mathlib.Analysis.Complex.RiemannMapping`).
5. **Harmonic functions beyond Mathlib.** Done in part (`Harnack`, `DirichletDisc`): the
   Poisson kernel bounds and Harnack's inequality on a disc, the Dirichlet problem on a disc
   with continuous boundary data (existence by the Poisson integral, uniqueness by the maximum
   principle); Harnack's principle for monotone sequences, the Perron method with barriers
   and the Dirichlet problem on bounded open sets with the exterior disc property
   (`HarmonicLimit`, `Perron`, `Perron.Barrier`). Still missing: harmonic majorization,
   Green's functions, reflection across analytic arcs. References: C1 X.2, X.4–5, Bu V.3, V.5,
   BN 16.1, Ga III, X, C2 13.4. Mathlib: Poisson representation of harmonic functions.
6. **Local behavior and the residue calculus.** Done in part (`LocalMapping`,
   `ResidueAtInfinity`): the local $m$-to-one mapping theorem with simple preimages, the residue
   at infinity and the total residue theorem; the partial fractions of $\cot$ are in Mathlib.
   Still missing: Jordan's lemma, indented contours, principal values, summation of series by
   residues, Mittag-Leffler expansions beyond $\cot$. References: Si 3.4–5, C1 IV.7, Bu V.7,
   APP 32–36, BN 11–12, Ga VI.4–VII.8, He VII.
7. **Analytic continuation.** Done in part (`AnalyticContinuation`, `NaturalBoundary`):
   function elements along a path and uniqueness of the continuation, and the lacunary series
   $\sum z^{2^n}$ as an example of a natural boundary. Still missing: the monodromy theorem,
   the sheaf of germs and the Riemann surface of a function element, continuation of
   Dirichlet series. References: C1 IX, APP 27, Ga V.8, BN 18. Mathlib: covering-space
   lifting (`IsCoveringMap`, `Mathlib.Topology.Homotopy.Lifting`).
8. **Advanced topics.** Bloch, Picard, Schottky (C1 XII, Bu XII; Mathlib is building
   Nevanlinna theory in `Mathlib.Analysis.Complex.ValueDistribution`); Carathéodory–Julia–Wolff,
   subordination, iteration (Bu VI.4–5, VII.4–5); prime ends and boundary behavior of Riemann
   maps, area theorem, Koebe, finitely connected regions (C2 14–15); Hardy spaces and the
   Nevanlinna class (C2 20); harmonic measure, Green potentials, capacity, polar sets,
   Wiener's criterion (C2 21); Bernoulli functions (Bu III.4, Re 7.5); Carleman approximation
   and harmonic functions on a half-plane (Bu VIII.5–6). None of these has a foundation in the
   project or in Mathlib.

## 3. Relation to Mathlib

The library reproves in Banach-valued form several results that Mathlib has for scalar or
particular targets (Cauchy formula and derivatives on simply connected sets, Laurent series,
Cauchy estimates); these are kept. Results that the pinned Mathlib covers in at least the same
generality are not reproved: where an earlier project proof has been replaced by a Mathlib
invocation, the module docstring says so. The replacement audit of 2026-09-23 (recorded in
REMINDERS.md) found two such cases, the derivative of the circle Cauchy kernel in the
evaluation point (`Complex.hasDerivAt_circleIntegral_sub_zpow_smul`) and the reflection
invariance of circle averages (`circleAverage_neg_radius`); everything else in the library is
either absent from Mathlib or more general than the Mathlib version.

## 4. Second review: additional chapters (2026-09-23)

Chapters reviewed: Burckel [Bu] IX–XII; Conway II [C2] 18–21; Gamelin [Ga] VIII–XIII;
Heins [He] XI–XVII; Lang [La] IX–XIII (*Complex Analysis*, 4th ed.); Remmert [Re] 9–13;
Simon [Si] 5–9 (table of contents only); Stein–Shakarchi [SS] 4, 5, 8. Status labels as in
Section 1; "Deferred" marks topics judged too far from the project or too dependent on missing
foundations (Jordan curve theorem, Lebesgue boundary theory, covering-space theory).

### 4.1 Coverage by chapter

| Reference | Contents | Status |
| --- | --- | --- |
| Bu IX | Riemann mapping theorem (Carathéodory–Koebe and Fejér–Riesz proofs, uniqueness); boundary behavior for Jordan regions; general Dirichlet problem; Dirichlet problem and Riemann mapping; half-plane onto polygon | Project (existence, uniqueness); Gap (boundary behavior, general Dirichlet problem: see B); Deferred (Jordan regions, Schwarz–Christoffel) |
| Bu X | Simple, double and higher connectivity; Aumann–Carathéodory | Gap (characterizations of simple connectivity); Deferred (annulus classification, finitely connected regions) |
| Bu XI | Laurent series and singularities; rational functions; singularities on the circle of convergence (Pringsheim–Vivanti); residue theorem and applications; Mittag-Leffler; meromorphic functions; harmonic functions | Project (Laurent, residues, Mittag-Leffler); Gap (Pringsheim–Vivanti: see H) |
| Bu XII | Logarithmic means and Jensen; Miranda's theorem; Schottky, Bloch, sectorial limits (Lindelöf); iteration; Ostrowski's proof of Schottky | Mathlib (Jensen); Deferred (Miranda, Schottky, Bloch: item 8 of Section 2); Gap (sectorial limit theorems: see H) |
| C2 18 | Bergman spaces; partitions of unity; convolution; distributions; Cauchy transform; rational approximation; Fourier series and Cesàro sums | Project (Cauchy transform, smooth cutoffs); Deferred (Bergman spaces, distributions) |
| C2 19 | Harmonic functions on the disc; Fatou's theorem; semicontinuous and subharmonic functions; logarithmic potential; approximation by harmonic functions; Dirichlet problem; harmonic majorants; Green function; regular points; Dirichlet principle | Project (disc, subharmonic); Mathlib (Poisson); Gap (Dirichlet problem, Green function: see B); Deferred (Fatou, logarithmic potential, Dirichlet principle) |
| C2 20 | Hardy spaces; Nevanlinna class; factorization; disc algebra; invariant subspaces; Szegő | Gap (Blaschke products and the Blaschke condition: see C); Deferred (Hardy spaces, inner–outer factorization, Szegő) |
| C2 21 | Potential theory: harmonic measure, Green potential, polar sets, capacity, fine topology, Wiener criterion | Deferred |
| Ga VIII | Argument principle, Rouché, Hurwitz, open mapping, critical points, winding numbers, jump theorem for Cauchy integrals, simply connected domains | Project (all but the last two); Gap (Sokhotski–Plemelj jump theorem: see H; characterizations of simple connectivity) |
| Ga IX | Schwarz lemma, conformal self-maps of the disc, hyperbolic geometry | Mathlib + Project; Gap (Schwarz–Pick and the hyperbolic metric: see H) |
| Ga X | Poisson integral, characterization of harmonic functions, Schwarz reflection | Project + Mathlib |
| Ga XI | Mappings to disc and half-plane, Riemann mapping theorem, Schwarz–Christoffel, compactness of families | Project; Deferred (Schwarz–Christoffel) |
| Ga XII | Marty's theorem, Montel and Picard, Julia sets, Mandelbrot set | Gap (Marty: see E); Deferred (Picard, Julia sets) |
| Ga XIII | Runge, Mittag-Leffler, infinite products, Weierstrass | Project |
| He XI | Wirtinger derivatives, harmonic functions of two real variables | Mathlib (Wirtinger derivatives, harmonic functions) |
| He XII | Formal power series, majorant calculus, analytic ODEs, two-variable power series, analytic continuation | Mathlib (formal series) + Project (continuation); Deferred (majorant calculus, analytic ODEs) |
| He XIII | Poisson integral, Schwarz reflection, Carleman extension principle, subharmonic functions | Project; Gap (reflection in analytic arcs: see H) |
| He XIV | Gauss sums by residues, divisors and residues of doubly periodic functions, Weierstrass preparation theorem, polynomial approximation, boundary behavior of integrals, Weierstrass classes | Project in part (Liouville's first theorem: see F); Gap (Liouville's second and third theorems: see F; Weierstrass preparation: SCV candidate); Deferred (Gauss sums, Weierstrass classes) |
| He XV | Classification of Möbius transformations | Mathlib in part (`GL(2, K)` action on the projective line, parabolic and elliptic elements); Gap (cross ratio, circles, symmetry: see H) |
| He XVI | Modular function λ, Picard theorems | Deferred (item 8 of Section 2) |
| He XVII | Riemann mapping (Fejér–Riesz), Carathéodory's theorem on variable regions (kernel convergence), boundary behavior of univalent functions | Project (Riemann mapping); Gap (area theorem and distortion: see G); Deferred (kernel convergence, boundary behavior) |
| La IX | Schwarz reflection, reflection across analytic arcs, applications | Project (real axis); Gap (analytic arcs: see H) |
| La X | Riemann mapping theorem, compact sets in function spaces, behavior at the boundary | Project; Deferred (boundary behavior) |
| La XI | Analytic continuation along curves, dilogarithm, application to Picard | Project (continuation along curves); Deferred (dilogarithm, Picard) |
| La XII | Jensen's formula, Picard–Borel, Borel–Carathéodory, three circles and small derivatives, Hermite interpolation, entire functions with rational values (Pólya), Phragmén–Lindelöf and Hadamard | Mathlib (Jensen, Borel–Carathéodory, Phragmén–Lindelöf, three lines); Gap (three circles, Pólya's theorem: see A, H) |
| La XIII | Infinite products, Weierstrass products, functions of finite order, Mittag-Leffler | Project; Gap (finite order, Hadamard: see A) |
| Re 9 | Fundamental theorem of algebra, Schwarz lemma and Aut 𝔼, Aut ℍ, logarithms and roots, local normal forms, general Cauchy theory, asymptotic power series | Mathlib + Project; Deferred (asymptotic expansions, Ritt's theorem) |
| Re 10 | Isolated singularities, automorphisms of punctured domains, meromorphic functions | Mathlib + Project; Deferred (automorphisms of punctured domains) |
| Re 11 | Series of meromorphic functions, partial fractions of `π cot π z`, Euler's formulas for `ζ(2n)`, Eisenstein theory | Mathlib (`cot_series_rep`, zeta values, Eisenstein series) |
| Re 12 | Laurent series, periodic holomorphic functions and Fourier series, theta function | Project (Laurent) + Mathlib (periodic functions, Jacobi theta) |
| Re 13 | Residue theorem and consequences | Project |
| Si 5 | Phragmén–Lindelöf, three lines and Riesz–Thorin, Poisson representations, harmonic functions, reflection, reflection in analytic arcs, definite integrals | Mathlib (Phragmén–Lindelöf, three lines, Poisson); Project (harmonic, reflection); Gap (analytic arcs: see H); Deferred (Riesz–Thorin, definite integrals) |
| Si 6 | Fréchet space of analytic functions, Montel and Vitali, Runge, Hurwitz, Marty | Project; Gap (Marty: see E) |
| Si 7 | Riemann sphere, PSL(2, ℂ), self-maps of the disc, continued fractions and the Schur algorithm | Mathlib in part; Project (disc); Gap (cross ratio: see H); Deferred (Schur algorithm) |
| Si 8 | Riemann mapping, boundary behavior, elliptic modular function, explicit maps, covering maps, doubly connected regions, uniformization, Ahlfors function and analytic capacity | Project (Riemann mapping); Deferred (rest) |
| Si 9 | Infinite products, Euler product, Mittag-Leffler, Weierstrass, general regions, Gamma, Euler–Maclaurin and Stirling, Jensen, Blaschke products, finite order and Hadamard | Project + Mathlib (Gamma, Stirling, Jensen); Gap (Weierstrass on general regions, Blaschke, finite order and Hadamard: see A, C) |
| SS 4 | Fourier transform on the class F, Paley–Wiener theorem | Mathlib (Fourier transform, Schwartz space, inversion); Gap (Paley–Wiener: see D) |
| SS 5 | Jensen's formula, functions of finite order, infinite products, Weierstrass products, Hadamard factorization | Mathlib (Jensen) + Project (products); Gap (finite order, Hadamard: see A) |
| SS 8 | Conformal equivalence, Dirichlet problem in a strip, automorphisms, Riemann mapping, Schwarz–Christoffel, boundary behavior, elliptic integrals | Project; Deferred (Schwarz–Christoffel) |

### 4.2 Prioritized selection of items new to Mathlib

Ordered by value to the project and feasibility with the present modules.

A. **Entire functions of finite order and Hadamard's factorization.** Done (2026-09-23):
   `FiniteOrder`, `CanonicalProduct.*`, `Hadamard` prove the zero counting bound, the
   summability of inverse powers, the canonical product estimates and Hadamard's theorem.
   Still open in this item: F. Carlson's uniqueness theorem and Pólya's integer-valued
   theorem. Original description: order and type of an entire function; Jensen's formula (Mathlib, `AnalyticOnNhd.sum_divisor_le`) gives the zero-counting
   bound `n(r) = O(r^(ρ+ε))` and the convergence exponent; canonical products of finite genus and
   their growth (our elementary factors and `WeierstrassProduct`); Hadamard's theorem `f = e^P
   z^m ∏ E_p(z / a_n)` with `deg P ≤ ρ` by Borel–Carathéodory (Mathlib); corollaries (non-integer
   order implies infinitely many zeros; Lindelöf's theorem). Then functions of exponential type:
   F. Carlson's uniqueness theorem (type `< π`, vanishing on `ℕ`) by Phragmén–Lindelöf
   (Mathlib), and Pólya's theorem on integer-valued entire functions of type `< log 2` via
   Newton series (our `NewtonTaylor` divided-difference machinery), the natural link to the
   Dirichlet and Carlson libraries. References: SS 5.2–5.5, La XII.5–6, XIII.3, Si 9.10,
   C1 XI.2–3, Bu XII.1. Mathlib: nothing beyond Jensen, Borel–Carathéodory, Phragmén–Lindelöf.
B. **Perron's method and Green's functions.** Done in part (2026-09-23/24, `HarmonicLimit`,
   `Perron`, `Perron.Barrier`, `GreenFunction`): Harnack's principle for monotone sequences;
   Perron families of subharmonic functions and the Perron solution; barriers and the
   exterior-disc criterion; the Dirichlet problem on bounded open sets with the exterior disc
   property; existence and nonnegativity of the Green function as the harmonic compensator for
   the logarithmic singularity at a pole. Still open: strict positivity of the Green function
   (needs the strong maximum principle on the preconnected punctured domain), its symmetry, the
   segment criterion for regular boundary points, and the Riemann mapping theorem revisited
   through the Green function.
   Original description: Harnack's principle for monotone sequences (from
   `Harnack`); Perron families of subharmonic functions and the Perron solution; barriers and
   regular boundary points (exterior-disc and segment criteria); the Dirichlet problem on general
   bounded domains; the Green function of a domain and its symmetry; the Riemann mapping theorem
   revisited through the Green function. Builds directly on `DirichletDisc` and `Subharmonic.*`.
   References: Ga XV.2–7, C2 19.7–19.10, Bu IX.7–8, He XIII, La VIII.5, C1 X.4–5.
   Mathlib: nothing.
C. **Blaschke products and the Blaschke condition.** Done (2026-09-24, `Blaschke`,
   `RieszFactorization`; boundedness of `g` added 2026-09-23): the Riesz factorization theorem
   `f = z ^ m B g` with `B` the Blaschke product of the zeros of `f` counted with multiplicity
   and `g` holomorphic, nonvanishing, and bounded on the disc by the same bound as `f`, proved
   by comparing `f` to finite Blaschke prefixes on circles of radius `r → 1` (maximum modulus,
   `Complex.norm_le_of_blaschkeProduct_bounded`) and passing to the limit of the full product.
   Original description: convergence of `∏ (|a_n| / a_n) φ_{a_n}`
   under `∑ (1 - |a_n|) < ∞` (our `InfiniteProduct` and `DiscMobius`, Mathlib's finite canonical
   factors); the Blaschke condition for bounded holomorphic functions on the disc from Jensen's
   formula (F. Riesz), hence the uniqueness theorem for bounded functions with zeros
   accumulating too fast; prescribed zeros on the disc. References: Si 9.9, C2 20.2–20.3,
   C1 VII.5 (exercises), Bu XII.1. Mathlib: `canonicalFactor` only.
D. **The Paley–Wiener theorem.** Entire functions of exponential type with square-integrable
   restriction to `ℝ` are exactly the Fourier transforms of functions supported in a bounded
   interval; holomorphic extension of Fourier transforms of rapidly decaying functions; uses
   Mathlib's Fourier transform, inversion and Plancherel with Phragmén–Lindelöf in strips.
   Ties to A. References: SS 4.1–4.3, Si 11.1. Mathlib: Fourier infrastructure, no Paley–Wiener.
E. **Normal families of meromorphic functions.** Chordal metric on `ℂ ∪ {∞}` (Mathlib has the
   topology of `OnePoint ℂ` and its homeomorphism with the sphere), spherical derivative, Marty's
   criterion for normality, and Zalcman's rescaling lemma. Extends `Montel`. References:
   Ga XII.1, Si 6.5, 11.4, C1 VII.3, Bu VII.2. Mathlib: nothing.
F. **Elliptic functions: the general theory.** Liouville's first theorem done (2026-09-23,
   `EllipticLiouville`): an entire function doubly periodic with respect to a lattice
   (Mathlib's `PeriodPair`) is constant, by boundedness on the compact fundamental
   parallelogram together with the classical Liouville theorem for bounded entire functions.
   Still open: Liouville's second and third theorems for doubly periodic meromorphic functions
   (vanishing residue sum; equal numbers of zeros and poles; Abel's relation). The general
   residue theorem itself is already available (`Cycle.Residue.integral_eq_sum_index_smul_residue`)
   and so is the argument principle for cycles (`Cycle.ArgumentPrinciple`). Partial progress
   (2026-09-23, `Cycle.Parallelogram`): the parallelogram boundary is now a genuine `C^∞`
   `Loop`/`Path`, built by gluing the four edges with `Real.smoothTransition` (flat, so smooth
   across the corners with no case analysis), and its index is proved to vanish at every point
   *outside* the closed parallelogram, by a convexity-coning nullhomotopy toward a vertex. The
   index equalling `1` on the *open interior* — the fact actually needed to apply the residue
   theorem to a period parallelogram — is NOT proved: the exterior nullhomotopy gives no
   information about the interior, and pinning the interior value needs either a direct winding
   computation (bounding and signing four edge-wise argument changes so they sum to exactly
   `2π`, not `0` or `4π`) or an orientation hypothesis on `w1, w2` (swapping them reverses the
   traversal and negates the index) plus that computation; see `REMINDERS.md` for the
   considered strategies and why none was completed. Also open: order of an elliptic function,
   and the facts that Mathlib's `℘` and `℘'` generate the field. References:
   SS 9.1, La XIV.1–2, Si 10.3–10.4, He XIV.2. Mathlib: `PeriodPair.weierstrassP` with its
   differential equation, no Liouville theorems, no residue calculus.
G. **Univalent functions: area and distortion theorems.** Done (2026-09-24, `Parseval`,
   `DiscCauchyTransform`, `AreaTheorem`, `Koebe`, `KoebeDistortion`, `KoebeGrowth`), except the
   growth theorem's lower bound: the area theorem for the class Σ, Bieberbach's `|a₂| ≤ 2`, the
   Koebe one-quarter theorem, the pre-Schwarzian bound `|(1-|z|²) f''/f' - 2z̄| ≤ 4`, the full
   Koebe distortion theorem `(1-r)/(1+r)³ ≤ |f'(z)| ≤ (1+r)/(1-r)³` (integrating the
   pre-Schwarzian bound along a ray through a holomorphic logarithm of `f'`), and the growth
   theorem's upper bound `|f(z)| ≤ r/(1-r)²`. Still open: the growth theorem's lower bound
   `r/(1+r)² ≤ |f(z)|`, which needs a genuinely different argument (bounding the rotation of
   `f'` along the ray, not a direct consequence of the distortion theorem by integration).
   Original description: the area theorem for the class Σ
   (Laurent coefficients of injective functions), Bieberbach's `|a₂| ≤ 2`, the Koebe one-quarter
   theorem, and the Koebe distortion theorems. Builds on `LaurentSeries`, `Injective`,
   `HolomorphicInverse`. References: C2 14.6–14.7, He XVII, Bu VI (in part). Mathlib: nothing.
H. **Smaller self-contained items.** (1) Done (2026-09-24, `SchwarzPick`): Schwarz–Pick lemma
   and the hyperbolic metric of the disc (Ga IX.3, Si 7.4, Bu VI.1) on top of `DiscMobius`.
   (2) Done (2026-09-24, `MobiusGeometry`): Möbius transformations on the plane: cross ratio and
   its invariance, generalized circles (circles or lines) mapping to generalized circles (by
   decomposition into translations, scalings, and inversion), and symmetric points via the
   cross-ratio criterion with their invariance under Möbius transformations (Si 7.3, He XV,
   La VII.5, Ga II.7). Not treated: the point at infinity / `OnePoint ℂ` formalism itself, and
   the connection of the cross-ratio symmetric-point criterion to the classical geometric
   inverse-point formula for a genuine circle.
   (3) reflection across analytic arcs and the Carleman extension principle (La IX.2,
   Si 5.6, He XIII, C2 13.4) extending `Reflection`; (4) Done (2026-09-24, `ThreeCircles`):
   Hadamard's three-circle theorem (La XII.4, Si 5.2), via the maximum principle for subharmonic
   functions (`Perron`) rather than Mathlib's three-lines theorem, applied to
   `log ‖f‖ - a log ‖z‖` on the annulus. (5) the
   Pringsheim–Vivanti theorem on singularities of power series with nonnegative coefficients
   (Bu XI.3, Re 8.1); (6) the Sokhotski–Plemelj jump relations for Cauchy integrals (Ga VIII.7).
   Checked (2026-09-23): this is not a small extension of `CauchyTransform` (which is the
   several-variable area-integral Cauchy transform, `∂/∂z̄ = g` for compactly supported `C¹`
   functions) or of `DiscCauchyTransform` (the area Cauchy transform of a disc indicator). The
   classical jump relations concern a genuinely different object, the boundary Cauchy-type
   *contour* integral `Cφ(z) = (2πi)⁻¹ ∮ φ(w)/(w - z) dw` of a density on a curve, with no
   counterpart yet in the project; formalizing it needs its own module (existence, continuity,
   and the jump formula as `z` approaches the curve from each side), not an extension of
   existing code. (7) the characterizations of simple connectivity (Bu X.1,
   Ga VIII.8, C1 VIII.2, Si 4.5), already listed under item 2 of Section 2.

Deferred: Picard, Schottky, Bloch and the modular function (item 8 of Section 2; Mathlib's
value distribution theory is the likely route); Carathéodory's boundary theorem and everything
resting on the Jordan curve theorem; annulus and finitely connected classification; Hardy
spaces, Fatou's theorem, harmonic measure, capacity and Bergman spaces; Riesz–Thorin;
Schwarz–Christoffel; Mergelyan and Carleman approximation; Julia sets; uniformization; the
analytic Weierstrass preparation theorem (a candidate for `SeveralComplexVariables`).
