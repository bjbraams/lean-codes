# TauCeti reuse review — 4 October 2026

TauCeti is now an explicit dependency of lean-codes. The preference is **Mathlib, then the
pinned TauCeti, then local project code**, preserving the scope of the mathematics.
Dependency setup and synchronization are complete. Items 1–3 below are now implemented
in the production library; items 4–6 remain recommendations for later work.

## Scope and dependency setup

The inventory covers all **439 Lean files** in the seven main directories: 51 in `ToMathlib`
(including its three umbrellas), 23 in `ComplexAnalysis`, 21 in `SeveralComplexVariables`,
32 in `StdSimplexMeasure`, 11 in `Pochhammer`, 60 in `Dirichlet`, and 241 in `Carlson`.
Module inventories, documentation, declaration searches and the import graph were screened;
promising matches received statement/proof inspection and the small adapters below were compiled.
This is a reuse review, not a new line-by-line audit of every proof or an exhaustive claim
that no alternative formulation exists upstream. Findings refer to the pinned source checkout,
not unfinished roadmap proposals or TauCeti's latest branch.

- Lean remains `v4.35.0-rc3`.
- Mathlib remains `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.
- TauCeti is pinned to [`a780c7ad6beb23f60a17351a492d177878020ad5`][tau], matching CA and SCV.
- `lake update TauCeti` added only TauCeti to the package set. Every pre-existing package's
  resolved revision is unchanged. Lake normalized `Cli`'s scope and requested revision
  metadata from `main` to `v4.35.0-rc3`, without changing its resolved commit.
- `.lake` remains the symlink to `/export/scratch1/braams/lean-codes-lake` and project outputs
  remain in `.lake/build-codes`.
- `AGENTS.md` now permits suitable TauCeti imports throughout all seven layers, requires
  attribution, and retains the local dependency hierarchy and master-copy rules.
- Import particular TauCeti modules; `import TauCeti` is not a library umbrella.

## Copied sources: completed synchronization

The transitive import graph was computed from the substantive application and support modules,
using the primary projects' source contents. The two CA/SCV inventory umbrellas were excluded
as roots, so an unused copied file cannot justify its own retention.

- All **23** files in `ComplexAnalysis/` are needed and now match `../lean-CA` byte for byte.
- All **21** files in `SeveralComplexVariables/` are needed and already match `../lean-SCV`.
- No copied modules needed adding or removing, and no local imports were unresolved.
- The project-specific root umbrellas remain appropriate to these subsets.

Three CA copies were refreshed: `Injective`, `HolomorphicInverse`, and `HalfPlane`. They now
inherit the master project's TauCeti proofs of nonzero derivative, inverse continuity/holomorphy
and its derivative, and the right-half-plane quotient's membership in the slit plane.
`ToMathlib/Analysis/Connected.lean` was refreshed from SCV, inheriting its TauCeti exterior
preconnectedness proof while preserving the local annulus results.

All **10** shared ToMathlib implementation files present in CA, and all **14** present in SCV,
now agree byte for byte with lean-codes; these counts overlap. The three support umbrellas are
project-specific. The sole other discrepancy was the newer OpenMapping PR #44201 header note
already present here. It was retained and copied into SCV's otherwise identical file, without
changing its proofs. SCV was rebuilt and its changed file checked directly.

The other recently simplified CA modules (Riemann mapping, Hurwitz, Montel, Schwarz–Pick,
Harnack, reflection and disc automorphisms) are not needed by this project's copied subset.
They were not added merely to make TauCeti available.

## Replacements and remaining recommendations

### 1. Replace the simplex moment-determination proof

[StdSimplexMeasure/MomentDetermination.lean](StdSimplexMeasure/MomentDetermination.lean)
contains `MeasureTheory.eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex`.
[TauCeti.Probability.Moments.CompactDeterminacy][tau-moments] provides the more general
`TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support` for any compact subset of a
finite real coordinate space.

A checked adapter uses the compactness of `Convexity.StdSimplex.coordinateSet` and converts
`μ.restrict K = μ` and `ν.restrict K = ν` to `μ Kᶜ = 0` and `ν Kᶜ = 0`. The existing local
`ae_mem_of_restrict_eq_self` supplies the latter conversion via `ae_iff`.
This preserves both finite-measure hypotheses, both support hypotheses, arbitrary finite index
types including the empty case, and the full monomial-moment statement.

The final Stone–Weierstrass proof has been replaced by this adapter, and its two unused
private approximation helpers removed. The public integration/polynomial helpers remain.
The imported determinacy theorem is generic compact-support measure theory; no local
Dirichlet or Carlson dependency was introduced into the simplex foundation.

**Status:** implemented with the original theorem statement and hypotheses.

### 2. Replace finite-product nonnegative integration

[ToMathlib/Analysis/Integral/Pi.lean](ToMathlib/Analysis/Integral/Pi.lean) has
`MeasureTheory.lintegral_fintype_prod_eq_prod` for dependent coordinate spaces and
almost-everywhere measurable factors. The matching imported result is
`TauCeti.lintegral_fintype_prod_eq_prod₀` in [MeasureTheory.Integral.Pi][tau-pi].

Its checked replacement is simply:

```lean
  TauCeti.lintegral_fintype_prod_eq_prod₀ μ hf
```

The subscript-zero variant matters: the unsuffixed TauCeti theorem assumes measurability.
Sigma-finiteness, dependent coordinate types and the empty index case are preserved.
The two local measurable-factor induction and reindexing helpers have been removed.

**Status:** implemented with the original theorem statement and hypotheses.

### 3. Replace covering-map injectivity, retaining the stronger properness lemma

[ToMathlib/Topology/ProperCovering.lean](ToMathlib/Topology/ProperCovering.lean) proves
`IsCoveringMap.injective_of_simplyConnectedSpace`. TauCeti's
[Topology.Homotopy.Covering][tau-covering] supplies `IsCoveringMap.injective` with the same
path-connected-source and simply-connected-target hypotheses. The checked proof is
`hf.injective`. This removes the local path-lifting argument and benefits Carlson's
Schwarz–Christoffel mapping theorem.

Retain the rest of the local support. In particular, our
`IsLocalHomeomorph.isCoveringMap_of_isProperMap` only requires a Hausdorff source.
TauCeti's [Topology.Covering.Proper][tau-proper] theorem is formulated using compact preimages
over an open target set and additionally assumes a Hausdorff, locally compact target.
It is not a same-generality replacement for the whole local file.

**Status:** implemented with the original theorem statement and hypotheses; the other three
local topological results are retained.

### 4. Resolve the beta name collision, then use TauCeti's beta interface

The current local [BetaDensity.lean](ToMathlib/Analysis/SpecialFunctions/BetaDensity.lean)
and TauCeti's [Analysis.SpecialFunctions.Beta][tau-beta] both declare
`ProbabilityTheory.beta_add_one_left`. A compiled coimport attempt fails with that exact
duplicate-declaration error. This also affects TauCeti's beta and Dirichlet distribution
modules, which depend on its beta support. The current production build does not import
these modules and remains successful.

The local theorem assumes `0 < a` and `0 < b`; TauCeti's version only requires `a ≠ 0`
and `a + b ≠ 0`. Remove the duplicate local declaration and adjust its one local caller
inside `mul_betaPDFReal_eq`, supplying `ha.ne'` and `(add_pos ha hb).ne'`. Alternatively,
keep a distinctly named positivity adapter if preserving that interface is useful.

Then [Probability.Distributions.Beta.Basic][tau-beta-law] replaces at least:

- `betaPDFReal_nonneg`, directly by `TauCeti.Probability.betaPDFReal_nonneg`;
- `integral_betaMeasure`, by `TauCeti.Probability.integral_betaMeasure_eq` specialized to real
  values (`simpa only [smul_eq_mul]`);
- `integral_mul_betaPDFReal`, by the integral transfer and
  `TauCeti.Probability.integral_id_betaMeasure`.

The three adapters compile in isolation with exactly the local hypotheses and conclusions.
They are not yet a successful full-project coimport: the duplicate name must first be resolved.
Keep the concentration-ratio, two-crossing and strict convex-comparison arguments in
`BetaKernel`, `BetaConcentration`, and the related Pochhammer/mean development; the inspected
TauCeti distribution API does not supply their full statements.

### 5. Prove a real Dirichlet measure bridge before replacing its probability theory

TauCeti has completed [Dirichlet.Basic][tau-dirichlet], [Density][tau-density],
[Aggregation][tau-aggregation], [Marginal][tau-marginal], and [Moments][tau-dirichlet-moments]
modules. Their support, aggregation, beta marginals, coordinate means, variances and
covariances overlap substantially with `Dirichlet/Real/*`.

The measures are not definitionally identical:

- Local `ProbabilityTheory.dirichletMeasure` is a density against `stdSimplexMeasure` on
  `ι → ℝ`, using this project's coordinate-normalized affine-hyperplane measure.
- `TauCeti.Probability.dirichletMeasure` is the pushforward of independent unit-rate Gamma
  variables under normalization, with values in `EuclideanSpace ℝ ι`.
- TauCeti explicitly makes its measure zero for an empty coordinate type or invalid
  parameters, and handles singleton types by a Dirac law. An unconditional equality of
  totalized definitions must not be assumed.

A useful first bridge would identify the pushforward of the local measure under the canonical
coordinate equivalence with TauCeti's measure, for positive parameters and a nonempty index type.
The proved upstream `dirichletMeasure_eq_map_withDensity_dirichletChartPDF` gives an explicit
chart-density route: check its chart and normalization against `StdSimplexMeasure.Coordinates`
and `Measure.Basic`. The support/moment route is another possibility once enough upstream
mixed-moment identities are available. Handle singleton coordinates explicitly.

After that bridge, transport mean/variance, beta marginal and aggregation statements instead
of maintaining separate probability proofs. The general complex Dirichlet density, regularized
entire parameter continuation, smooth-kernel transforms, integration by parts and Carlson
averages remain local: a positive-real probability distribution does not replace them.

**Status:** the TauCeti density, moments and aggregation modules compile and their APIs were
checked in isolation; no measure-equivalence bridge was proved in this review. Resolve item 4
before combining them with the full local application library.

### 6. Treat Schwarz–Christoffel reuse as a separate interface migration

TauCeti supplies a normalized primitive, boundary extension, covering criteria and polygon
mapping theorems in its [SchwarzChristoffel][tau-sc] hierarchy. This is substantial overlap
with `Carlson/Elliptic/{SchwarzChristoffel,VertexLimits,Polygon,Mapping}`.

Our map is explicitly a Carlson R-function, and its derivative has the factor `-a`.
A bridge would identify it with an affine rescaling/translation of TauCeti's primitive
with exponents `eᵢ = -bᵢ`, then relate the boundary and polygon descriptions.
There is also a material range difference: TauCeti's
`bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull` assumes strictly ordered finite
prevertices and `∑ eᵢ = -2`. Here `∑ bᵢ = a + 1` with `0 < a ≤ 1`, so that theorem directly
matches only `a = 1`. Its more general simple-boundary/covering results may support the
remaining range, but require corresponding boundary hypotheses to be proved.

Retain the present Carlson identification, full parameter range, elliptic reductions,
half-periods and inversion formulas. Item 3 now supplies the small covering-injectivity simplification without
undertaking this larger migration. No complete mapping adapter was proved here.

## Remaining inventory

| Area | Assessment at this pin |
| --- | --- |
| `ToMathlib/Algebra` | No further direct replacement identified for saturation/localization, finite-dependence bounds or positive proportionality. |
| Topology, Baire bounds, separate continuity and locally constant gluing | Retain the current interfaces. Items 3 and the synchronized exterior lemma are the identified changes; broader covering/monodromy packages do not automatically replace generic gluing or first-exit statements. |
| Shared CA and SCV files | Keep the verified minimal copies. Banach-valued integration, polydisc estimates and Hartogs/separate analyticity retain scope beyond TauCeti's planar scalar theory. Further changes should originate in the master projects. |
| Holomorphic spaces, normal families, polynomial approximation, open mapping and Taylor support | Retain the bundled/general-source interfaces and existing Mathlib-based proofs. The companion reviews describe the narrower one-variable overlaps and the separately tracked Mathlib PRs. |
| Curve integrals, compact/parameter integrals, Cauchy boundary values and tails | Retain general one-form/Banach-valued and parameter-uniform interfaces. TauCeti's contour representation differs; no matching replacement for the current segment Plemelj or quantitative complex Laplace-error statements was verified. |
| Gamma/Laplace, Gamma-ratio bounds, Bessel and incomplete Mellin support | No direct replacement identified for the current complex-rate, regularized complex-parameter and series interfaces. TauCeti's incomplete beta/gamma functions have real integral definitions; Mathlib already supplies the generalized hypergeometric functions used here. |
| Simplex geometry, volume normalization, slicing, aggregation, calculus and Newton–Taylor | Retain the coordinate-normalized measure and general smooth-kernel calculus. Item 1 concerns moment determination only; the real Dirichlet bridge may later reuse some chart calculations. |
| `Pochhammer` | Retain the complex identities, growth estimates, binomial series, regularized incomplete Mellin transform and polynomial transform. No wholesale replacement was identified. |
| Complex `Dirichlet`, transforms and averages | Retain entire continuation in complex parameters and the structural differentiation/shift laws. Item 5 is restricted to the real probability layer. |
| Carlson R/L/S/T, R-polynomials, means and transformations | No direct upstream replacements identified for these continued special functions, exceptional-parameter behavior or their multivariate transformations. Beta probability reuse supports parts of their foundations. |
| Jacobi, Gegenbauer, Hermite and Chebyshev | TauCeti has Gaussian Hermite orthogonality and Chebyshev Hilbert-basis/Parseval theory. These are useful related work; its standard integer Hermite polynomials with weight `exp(-x²/2)` differ from the local monic complex family with weight `exp(-x²)`. A scaling/complexification bridge would precede reuse. The complex-endpoint Jacobi, second-kind, boundary, contour and saddle-asymptotic theory remains local. |
| Elliptic functions and conformal mapping | Item 6 is the principal overlap. Carlson normalizations, R-function identities, duplication/Landen algorithms and their range conditions remain local. |

## Dependency-setup review validation

- `lake update TauCeti`: passed; resolved existing revisions and toolchain preserved.
- Full `lake build`: passed, **4,410 jobs**.
- `lake build Statement Solution`: passed, **4,413 jobs**.
- `lake env lean` passed for all four synchronized Lean files and `Main.lean`.
- SCV full build: passed, **3,552 jobs**; its header-only changed file passed a direct check.
- Import-closure and byte-comparison checks passed for both copied directories and shared support.
- `git diff --check` and production admission scans passed. No production library `sorry`s
  or new axioms were introduced. The **22 existing `Statement.lean` placeholders** remain;
  `Solution.lean` is admission-free.
- Temporary adapters for items 1–3 compiled alongside `Carlson`; the three beta adapters
  compiled separately. Their axiom checks list only `propext`, `Classical.choice` and
  `Quot.sound`. The beta coimport failure is documented in item 4, not hidden by the isolated test.
- No assumptions were strengthened and no false theorem was identified. No export-comparator
  replay or proof of the larger bridges in items 5–6 was performed.

## Implementation validation for items 1–3

The production proofs now import TauCeti's compact-support moment determinacy, finite-product
lower integration and covering injectivity results. All nine public theorem signatures across
the three edited files match their pre-change versions. Four unused private helpers were
removed (two approximation lemmas and two product-induction/reindexing lemmas). The generic
properness criterion and all public integration/polynomial helpers remain.

- Full `lake build`: passed, **4,422 jobs**.
- `lake build Statement Solution`: passed, **4,425 jobs**.
- `lake env lean` passed for each of the three edited files.
- The three production theorem axiom checks, and the combined proper-local-homeomorphism
  injectivity corollary, use only `propext`, `Classical.choice` and `Quot.sound`.
- `git diff --check` and the production admission scan passed. The 22 existing
  `Statement.lean` placeholders remain; the production libraries and `Solution.lean`
  contain no `sorry`s. No assumptions changed and no false theorem was identified.
- The copied subsets remain exactly the 23 required CA modules and 21 required SCV modules,
  with byte-for-byte matching contents. All shared support implementations still match too.
  None of these three edited files is shared with CA or SCV, so no companion edits were needed.
- Toolchain, dependency pins and build topology were unchanged in this implementation batch.
  Items 4–6 remain deferred.

[tau]: https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5
[tau-moments]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Moments/CompactDeterminacy.lean
[tau-pi]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/MeasureTheory/Integral/Pi.lean
[tau-covering]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Topology/Homotopy/Covering.lean
[tau-proper]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Topology/Covering/Proper.lean
[tau-beta]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean
[tau-beta-law]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Beta/Basic.lean
[tau-dirichlet]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Basic.lean
[tau-density]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Density.lean
[tau-aggregation]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Aggregation.lean
[tau-marginal]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Marginal.lean
[tau-dirichlet-moments]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Moments.lean
[tau-sc]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Polygon/Mapping.lean
