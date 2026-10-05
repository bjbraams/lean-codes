# Credits

This file collects credits and related-work notes for the open-mapping, holomorphic,
and curve-integral modules retained in `lean-codes` after removal from `lean-PR`.
For other credits, see [lean-PR/CREDITS.md](../lean-PR/CREDITS.md).

The normal-family development in
`ToMathlib/Analysis/Holomorphic/NormalFamily.lean`
acknowledges Vincent Beffara's [RMT4 formalization of the Riemann mapping theorem](https://github.com/vbeffara/RMT4),
in particular [RMT4/Montel.lean](https://github.com/vbeffara/RMT4/blob/main/RMT4/Montel.lean)
for the one-variable scalar case. That file develops compact-boundedness,
equicontinuity, and Montel's theorem. Our development uses bundled holomorphic
maps and retains a general compactness result for finite-dimensional source and target
spaces, assuming closedness of the holomorphic subspace. For domains in `ℂ`, closedness
is now proved from Mathlib's Weierstrass theorem, giving unconditional Montel and Vitali
entry points.

## TauCeti dependency and adopted proofs — 4 October 2026

The project now depends on the Tau Ceti contributors' work at revision
`a780c7ad6beb23f60a17351a492d177878020ad5`, compatible with Lean `v4.35.0-rc3`.
The synchronized master copies import its proofs in four files:

- `ComplexAnalysis/Injective.lean`: nonvanishing of the derivative of an injective holomorphic
  function, from [Conformal.LocalDegree][tau-codes-degree].
- `ComplexAnalysis/HolomorphicInverse.lean`: inverse continuity, holomorphy and derivative,
  from [Conformal.Inverse.Function][tau-codes-inverse].
- `ComplexAnalysis/HalfPlane.lean`: the right-half-plane quotient criterion for the slit plane,
  from [Complex.SlitPlane][tau-codes-slit].
- `ToMathlib/Analysis/Connected.lean`: preconnectedness of a closed ball's complement in a real
  normed space of dimension greater than one, from [Ball.Exterior][tau-codes-exterior].

The CA files were synchronized from `../lean-CA`, and the connectedness file from `../lean-SCV`.
Module headers and theorem docstrings retain the master projects' attribution. See also
[lean-CA/CREDITS.md](../lean-CA/CREDITS.md).

The first three recommendations in the [TauCeti reuse review](TauCetiReview.md) are now adopted:

- `StdSimplexMeasure/MomentDetermination.lean` specializes
  `TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support` from
  [CompactDeterminacy][tau-codes-moments], retaining both support hypotheses and arbitrary
  finite coordinate types. The two unused private approximation helpers were removed.
- `Dirichlet/Gamma.lean` uses `TauCeti.lintegral_fintype_prod_eq_prod₀` from
  [Integral.Pi][tau-codes-pi] directly; the former local adapter
  `ToMathlib/Analysis/Integral/Pi.lean` was removed.
- `ToMathlib/Topology/ProperCovering.lean` uses `IsCoveringMap.injective` from
  [Homotopy.Covering][tau-codes-covering] directly; the local adapter
  `IsCoveringMap.injective_of_simplyConnectedSpace` was removed. The more general local
  properness criterion remains.

All retained public theorem statements and assumptions are unchanged. The imported proofs
are credited to the Tau Ceti contributors in the module headers and theorem docstrings.
These three files are not part of the shared CA/SCV implementation subsets.

### Further adoptions — 5 October 2026

- `ToMathlib/Analysis/SpecialFunctions/BetaDensity.lean`: `ProbabilityTheory.beta_add_one_left`
  from [SpecialFunctions.Beta][tau-codes-beta] (the conflicting local declaration was removed),
  and `betaPDFReal_nonneg`, `integral_betaMeasure_eq` and `integral_id_betaMeasure` from
  [Distributions.Beta.Basic][tau-codes-beta-law].
- `ToMathlib/Analysis/Integral/ProdAbsRPow.lean`: `locallyIntegrable_norm_sub_rpow` from
  [Integral.NormRpow][tau-codes-normrpow].
- `Carlson/Jacobi/SegmentOrthogonality.lean`, `Carlson/T/TwoF0Connection.lean` and
  `Carlson/R/SingleIntegral/PositiveRay.lean`: `ofReal_mul_cpow` and `cpow_sum` from
  [Pow.Complex][tau-codes-pow], and `intervalIntegrable_rpow_mul_one_sub_rpow` from
  [SpecialFunctions.Beta][tau-codes-beta].
- `Dirichlet/TauCetiBridge.lean`: identifies the local real Dirichlet measure with
  `TauCeti.Probability.dirichletMeasure` from [Dirichlet.Basic][tau-codes-dirichlet].

- `ComplexAnalysis/LogDerivIntegral.lean`, `CurveIndex.lean` and `CurveIndex/Continuity.lean`,
  resynchronized from `../lean-CA`, import TauCeti's `Contour.Winding` modules; their headers
  retain the master project's attribution.

### Further adoptions — 5 October 2026 (second round)

- `Dirichlet/Real/Moments.lean`, `Dirichlet/Real/Marginals.lean` and
  `Dirichlet/Real/Aggregation.lean`: the coordinate mean, variance and covariance, the beta
  coordinate marginals and the aggregation law are transferred through `Dirichlet.TauCetiBridge`
  from `integral_eval_dirichletMeasure`, `variance_eval_dirichletMeasure`,
  `covariance_eval_dirichletMeasure_of_ne` ([Dirichlet.Moments][tau-codes-dir-moments]),
  `map_eval_dirichletMeasure` ([Dirichlet.Marginal][tau-codes-dir-marginal]) and
  `map_euclideanFiberSum_dirichletMeasure` ([Dirichlet.Aggregation][tau-codes-dir-aggregation]).
  The local moment-determination proof of aggregation, its multinomial helpers and the direct
  two-coordinate marginal proof were removed. The monomial moment formulas remain local.
- `Pochhammer/BinomialSeries.lean`: `hasSum_multichoose_mul_geometric_complex_of_norm_lt_one`
  from [Analytic.Binomial][tau-codes-binomial].
- `Carlson/Jacobi/Hermite.lean`: Theorem 7.10-4 is transported from
  `TauCeti.integral_hermite_mul_hermite_mul_gaussian` ([Hermite.Orthogonality][tau-codes-hermite])
  by the scaling bridge `sqrt_two_pow_mul_eval_monicHermite` to Mathlib's `Polynomial.hermite`.
- `Carlson/Elliptic/SchwarzChristoffel.lean`: Carlson's map `R_{-a}(b; z - x)` is identified with
  an affine image of `TauCeti.schwarzChristoffelPrimitive`
  ([SchwarzChristoffel.Primitive][tau-codes-sc-primitive]); openness and boundedness of the image
  follow from [SchwarzChristoffel.Image][tau-codes-sc-image]. The local boundary, polygon and
  mapping proofs are retained.

The comparison of the local polygon and mapping theorems with TauCeti's boundary, covering and
image theory, and the Chebyshev developments, remain related work.

### Carlson (1969), Theorem 8 — 5 October 2026

- `Dirichlet/Average/Chart.lean` takes its convex charts from the Tau Ceti contributors'
  Riemann mapping theorem `TauCeti.exists_bijOn_ball_differentiableOn_invFunOn`
  ([RiemannMapping.Existence][tau-codes-riemann]). The simply connected case of Theorem 8
  (`Dirichlet/Average/SimplyConnected.lean`) depends on it.

## Related-work review, 2026-10-04

The following notes were moved from the lean-PR review. They compare relevant statements
with public Lean Zulip discussions, Mathlib pull requests, and TauCeti sources. They
acknowledge related work and support coordination; finding a similar result does not
establish that a proof was borrowed from it.

PR statuses below are those observed on the review date. “Merged by Bors” follows the PR's
recorded title; an open or closed-unmerged PR is not an available Mathlib dependency.
TauCeti source links are pinned to the inspected revision
[`680bd1855971`](https://github.com/TauCetiProject/TauCeti/tree/680bd1855971ac82971b9d18f2f85914d62270de).
The external sources were inspected, not built against the pinned Mathlib shared by these projects.
Zulip searches used the public archive; newer discussion links supplied by PR authors are
included as coordination pointers where their message contents were not accessible.

### Analysis

- **Open mapping** (`ToMathlib/Analysis/OpenMapping.lean`, removed from `lean-PR`):
  **direct overlap with a more general proposed API**.
  Kevin H. Wilson's open
  [PR #44201](https://github.com/leanprover-community/mathlib4/pull/44201)
  generalizes `ContinuousLinearMap.isOpenMap` to complete first-countable source spaces
  and Hausdorff Baire targets, including semilinear maps. Inspection of its
  [proposed Banach module](https://github.com/leanprover-community/mathlib4/blob/1ad0026d4bd4fad2154b8b5811fa6b66e61201a0/Mathlib/Analysis/Normed/Operator/Banach.lean)
  shows that the target need not have the pseudometrizability/uniformity required by
  our implementation. The lean-PR module has been removed; the copy in `lean-codes`
  is retained for review upon the anticipated adoption of that PR. Our linear theorem
  should become a specialization if it lands. TauCeti's
  [Henkel open-mapping theorem](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Topology/Algebra/OpenMapping/Henkel.lean)
  is another related development: it assumes a nonarchimedean source group but permits
  a more general scalar action with a zero sequence of units. It is not a direct
  substitute for our real/complex vector-space theorem.

- **Holomorphic spaces, Montel, and Vitali** (the `ToMathlib/Analysis/Holomorphic/` modules were
  adopted from `lean-PR`, including the improved function-space API, closedness,
  completeness, and one-variable Montel/Vitali results). The module headers include
  the related-work credits and a review note for anticipated adoption of PR #33505.
  In addition to Beffara's RMT4 credited
  above, Yury Kudryashov's open draft
  [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505)
  develops the Riemann mapping theorem and contains a holomorphic-family equicontinuity
  result. The [Zulip “Multivariate complex analysis” thread](https://leanprover-community.github.io/archive/stream/116395-maths/topic/Multivariate.20complex.20analysis.html)
  documents this effort and explicitly discusses RMT4 and avoiding duplication.
  TauCeti already has
  [normal-family bounds](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/NormalFamilies.lean),
  [compact-open precompactness](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Montel/Precompact.lean),
  [Montel selection](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean), and
  [Vitali convergence](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Vitali.lean).
  This is substantial mathematical overlap: its Montel theorem allows proper complex
  normed targets, while its accumulation-point Vitali theorem is scalar-valued. Our
  bundled submodule interface and finite-dimensional-vector-valued Vitali statement
  distinguish the packaging and target generality. TauCeti itself identifies these
  modules as temporary implementations to reconcile with Mathlib's RMT work.

- **Curve integrals and exact forms** (`ToMathlib/Analysis/Integral/CurveIntegral.lean` and its `Map`,
  `Bounds`, and `Improper` modules, now retained in `lean-codes` and removed from
  `lean-PR`'s submission inventory). The newer bounds, with redundant nonnegativity
  hypotheses removed, were adopted in `lean-codes`. The module headers point to both
  PRs below for review upon anticipated adoption; matching headers in `lean-CA`
  are synchronized. The open
  [Mathlib PR #39524](https://github.com/leanprover-community/mathlib4/pull/39524)
  by `FordUniver` proves segment integrability and fundamental-theorem formulas
  `curveIntegral_fderiv_segment` and `curveIntegral_fderivWithin_segment`, overlapping
  our segment endpoint-difference results. Yury Kudryashov's open
  [PR #39254](https://github.com/leanprover-community/mathlib4/pull/39254)
  specializes `curveIntegral` to complex contour integrals and explicitly discusses
  further review of the curve-integral API. TauCeti's
  [primitive construction](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Contour/Primitive.lean)
  and [integral bound](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Contour/Curve/IntegralBound.lean)
  are related consumers and estimates. They do not by themselves replace the full
  Banach-valued pullback, operator-norm, and improper-endpoint API retained here.

### Coverage and limits of the search

The review also covered `ToMathlib/Analysis/Holomorphic/PolynomialApproximation.lean`,
which was adopted from `lean-PR`. No sufficiently specific additional overlap was verified
for its disk and entire-function approximation results. The general analytic polynomial
approximation helper remains in both projects; see the lean-PR credits linked above.

This is not a claim of novelty or an exhaustive search of all branches or Zulip messages.
No external Lean code was incorporated as part of the related-work survey.

[tau-codes-degree]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/LocalDegree.lean
[tau-codes-inverse]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/Inverse/Function.lean
[tau-codes-slit]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/SlitPlane.lean
[tau-codes-exterior]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Normed/Module/Ball/Exterior.lean

[tau-codes-moments]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Moments/CompactDeterminacy.lean
[tau-codes-pi]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/MeasureTheory/Integral/Pi.lean
[tau-codes-covering]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Topology/Homotopy/Covering.lean
[tau-codes-beta]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean
[tau-codes-beta-law]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Beta/Basic.lean
[tau-codes-normrpow]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/MeasureTheory/Integral/NormRpow.lean
[tau-codes-pow]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Pow/Complex.lean
[tau-codes-dirichlet]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Basic.lean
[tau-codes-dir-moments]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Moments.lean
[tau-codes-dir-marginal]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Marginal.lean
[tau-codes-dir-aggregation]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Dirichlet/Aggregation.lean
[tau-codes-binomial]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Analytic/Binomial.lean
[tau-codes-hermite]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean
[tau-codes-sc-primitive]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Primitive.lean
[tau-codes-sc-image]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Image.lean
[tau-codes-riemann]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean
