# Elementary several complex variables: coverage ledger

Scope: Boas Chapters 1–2; Lebl Chapter 1; Suwa Chapter 1; Scheidemann Chapters 1–2;
Fritzsche–Grauert Chapter I, Sections 1–7. The first implementation commitment is
Stages 1–4 of the agreed plan. Later stages are recorded, not silently counted as complete.

The four-stage elementary commitment is implemented. The second batch completes locally
bounded Osgood, mixed Taylor coefficients and separate-radius expansions, derivative
convergence, coordinate transport, and Montel. This does not claim the later textbook branches
listed below, notably unrestricted Hartogs separate holomorphy or analytic Weierstrass division.

## Conventions

- Use `AnalyticAt ℂ` / `AnalyticOnNhd ℂ` and prove equivalences with textbook definitions.
- Coordinate results use finite index types; basis-independent results use finite-dimensional
  complex normed spaces. The function-space sup norm is not the Euclidean norm.
- Retain Banach-valued analytic and integral results when possible. Normal-family compactness
  needs scalar or finite-dimensional targets, not arbitrary Banach targets.
- Use existing `FormalMultilinearSeries`, `MvPowerSeries`, continuous maps and germs.
- Empty and singleton index types are included unless a theorem explicitly needs dimension ≥ 2.
- SCV does not import Dirichlet, simplex or Carlson modules; compatibility bridges point upward
  from applications to SCV.

## Mathlib inventory

Checked against the project's pinned Mathlib v4.33.1. Recheck upstream before proposing PRs.
These are reusable existing results, not planned reimplementations.

| Topic | Mathlib file and representative declaration |
| --- | --- |
| General identity principle | `Analysis/Analytic/Uniqueness`: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` |
| Maximum modulus | `Analysis/Complex/AbsMax`: `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` |
| Scalar open mapping, general source | `Analysis/Complex/OpenMapping`: `AnalyticOnNhd.is_constant_or_isOpen` |
| Liouville, general source/target | `Analysis/Complex/Liouville`: `Differentiable.exists_eq_const_of_bounded` |
| Analytic Fréchet derivatives | `Analysis/Calculus/FDeriv/Analytic`: `AnalyticOnNhd.fderiv`, `AnalyticOnNhd.iteratedFDeriv` |
| Derivative of a coordinate update | `Analysis/Calculus/Deriv/Pi`: `hasDerivAt_update` |
| Symmetry of the second derivative | `Analysis/Calculus/FDeriv/Symmetric`: `ContDiffAt.isSymmSndFDerivAt_of_omega` |
| Taylor coefficients on the diagonal | `Analysis/Calculus/FDeriv/Analytic`: `HasFPowerSeriesOnBall.factorial_smul`, `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` |
| Uniform Taylor convergence and remainder bounds | `Analysis/Analytic/Basic`: `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn`, `HasFPowerSeriesOnBall.uniform_geometric_approx` |
| Coordinate Cauchy bound | `Analysis/Complex/Liouville`: `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` |
| Analytic inverses | `Analysis/Analytic/Inverse`: `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` |
| Real/complex derivative bridge | `Analysis/Complex/Conformal`: `differentiableAt_complex_iff_differentiableAt_real` |
| One-variable derivative convergence | `Analysis/Complex/LocallyUniformLimit`: `TendstoLocallyUniformlyOn.deriv` |
| Compactness of equicontinuous families | `Topology/UniformSpace/Ascoli`: `ArzelaAscoli.isCompact_of_equicontinuous` |
| Compact-open convergence and completeness | `Topology/UniformSpace/CompactConvergence`: `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`, `ContinuousMap.instCompleteSpaceOfCompactlyCoherentSpace` |
| Germs and evaluation | `Topology/Germ`, `Order/Filter/Germ/Basic` |
| Formal multivariable algebra | `RingTheory/MvPowerSeries/*` |
| Formal Weierstrass preparation | `RingTheory/PowerSeries/WeierstrassPreparation`; not analytic convergence of germs |

## First commitment

Status is deliberately fine-grained: a proved special case does not discharge a stronger goal.

| Stage | Topic | Status / home |
| --- | --- | --- |
| 1 | Equal-radius polydisc geometry and Cauchy formula | Proved; extracted to `Polydisc`, `CauchyIntegral` |
| 1 | Cauchy coefficient construction and estimates | Proved; extracted to `CauchySeries` |
| 1 | Continuous separate holomorphy ⇒ analyticity | Proved; `Osgood` |
| 1 | Arbitrary finite indices and separate radii | Proved; `Polydisc`, `CauchyIntegral`, and `polydisc_cauchy_reindex` in `Reindex` |
| 1 | Basis-independent differentiability ⇒ analyticity | Proved; `Basic` |
| 2 | Coordinate derivatives and Fréchet derivative bridge | Proved; `Derivatives`, including reconstruction as a finite sum |
| 2 | Mixed derivatives and Jacobian | Proved; `Derivatives`: arbitrary reordering, finite-sum linearity and matrix chain rule; `Reindex`: coordinate and iterated derivative transport |
| 2 | Wirtinger derivatives and Cauchy–Riemann equivalence | Proved; `CauchyRiemann`: real differentiability plus coordinate CR equations iff analyticity on an open set |
| 2 | Locally bounded separate holomorphy ⇒ analyticity | Proved; `LocallyBounded`: explicit joint Lipschitz estimates supply continuity for Osgood |
| 3 | Full polydisc expansion | Proved; equal-radius `FormalMultilinearSeries` in `CauchySeries`; full separate-radius multi-index `HasSum` in `PolydiscTaylor`; scalar bridge to Mathlib `MvPowerSeries` |
| 3 | Derivative coefficients and radius independence | Proved; `CauchyCoefficients`: mixed derivatives equal multi-index factorials times integral coefficients; arbitrary positive admissible radii give the same coefficients |
| 3 | Multi-index Cauchy estimates | Proved; `norm_multiIndexDeriv_le` in `CauchyCoefficients` gives the factorial and separate-radius factors |
| 3 | Uniform convergence and remainders | Proved; `PolydiscTaylor`: uniform convergence on smaller closed polydiscs, locally uniform convergence on the full open polydisc, arbitrary finite-polynomial geometric-tail bounds (also a finite product/sum formula), and termwise mixed differentiation; equal-radius geometric-in-degree estimates also follow from Mathlib's `uniform_geometric_approx` |
| 4 | Locally uniform limits / normally convergent analytic sums | Proved; `LocallyUniform` |
| 4 | Locally uniform convergence of all derivatives | Proved; `LocallyUniform`: mixed derivatives, termwise differentiation of holomorphic series, and all iterated Fréchet derivatives in operator norm on arbitrary finite-dimensional complex domains |
| 4 | Holomorphic function space and compact-open topology | Proved for finite-coordinate domains and Banach targets; `FunctionSpace` uses a closed submodule of `C(U, F)` |
| 4 | Completeness, restriction/evaluation/differentiation | Proved; `FunctionSpace` |
| 4 | Equicontinuity from local bounds and Montel | Proved; `Montel`: compact-local bounds give equicontinuity (Banach targets) and compact closure in the holomorphic function space (finite-dimensional targets) |

`ParametricIntegral` and `AnalyticUniqueness` are additional proved infrastructure retained
for Carlson and other applications. Compact-domain differentiation under the integral is used
to differentiate the higher Cauchy kernels without varying the contour.

## Boundaries and next review

- The contour theorems assume continuity and coordinate-slice analyticity on the closed
  polydisc. Analyticity on a neighborhood of that polydisc supplies these assumptions.
- Mixed coefficients are identified by differentiating the Cauchy integral, not by incorrectly
  inferring equality of arbitrary multilinear maps from their diagonals.
- Montel is compactness of the closure in the compact-open holomorphic function space.
  Finite-dimensional targets are essential; the unrestricted Banach-target assertion is false.
- Arbitrary finite-index integrals use an enumeration by `Fin n`. The proven Cauchy formula
  makes their value independent of the enumeration under its hypotheses. This is not a new
  general permutation-invariance theorem for arbitrary torus integrands.
- Review naming, minimal imports and upstream overlap before packaging Mathlib PRs. Further
  convenience wrappers are not prerequisites for the proved four-stage core.

## Explicitly deferred branches

- Boas §2.7: full Hartogs separate-holomorphy theorem, without continuity or local bounds.
- Boas §2.4, Scheidemann §2.3, Fritzsche–Grauert I §5: Hartogs figures and shell extension.
- Lebl §1.6: hypersurface removable singularities and injective-map theorem.
- Boas §§2.1–2.2, 2.5–2.6 and Scheidemann §§1.5, 2.1–2.2: Reinhardt/Laurent theory,
  convergence-domain characterization, natural boundaries, representation interpretation.
- Lebl §§1.4–1.5: ball–polydisc inequivalence and Cartan uniqueness.
- Suwa §1.4: analytic germs/local rings, analytic Weierstrass division and preparation,
  Noetherianity and unique factorization.

## Validation

After every Lean edit: root `lake build`. Before handoff: direct `lake env lean` checks for
every changed Lean file, `git diff --check`, admission scan, and axiom audits of major results.
Preserve the `.lake` symlink, package versions, and existing Carlson interfaces.

Validation of the first batch (2026-09-13):

- Root `lake build`: successful, 3,248 jobs, including the Carlson dependents.
- `lake env lean` on the umbrella and all ten changed/new SCV implementation files:
  successful, with no warnings from those direct checks.
- `git diff --check`: successful.
- SCV admission scan: no `sorry`; the three pre-existing Carlson admissions remain unchanged.
- Axiom audits of the separate-radius Cauchy formula, full-radius series, diagonal Taylor
  coefficients, basis-independent analyticity, mixed derivative symmetry, Jacobian chain rule,
  CR characterization, Cauchy bound, derivative convergence, closedness of the holomorphic
  function space, and continuity of differentiation/restriction: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- No existing theorem was found false or given additional hypotheses. Existing equal-radius
  and Carlson-facing interfaces are preserved; no package versions or build topology changed.

Validation of the completion batch (2026-09-13):

- Root `lake build`: successful, 3,255 jobs, including the Carlson dependents. No SCV warnings;
  existing warnings elsewhere in the project remain.
- Direct `lake env lean` checks of the umbrella and all 17 SCV implementation modules:
  successful, without warnings or errors. This includes every file edited in this batch.
- `git diff --check`: successful.
- `rg -n '\bsorry\b' --glob '*.lean' .`: no SCV admissions. The only remaining admissions are
  unchanged at `Carlson/R/AssociatedDependence.lean:258`,
  `Carlson/R/AssociatedRecurrence.lean:363`, and `Carlson/TwoVariable/Quadratic.lean:468`.
- Twenty major-result axiom audits passed: locally bounded Osgood and its Lipschitz estimate;
  equicontinuity and Montel; compact-domain integral differentiation; higher Cauchy-transform
  differentiation; mixed coefficient identification, radius independence and Cauchy estimates;
  the `MvPowerSeries` coefficient bridge; pointwise, uniform and locally uniform Taylor sums;
  the explicit remainder and differentiated Taylor series; coordinate transport; termwise
  differentiation of general holomorphic series; and basis-independent Weierstrass and iterated
  Fréchet derivative convergence. Dependencies are only `propext`, `Classical.choice`, and
  `Quot.sound`, with no `sorryAx` or new axioms.
- Explicit zero-dimensional and one-coordinate mixed-derivative regression checks passed.
- No existing theorem was found false or had its assumptions strengthened. Some helper
  assumptions were weakened by removing unused completeness/finiteness instances. Montel's
  finite-dimensional-target restriction is explicit; an unrestricted Banach-target variant
  has not been asserted.
- Existing user changes, Carlson files, package versions, and the intentional `.lake` symlink
  were preserved. No `Scratch.lean` remains in the project.
