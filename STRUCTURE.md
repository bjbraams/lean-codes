# Carlson project module structure

The project's mathematical libraries are the general support in `ToMathlib` (`Algebra`,
`Analysis`, `Topology`), `Pochhammer`, `StdSimplexMeasure`, the complex-analytic subsets
`ComplexAnalysis` and `SeveralComplexVariables`, `Dirichlet`, `SimplexMellin`, and `Carlson`.
General support and simplex geometry/integration (`StdSimplexMeasure`) feed into `Dirichlet`,
which is the shared basis of two collections: `SimplexMellin` (the theory of the regularized
Dirichlet transform as a transform in its own right) and `Carlson` (Carlson's special
functions). The support libraries do not import the application layers, Dirichlet theory
imports neither `SimplexMellin` nor `Carlson`, and those two do not import each other.
The complex-analytic libraries (`ToMathlib`,
`ComplexAnalysis`, `SeveralComplexVariables`) may depend on Mathlib, the pinned TauCeti and earlier support layers;
complex kernels integrated over simplices (divided differences, repeated integrals) live in
`StdSimplexMeasure.Complex`.

The root modules and the topic umbrellas below are convenient entry points.


TauCeti is pinned to the same revision as the CA and SCV companion projects. Prefer Mathlib,
then TauCeti, then local proofs. [TauCetiReview.md](TauCetiReview.md) records checked reuse
candidates and the dependency-closure audit: all 23 copied CA files and 21 copied SCV files
are needed and match their primary sources byte for byte. The synchronized injectivity,
holomorphic-inverse, half-plane quotient and exterior-connectedness proofs now use TauCeti.
The simplex moment-determination theorem, finite-product lower-integral formula and covering-map
injectivity also adapt TauCeti, preserving their existing local interfaces and hypotheses.
The synchronized logarithmic-derivative and curve-index copies (resynchronized 5 October 2026)
import TauCeti's winding-number theory for the endpoint-ratio identity, local constancy and
vanishing on unbounded components; `ToMathlib.Analysis.TaylorBounds` now derives its uniform
bound from Mathlib's `Convex.isLittleO_pow_succ`.
Since 5 October 2026 the beta-density lemmas, the singular power integrability lemma, and
several complex-power identities in the Carlson library also use TauCeti, and
`Dirichlet.TauCetiBridge` identifies the local real Dirichlet measure with TauCeti's
Gamma-normalization law.

## General algebra

`ToMathlib.Algebra.Submodule.Saturation` defines `Submodule.IsSaturated S` and the
saturation of a submodule at a multiplicative set `S`. The closure is the inverse image
of Mathlib's `S`-torsion submodule of the quotient; it includes a closure operator and
the equivalence between saturation at non-zero-divisors and a torsion-free quotient.
`ToMathlib.Algebra.Submodule.SaturationLocalization` identifies this closure with the
inverse image of the localized submodule.

`ToMathlib.Algebra.LinearDependence` proves finite independence bounds and existence of
nontrivial relations in saturated finite spans over commutative rings, assuming only
that `0 ∉ S`. It uses Mathlib's localization and span-cardinality results. The associated
Carlson-function arguments specialize this support to nonzero polynomial denominators.
All three support modules depend only on Mathlib and each other.

The proposed upstream homes are `Mathlib/Algebra/Module/Submodule/Saturation.lean` for
the basic API, additions to `Mathlib/Algebra/Module/LocalizedModule/Submodule.lean` for
the localization bridge, and `Mathlib/LinearAlgebra/Dimension/Saturation.lean` for the
independence and dependence results.

## General analysis and topology

`ToMathlib/Analysis.lean` and `ToMathlib/Topology.lean` expose general support extracted from
the complex-analytic and application libraries. Files that also exist in `lean-CA` or
`lean-SCV` are kept identical there; some (the holomorphic function spaces and the open mapping
theorem) are used only by those projects.
Both may use Mathlib and the pinned TauCeti. Complex analysis and SCV import individual support modules
as needed; the general foundations do not import either complex function-theory library.
Their directory names are not blanket namespaces. Existing namespaces such as
`ContinuousLinearMap`, `ContDiffAt`, `MeasureTheory`, `IsOpen`, `Path`, `Homeomorph`,
`Set` and `Real` are used, with root-level results where
that matches the underlying API.

| Module | Content |
| --- | --- |
| `ToMathlib.Algebra.LinearMap.Ordered` | Half-space inclusion and nonnegative or positive proportionality of linear functionals over ordered fields |
| `ToMathlib.Analysis.SpecialFunctions.Bessel` | The series of the regularized hypergeometric functions, bounds for Bessel functions of integer order, the modified Bessel function `I_a`, and for the regularized `₀F₁` termwise derivatives, a contiguous relation and the reflection formula (Carlson's (6.9-23), (6.9-24), Exercise 6.9-20) |
| `ToMathlib.Analysis.SpecialFunctions.GammaRatio` | Monotonicity of `Γ(x)/|Γ(x + iy)|` for `x > 0`, the bound `√(cosh πy)` for `x ≥ 1/2`, and `|Γ(1/2 + iy)|² = π/cosh πy` |
| `ToMathlib.Analysis.SpecialFunctions.Gamma` | Complex-rate Gamma/Laplace kernel bounds, integrability, differentiation, holomorphy, and evaluation |
| `ToMathlib.Analysis.SpecialFunctions.GammaBounds` | `|Γ(s)| ≤ Γ(re s)`, `Γ(x) ≤ Γ(y)` for `1 ≤ x ≤ y`, `2 ≤ y`, monotonicity of `Γ(x + r)/Γ(x)`, and `(x)ₙ ≤ (x + n)ⁿ` |
| `ToMathlib.Analysis.SpecialFunctions.LaplaceOneSubCos` | Partial fractions of `1/∏(y + j)` and the Laplace integral of `(1 - cos t)ⁿ` over `(2mπ, ∞)` (Carlson's Exercise 6.6-17) |
| `ToMathlib.Analysis.SpecialFunctions.Pow` | A power between two others is bounded by their sum; positive real bases to complex powers as exponentials; positivity of `re (1 - v)` for `‖v‖ < 1` |
| `ToMathlib.Analysis.Integral.ProdAbsRPow` | Integrability on `ℝ` of `∏ |σ - xᵢ|^{-bᵢ}` for distinct nodes, `bᵢ < 1` and `∑ bᵢ > 1`, allowing nonsingular positive powers |
| `ToMathlib.Analysis.UpperHalfPlaneMaximum` | Minimum principle for `im f` on the upper half-plane, for `f` holomorphic, continuous up to the axis, with a limit at infinity |
| `ToMathlib.Analysis.Connected` | Connected shells and complements of balls in real normed spaces |
| `ToMathlib.Analysis.ConvexHullDomain` | Path connectedness of configurations whose convex hull stays in a path-connected set; arbitrary index types and real topological vector spaces |
| `ToMathlib.Analysis.OpenMapping` | Open mapping for complete metrizable vector spaces over any nontrivially normed field |
| `ToMathlib.Analysis.TaylorBounds` | Vector-valued second-order Taylor bounds, the Taylor–Peano little-o remainder, and the real-valued corollary |
| `ToMathlib.Analysis.Integral.CompactSupport` | Compact weighted integrability over a normed ring with a bounded scalar action and half-line integration support |
| `ToMathlib.Analysis.Integral.CauchyBoundary` | Real-line and segment Cauchy jumps; continuity of the regularized integral at zero height, height-based vertical Plemelj limits, symmetric-truncation principal values, and integrability of the regularized quotient from differentiability at the pole |
| `ToMathlib.Analysis.Integral.Laplace` | Complex-phase Laplace asymptotics for measurable amplitudes and quadratic coefficients; absolute integrability, Gaussian moments, explicit normalized error `(L/c + M B/c²)/√n`, uniform parameter limits, finite-interval variants, and a nonzero-leading-term asymptotic equivalent |
| `ToMathlib.Analysis.Integral.Parametric` | Fréchet differentiation of compact integrals with fixed integrable weights and arbitrary real or complex normed parameter spaces |
| `ToMathlib.Analysis.Integral.CurveIntegral` | Endpoint formulas for exact one-forms on real or complex normed spaces, with Banach-valued potentials |
| `ToMathlib.Analysis.Integral.CurveIntegral.Map` | Pullback of one-forms under differentiable maps and identification of finite-interval parametrizations with Mathlib curve integrals |
| `ToMathlib.Analysis.Integral.CurveIntegral.Improper` | Limits determined by endpoint potentials, and convergence of finite curve integrals to integrable half-line pullbacks |
| `ToMathlib.Analysis.Integral.CurveIntegral.Bounds` | Operator-norm and speed estimates, vanishing connector integrals, and explicit power-decay rates for growing paths |
| `ToMathlib.Analysis.Integral.Reciprocal` | Inversion change of variables on arbitrary measurable sets avoiding zero, with half-line corollaries |
| `ToMathlib.Analysis.Integral.Tail` | Uniformly vanishing tails under a common integrable majorant, uniform finite-interval approximation, and a quantitative power-decay tail estimate |
| `ToMathlib.Analysis.Integral.EndpointDeformation` | Equality of two path integrals through a convex domain of holomorphy with possibly singular common endpoints, from a primitive and an endpoint compatibility estimate |
| `ToMathlib.Analysis.Holomorphic.FunctionSpace` | Bundled compact-open holomorphic maps, pointwise algebra, evaluation and restriction as continuous linear maps, and convergence directly on the domain |
| `ToMathlib.Analysis.Holomorphic.LocallyUniformLimit` | Closedness and completeness on open subsets of the complex plane with Banach targets, using Mathlib's Weierstrass theorem |
| `ToMathlib.Analysis.Holomorphic.NormalFamily` | Equicontinuity under compact-local bounds; Montel compactness, subsequences, and Vitali convergence on planar domains with finite-dimensional targets; general-source versions retain a closedness hypothesis. Related work: RMT4, [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), and TauCeti (links in the module header) |
| `ToMathlib.Analysis.Analytic.PolynomialApproximation`, `Holomorphic.PolynomialApproximation` | Explicit polynomial partial sums over normed fields, and complex disk/entire-function approximation; used by `Carlson.Jacobi.AnalyticExpansion` |
| `ToMathlib.Topology.LocallyConstantGluing` | Unique normalized gluing of functions with locally constant quotients or differences on an open cover, for arbitrary groups or additive groups; local-domain versions and uniqueness under preconnectedness |
| `ToMathlib.Topology.Frontier` | Frontiers and complementary components |
| `ToMathlib.Topology.Order.IntermediateValue`, `Path` | First exit through the frontier for continuous functions on real intervals and for paths |
| `ToMathlib.Topology.Baire.Bounded` | Local uniform upper bounds for pointwise bounded families of lower semicontinuous real functions, and the dense open set of local uniform boundedness |
| `ToMathlib.Topology.SeparateContinuous` | The Baire bound for separately continuous maps into seminormed groups, with a compact parameter set |
| `ToMathlib.Topology.ProperCovering` | Continuous open locally injective maps are local homeomorphisms; proper local homeomorphisms are covering maps; coverings of simply connected spaces from path-connected spaces are injective |

The generic Baire and real-estimate blocks were separated from the SCV Hartogs proof.
General curve integration lives in `ToMathlib.Analysis`; its complex-specific
applications are in `ComplexAnalysis.CauchyIntegral`.

## Pochhammer support modules

`Pochhammer.Estimates` includes factorial-geometric bounds, half-integer comparison,
and nonvanishing of ascending Pochhammer symbols in the right half-plane.
`Pochhammer.Gamma` includes uniform factorial decay of reciprocal Gamma after a
common natural shift on compact sets, with a finite-coordinate-sum specialization, and the
natural-shift identity `Γ(z + m) = (z)ₘ Γ(z)` at every Gamma-regular `z`.

## Single-variable complex analysis

`ComplexAnalysis/` holds the modules of the separate one-variable project `lean-CA` that the
Dirichlet and Carlson layers use, directly or through the several-variable modules. Each file is
an exact copy of the `lean-CA` file of the same name, which is the primary source; the full
one-variable library and its documentation are in that project. Complex-specific declarations
use the `Complex` namespace; extensions to existing APIs retain namespaces such as
`AnalyticOnNhd` and `DiffContOnCl`. General support is imported from `ToMathlib`; the modules
do not import the application layers, `StdSimplexMeasure`, or several-variable function theory.

| Module | Proved content |
| --- | --- |
| `ComplexAnalysis.HalfPlane`, `Pow` | Right-half-plane branch geometry, sector square roots, finite-family containing disks, and principal-power multiplication and holomorphy |
| `ComplexAnalysis.BranchLog` | Differentiation of continuous logarithm branches; holomorphic logarithms and roots on simply connected open sets; prescribed branch value and uniqueness |
| `ComplexAnalysis.BranchLog.Analytic` | Analytic dependence of logarithm branches, including normed source spaces and normalization along a zero section |
| `ComplexAnalysis.ExteriorPath` | Compactified exterior paths, escape to infinity, derivatives and normalized node factors |
| `ComplexAnalysis.HasPrimitives` | Local-to-global primitives on simply connected open domains; Banach-valued holomorphic primitives, normalization, uniqueness, and Morera's global primitive consequence |
| `ComplexAnalysis.CauchyIntegral` | Path independence for functions with primitives; Banach-valued Cauchy's theorem on simply connected open sets; logarithmic-derivative integrals |
| `ComplexAnalysis.CauchyFormula` | Banach-valued Cauchy formula on simply connected open sets, retaining the scalar kernel integral explicitly; normalized formula when that integral is `2πi` |
| `ComplexAnalysis.LogDerivIntegral`, `CurveIndex` | Exponential endpoint identity for logarithmic-derivative integrals; integer-valued index for closed C¹ curves avoiding the pole; reversal, concatenation, vanishing, and the index-weighted Banach-valued Cauchy formula |
| `ComplexAnalysis.Integral.CirclePath` | Smooth circle paths and equality of curve and circle integrals; used to normalize the index inside and outside a circle |
| `ComplexAnalysis.CurveIndex.Continuity` | Continuous and locally constant dependence on the pole off the curve; constancy on connected components and vanishing on every unbounded component of the complement |
| `ComplexAnalysis.CauchyDerivatives`, `CauchyEstimates`, `CauchySeries` | Higher derivative circle formulas at any interior point (from Mathlib's kernel derivative), compact derivative bounds, geometric Taylor-coefficient majorants, and one-variable Cauchy-series estimates |
| `ComplexAnalysis.Cycle` | Cycles as finite families of closed curves with base points; integrals and indices summed over the family; integer, locally constant and eventually vanishing index; length-type integral bounds; concatenation and integer multiples of a closed curve |
| `ComplexAnalysis.Cycle.Cauchy` | Homology form of Cauchy's theorem and Cauchy's formula for Banach-valued functions: for a `C¹` cycle whose index vanishes outside the open set (Dixon's proof) |
| `ComplexAnalysis.HolomorphicIntegral` | Fubini for interval integrals with continuous integrands, continuity and holomorphy of parametric interval integrals, and joint continuity of the divided slope of a holomorphic function |
| `ComplexAnalysis.Injective`, `HolomorphicInverse` | Nonvanishing derivative of injective holomorphic functions; the inverse of an injective holomorphic function is holomorphic on the open image |
| `ComplexAnalysis.ParametricIntegral`, `RealUniqueness` | Compact integration in one complex parameter and uniqueness from real parameters |
| `ComplexAnalysis.Subharmonic.Submean` | Circle submean inequality for positive powers of norms of holomorphic functions |

## Several complex variables support modules

`SeveralComplexVariables/` holds the modules of the separate several-variable project
`lean-SCV` that the Dirichlet and Carlson layers use; each file is an exact copy of the
`lean-SCV` file of the same name, which is the primary source. Besides the interfaces below,
the retained modules are `Polydisc`, `Reinhardt`, `CauchyIntegral`, `CauchySeries`, `Osgood`,
`LocallyBounded`, `RemovableSingularity.Cauchy`, and the `SeparateAnalytic` submodules, which
supply the polydisc Cauchy theory and the proof of Hartogs' theorem. The main interfaces used
by Dirichlet and Carlson are:

| SCV module | Application |
| --- | --- |
| `Analyticity`, `ParametricIntegral` | Analytic dependence of native Dirichlet integrals and differentiation under integrals |
| `SeparateAnalytic` | Hartogs' theorem for joint dependence on Dirichlet parameters, auxiliary variables, nodes, and the Carlson R exponent |
| `RealUniqueness` | Recognition and uniqueness of entire continuations from positive real parameters |
| `CauchyEstimates` | Coordinate derivative estimates; planar bounds and circle derivative formulas are in `ComplexAnalysis.CauchyEstimates` and `ComplexAnalysis.CauchyDerivatives` |
| `Derivatives`, `PolynomialDerivatives` | Coordinate derivatives, mixed derivative symmetry, and recurrence coefficients |
| `ContourIntegral` | Analytic dependence of continued circle-integral representations |
| `DominatedIntegral`, `LocallyUniform` | Joint analyticity of Carlson's single integral and of convergent Taylor and S series |

Hartogs' theorem removes the need to prove local boundedness when combining
already analytic coordinate slices. The public local-bound results in
`Dirichlet.Complex.Parametric` and `Dirichlet.Average.Associated.Analytic` remain
useful with merely continuous kernels or averaged functions.

The simply connected case of Carlson (1969), Theorem 8, uses SCV Hartogs (for the joint
holomorphy of a chart difference quotient and for removing Gamma poles), the CA logarithm
branches on simply connected domains, and the Tau Ceti Riemann mapping theorem; no Jordan-domain
contour constructions or planar exhaustion are needed.

## Simplex foundation modules

`StdSimplexMeasure.Normalization` supplies measurable normalization by coordinate
sum. Two-coordinate interior and ambient-measure projection facts live in
`StdSimplexMeasure.Interior` and `StdSimplexMeasure.Measure.Basic`; aggregation
commutes with semiring homomorphisms in `StdSimplexMeasure.Aggregation`.
`StdSimplexMeasure.Radial` integrates over the positive orthant in simplicial polar
coordinates `x = t • u` (`t = ∑ xᵢ`, `u` in the simplex): Lebesgue measure on the orthant is the
image of `t^(card ι - 1) dt ⊗ du` (`map_polarMap`), for nonnegative and for integrable
Banach-space-valued functions.
`StdSimplexMeasure.MomentDetermination` shows that finite measures on the simplex are
determined by their moments, and that functions with vanishing moments vanish almost
everywhere, and pointwise on the simplex when continuous.
`StdSimplexMeasure.MomentProblem` solves the moment problem on the simplex
(`exists_measure_iff`): a sequence on `ℕ^ι` is the moment sequence of a finite measure on the
simplex if and only if it is nonnegative and satisfies the sum-shift equation
`a n = ∑ᵢ a (n + eᵢ)`. Sufficiency uses discrete approximating measures with multinomial weights,
Stone–Weierstrass, and the Riesz–Markov–Kakutani theorem; for two coordinates this is Hausdorff's
moment problem on `[0, 1]`.

### `StdSimplexMeasure.PositiveSimplex`

Contains modules `Basic`, `SumIntegral`, `Aggregation`.

Geometric operations. Solid-simplex geometry and volume; sum-coordinate integration; aggregation.

### `StdSimplexMeasure.Measure`

Contains modules `Basic`, `Aggregation`.

Ambient coordinate measure and invariance; aggregation pushforward density.

`stdSimplexMeasure` is a measure on the **entire sum-one affine hyperplane**, not a measure
supported only on the simplex.
Intrinsic simplex measure is its restriction transported through the coordinate
homeomorphism.

### `StdSimplexMeasure.Integral`

Contains modules `Basic`, `Slicing`, `Monomial`, `Aggregation`.

Coordinate integral API; slicing/Fubini; polynomial integration; aggregation.

Ambient smooth neighborhoods and derivatives remain in the coordinate vector
space.

### `StdSimplexMeasure.Complex`

Contains modules `Integral`, `DividedDifference`, `NewtonTaylor`, `RepeatedIntegral`.

Complex kernels integrated over simplices, in the `Complex` namespace: unnormalized simplex
kernel integrals with permutation symmetry, coalescence and the simplex FTC; Hermite–Genocchi
divided differences including coincident nodes, with the recurrence and exact Newton and
Taylor remainders; segment integration identified with Mathlib curve integrals, and repeated
integration as a coalesced simplex integral under continuity. These modules depend only on
`StdSimplexMeasure.SimplexFTC` and Mathlib; they are used by `Dirichlet.Average.NewtonTaylor`.

### `StdSimplexMeasure.Real`

Contains module `NewtonTaylor`.

The same theory for real nodes and kernels `f : ℝ → ℂ` that are only finitely often continuously
differentiable on an open interval, in the `Real` namespace: simplex FTC for `C¹` kernels,
Hermite–Genocchi divided differences with the recurrence (Lemma 5.5-1), and Newton and Taylor
formulas with exact remainder (Theorem 5.5-2, (5.5-8)), all in Carlson's case (i).

## Dirichlet theory modules

### `Dirichlet.Beta.Complex.Basic`

Contains module `Integral`.

Complex multivariate beta. Gamma quotient and parameter identities.
Simplex integral evaluation.

### `Dirichlet.Real`

Real probability results. `Dirichlet.Real.Moments`, `Real.Aggregation` and `Real.Marginals` are
downstream of the real distribution and of `Dirichlet.TauCetiBridge`. The monomial and
power-product moment formulas are local; the coordinate mean, variance and covariance, the
aggregation law and the beta marginals are transferred from TauCeti's Dirichlet development.
`Dirichlet.Real.Average` supplies integrability on the compact simplex, Jensen bounds,
and mixed affine moments. Almost-sure equality of affine combinations is equivalent
to equality of their node vectors. `Dirichlet.Real.StrictAverage` uses this to prove
strict Jensen bounds and strict convexity or concavity in the nodes for general kernels.
The Jensen bounds need only convexity of the kernel's domain, not closedness.
`Dirichlet.TauCetiBridge` shows that, for positive parameters on a nonempty index type, the
image of `dirichletMeasure b` in `EuclideanSpace ℝ ι` is `TauCeti.Probability.dirichletMeasure b`,
and transfers integrals between the two measures without measurability assumptions.
`Dirichlet.Merge` merges two coordinates: the Dirichlet measure is the image of the product
of a two-coordinate and a merged Dirichlet measure under the merging map (moment
determination), with the corresponding iterated integral for continuous kernels.

### `Dirichlet.Complex`

Complex Dirichlet results.
Analytic dependence and
continuation are downstream of the native complex integrals.

### `Dirichlet.Bridge`

Compatibility between Real and Complex results.
The real probability distribution and complex integral interface share analytic
foundations; neither interface imports the other.

### Namespaces

The real Dirichlet distribution and its moments use `ProbabilityTheory`. Complex Dirichlet
densities and integrals, the regularized transform, and Carlson's Dirichlet averages use
`Dirichlet`. Carlson's R-polynomials and R/L/S/T functions use `Carlson`, with the two-node
specializations in `Carlson.TwoVariable`. Simplex geometry and smooth simplex functions are
root-level declarations or extend `MeasureTheory` and `Convexity.StdSimplex`.

### Dirichlet layers

| Module | Role |
| --- | --- |
| `StdSimplexMeasure.Interior` | Positive-coordinate simplex interior, measurability, permutation invariance, and almost-everywhere membership |
| `Dirichlet.Integral.Real` | Nonnegative and real monomial integrals, beta normalization, and real integrability |
| `Dirichlet.Integral.Complex` | Absolutely convergent complex monomial integrals and logarithmic majorants |
| `Dirichlet.Complex.Analytic` | Parameter analyticity on the absolute-convergence domain |
| `Dirichlet.Transform` | Finite-order tangential continuation by the explicit formula `regDirichletShiftFormula`, and existence of entire continuations for smooth simplex kernels |
| `Dirichlet.Transform.Basic` | General continuation predicate, canonical smooth-kernel transform, uniqueness, linearity, and independence of extension away from the simplex |
| `Dirichlet.Transform.Laws` | Permutations, coordinate and monomial shifts, the sum-shift identity, tangential differentiation, and coordinate-divisibility annihilation |
| `Dirichlet.Transform.Aggregation` | Aggregation of arbitrary kernels and Dirichlet parameters |
| `Dirichlet.Transform.Joint` | Joint continuation with auxiliary holomorphic parameters and commutation with auxiliary derivatives |
| `Dirichlet.Transform.Euler` | Two-endpoint Gamma-regularized Euler integrals, their identification with the two-coordinate Dirichlet transform, and joint entire continuation with holomorphic auxiliary parameters |
| `Dirichlet.Transform.Series` | Dominated native termwise integration and recognition of locally uniformly convergent series of continued transforms |
| `Dirichlet.Transform.Merge` | The merging (stick-breaking) identity `T_b[g] = Γ(b a + b a') T₂[v ↦ T_{b'}[g ∘ mergeMap v]]`: native for continuous kernels, as an identity of entire functions (with `Γ(b a + b a')⁻¹`) given a jointly holomorphic inner continuation, which exists for kernels holomorphic near the simplex |

| Topic | Modules |
| --- | --- |
| Divided differences and repeated integrals | `Dirichlet.Average.NewtonTaylor`: unweighted probability normalization, equality with the general `Complex` constructions, and compatibility statements for Carlson Section 5.5 |
| Native averages | `Dirichlet.Average.Basic`: regularized and ordinary definitions together |
| Associated average analysis | `Dirichlet.Average.Associated.Relations` → `Deriv` → `Analytic` |
| Holomorphic kernels and joint continuation | `Dirichlet.Complex.Parametric` → `Dirichlet.Transform.Parametric` → `Dirichlet.Transform.Joint` → `Dirichlet.Average.JointContinuation`: Carlson 6.3-6 on general convex open node domains; the general Jordan-curve representation remains separate |
| Continued Cauchy representations | `Dirichlet.Average.ResolventContinuation` and `CauchyContinuation`, using `SeveralComplexVariables.ContourIntegral`: entire-parameter resolvents and circle representations |
| Continuation on nonconvex domains | `Dirichlet.Average.HolomorphicDomain`: domain-aware characterization, uniqueness, and increasing-domain gluing |
| Hull-admissible integral domains | `Dirichlet.Average.IntegralDomain`: open node-domain geometry, joint continuation on the native node domain, and recognition of a given continuation on connected open scalar domains |
| Merging two nodes | `Dirichlet.Merge` → `Dirichlet.Transform.Merge` → `Dirichlet.Average.Merge`: the Dirichlet measure as the image of a two-node and a merged Dirichlet measure (moment determination), the merging identity for general kernels, and its specialization `𝓡_b(z; f) = Γ(b a + b a') 𝓡₂(…; 𝓡_{b'}(z'(w); f))` for positive real parameters (Carlson 1969, (4.21)) |
| Simply connected domains | `Dirichlet.Average.Chart` → `TwoNode` → `SimplyConnected`: convex charts and difference-quotient logarithms; the parametric two-node continuation by pulling back to a straight segment, with agreement by endpoint deformation (`ToMathlib.Analysis.Integral.EndpointDeformation`); and Carlson (1969), Theorem 8, simply connected case, by induction on the number of nodes with Gamma-pole removal (`Dirichlet.GammaPoles`) |
| Simply connected fibres | `Dirichlet.Average.FibreContinuation`: for a kernel holomorphic on an open `𝒲 ⊆ ℂ × P` with simply connected fibres, the two-node average (and the Euler integral with endpoints `0`, `1`) continues holomorphically in the Dirichlet parameters, nodes and parameter wherever the nodes lie in the fibre; fibrewise Riemann charts glued through relatively compact chart pieces (`IsConvexChart.exists_restrict`) and the identity theorem |
| Several variables | `Dirichlet.Average.SeveralVariables`: averages `𝓡_b(Z; h)` of a function holomorphic on `D ⊆ ℂⁿ` with vector nodes, continued to all nodes in `D` when the complex-line sections of `D` are simply connected (convex and `ℂ`-convex domains), by merging and the Euler continuation over moving simply connected fibres; Theorem 8 recovered for `n = 1` |
| Exterior-path kernels | `Carlson.R.ContourKernel`: holomorphic branch construction under path-avoidance hypotheses, compactified kernel continuation through the Euler transform, and identification of the straight-path case with the slit resolvent; general path independence remains open |

The generic transform modules do not import `Dirichlet.Average` or `Carlson`.
`Dirichlet.Average.KernelAnalytic` supplies the first stage of Carlson's transform:
`carlsonComplexKernel f (z, u) = f (∑ i, u i * z i)`. The Carlson continuation
predicate specializes `IsRegDirichletContinuation` to its real-simplex restriction;
native and continued joint holomorphy then follow from the general kernel theorems.
The canonical operator requires smoothness near the closed simplex. Its value at
parameters outside the convergence region is an analytic continuation, not the
value of the totalized native integral.

The series recognition theorem assumes local uniform convergence of the transformed
series; it does not deduce that convergence from a bound on the kernels alone.
Coordinate-divisibility annihilation is available at zero parameters, while a general
smooth-kernel face-restriction theorem remains separate work.

`Dirichlet.Beta.Complex`, `Dirichlet.Moments`, and
`Dirichlet.Average.Associated` re-export their topic modules.
`Dirichlet.Real` remains the basic distribution interface, not an umbrella
over its probability corollaries.

Analytic continuation remains downstream of native complex integration.
The general affine-form convex-hull characterization belongs in
`Dirichlet.Average.Kernel`, not in the T-function application.

## Simplex Mellin transform modules

`SimplexMellin` develops the regularized Dirichlet transform `T_b[g]` beyond what Carlson's
averages need. Its definition, entire continuation and structural laws stay in
`Dirichlet.Transform` (shared with `Dirichlet.Average` and `Carlson`). Declarations keep the
`Dirichlet` namespace. Generic inputs live in `ToMathlib.Analysis.MvMellinTransform`
(multivariable Mellin transform), `ToMathlib.Analysis.SchwartzExpExp` (a double-exponential
Schwartz function), `ToMathlib.Analysis.Fourier.PaleyWiener` (the classical Paley–Wiener theorem
on `ℝⁿ`, both directions, and injectivity of the Fourier–Laplace transform),
`ToMathlib.Analysis.Complex.Carlson` (Carlson's theorem on functions of exponential type vanishing
at `ℕ`), `ToMathlib.Analysis.MellinBarnes` and `ToMathlib.Analysis.SpecialFunctions.RamanujanMaster`
(moving Mellin–Barnes contours; Ramanujan's master theorem) and `StdSimplexMeasure.Radial`
(simplicial polar coordinates). The research
programme is [DirichletTransformProgram.md](DirichletTransformProgram.md).

| Module | Content |
| --- | --- |
| `SimplexMellin.Face` | Face formulas at nonpositive integer parameters: restriction to a face at `bᵢ = 0`, iterated integration by parts, and the binomial face formula at `bᵢ = -m` |
| `SimplexMellin.Uniqueness` | Monomial moments as transform values; a continuous kernel is determined on the simplex by its transform at positive integer parameters |
| `SimplexMellin.Bridge` | The Mellin bridge: in simplicial polar coordinates `mvMellin (φ(∑x) g(x/∑x)) b = mellin φ (∑ bᵢ) · ∏ Γ(bᵢ) · T_b[g]`, without integrability assumptions; for `φ = e^(−t)` the radial factor is `Γ(∑ bᵢ)` |
| `SimplexMellin.Inversion` | Inversion on a vertical plane `b = c − 2πiξ` by Fourier inversion in logarithmic coordinates, for any radial profile `φ`: `g u = φ(1)⁻¹ ∫ (∏ uᵢ^(−bᵢ)) ℳ[φ](∑ b) ∏ Γ(bᵢ) T_b[g] dξ` (for `φ = e^(−t)`: factor `e` and `Γ(∑ b)`), under integrability on the plane; unconditional for smooth kernels vanishing near the faces with a smooth profile compactly supported in `(0, ∞)` (TauCeti) |
| `SimplexMellin.Schwartz` | The exponential-profile inversion is unconditional for smooth kernels vanishing near the faces: the function in logarithmic coordinates is `G · A` with `A = exp(∑ (cᵢyᵢ − e^{yᵢ}))` Schwartz (`ToMathlib.Analysis.SchwartzExpExp`) and `G(y) = g(e^y/∑e^y)` of temperate growth |
| `SimplexMellin.PaleyWiener` | Necessity half of Paley–Wiener: for `g` continuous on the simplex and vanishing where some `uᵢ < δ`, the native integral `T_b[g]` is entire (Pochhammer shift identity), `S_g(b) = ∫_Δ u^{b−1} g` satisfies `|S_g(b)| ≤ ‖g‖₁ ∏ max(1, δ^{Re bᵢ−1})`, and `ℳ[φ](∑ b) S_g(b)` is a Schwartz function on vertical planes |
| `SimplexMellin.LogRatio` | Log-ratio coordinates `u(w) = e^{w̃}/∑e^{w̃}` relative to an index `i₀` and the change of variables `∫_Δ f = ∫ (∏ u(w)) f(u(w)) dw`, proved from the Mellin bridge at `b = 𝟙` and a shear of exponential coordinates |
| `SimplexMellin.Hyperplane` | On `∑ bᵢ = s`, `S_g(b) = ∫ e^{⟨b′,w⟩} Z(w)^{−s} g(u(w)) dw`; Laplace transforms of compactly supported functions are entire; **sufficiency**: every function of `b′` with Paley–Wiener bounds is the hyperplane restriction of `S_g` for a kernel continuous on and smooth near the simplex, vanishing near the faces (`exists_kernel_of_paleyWiener`); **necessity**: for smooth `g` vanishing near the faces the restriction has Paley–Wiener bounds for the box `|wⱼ| ≤ |log δ|` (`norm_integral_hyperplane_le`); **injectivity** on one hyperplane (`eqOn_of_integral_hyperplane_eq`) |
| `SimplexMellin.Image` | **Paley–Wiener description of the image** (`exists_kernel_iff`): `S` is `S_g` for a kernel smooth near the simplex and vanishing near its faces iff `S` is entire, satisfies the sum-shift equation `S(b) = ∑ᵢ S(b + eᵢ)`, the bound `‖S b‖ ≤ C ∏ max(1, δ^{Re bᵢ−1})`, and Paley–Wiener bounds on one hyperplane. Sufficiency uses Carlson's theorem on lines transversal to the hyperplanes `∑ b = s₀ − n`; `S_g` is entire (`differentiable_simplexMoment`) |
| `SimplexMellin.Lattice` | The transform `S_g(b) = ∫_Δ u^{b−1} g` of a continuous kernel is holomorphic on `Re b > 0`, bounded by `‖g‖₁` on `Re b ≥ 1`, and determined there by its values on `ℕ^ι + 𝟙` (the monomial moments), by Carlson's theorem in several variables (`simplexMoment_eqOn_of_moments_eq`). Nonnegative lattice data with the sum-shift equation, shifted by `𝟙`, have a unique continuation holomorphic on `Re b > −1` and bounded on `Re b ≥ 0`, given by the measure of the moment problem (`exists_continuation_of_satisfiesSumShift`, `eqOn_of_natCast_eq_of_bounded`) |
| `SimplexMellin.Estimate` | Quantitative continuation estimate: on compact parameter sets `‖T_b[g]‖ ≤ C·A` when the derivatives of `g` up to a fixed order are bounded by `A` on the simplex (`exists_norm_regDirichletContinuation_le`, `exists_norm_regDirichletTransform_le`), by bounding the explicit formula `regDirichletShiftFormula` |
| `SimplexMellin.Master` | A master theorem with simplex structure: for `Φ` the function of Ramanujan's master theorem (`ToMathlib.Analysis.SpecialFunctions.RamanujanMaster`), `Φ(∑x) g(x/∑x) = ∑ φ(k)(−∑x)^k g(x/∑x)` near the origin, and its several-variable Mellin transform is `π/sin(π∑b) · φ(−∑b) · ∏Γ(bᵢ) · T_b[g]` |

## Carlson functions modules

The scalar Gamma/Laplace integral is independent support in
`ToMathlib.Analysis.SpecialFunctions.Gamma`, under namespace `Complex`. Carlson's Laplace module
retains the R/S integral definitions and the inverse-confluence theorems, importing this
scalar API. The foundation uses only Mathlib, including its positive-real-rate evaluation.

### Hypergeometric means

`Carlson.Mean` re-exports the complex definitions and the positive-real inequality theory.
The order convention is `R_t = E[(∑ uᵢ xᵢ)^t]`, so the real mean is `R_t^(1/t)`
away from zero and `exp(E[log(∑ uᵢ xᵢ)])` at zero. Positive nodes and parameters
allow every real order, without restricting to the Euler integral's convergence strip.

| Module | Content |
| --- | --- |
| `Carlson.Mean.Basic` | Complex means, ratio means, power-transformed means, and their analytic continuation and branch hypotheses |
| `Carlson.Mean.Weights` | Complex derivative weights and removable limits at zero order or power |
| `Carlson.Mean.Real` | Real probability-integral definitions and agreement with the complex functions |
| `Carlson.Mean.Inequalities` | Weak and strict arithmetic-power, weighted-power, and logarithmic Jensen bounds |
| `Carlson.Mean.Order` | Monotonicity across the entire real order axis |
| `Carlson.Mean.Properties` | Normalization, homogeneity, strict node monotonicity, and bounds by node extrema |
| `Carlson.Mean.Euler` | Euler inversion and identification of order minus the total parameter with the geometric mean |
| `Carlson.Mean.StrictOrder` | Strict order monotonicity for nonconstant nodes and exact equality conditions for order, arithmetic, and geometric comparisons |
| `Carlson.Mean.Minkowski` | Minkowski and reverse Minkowski at all real orders, proportional-vector equality cases, and convexity or concavity in the nodes |
| `Carlson.Mean.LogConvex` | Convexity of log R in the order, strict for nonconstant nodes; equivalently convexity of order times log mean |
| `Carlson.Mean.Ratio` | Real ratio-mean normalization, homogeneity, and comparison with one |
| `Carlson.Mean.Holder` | Hölder for nonnegative orders, its reversal below minus the total parameter, the geometric endpoint identity, and exact equality cases |
| `Carlson.Mean.Dresher` | Beckenbach–Dresher for `0 < s ≤ 1 ≤ t`, `s < t`, including proportional-vector equality cases |
| `Carlson.Mean.Bounds` | All five strict chains in Carlson (1966), Theorem 2; exceptional values and refinements of the minima |
| `Carlson.Mean.ConcentrationZero` | Zero-concentration limits for complex R and L, and real weighted-power/geometric mean limits |
| `Carlson.Mean.Concentration` | Continuity in positive concentration and infinite-concentration limits for R, L, and every real-order mean |
| `Carlson.Mean.ConcentrationQuadratic` | Exact quadratic concentration formula, strict decrease, strict log-convexity, and negative derivative for arbitrary finite nonconstant real nodes |
| `Carlson.Mean.ConcentrationTwo` | Strict concentration monotonicity of two-node R and means in every real order range, including the logarithmic mean |
| `Carlson.Mean.OrderLimits` | Limits at positive and negative infinite order: maximum and minimum node |

The positive-parameter theory now covers the comparison, continuity, endpoint limits,
log-convexity, Euler inversion, Minkowski, Hölder, and Beckenbach–Dresher results of
Carlson (1965), together with the five bound chains of Carlson (1966), Theorem 2.
The zero-concentration results are limits; they do not redefine the original
functions at the singular parameter vector zero. All real orders are allowed.
Strict results require nonconstant nodes or nonproportional vectors as appropriate;
constant and singleton cases are retained in the weak inequalities and limits.

The new probability support is in `Dirichlet.Real.Support` (equivalent null sets
for positive Dirichlet laws and exact essential affine bounds) and
`Dirichlet.Real.Concentration` (coordinate deviation estimates and convergence of
Lipschitz or continuously differentiable simplex averages).

Carlson–Tobey (1968) is now partly formalized. For two distinct positive nodes and
positive, possibly unnormalized parameters, R strictly decreases in concentration
for `t < 0` and `t > 1`, and increases for `0 < t < 1`. The mean increases for
`t < 1` (including zero) and decreases for `t > 1`. These are finite-difference
monotonicity results; the paper's strict derivative signs are not yet formalized
except at quadratic order. At order two, arbitrary finite real node sets satisfy
`R₂(cw; x) = A² + V / (c + 1)` for positive normalized weights. Nonconstant nodes
give strict decrease, strict log-convexity, and a strictly negative derivative;
the mean consequence additionally assumes positive nodes.

The reusable support includes exact affine second moments in
`Dirichlet.Real.Variance`, beta-average conversion in `Dirichlet.Real.BetaAverage`,
a general two-crossing integral comparison, and strict convex comparison of beta
laws. The scalar Pochhammer ratio `(cw)ₙ / (c)ₙ` is also proved decreasing and
log-convex for `0 < w < 1`, strictly so for `n ≥ 2`.

Remaining Carlson–Tobey work includes arbitrary finite-node concentration
monotonicity, strict derivative signs beyond the quadratic case, log-convexity at
negative orders and integer orders above two, concavity for `0 < t < 1`, and
convexity for `1 < t < 2`. The paper only conjectures log-convexity for all real
orders greater than one. Carlson–Gustafson remains deferred.

### Chapter 7: Jacobi polynomials

`Carlson.Jacobi` is the umbrella for the polynomial core and the second-kind
results. Polynomial definitions use namespace `Polynomial`; the continued-average
coefficients, numerator bridges and second-kind functions use `Carlson.TwoVariable`.
The standard polynomial is `jacobi α β n`, and the shifted polynomial is
`shiftedJacobi α β n = Pₙ⁽α,β⁾(1 - 2X)`. The shifted weight is
`x^α (1-x)^β` on `[0,1]`.

| Module | Scope |
| --- | --- |
| `Jacobi.Basic` | Finite Pochhammer definitions over any commutative ℚ-algebra, coefficient formulas, degree bounds, endpoints, and transport between coefficient rings |
| `Jacobi.Derivative` | First and arbitrary iterated derivatives, without parameter restrictions |
| `Jacobi.Basis` | Exact degree and polynomial bases under explicit nonvanishing conditions; admissibility for real `α, β > -1` |
| `Jacobi.Carlson`, `Jacobi.Normalization` | All-complex-parameter numerator identification and the standard-to-monic normalization |
| `Jacobi.Endpoint`, `Jacobi.DifferentialEquation` | Endpoint derivative recurrence, polynomial uniqueness, and both standard and shifted Jacobi equations |
| `Jacobi.Weight`, `Jacobi.RealOrthogonality` | Integrability, endpoint control, the weighted Wronskian argument, and orthogonality throughout the real range `α, β > -1` |
| `Jacobi.Expansion` | The real specialization of the algebraic finite expansion, with agreement of integral and algebraic beta averages; the coefficient of index `m` is the integral of the `m`th derivative against the weight with parameters `α+m, β+m`, divided by the weight's mass and the Jacobi normalization factor; orthogonality to all lower-degree polynomials |
| `Jacobi.Raising`, `Jacobi.AnalyticRodrigues` | Parameter-unrestricted polynomial raising identity and analytic Rodrigues formula for arbitrary real exponents on `(0,1)` |
| `Jacobi.WeightedIntegral` | Repeated weighted integration by parts for continuous derivative towers and `Cⁿ` functions on `[0,1]`, with a polynomial specialization; specialized from `Jacobi.ComplexOrthogonality` |
| `Jacobi.Norm` | Squared Jacobi norms in beta function form, strict positivity, agreement of derivative-average and orthogonal projection coefficients, and the shifted Legendre norm by specialization |
| `Jacobi.Rodrigues`, `Jacobi.Orthogonality` | Polynomial Rodrigues identity for nonnegative integer parameters, repeated polynomial integration by parts, and integer-weight specializations of the general orthogonality theorem |
| `Jacobi.Legendre`, `Jacobi.Chebyshev` | Identifications with Mathlib's shifted Legendre and Chebyshev `T` and `U` polynomials |
| `Jacobi.Gegenbauer` | A finite definition valid at every parameter, the denominator-free symmetric-Jacobi relation, Legendre and Chebyshev `U` specializations, and real weighted orthogonality |
| `Jacobi.GegenbauerDerivative` | Derivatives of every order derived from Jacobi derivatives, extended to all complex parameters by analytic continuation |

The definitions remain valid when the expected degree drops. Assertions of exact
degree, monicity, and a polynomial basis impose the corresponding nonvanishing
hypotheses. In particular, a Gamma-product evaluation at a parameter pole is not
used to define Jacobi polynomials. The Gegenbauer definition also retains the
exceptional parameters where dividing by `(ρ+1/2)ₙ` would be invalid.

`Carlson.PolynomialAverage` supplies a linear functional on complex polynomials
whose moments are the regularized Carlson R-polynomials. It is the unique entire
parameter continuation of the native average and commutes with affine substitutions.

| Module | Further Chapter 7 scope |
| --- | --- |
| `Jacobi.BetaAverage` | Algebraic beta moments and their Pearson identity over a field; vanishing Jacobi means at admissible parameters |
| `Jacobi.AlgebraicExpansion` | Derivative-average coefficient functionals and finite expansions over any characteristic-zero field |
| `Jacobi.ComplexAverage` | Identification of the algebraic beta functional with the continued complex Carlson polynomial average |
| `Jacobi.Endpoints` | Monic Jacobi polynomials and bases at arbitrary endpoints; coincident endpoints give Taylor monomials |
| `Jacobi.EndpointBridge` | Identification of the endpoint polynomials with Carlson's two-node numerator quotient |
| `Jacobi.FiniteExpansion` | Theorem 7.2-2 for arbitrary complex endpoints and complex parameters with `α+β+2` away from nonpositive integers; duality of the coefficient functionals |
| `Jacobi.SecondKind` | Adjoint second-kind functions off the endpoint segment, joint analytic dependence, native integral agreement, the coincident-endpoint Cauchy kernel, contour coefficient extraction and biorthogonality on enclosing circles |
| `Jacobi.Contour` | Polynomial coefficient extraction and biorthogonality on arbitrary `C¹` cycles avoiding the segment, weighted by the index; contour independence for holomorphic functions under the homology condition |
| `Jacobi.SeriesCoefficients` | Uniform bounds and continuity of contour coefficient functionals; coefficient recovery and uniqueness for Jacobi series uniformly convergent on a cycle of nonzero index |
| `Jacobi.Pearson` | Pearson's relation for continued two-node averages, with arbitrary complex parameters and coincident endpoints |
| `Jacobi.SecondKindEquation` | Three consecutive resolvent orders, parameter-shift differentiation, and the adjoint Jacobi differential equation off the endpoint segment |
| `Jacobi.SecondKindInfinity` | Affine covariance, the analytic reciprocal chart, and normalization at infinity in every complex direction |
| `Jacobi.SecondKindIntegral` | Euler and weighted Jacobi Cauchy representations off the entire unit segment, for real parameters greater than `-1`; specialized from `Jacobi.ComplexSecondKind` |
| `Jacobi.BoundaryKernel` | Compatibility import of the general Cauchy boundary theory in `ToMathlib.Analysis.Integral.CauchyBoundary` |
| `Jacobi.SecondKindBoundary` | Jacobi boundary jumps at interior points of the unit segment and their transport to distinct complex endpoints, specialized from `Jacobi.ComplexSecondKind` |
| `Jacobi.SecondKindPlemelj` | Separate upper and lower limits for `re α, re β > -1`, the normalized principal value as a symmetric-truncation limit, and affine transport to distinct complex endpoints |
| `Jacobi.ComplexRodrigues` | Principal complex weights and Rodrigues' formula at all complex parameters; agreement with the real weight and polynomials at real parameters |
| `Jacobi.ComplexOrthogonality` | Complex derivative-tower integrals, bilinear orthogonality and squared integrals for `re α, re β > -1` |
| `Jacobi.ComplexSecondKind` | Euler representations at arbitrary endpoints under degree-shifted positivity; weighted Cauchy representations for `re α, re β > -1`, and symmetric jumps on nondegenerate complex segments |
| `Jacobi.SecondKindBounds` | Degree-dependent bounds from shifted Euler weights, including estimates that retain the combined weight-resolvent factor |
| `Jacobi.SecondKindRayBounds` | Elliptic-rate upper bounds and absolute convergence on exterior focal rays at arbitrary complex parameters, transported by invertible complex affine maps |
| `Jacobi.SaddleGeometry` | Compatible endpoint square roots, the fractional linear saddle curve, its elliptic norm bound, and principal-branch membership; the deformation itself is in `Jacobi.SecondKindSaddle` |
| `Jacobi.SaddleLaplace` | Explicit centered phase and tail estimates; Gaussian limits for the actual Möbius integral; pointwise second-kind asymptotics with a nonzero degree-independent coefficient for all complex parameters, including coincident endpoints |
| `Jacobi.SaddleUniform` | Joint analytic amplitude, common derivative and Gaussian bounds on compact sets; compact-uniform relative second-kind asymptotics for arbitrary complex parameters and fixed endpoints, including coincident endpoints, with the degree shift removed |
| `Jacobi.SaddleJoint` | Joint endpoint Gaussian and relative limits; Theorem 7.4-3 in Carlson's R-average notation, uniformly on compact subsets of `W`, for all complex parameters, including the diagonal |
| `Jacobi.PolynomialSaddle` | Exact Chebyshev two-saddle formula (7.4-1), including cancellation points; difference-based equivalent and compact-uniform dominant-term relative convergence on `W`, with exact error `‖(x-y)/(x+y)‖^(2n)` |
| `Jacobi.AsymptoticZeros` | Odd-degree Chebyshev midpoint zeros and their Carlson numerator form; counterexample to the literal unextended ratio interpretation of Theorem 7.4-2 at `(1,I)`, with nonsingular polynomial normalization |
| `Jacobi.SecondKindSeries` | Absolute and locally uniform convergence, and holomorphy of second-kind series with geometrically bounded coefficients on a sufficient distance-based region |
| `Jacobi.PolynomialBounds` | Explicit large-degree bounds from the Carlson numerator, and geometric bounds uniform on compact sets, with arbitrary complex parameters and endpoints |
| `Jacobi.KernelSeries` | Summable majorants and uniform convergence for polynomial–second-kind products on sufficiently separated sets |
| `Jacobi.CauchyKernel` | Cauchy-kernel coefficient identity; kernel expansion for sufficiently distant poles, uniformly on compact products; exact circular case; identity-principle extension under local uniform convergence, subsequently supplied by `Jacobi.EllipticExpansion` |
| `Jacobi.EllipseCoordinates` | Branch-independent square-root formula, characteristic roots and their strict exterior dominance, Joukowski coordinates, and preconnected elliptic exteriors |
| `Jacobi.AnalyticExpansion` | Passage from polynomial approximation to Jacobi expansions; sufficient disk criteria; absolute and locally uniform convergence to every entire function, using any fixed index-one cycle off the segment |
| `Jacobi.Ellipse` | Confocal mean-radius geometry, convex open disks, compact closed disks, affine covariance and elliptic neighborhoods of the focal segment |
| `Jacobi.Recurrence` | Denominator-free three-term recurrence for shifted Jacobi polynomials and Carlson's monic recurrence (Exercise 7.1-6) with coefficients `V n`, `W n` |
| `Jacobi.PolynomialGrowth` | Perturbed constant-coefficient recurrences; `‖pₙ(x)‖ ≤ C (ρ + ε)ⁿ` on closed elliptic disks via the maximum modulus principle |
| `Jacobi.SecondKindSaddle` | Deformation of the Euler integral onto the saddle curve by a real Möbius substitution and the identity theorem; `‖qₙ(y)‖ ≤ C (1/σ + ε)ⁿ` on closed elliptic exteriors |
| `Jacobi.EllipseContour` | Confocal ellipses as `C¹` cycles (Joukowski images of circles) and their winding numbers |
| `Jacobi.EllipticExpansion` | Lemma 7.6-1 on `μ(x) < μ(y)` and Theorem 7.6-2 on open elliptic disks, with uniform convergence on closed subdisks |
| `Jacobi.GrowthLimits` | Lower bounds by analytic continuation and recurrence dichotomies; Theorem 7.5-1 for `pₙ`, Theorem 7.5-3, uniqueness and the maximal ellipse of convergence |
| `Jacobi.SecondKindLimits` | The second-kind recurrence (for large degrees, and at every degree when `α + β + 1` is regular), the Casoratian (Exercise 7.1-11) and Christoffel's second summation formula (Exercise 7.1-7), Theorem 7.5-1 for `qₙ`, and divergence of second-kind series inside the critical ellipse |
| `Jacobi.SecondKindJump` | The jump (7.8-5) of `qₙ` across the segment for all complex parameters, via Carlson's Theorem 8 on rotated slit planes, and Carlson's deduction of orthogonality from biorthogonality |
| `Jacobi.GrowthMaxima` | The maxima `p̂ₙ(ρ)`, `q̂ₙ(σ)` on confocal ellipses and their root limits (Theorem 7.5-2) |
| `Jacobi.PlaneWave` | The plane-wave expansion of Example 7.7-1 with Carlson `S`-function coefficients |
| `Jacobi.EllipseCoefficient` | The coefficient formula (7.6-8) on confocal ellipses, as a continued Dirichlet average of `f⁽ⁿ⁾` |
| `Jacobi.FourierCosine` | The Fourier cosine expansion of Example 7.7-2, equation (5) |
| `Jacobi.Bessel` | Bessel applications of Section 7.7: the spherical-Bessel plane wave (7.7-1 (3)), the cosine coefficients (7.7-2 (6)), and the Jacobi–Anger expansions and Bessel generating functions (7.7-3 (7)–(10), with `Jₘ` and `Iₘ`), using Mathlib's `Complex.besselJ` |
| `Jacobi.SegmentOrthogonality` | Carlson's segment integral at arbitrary distinct complex endpoints; Representation 7.8-2 and Theorem 7.8-3 |
| `Jacobi.EndpointRodrigues` | Rodrigues' formula (7.8-1) at arbitrary complex endpoints on the principal branch |
| `Jacobi.Laguerre`, `Jacobi.LaguerreRepresentation` | Monic Laguerre polynomials: the Jacobi limit (Theorem 7.9-1), Rodrigues' formula (7.9-8), the weighted representation (Theorem 7.9-3) and orthogonality (Theorem 7.9-4) |
| `Jacobi.HermiteSecondKind` | The Hermite function of the second kind (Definition 7.10-2) as the limit (7.10-3), via rotation, the first quadratic transformation, and a shifted confluence limit |
| `Jacobi.GegenbauerAddition` | Formula (7.3-7), Gegenbauer's addition theorem 7.3-1, its Jacobi form, `P_n^{-k}` with the reflection (6.10-19), and both forms of the Legendre addition theorem (7.3-11) |
| `Jacobi.ChebyshevSecondKind` | Lemma 7.4-1: `R_{-n-1}(1/2+n, 1/2+n; x², y²) = (xy)⁻¹((x+y)/2)^{-2n}` on `re (x ȳ) > 0`, by the second quadratic transformation and the identity theorem |
| `Jacobi.LaguerreSecondKind` | The Laguerre function of the second kind `q̃ₙ` (Definition 7.9-2) as the limit (7.9-4), and Theorem 7.9-5 with its converse, from the connection formula (5.12-18) |
| `Jacobi.Hermite`, `Jacobi.HermiteRepresentation` | Monic Hermite polynomials: the Jacobi limit (Theorem 7.10-1), Rodrigues' formula (7.10-6), the weighted representation (Theorem 7.10-3) and orthogonality (Theorem 7.10-4), transported from TauCeti's Gaussian orthogonality of `Polynomial.hermite` by the scaling `2^{n/2} p̃ₙ(x) = Heₙ(√2 x)` |

The finite complex theorem includes coincident endpoints and recovers Taylor's
formula there. Its parameter restriction concerns the total `α+β+2`, not the real
parts of the individual parameters. The old real integral expansion is now derived
from the algebraic expansion after identifying the two coefficient functionals.

The second-kind functions use the continued integer resolvent, so their domain is
the complement of the segment, without an additional principal-logarithm cut.
The ordinary Gamma normalization is analytic away from its total-parameter poles.
No removable interpretation is assigned to totalized values at those poles.
The differentiation rule and adjoint differential equation also hold for these
totalized values. Their proof uses `Dirichlet.Average.ResolventDeriv` to extend
resolvent differentiation to all complex parameters, followed by the continued
Pearson relation; no distinctness assumption on the endpoints is needed.

The contour extension uses the existing homology form of Cauchy's theorem.
On any `C¹` cycle avoiding the endpoint segment, the normalized integral of a
polynomial against `qₙ` equals its Jacobi coefficient times the cycle's index
about either endpoint. Biorthogonality follows by specializing to `pₘ`.
For a function holomorphic on an open domain, contour integrals agree when the
cycles' indices agree outside that domain and at an endpoint, provided both
cycles lie in the domain and avoid the segment. This includes noncircular
contours, reversed orientations, multiple windings and coincident endpoints;
it does not construct branches along contours crossing the segment.

The contour coefficient functional is bounded for the uniform norm on each
fixed cycle. Uniform convergence of Jacobi partial sums there therefore permits
coefficient extraction. If the cycle has nonzero index, two series with the same
uniform limit have identical coefficients. This proves conditional uniqueness
without assuming absolute convergence. The existence results below use summable
majorants to establish convergence independently.

The real §7.8 results include nonintegral Rodrigues formulas and weighted
coefficient integrals for `Cⁿ` functions, using derivatives within the closed
interval. Squared norms are expressed as a Pochhammer factor times a beta
function, including degree zero when `α+β=-1`; this form avoids a removable
singularity in a common Gamma quotient. The shifted Legendre norm `1/(2n+1)`
is derived from the Jacobi formula.

The complex Rodrigues formula uses `z^α (1-z)^β` where both bases lie in the
principal slit plane, with no parameter restriction. On the unit interval,
`re α, re β > -1` suffices for derivative-tower integration by parts, bilinear
orthogonality and the squared-integral evaluation. These complex integrals involve
no conjugation and are not assertions about positive Hermitian norms.

`Dirichlet.Average.ResolventInfinity` proves affine covariance and the leading
coefficient at infinity for the continued regularized resolvent, for every finite
index type and all complex parameters. Specialization gives `x^(n+1) qₙ(x) → 1`
when `α+β+2n+2` is Gamma-regular; this needs no distinctness condition on endpoints.
For complex `re α, re β > -1`, the second-kind function is the Cauchy transform of
`(-1)^n / B(α+n+1, β+n+1)` times the shifted Jacobi weight and polynomial.
The upper-minus-lower difference tends to `-2πi` times that density on the unit
segment. Affine covariance gives the corresponding perpendicular jump across
any nondegenerate complex segment. `Jacobi.SecondKindPlemelj` also proves the
separate perpendicular limits: the principal value minus or plus `πi` times
the normalized density. On the unit segment, the principal value is the limit
of symmetric real-axis truncations. The general support theorem requires an
integrable density and an integrable regularized difference quotient;
differentiability at the interior point supplies the latter condition for the
Jacobi density, while allowing its integrable endpoint singularities.

The elliptic mean radius has minimum `‖r-s‖/4`, attained exactly on the focal
segment. Its open disks above that radius are convex; its closed disks are compact.
Joukowski coordinates describe connected elliptic exteriors, and confocal ellipses
are `C¹` cycles of index one. Affine covariance includes zero scales; coincident
endpoints recover circular disks.

The preliminary distance-to-segment and exterior-ray bounds are strengthened to
sharp bounds on closed elliptic disks and exteriors. `Jacobi.SaddleGeometry` constructs
the fractional linear curve `u=bt/(a(1-t)+bt)` for compatible square roots
`a²=z-r`, `b²=z-s`; `Jacobi.SecondKindSaddle` proves the Euler integral deformation
and the resulting exponential upper bound. `Jacobi.PolynomialGrowth` derives the
polynomial upper bound from the recurrence. `Jacobi.GrowthLimits` and
`Jacobi.SecondKindLimits` prove matching pointwise root limits off the segment,
using the Cauchy kernel and perturbed recurrences. `Jacobi.GrowthMaxima` proves
the root limits for maxima on confocal ellipses.

`Jacobi.EllipticExpansion` proves `∑ pₙ(x) qₙ(y) = (y-x)⁻¹` on the full domain
`μ(x) < μ(y)`, uniformly on a closed elliptic disk times a larger closed exterior.
Integrating the kernel expansion gives Theorem 7.6-2 on open elliptic disks, with
absolute convergence, uniform convergence on closed subdisks, contour independence
and uniqueness. The coefficient is also the continued average of the nth derivative
(7.6-8). Entire functions have expansions throughout the plane. The general theory
allows complex endpoints and parameters with `α+β+2` away from nonpositive integers;
coincident endpoints give Taylor series.

Gegenbauer and Legendre polynomial addition theorems and the Bessel expansions of
Examples 7.7-1 through 7.7-3 are proved. Laguerre and Hermite polynomials and their
second-kind functions are obtained as confluent limits; the Laguerre second-kind
limit assumes `re(1+β+n) > 0`. Their weighted coefficient representations require
growth control also on the nth derivative.

`ToMathlib.Analysis.Integral.Laplace` supplies the quantitative Gaussian estimate.
`Jacobi.SaddleLaplace` applies it after centering the Möbius curve at `t = 1/2`.
For `w = ((c-1)/(c+1))²`, with `c = jacobiSaddleRatio r s z`, the normalized kernel
is `(1-u²)/(1-wu²)` and `‖w‖ < 1`. Its logarithmic phase coefficient differs from
`1-w` by at most `2u²` on `|u| ≤ 1/2`. The outer pieces have the explicit bound
`‖A‖₁ (1-(1-‖w‖)δ²)ⁿ`. Differentiability of the actual amplitude at zero supplies
the local variation bound; a fixed degree shift makes it integrable at both endpoints.

The full Möbius integral therefore has a nonzero Gaussian leading constant.
Comparison with the reference beta integral cancels the Gamma normalization and
proves `qₙ(z) ∼ C (4/Λ(z))ⁿ`, where `C ≠ 0` and
`Λ(z) = (z-r)(1+c)²`. The theorem `exists_isEquivalent_jacobiSecondKind_geometric`
has no restrictions on the complex Jacobi parameters, only that `z` is outside
the endpoint segment. Coincident endpoints are included. `norm_jacobiSaddleScale`
identifies `‖Λ(z)‖ = 4μ(z)`.

`Jacobi.SaddleUniform` proves the relative limit uniformly on every compact set
outside the fixed focal segment. Joint analyticity of the centered amplitude
supplies a common derivative bound. Compactness keeps the shape strictly inside
the unit disk, and gives common amplitude and tail bounds. The beta comparison
preserves uniformity; removing the fixed degree shift gives
`exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric`, with a single nonzero
coefficient function for all compact exterior sets. This proves the second-kind
part of Corollary 7.4-4.

`Jacobi.SaddleJoint` extends the amplitude and its derivative jointly in both
endpoints. The uniform Gaussian and relative limits then hold for compact
families of endpoint pairs whose segments avoid the origin. For endpoints
`-x²,-y²` on Carlson's `W`, the saddle ratio is `y/x` and the scale is `(x+y)²`.
The theorem `exists_tendstoUniformlyOn_carlsonR_secondKind_div` is Theorem 7.4-3:
one nonzero coefficient function gives relative convergence uniformly on every
compact subset of `W`, for arbitrary complex parameters. Coincident arguments
are included. A fixed degree threshold identifies the continued function with
Carlson's ordinary Dirichlet average; no condition on the initial degrees is needed.

`Jacobi.AsymptoticZeros` checks an issue in Theorem 7.4-2's printed definition of
relative asymptotics. At `α = β = -1/2` and `(x,y) = (1,I)`, the polynomial is
zero in every odd degree, while its Pochhammer normalization is nonzero at every
degree. No unextended quotient by any sequence tends to one there. This does
not disprove a version with removable extensions or an additive error controlled
by the magnitudes of the two saddle contributions.

`Jacobi.PolynomialSaddle` proves the exact Chebyshev formula (7.4-1) for all
complex argument pairs in positive degree. It gives a difference-based asymptotic
equivalent even where the sum vanishes. On `W` the dominant-term relative error
is exactly `‖(x-y)/(x+y)‖^(2n)`, and tends to zero uniformly on compact sets.

Remaining work includes the general-parameter polynomial asymptotics of §7.4
with a formulation accounting for zeros, the compact-uniform root limits
asserted in 7.5-1, Bessel addition
Example 7.7-4, and boundary theory beyond `re α, re β > -1`. Continuation of the
boundary formulas to all admissible parameters, endpoint regularization, and
branches for contours crossing the segment remain open.
The physical examples in §§7.9–7.10 and many exercises are not formalized.
[CarlsonCoverage.md](CarlsonCoverage.md) records the section-level inventory.

### R-function analytic construction

`Carlson.R.SingleIntegral` is an umbrella over four steps:

1. `SingleIntegral.Series`: unit-interval definition and near-one series.
2. `SingleIntegral.Analytic`: joint analyticity in endpoint exponents, parameters, and nodes.
3. `SingleIntegral.UnitInterval`: node analyticity as a specialization, and native representation.
4. `SingleIntegral.PositiveRay`: positive-ray substitution and representations.

`Carlson.R.SingleIntegralAnalytic` retains the original import path for joint analyticity.

The unit-interval representation at arbitrary Dirichlet parameters is a theorem of
`R.Explicit`; ray-kernel arguments use `PositiveRay`. The contour formula (6.8-7) on `C¹`
cycles is proved in `R.ContourRepresentation`.

The slit-domain API separates `SlitRelations` (parameter-shift identities),
`SlitDeriv` (node derivatives and differential identities), and
`EulerPoisson` (the second-order system).
`AssociatedExercises` adds Zill's relation and Carlson's Exercises 5.9-7 to 5.9-9, and
`TwoVariable.R.Elementary` the two-variable Exercises 5.9-10 and 5.9-13
(`R_t(1, 0; x, y) = x^t`, `(x - y) R_{-1}(1, 1; x, y) = log x - log y`).

The R-function has one definition. `R.Explicit` defines `regCarlsonR t b z` for all
complex exponents and parameters by a finite recursion in the style of `Complex.Gamma`:
in the strip `re t < 0 < re (∑ b + t)` it is the doubly Gamma-regularized Euler integral
on the product slit plane, and outside the strip it is reached by the two denominator-free
associated relations, one raising the total parameter and one lowering the exponent.
Independence of the recursion depth and joint analyticity in all variables are proved by
the identity theorem in the joint variables, packaged as functions on `Option (ι ⊕ ι)`.
The same file proves the three associated relations on the whole domain, agreement with
the native integral `regCarlsonRIntegral` for convergent parameters and right-half-plane
nodes at every exponent, and the characterization of `regCarlsonR` as the unique entire
continuation in the parameters (`Carlson.R.Continuation` keeps the predicate). The native
integral plays the role of `Complex.GammaIntegral`: theorems about it are stepping stones,
transported to `regCarlsonR` by continuation in the parameters and then in the nodes.
The L-function likewise has one definition: `L.Continuation` defines `regCarlsonL` as
the exponent derivative of `regCarlsonR`, proves its joint holomorphy, and identifies it
with the native power-logarithm average `regCarlsonLIntegral` on the convergence domain.
`L.Relations` derives the associated L-relations on the whole domain by differentiating
the R-relations.
`R.SlitIntegral` and `L.SlitIntegral` prove native-integral agreement when the whole node
convex hull stays in the slit plane; individual slit-plane nodes alone are insufficient.
`R.SlitIntegral` also specializes the continued circle representation to R. Ordinary
normalization still uses the total-parameter Gamma factor; Lean's totalized values at
Gamma poles are not assertions of finite ordinary-function values.

`Dirichlet.GammaPoles` (formerly `Carlson.Normalization.Basic` and part of
`Normalization.EqualParameter`) proves the scalar Gamma pole factorization, residue,
one-variable removability criterion, and finite removable limit. It also supplies
a joint analytic pole numerator, a sufficient joint removal criterion from
local divisibility by the exceptional total-parameter factor, and the Hartogs-based removal
`Complex.analyticOnNhd_GammaRemovedValue`.
`Carlson.Normalization` applies these results uniformly to R, L, S, native T, and
principal slit-plane T. It proves ordinary joint holomorphy away from Gamma poles
and meromorphy under analytic one-variable substitutions. At total parameter
`-m`, a transverse parameter line has residue `(-1)^m / m!` times the regularized
value. Vanishing of that value characterizes removability of the transverse slice;
it does not by itself establish removability along the whole parameter hypersurface.

### Recurrences and associated dependence

| Module | Responsibility |
| --- | --- |
| `ToMathlib.Algebra.Submodule.Saturation` | Saturated submodules and the saturation closure operator |
| `ToMathlib.Algebra.Submodule.SaturationLocalization` | Identification with the inverse image of a localized submodule |
| `ToMathlib.Algebra.LinearDependence` | Independence bounds and dependence in saturated finite spans; no Carlson or Dirichlet imports |
| `Carlson.Associated.Shift` | Shift indices and rational-coefficient data |
| `Carlson.R.Recurrence.Coefficients` | Symmetric-polynomial recurrence coefficients, independently of R-functions |
| `Carlson.R.AssociatedRecurrence` | Native homogeneity recurrence |
| `Carlson.R.Associated.ExponentReduction` | Polynomial and rational reduction to a finite exponent window |
| `Carlson.R.SlitRecurrence` | Transport of polynomial relations to slit nodes; the homogeneity recurrence for all parameters and slit nodes |
| `Carlson.R.AssociatedDependence` | Parameter reduction and the fixed-parameter dependence theorem, on the slit domain |
| `Carlson.R.Recurrence.JointCoefficients` | Joint parameter/node coefficient polynomials and formal derivatives |
| `Carlson.R.JointRecurrence` | Universal R homogeneity identity using those polynomials |

The joint coefficient construction does not depend on the fixed-parameter
existential dependence theorem. This leaves a clean base for the still-open
extension of arbitrary associated-shift dependence to joint polynomial
coefficients, and hence for differentiating such identities to obtain
L-relations. Reorganization itself does not establish that extension.

Scalar Gamma-regularity and reciprocal-Gamma estimates live in
`Pochhammer.Gamma`.

### Two-variable and S-function theory

`Carlson.TwoVariable.Basic` contains only the two-coordinate and swap API.
Function abbreviations have their own `R.Basic`, `RPolynomial.Basic`, and
`S.Basic` modules.

The two-variable associated and inversion identities have parallel
`R.Associated` / `L.Associated` and `R.Inversion` / `L.Inversion` modules.
The L modules depend on the R modules, not conversely.
`TwoVariable.Associated` and `TwoVariable.Inversion` re-export both sides.

`TwoVariable.Quadratic` re-exports `Quadratic.Geometry`,
`Quadratic.Polynomial`, and `Quadratic.Integral`. Parameter continuation,
the finer equal-parameter normalization, and the exponent-derivative calculus with moving
Dirichlet parameters are in `QuadraticContinuation`, `EqualParameterSlit`, and `LQuadratic`.
`QuadraticSlit` extends the raw regularized R identities to all square-root
variables with positive real parts, without requiring their squared or
mean-square nodes to have positive real parts. `EqualParameterSlit` defines the finer
equal-parameter normalization `regEqualR` without proof arguments, jointly holomorphic on
slit-plane nodes, identifies it with the native integral, and extends the finer R and L quadratic
identities to the same domain. The former proof-dependent half-plane construction
(`TwoVariable.EqualParameter`) has been retired.

`Carlson.S` re-exports `S.Basic`, `S.Series`, `S.Analytic`, `S.Continuation`,
`S.Deriv`, and `S.Properties`: native definitions, series continuation, joint
analysis, named ordinary and regularized functions, continued node derivatives,
and functional identities. `S.Continuation` exposes `regCarlsonS b z` as the
existing entire series with the same argument order as the other families,
and defines its ordinary Gamma normalization `carlsonS b z`.

### T-function continuation

`Carlson.T` re-exports `Basic`, `Slit` (which imports `SlitSeries`), `TwoF0`, `TwoF0Sector`, `TwoF0Connection`, and `ZeroNode`:

| Module | Responsibility |
| --- | --- |
| `Carlson.T.Basic` | Native integrals, the zero-avoiding convex-hull node domain, and named joint continuations `regCarlsonT` and `carlsonT` |
| `Carlson.T.SlitSeries` | Cauchy bounds for negative integral R-functions, locally uniform convergence of their reciprocal-factorial series, and joint holomorphy of `regCarlsonTSlit` |
| `Carlson.T.Slit` | Agreement with native integrals, compatibility of the two regularized branches, and ordinary `carlsonTSlit` |
| `Carlson.T.TwoF0` | Carlson's `₂F₀` (Section 5.12): Euler double and single integrals, continuation through the remainder representation (5.12-10), symmetry, holomorphy (5.12-4), and the error bound and asymptotic expansion in `re x ≤ 0` |
| `Carlson.T.TwoF0Sector` | Continuation of `₂F₀` to the sector `|ph(-x)| < 3π/2` (5.12-6) via rotated Euler rays, with the error bounds (5.12-15), (5.12-16) and asymptotic expansion (5.12-17) on the sector |
| `Carlson.T.TwoF0Connection` | The single integral (5.12-7) for `|ph(-x)| < π` and the connection formulas (5.12-18), (5.12-20) (Theorems 5.12-8, 5.12-9) |
| `Carlson.T.ZeroNode` | The zero-node limit (5.12-2) of the two-variable T-function and formula (5.12-3), also in terms of `₂F₀` |

The native T node domain is `0 ∉ convexHull ℝ (range z)`. The principal T-series
is defined on all tuples of slit-plane nodes, including tuples outside that native
domain. Compatibility is proved when the **whole convex hull** lies in the slit
plane; membership of each node in the slit plane alone is not the compatibility
hypothesis. Both regularized continuations are entire in all Dirichlet parameters
and jointly holomorphic with the nodes on their respective domains. The empty
index type is included, with both continuations equal to zero.

### Further Chapter 5 and 6 results

| Module | Responsibility |
| --- | --- |
| `Dirichlet.Average.Intertwining` | The operator identity (5.3-4) for every power |
| `Dirichlet.Average.RealNodes` | Case (i) of 5.3-2 and 5.4-1: real nodes, `f ∈ Cⁿ` on an open interval; `Cⁿ` regularity of the average, iterated partial derivatives under the integral, (5.3-3), (5.3-4), the tangential relation and the Euler–Poisson system for `f ∈ C²` |
| `Dirichlet.Average.CauchyCycle` | Cauchy's formula for derivatives on `C¹` cycles, Representation 5.11-2 on cycles, and the contour form of 6.3-6 |
| `Carlson.R.Homogeneity` | Homogeneity (5.9-3) on the slit node domain under the principal branch condition |
| `Carlson.R.Confluence` | Confluence (5.10-1) with complex exponent tending to infinity, and the refinement (5.10-9) |
| `Carlson.R.ContourRepresentation` | Formula (6.8-7) on `C¹` cycles, for all complex parameters |
| `Carlson.RPolynomial.Concentration` | The concentration limits of Theorem 6.2-5 |
| `Carlson.Normalization.EqualParameter` | Equal parameters: removable Gamma singularities of `Γ(β) F/Γ(kβ)` (Theorems 6.2-6, 6.8-4, Corollary 6.3-7), by one-variable pole removal and Hartogs' theorem |
| `Carlson.RPolynomial.Appell` | Theorem 6.4-1 restated: for fixed parameters the R-polynomials satisfy the binomial theorem, are in Carlson's class `A_k` (`ToMathlib.Analysis.AppellSequence`), and satisfy (6.4-4); also in Carlson's normalization `Nₙ/(∑b)ₙ` |
| `Carlson.Jacobi.RPolynomialExercises` | Chapter 7 R-polynomial exercises: 7.1-1, Bateman's relation 7.1-2, 7.1-5, 7.1-9, 7.2-2, 7.8-5 |
| `Carlson.Jacobi.ChebyshevU` | The `U`-type Chebyshev cases of Exercise 7.4-1 |
| `Carlson.Jacobi.SeriesExercises` | Jacobi and Gegenbauer series of particular functions (Exercises 7.6-2, 7.7-14, 7.7-15) |
| `Carlson.Jacobi.LaguerreExercises` | Standard Laguerre polynomials and Exercises 7.9-1, 7.9-2, 7.9-5, 7.9-6, 7.9-8 |
| `Carlson.Jacobi.HermiteExercises` | Carlson's Hermite polynomials `Hₙ` and Exercises 7.10-1, 7.10-2, 7.10-4 – 7.10-6 |
| `Carlson.Jacobi.GegenbauerRecurrence` | The three-term recurrence of Gegenbauer polynomials for all complex parameters, and the Christoffel–Darboux formula (Exercise 6.7-5) |
| `Carlson.Jacobi.GegenbauerExercises` | Gegenbauer, Chebyshev and Legendre exercises: 6.7-1, 6.7-3, 6.7-4, 6.7-7 – 6.7-12, 6.9-9 – 6.9-11, 6.10-7 – 6.10-12 (Fibonacci part of 6.10-9), 7.1-12, 7.2-1, Unsöld's theorem 7.3-1, 7.3-2, the Rodrigues formulas 7.8-1 |
| `Carlson.Jacobi.BesselExercises` | Bessel exercises: Sonine's formula 7.7-1, Neumann's series 7.7-2, Bessel's integral 7.7-3, Gegenbauer's addition theorem (Example 7.7-4), 7.7-5 – 7.7-7, 7.8-7, 7.1-10, the Gegenbauer–Bessel limits 6.7-13 and the `(x⁻¹ d/dx)ⁿ` formulas of 6.9-20 |
| `Carlson.Jacobi.Appell` | Carlson (1970), Example 11: `jacobiOn (α - n) (β - n) r s n` is an Appell sequence when `α + β ∉ ℕ` |
| `Carlson.RPolynomial.NumeratorBinomial` | Theorem 6.4-1 for Pochhammer numerators, without parameter exclusions |
| `Carlson.RPolynomial.GeneratingIdentities` | Chapter 6 exercises from the generating relation 6.6-1: juxtaposition and addition of parameters (6.2-2, 6.6-6, 6.6-7), squared nodes (6.6-8), a raised parameter (6.6-12), Tobey's relation (6.6-13), degree two (6.2-13) |
| `Carlson.TwoVariable.RPolynomial.Hypergeometric` | Two-variable R-polynomials as terminating `₂F₁` (Mathlib's `ordinaryHypergeometric`): Exercises 6.2-1, 6.2-4, 6.2-5, 6.4-1, the six forms 6.5-2, 6.5-3 and the generating relation 6.6-10 |
| `Carlson.TwoVariable.R.ElementaryValues` | Elementary values of R-functions from the Chapter 6 exercises: (6.6-5), 6.3-2, 6.6-16, 6.8-5 – 6.8-7, the inverse trigonometric and hyperbolic functions as `R_C` (6.9-16), and trigonometric `R_C` values (6.9-17) |
| `Carlson.TwoVariable.RPolynomial.SpecialValues` | Special values of `Rₙ(β, 1 - 2β - n; 2, 1)` and of terminating `₂F₁` at `2`, `-1`, `½` (Exercise 6.9-2); the expansion of `Rₙ(β, β; x + y, x - y)` (6.9-6) |
| `Carlson.TwoVariable.RPolynomial.QuadraticGenerating` | The expansion of `(at² + 2bt + c)^(-ν)` in R-polynomials near `t = 0` (Exercise 6.6-4) and its second quadratic transform (6.10-6) |
| `Carlson.RPolynomial.RootsOfUnity` | Roots of unity as nodes (Exercise 6.9-13) and averages over regular polygons (6.9-14) |
| `Carlson.RPolynomial.PolygonSpecial` | Gauss's multiplication formula for Pochhammer symbols; S- and R-functions over a regular polygon as `₀F_{k-1}` and `ₖF_{k-1}` (Exercise 6.9-14) |
| `Carlson.RPolynomial.EqualParameterBounds` | Bounds for R-polynomials with equal parameters (Exercises 6.2-10 – 6.2-12) |
| `Carlson.RPolynomial.DifferentialForm` | R-polynomials as diagonal derivatives of `∏ zⱼ^{-bⱼ}` (Exercise 7.8-6) |
| `Carlson.RPolynomial.NearDiagonal` | The second-order expansion of `R_t(cw; x)` at the diagonal and Exercise 6.2-14 |
| `Carlson.TwoVariable.RPolynomial.BetaIntegral` | Carlson's normalized form of (6.9-6) and the Beta-integral relation (Exercise 6.9-7) |
| `Carlson.TwoVariable.SHypergeometric` | Three nodes in arithmetic progression: S as `₁F₂` (Exercise 6.9-15) and R as `₃F₂` (6.9-5) |
| `Carlson.TwoVariable.QuadraticGauss` | The quadratic transformation `₂F₁(2α, 2β; α + β + ½; z) = ₂F₁(α, β; α + β + ½; 4z(1 - z))` (Exercise 6.10-1), with its R-function form on `re z < 1/2` |
| `Carlson.R.LogContour` | The logarithmic contour formula on `C¹` cycles (Exercise 6.6-15) |
| `Carlson.RPolynomial.SmallParameters` | Small parameters: Exercises 6.2-6, 6.2-8 and the limit 6.3-4 |
| `Carlson.TwoVariable.RPolynomial.EqualParameter` | The explicit expansion of `Rₙ(β, β; x, y)` (Exercise 6.9-3) |
| `Carlson.Jacobi.GegenbauerProductComplex` | Ossicini's formula 6.11-3 and Gegenbauer's product formula 6.11-4 in the book's generality (complex angles); the bound 6.7-2; Gegenbauer coefficients and values at 0 (6.9-1, 6.9-4) |
| `Carlson.RPolynomial.Growth` | Theorem 6.6-2 (upper bound; lower bound for distinct nodes) and the counterexample to the printed statement |
| `Carlson.TwoVariable.FractionalIntegral` | The fractional integral (5.5-14) and its Riemann–Liouville form (5.5-15) |
| `Carlson.TwoVariable.FractionalContinuation` | Continuation of `I^ν f` in `ν` and `I^{-n} f = f⁽ⁿ⁾` (5.5-16): entire for holomorphic `f` on a convex set (Exercise 6.3-3, via a Taylor disk and the identity theorem, no contour), and to `re ν > -n` for `f ∈ Cⁿ` on a real interval (Riesz's integration by parts); the closed form of `R_m(1, -n; X, Y)/Γ(m+1-n)` |
| `Carlson.TwoVariable.SEqualParameter` | Theorem 6.9-2: `S(β, β; x, y)` as an exponential times `₀F₁` |
| `Carlson.TwoVariable.ConfluentHypergeometric` | `S(a, b; x, 0) = ₁F₁` (5.8-6), Kummer's second formula (6.9-6), and `J_μ`, `I_μ` of every complex order as S-functions (6.9-18), (6.9-21), with Mathlib's regularized hypergeometric functions |
| `Carlson.TwoVariable.QuadraticHybrid` | The hybrid transformation 6.10-4, `R_K` and Gauss's AGM formula, `R_C`, Borchardt's algorithm, and the elementary `R_C` values of 6.9-4 |
| `Carlson.TwoVariable.Borchardt` | The accelerated Borchardt algorithm (6.10-27)–(6.10-29), from a cubic expansion of `R_C` near the diagonal |
| `Carlson.TwoVariable.RCAsymptotic` | Asymptotics of `R_C`: Exercise 6.9-18, `((x + 2y)/3) R_C(x², y²) = 1 + (1/5)((x - y)/(x + 2y))² + O(ε³)` for complex `x, y` in the right half-plane; the real expansion of `R_C(x, y)` near the diagonal and `log(4x/y)/(2√x)` as `y → 0⁺` |
| `Carlson.TwoVariable.BilateralGenerating` | Generating Relation 6.11-1 and Meixner's formula 6.11-2 in the Euler strip |
| `Carlson.Jacobi.GegenbauerProduct` | Formula (6.7-21), the Gegenbauer generating function, Ossicini's formula 6.11-3, and Gegenbauer's product formula 6.11-4 |

The coverage against the book is recorded in `CarlsonCoverage.md`, and the
Chapter 6 exercises in `CarlsonChapter6Exercises.md`.

### Chapter 8: averages of `xᵗ`

| Module | Chapter 8 scope |
| --- | --- |
| `Carlson.R.IntegralEvaluation` | Formula 8.1-1 on the straight path from `x` to `y` for all complex Dirichlet parameters when each affine factor stays in the slit plane (the continuous phase is then the principal one), and Formulas 8.1-2 and 8.1-3 on rays with the principal-phase condition explicit; the earlier unit-interval and ray forms with compatible logarithms |
| `Carlson.R.AverageExercise` | Exercise 8.1-6: the Dirichlet average of `(u·x)^{-a} (u·y)^{-a'}` is `∏ yᵢ^{-bᵢ} R_{-a}(b; x/y) = ∏ xᵢ^{-bᵢ} R_{-a'}(b; y/x)`, by Fubini over two simplices and analytic continuation in `a` |
| `Carlson.R.IntegralExercises` | Formula 8.1-1 on a real segment with real limits, and Exercises 8.1-1, 8.1-2, 8.1-3 and 8.1-5 by the substitutions `s = t²` and `s = sin² θ` |
| `Carlson.R.SmallVariableContinuation` | Theorem 8.3-2: the small-variable limit for all complex `a, b` with `re (a' - bₖ) > 0`, by the recurrence 8.3(5), induction, and the identity theorem in the parameters; the one-node value of `R` |
| `Carlson.R.SmallVariableJoint` | The joint small-variable limit: `R` is continuous as `z → z₀` with `z₀ₖ = 0`, through the right half-plane, with the other nodes varying (the joint form of Theorem 8.3-2) |
| `Carlson.TwoVariable.GaussHypergeometric` | (8.3-7) with Mathlib's regularized Gauss function, Corollary 8.3-3, and Gauss's theorem 8.3-4 (with Abel's theorem and Euler's limit formula for `Γ`) |
| `Carlson.TwoVariable.GaussExercises` | Exercises 8.3-1 to 8.3-5: R-values at the nodes `(1/2, 1)`, `(1, 2)`, `(2, 1)`, Kummer's theorems for `₂F₁` at `-1` and `1/2`, and a series for the beta function |
| `Carlson.TwoVariable.ThreeFTwoExercises` | Euler's transformation of `₂F₁` for real `\|x\| < 1`; the `₃F₂` series, its absolute convergence and continuity on the closed unit disk, and its representation as a Dirichlet average of `₂F₁` (Exercise 8.3-10); the transformations of `₃F₂(1)` in Exercises 8.3-11 and 8.3-12 |
| `Carlson.TwoVariable.Reduction` | Table 8.5-1 (all seven rows) and Example 8.5-5, equation (6) |
| `Carlson.R.AssociatedRecurrenceExercises` | Exercise 8.4-1: the coefficients of Relation 8.4-1 for equal Dirichlet parameters are multiples of `Eₙ(z)` |
| `Carlson.R.AssociatedDependence` | Theorem 8.4-3: any `k+1` associated R-functions admit a nontrivial polynomial relation on slit-plane nodes, for each fixed exponent and parameter vector; coefficient dependence on those parameters is not asserted |
| `Carlson.R.LogarithmExercise` | Exercise 8.5-1: `R_{-1}(1/2, 1/2, 1; x, y, z)` as a logarithm, for positive real nodes with `z ≠ x, y`, by an explicit antiderivative on the positive ray |
| `Carlson.R.IntegerReduction` | Theorem 8.5-1: with integral exponent and parameters, `R_t(b; z)` is log-rational on the slit domain (`Q(z) R = P₀(z) + ∑ Pᵢ(z) log zᵢ`, polynomials `Q ≠ 0`, `P₀`, `Pᵢ`); deletion of a zero parameter and `R_t(β eᵢ; z) = zᵢ^t` on the slit domain; `(zᵢ - zⱼ) R_{-1}(eᵢ + eⱼ; z) = log zᵢ - log zⱼ` (8.5-2) |
| `Carlson.Elliptic.ArcLengthExercises` | Exercises 8.3-7 (lemniscate arc length `R_F(r⁻² + 1, r⁻², r⁻² - 1)`, perimeter `2π R_K(1, 2)`) and 8.3-8 (`t = x R_{-1/p}(1/p, 1; c^p - \|x\|^p, c^p)`, its derivative, and the quarter-period `(π/p) csc(π/p)`) |
| `Carlson.Elliptic.ChapterNineExercises` | Exercises 9.2-1, 9.2-3, 9.6-2, 9.7-1 to 9.7-5 (9.7-2 and 9.7-5 with the branch condition of Theorem 9.7-1) and 9.8-5 |
| `Carlson.Elliptic.ReductionRelations` | The contiguous relations of §5.9 for explicit parameter vectors with two, three and four variables, zero-parameter deletion, reindexing along an equivalence, and the closed forms `R̃_{-c}` at half-integer parameters |
| `Carlson.Elliptic.ReductionTables` | Carlson's reduction Tables 9.3-1 (all rows; the book's row `2b = (1, 3, 3)` has a sign error), 9.3-2 (all rows), the remaining rows 1 and 3 of Table 9.3-3 and rows 2, 3, 5 of Table 9.3-4, and Exercise 9.3-3; each row is a polynomial combination of contiguous relations found by exact linear algebra |
| `Carlson.Elliptic.LegendreStandard` | (9.2-12)–(9.2-15) and Example 9.3-1 for real arguments: `E(k) = (π/2) R_E(1 - k², 1)`, `F` and `R_G` in terms of `F`, `E`, `R_K`, `R_E` in terms of `K`, `E`, and Exercise 9.3-1 (`R_H` via `Π` and `F`) |
| `Carlson.Elliptic.LandenExercises` | Exercises 9.3-4 (`R_L(x, y, ρ) + R_L(x, y, xy/ρ) = 2 R_K`), 9.5-2 (Landen for `R_E`) and 9.5-5 (Landen for `R_G`) |
| `Carlson.Elliptic.AGMSecondKind` | Exercises 9.5-3 and 9.5-4: `R_E` along the arithmetic-geometric mean, `R_E(x², y²) = B/M` |
| `Carlson.Elliptic.Independence` | The `R_H` part of Theorem 9.2-1: `√ρ R_H(x, y, z, ρ)` has a nonzero limit as `ρ → ∞`, so `R_H` is independent of `(xyz)^{-1/2}`, `R_F`, `R_G` over coefficients polynomial in `ρ` |
| `Carlson.Elliptic.QuarticIntegral` | (9.8-10)–(9.8-13) and Exercises 9.8-3, 9.8-6: real integrals of `[(a + αt)(b + βt)(c + γt)(d + δt)]^{-1/2}` with positive linear factors as `2 R_F(U², V², W²)` |
| `Carlson.Elliptic.Applications` | §9.4 and Exercises 9.3-2, 9.4-1: pendulum, anharmonic oscillator, perimeter of an ellipse, arc of a hyperbola, potential of a charged ellipsoid, mutual inductance of coaxial circles |
| `Carlson.Elliptic.QuarticExercise` | Exercise 8.5-2: `R_{-1}(1/2, 1/2, 1/2, 1/2; w, x, y, z) = 2 [(x - w)(y - w)(z - w)]^{-1/2} [R_F(1/(x - w), …) - w^{1/2} R_F(x/(x - w), …)]` for real `0 < w < x, y, z` |
| `Carlson.Elliptic.RF` | `R_F` (8.2-6), its symmetry, the integral (8.2-5), `R_F(x, y, y) = R_C(x, y)` (8.2-13), and `R_F(x, y, 0) = (π/2) R_K(x, y)` (8.3-17) |
| `Carlson.Elliptic.SchwarzChristoffel` | The Schwarz–Christoffel differential equation (8.2-1) and integral (8.2-2), (8.2-3), the phase of the boundary derivative, the half-periods (8.2-8)–(8.2-10), (8.2-20) and (8.2-21) as real integrals, the elementary cases (8.2-14), (8.2-16), and the `sn` integral (8.2-18); identification with TauCeti's normalized Schwarz–Christoffel primitive, with openness and boundedness of the image |
| `Carlson.Elliptic.VertexLimits` | The Schwarz–Christoffel map `scMap` on the closed upper half-plane: agreement with `R_{-a}(b; z - x)`, continuity up to the real axis by dominated convergence, the boundary limits and vertices `w(xᵢ)`, `w(z) → 0` at infinity by complex homogeneity, and closure of the polygon |
| `Carlson.Elliptic.Polygon` | Carlson's direction `θ` of the boundary derivative and the turning angles; convexity of the polygon for `a ≤ 1` (monotone direction of total range at most `2π`); the open polygon `scPolygon` as an intersection of half-planes; `w` maps the upper half-plane into it (minimum principle) and the real axis to its boundary; the sides as explicit integrals |
| `Carlson.Elliptic.Mapping` | Theorem 8.2-1: `w` is a bijection from the upper half-plane onto the polygon (proper local homeomorphism onto a convex set), with holomorphic inverse and derivative `1/w'` |
| `Carlson.Elliptic.Inversion` | Examples 8.2-2 and 8.2-3: `R_F(z - x₁, z - x₂, z - x₃)` maps the upper half-plane onto the rectangle with half-periods `K₁, K₃`, and its inverse satisfies (8.2-11), (8.2-12); Carlson's `v(y)` maps onto the rectangle `(-K, K) × (0, K')`, agrees with (8.2-18) on `(0, 1)`, and its inverse `sn` satisfies `(sn')² = (1 - sn²)(1 - k² sn²)` |

The small-variable theorems use right-half-plane nodes and approach to zero;
Carlson's wider slit-sector approach is still open. The Gauss identification is
on the unit disk, and its limit approaches 1 within that disk; the summation
formula assumes `re(γ-α-β) > 0`. General reduction Theorems 8.5-3/8.5-4 and the
branch-point splitting formula are not yet proved. The rectangle inverses do not
yet have a doubly periodic meromorphic continuation. Further details are in
[CarlsonCoverage.md](CarlsonCoverage.md).

### Chapter 9: elliptic integrals

| Module | Chapter 9 scope |
| --- | --- |
| `Carlson.Elliptic.Asymptotic` | Positive-real node comparison for `R_F`; `isEquivalent_carlsonRF_atTop` (9.2-10) and `isEquivalent_carlsonRK_zero` (8.3-16), from comparison with elementary `R_C`, zero-variable duplication and homogeneity |
| `Carlson.Elliptic.Standard` | `R_G`, `R_H`, `R_E`, `R_L` (9.2-1), (9.2-2) and their symmetries; the zero-variable limits (9.2-3); Legendre's `F`, `E`, `Π`, `K`, `E(k)`, with `F` and `E` as `R` functions (9.2-11), (9.3-2) and `K(k) = (π/2) R_K(1 - k², 1)` (9.2-14) |
| `Carlson.Elliptic.LegendreThird` | Incomplete and complete `Π` as R-functions (9.2-11), (9.2-14), and their reductions to `R_F`, `R_H` and to `R_K`, `R_L`; Tables 9.3-3 (rows 2, 4) and 9.3-4 (rows 1, 4) on the full complex slit domain, including coincident nodes |
| `Carlson.Elliptic.CompleteK` | `K(k)` at an imaginary modulus and Landen's transformation for `K` (Exercise 6.10-5) |
| `Carlson.Elliptic.Addition` | The addition theorem 9.7-1 for positive variables (Euler's algebraic solution, constancy along the branch, and the limit `λ → 0`); the duplication theorem 9.6-1 on the whole slit domain (from positive reals by uniqueness, one variable at a time); Algorithm 9.6-2 for strictly positive real initial values; homogeneity of `R_F` |
| `Carlson.Elliptic.Landen` | Theorem 9.5-1 for all complex `t` in regularized form, for all positive `x, y, z` (positive `v, w` with `v² + w² = z² + xy`, `vw = zu`, or complex conjugate `v², w²` when `z` lies between `x` and `y`), via the substitution `r = s(s + xy)/(s + u²)` and continuation in `t`; Landen's transformation of `R_F` (9.5-4), with Carlson's explicit `v, w` |
| `Carlson.Elliptic.LandenAlgorithm` | Algorithms 9.5-2 (ascending Landen) and 9.5-3 (descending Gauss), with the limits `(1/M) arcsinh(M/S)` and `(1/M) arcsin(M/T)`; the equality endpoint `t₀ = a₀` is in `Carlson.Elliptic.AGMSecondKind` |
| `Carlson.Elliptic.ZeroVariable` | A vanishing variable: the joint limit (8.3-17), (9.2-4), Algorithm 9.5-2 with `s₀ = 0`, the duplication theorem with one variable `0`, and (9.7-17) |
| `Carlson.Elliptic.QuarticReduction` | Theorem 9.8-1: (9.8-3) for positive `A, B, C, D` by Carlson's substitution, and (9.8-4) `R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = 2 R_F(X², Y², Z²)` where `A, …, D, X, Y, Z` have positive real parts (identity theorem one variable at a time); the case `D = 0`; the case `X = 0` is in `Carlson.Elliptic.QuarticIntegral` |

The logarithmic results are leading asymptotic equivalents: for fixed positive
`x,y`, `R_F(x,y,z) ∼ log(4√z/(√x+√y))/√z` as `z → ∞`; for fixed positive
`x`, `R_K(x,y) ∼ log(16x/y)/(π√x)` as `y → 0+`. The full logarithmic
series and complex-sector extension are not included, nor are limits of the
additive remainder after subtracting the leading logarithm.

The Legendre third-kind identities assume real arguments with `k² < 1`. The
incomplete case requires `0 < φ < π/2` and `n sin² φ < 1`; the complete
case requires `n < 1`. They cover zero and negative characteristics, but not
principal-value integrals or complex amplitudes. The polynomial-coefficient
reduction identities themselves hold for arbitrary slit-plane nodes.

Remaining Chapter 9 work includes the standard-function independence 9.2-1 beyond its `R_H`
part, complex iteration and error estimates for duplication, Carlson's remark on complex
Landen transformations, and the multivariable applications of §9.4. See
[SYNOPSIS_GAPS.md](SYNOPSIS_GAPS.md) and [CarlsonCoverage.md](CarlsonCoverage.md).
