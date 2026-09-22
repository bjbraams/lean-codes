# Carlson project module structure

The project has nine mathematical libraries. General support and simplex
geometry/integration (`StdSimplexMeasure`) feed into `Dirichlet`, then `Carlson`.
The support libraries do not import either application layer, and Dirichlet theory
does not import Carlson functions. `ComplexAnalysis.Integral.Simplex` uses the
general simplex foundation for divided differences and repeated integrals; the
other support modules remain simplex-independent.

The root modules and the topic umbrellas below are convenient entry points.

## General algebra

`Algebra.LinearDependence` develops denominator closure and denominator-cleared
linear dependence over integral domains in namespace `Submodule`. It imports only
Mathlib; the associated Carlson-function arguments import this algebraic support.

## General analysis and topology

`Analysis.lean` and `Topology.lean` expose general support extracted from SCV and the
application libraries.
Both depend only on Mathlib. Complex analysis and SCV import individual support modules
as needed; the general foundations do not import either complex function-theory library.
Their directory names are not blanket namespaces. Existing namespaces such as
`ContinuousLinearMap`, `ContDiffAt`, `MeasureTheory`, `IsOpen`, `Path`, `Homeomorph`,
`Set`, `UpperSemicontinuousOn`, and `Real` are used, with root-level results where
that matches the underlying API.

| Module | Content |
| --- | --- |
| `Analysis.SpecialFunctions.Gamma` | Complex-rate Gamma/Laplace kernel bounds, integrability, differentiation, holomorphy, and evaluation |
| `Analysis.Deriv` | Diagonal chain rule over a nontrivially normed field, with normed-space targets |
| `Analysis.Integral.Pi` | Nonnegative integration of coordinate products over finite dependent product measure spaces |
| `Analysis.Connected` | Connected shells and complements of balls in real normed spaces |
| `Analysis.ConvexHullDomain` | Path connectedness of configurations whose convex hull stays in a path-connected set; arbitrary index types and real topological vector spaces |
| `Analysis.LinearFunctional` | Scalar actions and continuous linear functional lemmas |
| `Analysis.OpenMapping` | Open mapping for complete metrizable real or complex vector spaces |
| `Analysis.TaylorBounds` | `ContDiffAt.exists_taylor_bound` and real Taylor-remainder inequalities |
| `Analysis.GeometricBounds` | Real root limits and geometric majorants extracted from the Hartogs proof |
| `Analysis.Integral.CompactSupport` | Compact weighted integrability over a normed field and half-line integration support |
| `Analysis.Integral.Parametric` | Fréchet differentiation of compact integrals with fixed integrable weights and real or complex parameters |
| `Analysis.Integral.CurveIntegral` | Endpoint formulas for exact one-forms on real or complex normed spaces, with Banach-valued potentials |
| `Analysis.Integral.CurveIntegral.Map` | Pullback of one-forms under differentiable maps and identification of finite-interval parametrizations with Mathlib curve integrals |
| `Analysis.Integral.CurveIntegral.Improper` | Exact-form endpoint formulas on half-lines and open intervals, limits determined by endpoint potentials, and convergence of finite curve integrals to integrable half-line pullbacks |
| `Analysis.Integral.CurveIntegral.Bounds` | Operator-norm and speed estimates, vanishing connector integrals, and explicit power-decay rates for growing paths |
| `Analysis.Integral.Reciprocal` | Inversion change of variables between a positive half-line and a bounded interval, for both integrals and integrability |
| `Analysis.Integral.Tail` | Uniformly vanishing tails under a common integrable majorant, uniform finite-interval approximation, and a quantitative power-decay tail estimate |
| `Analysis.Holomorphic.FunctionSpace` | Shared compact-open holomorphic maps, evaluation, restriction, and the equivalence between function-space convergence and locally uniform convergence; closedness is supplied separately by each variable theory |
| `Analysis.Holomorphic.NormalFamily` | Equicontinuity under compact-local bounds, Montel compactness and subsequences with closedness as input, and Vitali convergence with a uniqueness-set hypothesis |
| `Topology.LocallyConstantGluing` | Gluing functions with locally constant additive differences over simply connected spaces, via a discrete-fiber covering bundle |
| `Topology.CompactExhaustion`, `Frontier`, `Path` | Compact exhaustions, frontier membership, and first exit of paths |
| `Topology.Graph`, `UpperSemicontinuous` | Graph homeomorphisms and semicontinuity operations |
| `Topology.SeparateContinuous` | Baire boundedness for separately continuous maps on a product with a compact factor |

The generic Baire and real-estimate blocks were separated from the SCV Hartogs proof.
General curve integration moved from `ComplexAnalysis` to `Analysis`; its complex-specific
applications remain in `ComplexAnalysis.CauchyIntegral`. Algebra-specific material such
as `SeveralComplexVariables.Polynomial.OfFn` is outside this reorganization.

## Pochhammer support modules

`Pochhammer.Estimates` includes factorial-geometric bounds, half-integer comparison,
and nonvanishing of ascending Pochhammer symbols in the right half-plane.
`Pochhammer.Gamma` includes uniform factorial decay of reciprocal Gamma after a
common natural shift on compact sets, with a finite-coordinate-sum specialization.

## Single-variable complex analysis

`ComplexAnalysis.lean` imports the single-variable foundation, including the planar theory
formerly developed inside SCV. Complex-specific declarations use the `Complex` namespace;
extensions to existing APIs retain namespaces such as `AnalyticOnNhd` and `DiffContOnCl`.
The modules do not import the application layers or several-variable function theory.
Its general support is now imported from the independent `Analysis` and `Topology`
libraries. The simplex kernel, divided-difference, Newton–Taylor, and repeated-integral
modules additionally use `StdSimplexMeasure.SimplexFTC`. There are no imports back into SCV.

| Module | Proved content |
| --- | --- |
| `ComplexAnalysis.Integral.Simplex` | Unnormalized complex simplex kernel integrals, permutation symmetry, coalescence, and the simplex FTC |
| `ComplexAnalysis.DividedDifference`, `NewtonTaylor` | Hermite–Genocchi divided differences including coincident nodes, recurrence, and exact Newton and Taylor remainders |
| `ComplexAnalysis.RepeatedIntegral` | Segment integration identified with Mathlib curve integrals, and repeated integration as a coalesced simplex integral under continuity |
| `ComplexAnalysis.HalfPlane`, `Pow` | Right-half-plane branch geometry, sector square roots, finite-family containing disks, and principal-power multiplication and holomorphy |
| `ComplexAnalysis.BranchLog` | Differentiation of continuous logarithm branches; holomorphic logarithms and roots on simply connected open sets; prescribed branch value and uniqueness |
| `ComplexAnalysis.BranchLog.Analytic` | Analytic dependence of logarithm branches, including normed source spaces and normalization along a zero section |
| `ComplexAnalysis.BranchLog.Homotopy` | Continuous logarithm lifts over homotopies in the punctured plane, normalization on endpoint edges, and invariance of terminal logarithm values |
| `ComplexAnalysis.ExteriorPath`, `ExteriorPath.Integral` | Compactified exterior paths, escape to infinity, derivatives and normalized node factors, and Banach-valued primitive endpoint formulas with explicit convergence assumptions |
| `ComplexAnalysis.HasPrimitives` | Local-to-global primitives on simply connected open domains; Banach-valued holomorphic primitives, normalization, uniqueness, and Morera's global primitive consequence |
| `ComplexAnalysis.HasPrimitives.Pullback` | Continuous potentials on simply connected parameter spaces after pullback of local holomorphic primitives; image-path integrals given by potential increments |
| `ComplexAnalysis.CauchyIntegral` | Path independence for functions with primitives; Banach-valued Cauchy's theorem on simply connected open sets; logarithmic-derivative integrals |
| `ComplexAnalysis.CauchyFormula` | Banach-valued Cauchy formula on simply connected open sets, retaining the scalar kernel integral explicitly; normalized formula when that integral is `2πi` |
| `ComplexAnalysis.LogDerivIntegral`, `CurveIndex` | Exponential endpoint identity for logarithmic-derivative integrals; integer-valued index for closed C¹ curves avoiding the pole; reversal, concatenation, vanishing, and the index-weighted Banach-valued Cauchy formula |
| `ComplexAnalysis.Integral.CirclePath` | Smooth circle paths and equality of curve and circle integrals; used to normalize the index inside and outside a circle |
| `ComplexAnalysis.CurveIndex.Continuity` | Continuous and locally constant dependence on the pole off the curve; constancy on connected components and vanishing on every unbounded component of the complement |
| `ComplexAnalysis.Integral.Map` | Holomorphic change of variables in curve integrals and preservation of path smoothness |
| `ComplexAnalysis.Integral.Homotopy` | Cauchy's theorem for `C²` homotopies on arbitrary open domains, including moving endpoint tracks and fixed-endpoint invariance |
| `ComplexAnalysis.Integral.ContinuousHomotopy` | Cauchy's theorem for continuous homotopies with differentiable, integrable boundaries; moving endpoints and passage to improper limits when endpoint-track integrals vanish |
| `ComplexAnalysis.CurveIndex.Homotopy` | Invariance of the analytic index under continuous based homotopies of `C¹` loops avoiding the pole, and vanishing under continuous contraction |
| `ComplexAnalysis.UnivalentDisk.Geometry`, `Separation` | Open and simply connected image disks, compact closures, embedded circle frontiers, and exactly two complementary components for circles mapped injectively and holomorphically on a larger disk |
| `ComplexAnalysis.UnivalentDisk.Index`, `CauchyFormula` | Index one in the image disk and zero outside its closure; normalized Banach-valued Cauchy formula on the mapped contour |
| `ComplexAnalysis.UnivalentDisk.Exhaustion` | Nested relatively compact image disks, with every compact subset eventually contained in one term; an injective holomorphic disk parametrization is required |
| `ComplexAnalysis.PolygonIntegral` | Sum of integrals over oriented polygon edges; vanishing for exact functions and holomorphic functions on simply connected open sets |
| `ComplexAnalysis.CauchyDerivatives`, `CauchyEstimates`, `CauchySeries` | Higher derivative circle formulas, compact derivative bounds, geometric Taylor-coefficient majorants, and one-variable Cauchy-series estimates |
| `ComplexAnalysis.LaurentSeries.Basic`, `Annulus`, `Geometry` | Banach-valued Laurent expansions, coefficient estimates and radius independence, annular Cauchy identities, and planar circular geometry |
| `ComplexAnalysis.Residue`, `Residue.LogDeriv`, `Residue.PrincipalPart` | Residues at isolated holomorphic singularities, Laurent coefficient identification, germ invariance and linearity, higher-pole derivative formulas, logarithmic-derivative residues equal to meromorphic orders, and finite principal parts of meromorphic germs with their circle integrals |
| `ComplexAnalysis.ArgumentPrinciple`, `Rouche` | The disk argument principle for meromorphic functions and preservation of holomorphic zero counts, with multiplicity, under strict boundary perturbations |
| `ComplexAnalysis.Hurwitz` | Eventual stability of disk zero counts, persistence of zeros, zero-free-or-identically-zero locally uniform limits, and constant-or-injective limits |
| `ComplexAnalysis.FunctionSpace`, `Montel`, `Vitali` | Closed and complete one-variable holomorphic spaces, compactness and subsequences under compact-local bounds, and Vitali convergence from pointwise convergence on a set with an interior accumulation point; no SCV imports |
| `ComplexAnalysis.EssentialSingularity` | Bounded punctured germs extend analytically, meromorphic isolated singularities have a finite limit or tend to infinity, and essential singularities have dense image on every punctured neighborhood (Casorati–Weierstrass) |
| `ComplexAnalysis.Subharmonic.Basic`, `Submean`, `Majorant`, `Convex`, `SmoothCriterion` | Planar subharmonicity, maximum and submean principles, polynomial majorants, convex examples, and the Laplacian criterion |
| `ComplexAnalysis.CauchyPompeiu`, `CauchyTransform` | Planar Cauchy–Pompeiu theory and the Cauchy transform with smooth parameters |
| `ComplexAnalysis.RemovableSingularity`, `Injective`, `ZeroPersistence` | Removal across planar analytic zero sets and countable sets under continuity, nonvanishing derivatives of injective functions, and persistence of zeros |
| `ComplexAnalysis.ParametricIntegral`, `RealUniqueness`, `LocallyUniform`, `Integral.Circle` | Compact integration in one complex parameter, uniqueness from real parameters, convergence of iterated derivatives, and circle-integration helpers |

SCV retains the multivariable Laurent theory, Hartogs expansions, plurisubharmonicity,
and holomorphic dependence on several parameters. In particular,
`SeveralComplexVariables.LaurentSeries.OneVariable` is now just the parameter-holomorphy
bridge to the planar Laurent coefficients. Mixed files for estimates, real uniqueness,
parametric integrals, and removability import the corresponding single-variable foundations.

Curve integrals use Mathlib's `curveIntegral` and `Path`; polygons use Mathlib's
`Polygon`. Polygon integration does not require simplicity and includes empty and
one-vertex polygons. Primitives and Cauchy theory now cover arbitrary simply connected open
domains. The analytic index is an integer for closed C¹ curves avoiding the pole. It is
locally constant off the curve, constant on connected components of the complement,
and zero on every unbounded such component. Its value is one inside a counterclockwise
circle and zero outside the closed disk.

The smooth homotopy integral results extend Mathlib's closed-one-form theorem.
The continuous-homotopy results instead glue local primitives on the parameter
square and only impose regularity on the boundary paths. Neither requires a
simply connected ambient domain. Logarithm continuation uses covering-space lifting
and also works for continuous homotopies.
Improper Bochner integrals have explicit integrability hypotheses, whereas the
limits of finite integrals of exact forms require only convergence of the
endpoint potential values in addition to the finite-path hypotheses.
Deformations of finite truncations preserve their limiting integrals when the
endpoint-track integrals vanish. Common majorants give uniform tail convergence,
and power decay with exponent greater than one makes connecting-path integrals
vanish when their speeds grow at most linearly with the radius. These are explicit
analytic criteria; admissible exterior path families and arbitrary-domain contour
exhaustions still need geometric construction.

`UnivalentDisk` supplies separation, orientation and Cauchy normalization for contours
obtained by injective holomorphic maps on a neighborhood of a closed disk. It also
constructs a relatively compact exhaustion of an injective holomorphic open-disk image,
without assuming extension to the limiting boundary. The disk parametrization remains
an explicit hypothesis: its existence for arbitrary simply connected proper planar
domains is not supplied by the pinned Mathlib's partial Riemann mapping development.
General Jordan separation and a general-domain contour construction or exhaustion
remain unfinished for the nonconvex Carlson/Dirichlet construction.

## Several complex variables support modules

The application layers import individual SCV modules. The main interfaces used
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
| `FunctionSpace`, `Montel` | Several-variable closedness and coordinate differentiation on the shared holomorphic space; Montel and open-subset Vitali from the common `Analysis.Holomorphic` arguments; the sequential theorem now allows compact-local bounds |

Hartogs' theorem removes the need to prove local boundedness when combining
already analytic coordinate slices. The public local-bound results in
`Dirichlet.Complex.Parametric` and `Dirichlet.Average.Associated.Analytic` remain
useful with merely continuous kernels or averaged functions.

The broader SCV continuation, removable-singularity, and approximation theory
does not by itself supply the local Jordan-domain contour constructions and
planar exhaustion needed by `Dirichlet.Average.HolomorphicDomain`.

## Simplex foundation modules

`StdSimplexMeasure.Normalization` supplies measurable normalization by coordinate
sum. Two-coordinate interior and ambient-measure projection facts live in
`StdSimplexMeasure.Interior` and `StdSimplexMeasure.Measure.Basic`; aggregation
commutes with semiring homomorphisms in `StdSimplexMeasure.Aggregation`.

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

## Dirichlet theory modules

### `Dirichlet.Beta.Complex.Basic`

Contains module `Integral`.

Complex multivariate beta. Gamma quotient and parameter identities.
Simplex integral evaluation.

### `Dirichlet.Real`

Real probability results. `Dirichlet.Real.Moments` → `Real.Aggregation` → `Real.Marginals`.
Probability statements about moments, aggregation, and beta marginals are downstream of the real distribution.

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
| `Dirichlet.Transform` | Finite-order tangential continuation and existence of entire continuations for smooth simplex kernels |
| `Dirichlet.Transform.Basic` | General continuation predicate, canonical smooth-kernel transform, uniqueness, linearity, and independence of extension away from the simplex |
| `Dirichlet.Transform.Laws` | Permutations, coordinate and monomial shifts, the sum-shift identity, tangential differentiation, and coordinate-divisibility annihilation |
| `Dirichlet.Transform.Aggregation` | Aggregation of arbitrary kernels and Dirichlet parameters |
| `Dirichlet.Transform.Joint` | Joint continuation with auxiliary holomorphic parameters and commutation with auxiliary derivatives |
| `Dirichlet.Transform.Euler` | Two-endpoint Gamma-regularized Euler integrals, their identification with the two-coordinate Dirichlet transform, and joint entire continuation with holomorphic auxiliary parameters |
| `Dirichlet.Transform.Series` | Dominated native termwise integration and recognition of locally uniformly convergent series of continued transforms |

| Topic | Modules |
| --- | --- |
| Divided differences and repeated integrals | `Dirichlet.Average.NewtonTaylor`: unweighted probability normalization, equality with the general `Complex` constructions, and compatibility statements for Carlson Section 5.5 |
| Native averages | `Dirichlet.Average.Basic`: regularized and ordinary definitions together |
| Associated average analysis | `Dirichlet.Average.Associated.Relations` → `Deriv` → `Analytic` |
| Holomorphic kernels and joint continuation | `Dirichlet.Complex.Parametric` → `Dirichlet.Transform.Parametric` → `Dirichlet.Transform.Joint` → `Dirichlet.Average.JointContinuation`: Carlson 6.3-6 on general convex open node domains; the general Jordan-curve representation remains separate |
| Continued Cauchy representations | `Dirichlet.Average.ResolventContinuation` and `CauchyContinuation`, using `SeveralComplexVariables.ContourIntegral`: entire-parameter resolvents and circle representations |
| Continuation on nonconvex domains | `Dirichlet.Average.HolomorphicDomain`: domain-aware characterization, uniqueness, and increasing-domain gluing; local Jordan-domain existence and planar exhaustion remain open |
| Hull-admissible integral domains | `Dirichlet.Average.IntegralDomain`: open node-domain geometry, joint continuation on the native node domain, and recognition of a given continuation on connected open scalar domains |
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

## Carlson functions modules

The scalar Gamma/Laplace integral is independent support in
`Analysis.SpecialFunctions.Gamma`, under namespace `Complex`. Carlson's Laplace module
retains the R/S integral definitions and the inverse-confluence theorems, importing this
scalar API. The foundation uses only Mathlib, including its positive-real-rate evaluation.

### R-function analytic construction

`Carlson.R.SingleIntegral` is an umbrella over five steps:

1. `SingleIntegral.Series`: unit-interval definition and near-one series.
2. `SingleIntegral.Analytic`: joint analyticity in endpoint exponents, parameters, and nodes.
3. `SingleIntegral.UnitInterval`: node analyticity as a specialization, and native representation.
4. `SingleIntegral.Continuation`: unit-interval representation with continued
   Dirichlet parameters.
5. `SingleIntegral.PositiveRay`: positive-ray substitution and representations.

`Carlson.R.SingleIntegralAnalytic` retains the original import path for joint analyticity.

`SlitContinuation` uses the continued unit-interval construction; ray-kernel
arguments use `PositiveRay`. The contour formula (6.8-7) is still a separate
mathematical task and has no module of its own.

The slit-domain API separates `SlitRelations` (parameter-shift identities),
`SlitDeriv` (node derivatives and differential identities), and
`EulerPoisson` (the second-order system).

The three R interfaces remain distinct: native simplex integrals,
right-half-plane parameter continuation, and slit-node continuation.
`R.SlitIntegral` and `L.SlitIntegral` prove native-integral agreement when the
whole node convex hull stays in the slit plane; individual slit-plane nodes
alone are insufficient. `R.SlitIntegral` also specializes the continued circle
representation to R. Ordinary normalization still uses the total-parameter
Gamma factor; Lean's totalized values at Gamma poles are not assertions of
finite ordinary-function values.

### Recurrences and associated dependence

| Module | Responsibility |
| --- | --- |
| `Carlson.Associated.LinearDependence` | Generic denominator-clearing and finite-dimensional dependence; no Carlson or Dirichlet imports |
| `Carlson.Associated.Shift` | Shift indices and rational-coefficient data |
| `Carlson.R.Recurrence.Coefficients` | Symmetric-polynomial recurrence coefficients, independently of R-functions |
| `Carlson.R.AssociatedRecurrence` | Native homogeneity recurrence |
| `Carlson.R.Associated.ExponentReduction` | Polynomial and rational reduction to a finite exponent window |
| `Carlson.R.AssociatedDependence` | Parameter reduction and fixed-parameter dependence theorem |
| `Carlson.R.SlitRecurrence` | Transport of polynomial relations and the homogeneity recurrence to slit nodes |
| `Carlson.R.SlitAssociated` | Fixed-parameter associated dependence on the slit domain |
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
the finer equal-parameter normalization, and differentiated L-transformations
remain in `QuadraticContinuation`, `EqualParameter`, and `LQuadratic`.
`QuadraticSlit` extends the raw regularized R identities to all square-root
variables with positive real parts, without requiring their squared or
mean-square nodes to have positive real parts. The finer equal-parameter
and L interfaces retain their original node domains and normalization.

`Carlson.S` re-exports `S.Basic`, `S.Series`, `S.Analytic`, `S.Deriv`,
and `S.Properties`: native definitions, series continuation, joint analysis,
continued node derivatives, and functional identities.
