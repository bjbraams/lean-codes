# Carlson project module structure

The project's mathematical libraries are the general support in `ToMathlib` (`Algebra`,
`Analysis`, `Topology`), `Pochhammer`, `StdSimplexMeasure`, the complex-analytic subsets
`ComplexAnalysis` and `SeveralComplexVariables`, `Dirichlet`, and `Carlson`. General support
and simplex geometry/integration (`StdSimplexMeasure`) feed into `Dirichlet`, then `Carlson`.
The support libraries do not import either application layer, and Dirichlet theory
does not import Carlson functions. The complex-analytic libraries (`ToMathlib`,
`ComplexAnalysis`, `SeveralComplexVariables`) depend only on Mathlib and on each other;
complex kernels integrated over simplices (divided differences, repeated integrals) live in
`StdSimplexMeasure.Complex`.

The root modules and the topic umbrellas below are convenient entry points.

## General algebra

`ToMathlib.Algebra.LinearDependence` develops denominator closure and denominator-cleared
linear dependence over integral domains in namespace `Submodule`. It imports only
Mathlib; the associated Carlson-function arguments import this algebraic support.

## General analysis and topology

`ToMathlib/Analysis.lean` and `ToMathlib/Topology.lean` expose general support extracted from
the complex-analytic and application libraries. Files that also exist in `lean-CA` or
`lean-SCV` are kept identical there; some (the holomorphic function spaces and the open mapping
theorem) are used only by those projects.
Both depend only on Mathlib. Complex analysis and SCV import individual support modules
as needed; the general foundations do not import either complex function-theory library.
Their directory names are not blanket namespaces. Existing namespaces such as
`ContinuousLinearMap`, `ContDiffAt`, `MeasureTheory`, `IsOpen`, `Path`, `Homeomorph`,
`Set`, `UpperSemicontinuousOn`, and `Real` are used, with root-level results where
that matches the underlying API.

| Module | Content |
| --- | --- |
| `ToMathlib.Analysis.SpecialFunctions.Bessel` | The series of the regularized hypergeometric functions, bounds for Bessel functions of integer order, and the modified Bessel function `I_a` |
| `ToMathlib.Analysis.SpecialFunctions.GammaRatio` | `Γ(x)/|Γ(x + iy)| ≤ √(cosh πy)` for `x ≥ 1/2`, and `|Γ(1/2 + iy)|² = π/cosh πy` |
| `ToMathlib.Analysis.SpecialFunctions.CosOrthogonality` | Orthogonality of `cos (kθ)` on `[0, π]` |
| `ToMathlib.Analysis.SpecialFunctions.Gamma` | Complex-rate Gamma/Laplace kernel bounds, integrability, differentiation, holomorphy, and evaluation |
| `ToMathlib.Analysis.Deriv` | Diagonal chain rule over a nontrivially normed field, with normed-space targets |
| `ToMathlib.Analysis.Integral.Pi` | Nonnegative integration of coordinate products over finite dependent product measure spaces |
| `ToMathlib.Analysis.Connected` | Connected shells and complements of balls in real normed spaces |
| `ToMathlib.Analysis.ConvexHullDomain` | Path connectedness of configurations whose convex hull stays in a path-connected set; arbitrary index types and real topological vector spaces |
| `ToMathlib.Analysis.LinearFunctional` | Scalar actions and continuous linear functional lemmas |
| `ToMathlib.Analysis.OpenMapping` | Open mapping for complete metrizable real or complex vector spaces |
| `ToMathlib.Analysis.TaylorBounds` | `ContDiffAt.exists_taylor_bound` and real Taylor-remainder inequalities |
| `ToMathlib.Analysis.GeometricBounds` | Real root limits and geometric majorants extracted from the Hartogs proof |
| `ToMathlib.Analysis.Integral.CompactSupport` | Compact weighted integrability over a normed field and half-line integration support |
| `ToMathlib.Analysis.Integral.Parametric` | Fréchet differentiation of compact integrals with fixed integrable weights and real or complex parameters |
| `ToMathlib.Analysis.Integral.CurveIntegral` | Endpoint formulas for exact one-forms on real or complex normed spaces, with Banach-valued potentials |
| `ToMathlib.Analysis.Integral.CurveIntegral.Map` | Pullback of one-forms under differentiable maps and identification of finite-interval parametrizations with Mathlib curve integrals |
| `ToMathlib.Analysis.Integral.CurveIntegral.Improper` | Exact-form endpoint formulas on half-lines and open intervals, limits determined by endpoint potentials, and convergence of finite curve integrals to integrable half-line pullbacks |
| `ToMathlib.Analysis.Integral.CurveIntegral.Bounds` | Operator-norm and speed estimates, vanishing connector integrals, and explicit power-decay rates for growing paths |
| `ToMathlib.Analysis.Integral.Reciprocal` | Inversion change of variables between a positive half-line and a bounded interval, for both integrals and integrability |
| `ToMathlib.Analysis.Integral.Tail` | Uniformly vanishing tails under a common integrable majorant, uniform finite-interval approximation, and a quantitative power-decay tail estimate |
| `ToMathlib.Analysis.Holomorphic.FunctionSpace` | Shared compact-open holomorphic maps, evaluation, restriction, and the equivalence between function-space convergence and locally uniform convergence; closedness is supplied separately by each variable theory |
| `ToMathlib.Analysis.Holomorphic.NormalFamily` | Equicontinuity under compact-local bounds, Montel compactness and subsequences with closedness as input, and Vitali convergence with a uniqueness-set hypothesis |
| `ToMathlib.Topology.LocallyConstantGluing` | Gluing functions with locally constant additive differences over simply connected spaces, via a discrete-fiber covering bundle |
| `ToMathlib.Topology.CompactExhaustion`, `Frontier`, `Path` | Compact exhaustions, frontier membership, and first exit of paths |
| `ToMathlib.Topology.Graph`, `UpperSemicontinuous` | Graph homeomorphisms and semicontinuity operations |
| `ToMathlib.Topology.SeparateContinuous` | Baire boundedness for separately continuous maps on a product with a compact factor |

The generic Baire and real-estimate blocks were separated from the SCV Hartogs proof.
General curve integration lives in `ToMathlib.Analysis`; its complex-specific
applications are in `ComplexAnalysis.CauchyIntegral`.

## Pochhammer support modules

`Pochhammer.Estimates` includes factorial-geometric bounds, half-integer comparison,
and nonvanishing of ascending Pochhammer symbols in the right half-plane.
`Pochhammer.Gamma` includes uniform factorial decay of reciprocal Gamma after a
common natural shift on compact sets, with a finite-coordinate-sum specialization.

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

The broader SCV continuation, removable-singularity, and approximation theory of
`lean-SCV` does not by itself supply the local Jordan-domain contour constructions and
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

### `StdSimplexMeasure.Complex`

Contains modules `Integral`, `DividedDifference`, `NewtonTaylor`, `RepeatedIntegral`.

Complex kernels integrated over simplices, in the `Complex` namespace: unnormalized simplex
kernel integrals with permutation symmetry, coalescence and the simplex FTC; Hermite–Genocchi
divided differences including coincident nodes, with the recurrence and exact Newton and
Taylor remainders; segment integration identified with Mathlib curve integrals, and repeated
integration as a coalesced simplex integral under continuity. These modules depend only on
`StdSimplexMeasure.SimplexFTC` and Mathlib; they are used by `Dirichlet.Average.NewtonTaylor`.

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
`ToMathlib.Analysis.SpecialFunctions.Gamma`, under namespace `Complex`. Carlson's Laplace module
retains the R/S integral definitions and the inverse-confluence theorems, importing this
scalar API. The foundation uses only Mathlib, including its positive-real-rate evaluation.

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
| `Jacobi.WeightedIntegral` | Repeated weighted integration by parts for continuous derivative towers and `Cⁿ` functions on `[0,1]`, with a polynomial specialization |
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
| `Jacobi.ComplexWeightedIntegral` | The weighted derivative-tower identity for complex-valued functions, derived from the real identity |
| `Jacobi.SecondKindIntegral` | Euler and weighted Jacobi Cauchy representations off the entire unit segment, for real parameters greater than `-1` |
| `Jacobi.BoundaryKernel` | Symmetric vertical jumps for real-line and interval Cauchy integrals with integrable densities continuous at the approach point |
| `Jacobi.SecondKindBoundary` | Jacobi boundary jumps at interior points of the unit segment and their transport to distinct complex endpoints |
| `Jacobi.ComplexRodrigues` | Principal complex weights and Rodrigues' formula at all complex parameters |
| `Jacobi.ComplexOrthogonality` | Complex derivative-tower integrals, bilinear orthogonality and squared integrals for `re α, re β > -1` |
| `Jacobi.ComplexSecondKind` | Euler representations at arbitrary endpoints under degree-shifted positivity; weighted Cauchy representations for `re α, re β > -1`, and symmetric jumps on nondegenerate complex segments |
| `Jacobi.SecondKindBounds` | Degree-dependent bounds from shifted Euler weights, including estimates that retain the combined weight-resolvent factor |
| `Jacobi.SecondKindRayBounds` | Elliptic-rate upper bounds and absolute convergence on exterior focal rays at arbitrary complex parameters, transported by invertible complex affine maps |
| `Jacobi.SaddleGeometry` | Compatible endpoint square roots, the fractional linear saddle curve, its elliptic norm bound, and principal-branch membership; the deformation itself is in `Jacobi.SecondKindSaddle` |
| `Jacobi.SecondKindSeries` | Absolute and locally uniform convergence, and holomorphy of second-kind series with geometrically bounded coefficients on a sufficient distance-based region |
| `Jacobi.PolynomialBounds` | Explicit large-degree bounds from the Carlson numerator, and geometric bounds uniform on compact sets, with arbitrary complex parameters and endpoints |
| `Jacobi.KernelSeries` | Summable majorants and uniform convergence for polynomial–second-kind products on sufficiently separated sets |
| `Jacobi.CauchyKernel` | Cauchy-kernel coefficient identity; kernel expansion for sufficiently distant poles, uniformly on compact products; exact circular case; extension to elliptic exteriors conditional on local uniform convergence |
| `Jacobi.EllipseCoordinates` | Branch-independent square-root formula, characteristic roots and their strict exterior dominance, Joukowski coordinates, and preconnected elliptic exteriors |
| `Jacobi.AnalyticExpansion` | Passage from polynomial approximation to Jacobi expansions; sufficient disk criteria; absolute and locally uniform convergence to every entire function, using any fixed index-one cycle off the segment |
| `Jacobi.Ellipse` | Confocal mean-radius geometry, convex open disks, compact closed disks, affine covariance and elliptic neighborhoods of the focal segment |
| `Jacobi.Recurrence` | Denominator-free three-term recurrence for shifted Jacobi polynomials and Carlson's monic recurrence (Exercise 7.1-6) with coefficients `V n`, `W n` |
| `Jacobi.PolynomialGrowth` | Perturbed constant-coefficient recurrences; `‖pₙ(x)‖ ≤ C (ρ + ε)ⁿ` on closed elliptic disks via the maximum modulus principle |
| `Jacobi.SecondKindSaddle` | Deformation of the Euler integral onto the saddle curve by a real Möbius substitution and the identity theorem; `‖qₙ(y)‖ ≤ C (1/σ + ε)ⁿ` on closed elliptic exteriors |
| `Jacobi.EllipseContour` | Confocal ellipses as `C¹` cycles (Joukowski images of circles) and their winding numbers |
| `Jacobi.EllipticExpansion` | Lemma 7.6-1 on `μ(x) < μ(y)` and Theorem 7.6-2 on open elliptic disks, with uniform convergence on closed subdisks |
| `Jacobi.GrowthLimits` | Lower bounds by analytic continuation and recurrence dichotomies; Theorem 7.5-1 for `pₙ`, Theorem 7.5-3, uniqueness and the maximal ellipse of convergence |
| `Jacobi.SecondKindLimits` | The second-kind recurrence for large degrees, Theorem 7.5-1 for `qₙ`, and divergence of second-kind series inside the critical ellipse |
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
| `Jacobi.Hermite`, `Jacobi.HermiteRepresentation` | Monic Hermite polynomials: the Jacobi limit (Theorem 7.10-1), Rodrigues' formula (7.10-6), the weighted representation (Theorem 7.10-3) and orthogonality (Theorem 7.10-4) |

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
any nondegenerate complex segment. This proves a limit of the difference, without
asserting existence of the separate boundary limits.

The elliptic mean radius has minimum `‖r-s‖/4`, attained exactly on the focal
segment. Its open disks above that radius are convex; its closed disks are compact.
Every open neighborhood of the segment contains a closed disk of strictly larger
radius. Affine covariance includes zero scales, and coincident endpoints recover
ordinary circular disks. Sharp root-growth estimates in this mean radius remain
to be proved.

A preliminary convergence theorem uses distance from the endpoint segment instead.
For arbitrary complex parameters and endpoints, coefficients satisfying
`‖aₙ‖ ≤ C Rⁿ`, with `C, R ≥ 0`, give absolute and locally uniform convergence of
`∑ aₙ qₙ(z)` on `dist(z, [r,s]) > R`, with holomorphic sum. The proof shifts past
a finite initial set of degrees to a bounded Euler weight. The simultaneous
reciprocal-beta normalization has consecutive ratio tending to `4`, proved in
`Pochhammer.BetaShift`, which compensates for the weight's `4⁻ⁿ` decay. This is a
sufficient region, not the sharp confocal-ellipse convergence theorem.

Keeping the combined Euler factor intact improves this result on the exterior
focal rays. For every complex parameter pair, `∑ aₙ qₙ(z)` converges absolutely
on either ray when `‖aₙ‖ ≤ C Rⁿ` and `R < μ(z)`; every exponential upper rate
strictly greater than `1/μ(z)` bounds the second-kind degree sequence. The proof
first treats real endpoints and then uses complex affine covariance, including
coincident endpoints. It does not prove a matching lower estimate.

For a general point off the segment, compatible square roots `a²=z-r`,
`b²=z-s` exist with `Re(a conj(b)) > 0`. The fractional linear curve
`u=bt/(a(1-t)+bt)` stays in the principal branch domains of both endpoint
weights, and its Euler factor is bounded by `1/(4μ(z))`. These geometric facts
are proved, but deformation of the Euler integral onto the curve, with endpoint
justification, remains to be formalized.

For the monic polynomials, the Carlson numerator bound and a Pochhammer lower
bound give a geometric estimate uniform on every compact set. Combined with the
second-kind bounds, this gives summable majorants for the candidate kernel series
on sufficiently separated product sets, and for contour-coefficient expansion
terms. Dominated convergence then transports finite polynomial expansions to
limits of polynomial approximations. `ToMathlib.Analysis.Holomorphic.PolynomialApproximation`
supplies those approximations from Mathlib's power-series theory.

Consequently a function holomorphic on a closed disk has its Jacobi expansion at
interior points when a cycle inside that disk meets the stated separation condition.
For an entire function, an auxiliary large circle and contour invariance remove
that separation condition: the expansion converges absolutely at every point and
uniformly on every compact set to the function. Coefficients use any fixed `C¹`
cycle of index one about the segment, avoiding the segment. The only parameter
restriction for identification with the function is that `α+β+2` is not a
nonpositive integer; endpoints may coincide.

For Lemma 7.6-1, the Cauchy kernel's contour coefficient is now proved to equal
`qₙ(y)` at every complex parameter pair when the pole is outside the enclosing
circle. The existing disk expansion theorem then proves
`∑ pₙ(x) qₙ(y) = (y-x)⁻¹` for sufficiently distant `y`. The radius can be chosen
uniformly for `x` in a compact set, with uniform convergence on compact product
sets. Coincident endpoints have the full circular-domain identity.

The mean radius also has Carlson's branch-independent square-root expression.
The exterior Joukowski coordinate has modulus exactly equal to that radius and
maps a circular exterior onto the corresponding elliptic exterior. This proves
preconnectedness and the identity-principle extension of the kernel identity,
conditional on local uniform convergence. The missing step for the full
`μ(x) < μ(y)` domain is the sharp degree-growth control from §§7.4–7.5, rather
than the contour-coefficient calculation or analytic-continuation argument.

Remaining work includes separate second-kind boundary values and principal-value
formulas, and boundary theory beyond the range `re α, re β > -1`;
branches adapted to contours crossing the endpoint segment;
the Gegenbauer addition theorem; the asymptotic formulas of §7.4 with their constants;
the Bessel-function examples 7.7-3 and 7.7-4; and the second-kind limits of §§7.9–7.10.
The sharp growth limits of §7.5 and the elliptic expansion theorems of §7.6 are proved
without the §7.4 asymptotics. `CarlsonChapter7Coverage.md` records the coverage in detail.

### R-function analytic construction

`Carlson.R.SingleIntegral` is an umbrella over five steps:

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

`Carlson.Normalization.Basic` proves the scalar Gamma pole factorization, residue,
one-variable removability criterion, and finite removable limit. It also supplies
a joint analytic pole numerator and a sufficient joint removal criterion from
local divisibility by the exceptional total-parameter factor.
`Carlson.Normalization` applies these results uniformly to R, L, S, native T, and
principal slit-plane T. It proves ordinary joint holomorphy away from Gamma poles
and meromorphy under analytic one-variable substitutions. At total parameter
`-m`, a transverse parameter line has residue `(-1)^m / m!` times the regularized
value. Vanishing of that value characterizes removability of the transverse slice;
it does not by itself establish removability along the whole parameter hypersurface.

### Recurrences and associated dependence

| Module | Responsibility |
| --- | --- |
| `Carlson.Associated.LinearDependence` | Generic denominator-clearing and finite-dimensional dependence; no Carlson or Dirichlet imports |
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
the finer equal-parameter normalization, and differentiated L-transformations
remain in `QuadraticContinuation`, `EqualParameter`, and `LQuadratic`.
`QuadraticSlit` extends the raw regularized R identities to all square-root
variables with positive real parts, without requiring their squared or
mean-square nodes to have positive real parts. `EqualParameterSlit` defines the finer
equal-parameter normalization `regEqualR` without proof arguments, jointly holomorphic on
slit-plane nodes, and extends the finer R and L quadratic identities to the same domain.

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
| `Dirichlet.Average.CauchyCycle` | Cauchy's formula for derivatives on `C¹` cycles, Representation 5.11-2 on cycles, and the contour form of 6.3-6 |
| `Carlson.R.Homogeneity` | Homogeneity (5.9-3) on the slit node domain under the principal branch condition |
| `Carlson.R.Confluence` | Confluence (5.10-1) with complex exponent tending to infinity, and the refinement (5.10-9) |
| `Carlson.R.ContourRepresentation` | Formula (6.8-7) on `C¹` cycles, for all complex parameters |
| `Carlson.RPolynomial.Concentration` | The concentration limits of Theorem 6.2-5 |
| `Carlson.Normalization.EqualParameter` | Equal parameters: removable Gamma singularities of `Γ(β) F/Γ(kβ)` (Theorems 6.2-6, 6.8-4, Corollary 6.3-7), by one-variable pole removal and Hartogs' theorem |
| `Carlson.RPolynomial.Growth` | Theorem 6.6-2 (upper bound; lower bound for distinct nodes) and the counterexample to the printed statement |
| `Carlson.TwoVariable.FractionalIntegral` | The fractional integral (5.5-14) and its Riemann–Liouville form (5.5-15) |
| `Carlson.TwoVariable.SEqualParameter` | Theorem 6.9-2: `S(β, β; x, y)` as an exponential times `₀F₁` |
| `Carlson.TwoVariable.ConfluentHypergeometric` | `S(a, b; x, 0) = ₁F₁` (5.8-6), Kummer's second formula (6.9-6), and `J_μ`, `I_μ` of every complex order as S-functions (6.9-18), (6.9-21), with Mathlib's regularized hypergeometric functions |
| `Carlson.TwoVariable.QuadraticHybrid` | The hybrid transformation 6.10-4, `R_K` and Gauss's AGM formula, `R_C`, Borchardt's algorithm, and the elementary `R_C` values of 6.9-4 |
| `Carlson.TwoVariable.Borchardt` | The accelerated Borchardt algorithm (6.10-27)–(6.10-29), from a cubic expansion of `R_C` near the diagonal |
| `Carlson.TwoVariable.BilateralGenerating` | Generating Relation 6.11-1 and Meixner's formula 6.11-2 in the Euler strip |
| `Carlson.Jacobi.GegenbauerProduct` | Formula (6.7-21), the Gegenbauer generating function, Ossicini's formula 6.11-3, and Gegenbauer's product formula 6.11-4 |

The coverage against the book is recorded in `CarlsonChapters5And6Coverage.md`.
