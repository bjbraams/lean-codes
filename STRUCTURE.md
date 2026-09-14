# Module structure

The project has five mathematical layers. Dependencies run from
simplex-independent support (`Pochhammer`, `SeveralComplexVariables`) and
simplex geometry/integration (`StdSimplexMeasure`) through `Dirichlet` to
`Carlson`. The support libraries do not import the simplex or either
application layer, and Dirichlet theory does not import Carlson functions.

The root modules and the topic umbrellas below are convenient entry points.
Internal modules should import the specific prerequisites they use, rather
than the whole application library. The reorganization preserves public
declaration names and mathematical statements; some formerly private helpers
are now shared between adjacent modules.

## Simplex foundations

| Topic umbrella | Implementation modules | Responsibility |
| --- | --- | --- |
| `StdSimplexMeasure.PositiveSimplex` | `PositiveSimplex.Basic`, `SumIntegral`, `Aggregation` | Solid-simplex geometry and volume; sum-coordinate integration; aggregation |
| `StdSimplexMeasure.Measure` | `Measure.Basic`, `Aggregation` | Ambient coordinate measure and invariance; aggregation pushforward density |
| `StdSimplexMeasure.Integral` | `Integral.Basic`, `Slicing`, `Monomial`, `Aggregation` | Coordinate integral API; slicing/Fubini; polynomial integration; aggregation |

`Coordinates`, `Intrinsic`, and `IntrinsicMeasure` retain their separate roles.
In particular, `stdSimplexMeasure` is still a measure on the **entire sum-one
affine hyperplane**, not a measure supported only on the simplex. Intrinsic
simplex measure is its restriction transported through the coordinate
homeomorphism. Neither construction nor its normalization has changed.
Ambient smooth neighborhoods and derivatives remain in the coordinate vector
space.

## Dirichlet theory

| Topic | Modules |
| --- | --- |
| Complex multivariate beta | `Dirichlet.Beta.Complex.Basic`: Gamma quotient and parameter identities; `Integral`: simplex integral evaluation |
| Native real and complex interfaces | `Dirichlet.Real`, `Dirichlet.Complex`; compatibility in `Dirichlet.Bridge` |
| Real probability results | `Dirichlet.Real.Moments` → `Real.Aggregation` → `Real.Marginals` |
| Density and integral parameter shifts | `Dirichlet.ParameterShift` |
| Native averages | `Dirichlet.Average.Basic`: regularized and ordinary definitions together |
| Associated average analysis | `Dirichlet.Average.Associated.Relations` → `Deriv` → `Analytic` |
| Holomorphic kernels and joint continuation | `Dirichlet.Complex.Parametric` → `Dirichlet.Transform.Parametric` → `Dirichlet.Average.JointContinuation`: Carlson 6.3-6 on general convex open node domains; the general Jordan-curve representation remains separate |
| Continued Cauchy representations | `Dirichlet.Average.ResolventContinuation` and `CauchyContinuation`, using `SeveralComplexVariables.ContourIntegral`: entire-parameter resolvents and circle representations |
| Continuation on nonconvex domains | `Dirichlet.Average.HolomorphicDomain`: domain-aware characterization, uniqueness, and increasing-domain gluing; local Jordan-domain existence and planar exhaustion remain open |
| Hull-admissible integral domains | `Dirichlet.Average.IntegralDomain`: open node-domain geometry, joint continuation on the native node domain, and recognition of a given continuation on star-convex scalar domains |

`Dirichlet.Beta.Complex`, `Dirichlet.Moments`, and
`Dirichlet.Average.Associated` re-export their topic modules.
`Dirichlet.Real` remains the basic distribution interface, not an umbrella
over its probability corollaries.

Real probability and native complex integration share foundations; neither
basic interface depends on the other. Probability statements about moments,
aggregation, and beta marginals are downstream of the real distribution.
Analytic continuation remains downstream of native complex integration.
The general affine-form convex-hull characterization belongs in
`Dirichlet.Average.Kernel`, not in the T-function application.

## Carlson functions

### R-function analytic construction

`Carlson.R.SingleIntegral` is an umbrella over four steps:

1. `SingleIntegral.Series`: unit-interval definition and near-one series.
2. `SingleIntegral.UnitInterval`: kernel analysis and native representation.
3. `SingleIntegral.Continuation`: unit-interval representation with continued
   Dirichlet parameters.
4. `SingleIntegral.PositiveRay`: positive-ray substitution and representations.

`SlitContinuation` uses the continued unit-interval construction; ray-kernel
arguments use `PositiveRay`. Euler transformation no longer imports the
declaration-free `Contour` placeholder. The contour formula is still a
separate mathematical task.

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
`Pochhammer.Gamma`; their existing `DirichletTransform` names are retained.

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

## What this reorganization does not change

- No Lean or Mathlib upgrade, namespace migration, or change to Lake topology.
- No changes to definitions, theorem assumptions, or treatment of empty index
  types.
- No new mathematical coverage is claimed. See
  [R coverage](Carlson/R/Coverage.md) and [L coverage](Carlson/L/Coverage.md).
- Several-complex-variable theory and the broader Pochhammer support library
  retain their current organization; a future Mathlib contribution can place
  their general results in upstream topic hierarchies.
