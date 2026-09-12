# Carlson special functions

A Lean 4 formalization of B. C. Carlson's approach to special functions through
integration over the standard simplex with respect to complex Dirichlet densities.
The foundational developments are intended as potential Mathlib contributions.

## Organization

| Directory | Scope |
| --- | --- |
| `StdSimplexMeasure/` | Coordinates, aggregation, measure, integration, smooth simplex functions, and moment determination |
| `Dirichlet/` | Real and complex beta functions, Dirichlet measures and densities, moments, averages, and analytic continuation |
| `Carlson/` | R-polynomials, R/S/T functions, and two-variable specializations |
| `Pochhammer/` | Simplex-independent Pochhammer, gamma/beta, complex-power, and Mellin support |
| `SeveralComplexVariables/` | Simplex-independent several-complex-variable analysis |

Dependencies flow from the support libraries and simplex foundations to
`Dirichlet`, then to `Carlson`. The simplex foundation never imports either
application layer; `Dirichlet` never imports `Carlson`. The two support libraries
never import the simplex or application layers.

Each directory has a matching umbrella module. `Main.lean` imports all five.
Carlson's reference chapters are in `Carlson/References/`.

### Dirichlet layers

The real probability distribution and complex integral interface share analytic
foundations; neither interface imports the other. Analytic dependence and
continuation are downstream of the native complex integrals.

| Module | Role |
| --- | --- |
| `StdSimplexMeasure.Interior` | Positive-coordinate simplex interior, measurability, permutation invariance, and almost-everywhere membership |
| `Dirichlet.Integral.Real` | Nonnegative and real monomial integrals, beta normalization, and real integrability |
| `Dirichlet.Integral.Complex` | Absolutely convergent complex monomial integrals and logarithmic majorants |
| `Dirichlet.Real` | Real probability density and measure, including vector-valued expectations |
| `Dirichlet.Complex` | Native regularized and normalized complex densities and integral functionals |
| `Dirichlet.Bridge` | Real/complex compatibility for densities and arbitrary integrands |
| `Dirichlet.Complex.Analytic` | Parameter analyticity on the absolute-convergence domain |
| `Dirichlet.Transform` | Continuation beyond the convergence domain for suitable test functions |

Import `Dirichlet.Complex.Analytic` when using `regDirichletIntegral_analyticOn`,
`analyticOnNhd_prod_invGamma`, or `hasFDerivAt_mvBetaMonomial`; these are no longer
exported by the basic `Dirichlet.Complex` module. The `Dirichlet` umbrella still
exports all layers. Existing declaration names, including historical namespaces,
are preserved.

At positive real parameters, `complexDirichletIntegral_ofReal` identifies the
normalized complex integral with a probability expectation, while
`regDirichletIntegral_ofReal` includes the reciprocal Gamma factor of the total
parameter. Both statements concern native, totalized Bochner integrals, not
analytic continuations. The Carlson-average compatibility theorem is now a
specialization of this general bridge.

## Import migration

Declaration names and mathematical namespaces are preserved; import paths changed.
There are no application-module compatibility shims under `StdSimplexMeasure`.

| Previous import | New import |
| --- | --- |
| `StdSimplexMeasure.Dirichlet` | `Dirichlet.Real` |
| `StdSimplexMeasure.ComplexDirichlet` | `Dirichlet.Complex` |
| `StdSimplexMeasure.MvBeta` | `Dirichlet.Beta.Complex` |
| `StdSimplexMeasure.DirichletMoments` | `Dirichlet.Moments` |
| `StdSimplexMeasure.DirichletTransform` | `Dirichlet.Transform` |
| `StdSimplexMeasure.DirichletIntegrationByParts` | `Dirichlet.IntegrationByParts` |
| `StdSimplexMeasure.CarlsonDirichletAverage.*` | `Dirichlet.Average.*` |
| `StdSimplexMeasure.CarlsonRPolynomial.*` | `Carlson.RPolynomial.*` |
| `StdSimplexMeasure.CarlsonR.*` | `Carlson.R.*` |
| `StdSimplexMeasure.CarlsonS` / `CarlsonT` | `Carlson.S` / `Carlson.T` |
| `StdSimplexMeasure.CarlsonTwoVariable.*` | `Carlson.TwoVariable.*` |
| `StdSimplexMeasure.BetaIntegral` | `Pochhammer.BetaIntegral` |
| `StdSimplexMeasure.ComplexPowMeasurable` | `Pochhammer.ComplexPowMeasurable` |
| `StdSimplexMeasure.IncompleteMellin` | `Pochhammer.IncompleteMellin` |
| `StdSimplexMeasure.AnalyticUniqueness` | `SeveralComplexVariables.AnalyticUniqueness` |

Mixed modules were split: real multivariate beta definitions are in
`Dirichlet.Beta.Real`, polynomial transforms in `Dirichlet.Polynomial`, general
simplex calculus in `StdSimplexMeasure.Smooth`, moment determination in
`StdSimplexMeasure.MomentDetermination`, positive-axis complex powers in
`Pochhammer.PositiveCpow`, and R-polynomial power-series specializations in
`Carlson.RPolynomial.PowerSeries`.

## Building

Run `lake build` from the repository root. The existing `.lake` symlink to the
local-disk cache is intentional and must not be replaced or retargeted.
