# Carlson special functions

A Lean 4 formalization of B. C. Carlson's approach to special functions through integration over the standard simplex with respect to complex Dirichlet densities.
The foundational developments are intended as potential Mathlib contributions.

## Organization

There are seven main directories.

- `ToMathlib/`.
General support that uses Mathlib and the pinned TauCeti, in the namespaces of the Mathlib APIs it
extends: `ToMathlib/Algebra` (submodule and linear-dependence support),
`ToMathlib/Topology` (compactness, path, semicontinuity, and Baire-theorem support),
and `ToMathlib/Analysis` (normed-space, functional-analysis, Taylor-estimate, and integration
support, including the Gamma integral with a complex Laplace parameter).

- `Pochhammer/`.
Support codes. Simplex-independent Pochhammer, gamma/beta and complex-power operations.

- `ComplexAnalysis/`.
The part of single-variable complex analysis that the Dirichlet and Carlson developments use:
holomorphic logarithm branches, Banach-valued primitives and Cauchy theory on simply connected
open domains, curve indices, cycles and the homology form of Cauchy's theorem, exterior paths,
Cauchy estimates and series, holomorphic parameter integrals, and principal powers on the right
half-plane. The files are exact copies of modules of the separate one-variable project
(`lean-CA`), which is their primary source.

- `SeveralComplexVariables/`.
The part of several-complex-variable analysis that the Dirichlet and Carlson developments use:
polydisc Cauchy theory and estimates, analyticity of holomorphic maps, holomorphic parameter
integrals, locally uniform limits, Osgood's theorem, and Hartogs' separate-analyticity
theorem. The files are exact copies of modules of the separate several-variable project
(`lean-SCV`), which is their primary source.

- `StdSimplexMeasure/`.
Coordinates, aggregation, measure, integration, smooth simplex functions, and moment determination.

- `Dirichlet/`.
Real and complex beta functions, Dirichlet measures and densities, moments, averages, and analytic continuation.
`Dirichlet.Transform.Basic` supplies the unique entire regularized transform of a
smooth simplex kernel. Its structural laws and auxiliary-parameter differentiation
are independent of Carlson's affine substitution; Carlson averages specialize this
interface.

- `SimplexMellin/`.
The regularized Dirichlet transform as a transform in its own right, beyond what Carlson's
averages need: face formulas at nonpositive integer parameters, uniqueness, the identification
with the multivariable Mellin transform in simplicial polar coordinates (with its continued
form), inversion on vertical planes, and Plancherel. It builds on `Dirichlet`, which it shares
with `Carlson`; the programme is [DirichletTransformProgram.md](DirichletTransformProgram.md).

- `Carlson/`.
R-polynomials, R/L/S/T functions, and two-variable specializations.
The regularized functions are entire in the Dirichlet parameters: R and L on
principal slit-plane nodes, S on all nodes, and T on its native zero-avoiding
convex-hull domain and on a separately defined principal slit-plane branch.
`Carlson.Normalization` treats ordinary Gamma normalization, exceptional-parameter
residues, and removable transverse parameter slices for all four families, and the
removable singularities of the equal-parameter functions `Γ(β) F(β, …, β; z)/Γ(kβ)`
(Theorems 6.2-6, 6.8-4 and Corollary 6.3-7).

Chapters 5 and 6 of Carlson's book are covered in large part. Beyond the general
average and R-polynomial machinery this includes the operator identity (5.3-4), confluence
with complex exponent (5.10-1), Cauchy representations of averages on `C¹` cycles (5.11-2,
6.3-6) and the contour formula (6.8-7), Carlson's `₂F₀` function with its continuation to the
sector `|ph(-x)| < 3π/2`, error bounds, asymptotic expansion and connection formulas with the
S-function (5.12-4 to 5.12-9), the zero-node limit of T (5.12-2, 5.12-3), the concentration and
growth theorems for R-polynomials (6.2-5, 6.6-2 with a corrected hypothesis and a counterexample
to the printed statement), the S-function with equal parameters (6.9-2), its identification with
Mathlib's confluent hypergeometric and Bessel functions (5.8-6, Kummer's second formula 6.9-6,
selected Bessel identities in §6.9), the quadratic transformations with their hybrid, the arithmetic–geometric
mean and Borchardt's algorithm with Carlson's acceleration (Section 6.10), the associated
Legendre functions of negative order (6.10-18, 6.10-19), the finer equal-parameter
normalization on the full slit domain, and product formulas of Section 6.11 (all
parameters, complex angles). See
`CarlsonCoverage.md` for a section-by-section account
(`CarlsonChapter6Exercises.md` for the Chapter 6 exercises).

`Carlson.Jacobi` develops the monic Jacobi polynomials and their adjoint functions of
the second kind at complex endpoints. Biorthogonality and coefficient extraction hold
on `C¹` cycles, with winding number explicit; coincident endpoints recover Taylor's
formula. Sharp pointwise root-growth limits and ellipse-maxima limits are proved.
The Cauchy-kernel expansion holds on the full domain `μ(x) < μ(y)`, and functions
holomorphic on an elliptic disk have absolutely convergent Jacobi expansions there,
uniformly on compact subsets. These convergence proofs are independent of the saddle-point
asymptotic equivalents of §7.4.

`Carlson.Jacobi.SaddleLaplace` applies the quantitative Laplace estimates to the
actual Jacobi saddle integral. It proves the pointwise second-kind equivalent
`qₙ(z) ∼ C (4/Λ(z))ⁿ`, with `C ≠ 0`, for arbitrary complex parameters and points
off the focal segment, including coincident endpoints. Here
`Λ(z) = (z-r)(1+c)²`, with `c` the principal square root of `(z-s)/(z-r)`, and
`‖Λ(z)‖ = 4μ(z)`. The proof controls the central Gaussian error and the outer
pieces, then cancels the Gamma normalization by comparison with the beta integral.
`Carlson.Jacobi.SaddleUniform` upgrades this to relative convergence uniformly on
every compact set off the fixed focal segment, with one nonzero coefficient
function for the full degree sequence. Joint analyticity of the amplitude gives
the common derivative bound needed for the uniform Laplace estimate.
`Carlson.Jacobi.SaddleJoint` allows both endpoints to vary and proves Theorem
7.4-3 in Carlson's R-average notation, jointly uniformly on compact subsets of
`W`, including coincident square arguments. The parameters are arbitrary complex
numbers, and the coefficient is nonzero throughout `W`.

Rodrigues formulas, weighted representations and orthogonality are available, including
complex segments when `re α, re β > -1`. In this range, the second-kind Jacobi
function has separate upper and lower boundary values, with a principal-value
formula and a symmetric real-axis truncation limit. The boundary formulas extend
to distinct complex endpoints by affine covariance. The reusable segment Plemelj
theorems are in `ToMathlib.Analysis.Integral.CauchyBoundary`.
Gegenbauer and Legendre polynomial addition,
plane-wave and Fourier/Bessel expansions, and Laguerre/Hermite polynomial and second-kind
limits are proved. The Laguerre second-kind limit retains `re(1+β+n) > 0`; the weighted
Laguerre/Hermite representations impose growth bounds also on the highest derivative.
Remaining Chapter 7 work includes the general-parameter polynomial asymptotics
of §7.4, compact-uniform root limits, the Bessel addition theorem of Example 7.7-4, and continued boundary theory
beyond the current orthogonality range. `Carlson.Jacobi.AsymptoticZeros` records a
qualification to the printed ratio definition in Theorem 7.4-2: odd-degree
Chebyshev zeros prevent an unextended quotient from tending to one at the
midpoint. `Carlson.Jacobi.PolynomialSaddle` proves the exact Chebyshev two-term
formula (7.4-1), including cancellation points, and its compact-uniform
dominant-term relative limit on `W`. The general polynomial expansion still
needs an error formulation accounting for zeros. See [CarlsonCoverage.md](CarlsonCoverage.md).

Chapter 8 includes straight-segment and ray integral evaluations with explicit principal
phase and endpoint-convergence conditions; the Schwarz–Christoffel map, its boundary
extension and bijection onto a convex polygon; and the Weierstrass/Jacobi inverses on
rectangles, with their half-periods and differential equations. Doubly periodic
meromorphic continuation is not yet formalized.

The small-variable limit holds for continued complex parameters satisfying
`re(a' - bₖ) > 0`, with right-half-plane nodes and approach, also jointly in the nodes.
The Gauss-function identification is on the unit disk, its boundary limit approaches
1 from inside that disk, and Gauss summation assumes `re(γ-α-β) > 0`.
The associated-function dependence theorem 8.4-3 is proved for fixed arbitrary complex
parameters on slit-plane nodes. Integer log-rational reduction 8.5-1, Table 8.5-1 and
Example 8.5-5 are proved. General reductions 8.5-3/8.5-4, the connection formula (8.3-10),
the full logarithmic expansion of `R_K`, and the wider slit-sector limits remain.
See [CarlsonCoverage.md](CarlsonCoverage.md).

Chapter 9 has the symmetric standard functions `R_F`, `R_G`, `R_H`, `R_K`, `R_E`, `R_L`,
their symmetries and several zero-variable limits. Legendre's `F`, `E`, `Π`, `K` and
complete `E` are defined; `F` and `E` are represented as R-functions and `K` is identified
with `R_K`. Both incomplete and complete `Π` now have R-function representations and
reductions to `R_F`, `R_H` and to `R_K`, `R_L`, respectively. These hold for real arguments
with `k² < 1`, `0 < φ < π/2`, and `n sin² φ < 1` in the incomplete case, and `n < 1`
in the complete case. Two rows each of Tables 9.3-3 and 9.3-4 are proved on the full
complex slit domain, including coincident nodes. The remaining table rows and the
standard-basis reduction of `E` are still missing. The transformation results include:

- Landen's Theorem 9.5-1 for all complex exponents, with positive real source and
  transformed variables, and its ascending/descending algorithms;
- duplication on the slit domain and convergence of Algorithm 9.6-2 for positive
  real initial values;
- addition for positive real variables and the zero-variable form (9.7-17);
- zero-variable duplication and ascending Landen with `s₀ = 0`;
- quartic reduction 9.8-1 when the source and transformed square roots have positive
  real parts, together with a `D = 0` boundary case.

`Carlson.Elliptic.Asymptotic` proves the leading logarithmic equivalents
`R_F(x,y,z) ∼ log(4√z/(√x+√y))/√z` as `z → ∞` for fixed positive `x,y`
(9.2-10), and `R_K(x,y) ∼ log(16x/y)/(π√x)` as `y → 0+` for fixed positive
`x` (8.3-16). The proofs use real integral comparison, elementary `R_C`,
duplication and homogeneity. The full logarithmic series, its complex-sector
extension and additive constant-term limits are not asserted by these equivalents.

The standard-basis independence theorem 9.2-1, the remaining reductions of §9.3, applications §9.4,
algorithmic error estimates, complex duplication iteration, and the practical quartic
integration formulas (9.8-10)–(9.8-13) remain priorities.
See [CarlsonCoverage.md](CarlsonCoverage.md) for detailed coverage.

Dependencies flow from the support libraries and simplex foundations to
`Dirichlet`, then to `Carlson`. The simplex foundation never imports either
application layer; `Dirichlet` never imports `Carlson`. The support libraries never
import the application layers, and remain independent of the simplex foundation.

`ToMathlib` may depend on Mathlib and TauCeti. `ComplexAnalysis` builds on it;
`SeveralComplexVariables` builds on both. The support libraries extend the
corresponding Mathlib namespaces (`Complex`, `MeasureTheory`, `Submodule`, and so on) and
several-variable theory uses the `SeveralComplexVariables` namespace. The real Dirichlet
distribution lives in `ProbabilityTheory`; complex Dirichlet densities, transforms and
averages live in `Dirichlet`; Carlson's special functions live in `Carlson` and
`Carlson.TwoVariable`. The Jacobi and Gegenbauer polynomial layer extends
`Polynomial`, including its identifications with Mathlib's classical families.

Each directory has a matching umbrella module (for `ToMathlib`, the three modules
`ToMathlib.Algebra`, `ToMathlib.Analysis`, and `ToMathlib.Topology`). `Main.lean` imports all of them.
See the [module structure guide](STRUCTURE.md) for the finer topic splits and import paths.
Statements of Carlson's book found false or in need of qualification during the formalization
are listed, with counterexamples and corrections, in [CARLSON_ERRATA.md](CARLSON_ERRATA.md).
A mathematical synopsis addressed to mathematicians starts at [SYNOPSIS.md](SYNOPSIS.md), which
summarizes the whole project and points to one synopsis per library: general algebra, topology
and analysis (`SYNOPSIS_ALGEBRA.md`, `SYNOPSIS_TOPOLOGY.md`, `SYNOPSIS_ANALYSIS.md`), one and
several complex variables (`SYNOPSIS_CA.md`, `SYNOPSIS_SCV.md`), Pochhammer symbols and the
standard simplex (`SYNOPSIS_POCHHAMMER.md`, `SYNOPSIS_STDSIMPLEX.md`), and the target libraries
(`SYNOPSIS_DIRICHLET.md`, `SYNOPSIS_SIMPLEXMELLIN.md`, `SYNOPSIS_CARLSON.md`). Open problems of
the target libraries are collected in [SYNOPSIS_GAPS.md](SYNOPSIS_GAPS.md). The full one- and
several-variable theories are documented in their own projects.

## Dependencies and upstream reuse

The project uses Lean `v4.35.0-rc3`, Mathlib revision
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, and TauCeti revision
`a780c7ad6beb23f60a17351a492d177878020ad5`, matching the companion CA and SCV projects.
Prefer existing results in **Mathlib, then TauCeti, then local code**, preserving hypotheses
and conclusions. Import the particular module, for example
`public import TauCeti.Analysis.Complex.SlitPlane`; `import TauCeti` is not an umbrella.
The shared `.lake` symlink remains in place and this project's outputs use `.lake/build-codes`.

The copied CA and SCV directories contain only the transitive dependency subsets needed here.
Make changes in their primary projects, then synchronize the relevant copies.
See [TauCetiReview.md](TauCetiReview.md) for reuse opportunities and checked replacements,
and [CREDITS.md](CREDITS.md) for attribution.

## Registry statement

[comparator.json](comparator.json) selects **11 Carlson and Dirichlet-average
continuation theorems and one R-function construction** for the proposed Palomar
snapshot. [Statement.lean](Statement.lean) and [Solution.lean](Solution.lean)
contain these claims and 11 additional foundational
theorems. Those supporting theorems are no longer separately selected for
registration. The statement module's broader description of its contents is
not the current Comparator selection. Keeping these declarations and the project
libraries does not presume that their supporting theory is already in Mathlib.

Solution connects the statements to project proofs and never imports the
intentional statement placeholders. See [PALOMAR.md](PALOMAR.md) for proof
locations and validation commands. The preceding submission passed Palomar's
mechanical verification, as reported by the maintainer, but was not offered
registration after editorial review. The narrowed selection and revised
provenance require a new submission. This is not yet a registered result.
The simply connected continuation theorem was added to the selection on 5 October 2026,
after that submission; it has not been through Palomar verification.

### Mathematical scope and research interest

The selected subject is Carlson's analytic theory of Dirichlet averages and its
R/L special functions, not a collection of independent elementary identities.
The construction, native agreement, continuation, differential equations, and
transformations together specify how one family of integral-defined functions
behaves beyond the parameters for which the defining integrals converge.

- `joint_average_continuation` gives a jointly holomorphic continuation in all
  complex Dirichlet parameters and nodes lying in a convex open scalar domain,
  for any function holomorphic there (Carlson 1977, 6.3-6).
- `simply_connected_average_continuation` extends this to simply connected open
  scalar domains: the continuation is holomorphic for all nodes in the domain,
  coincident nodes included, and agrees with the native average whenever the
  whole node convex hull lies in the domain (Carlson 1969, Theorem 8, simply
  connected case; the question raised in Carlson 1977, p. 156).
- `r_joint` and `r_native` characterize the Gamma-regularized R construction by
  joint holomorphy in the exponent, Dirichlet parameters, and principal slit-plane
  nodes, and agreement with the power average. Native agreement requires positive
  real parts of the Dirichlet parameters and the entire node convex hull inside
  the slit plane. `r_euler` and `r_euler_poisson` establish Euler inversion and
  the Euler-Poisson differential equations on the full slit-node domain, with
  no Dirichlet-parameter exclusions.
- `r_first_quadratic` and `r_second_quadratic` give the two regularized
  two-variable transformations, on the branch domain described below.
- `l_joint`, `l_native`, and `l_exponent_derivative` establish joint holomorphy
  of the corresponding L function, agreement with the power-logarithm average
  on the native hull-admissible domain, and existence of the exponent derivative
  of R giving L (Carlson 1987). L is defined by differentiation, but existence
  of that derivative and its integral representation are proved, not assumed.

The intended research audience is mathematicians working on multivariate
hypergeometric functions, complex analytic continuation, and special functions
of applied analysis. The mathematical interest is the unified treatment of
parameter singularities, principal branches, functional relations, and logarithmic
averages within the same analytic family. A serious specialist note could examine
this regularized continuation theory and its branch-sensitive transformation
laws. Carlson's treatments in Chapter 6 of his book and his 1987 research article
provide the source context for that interest. No novelty claim is made: these
are source-based formalizations and adaptations, and their significance is not
asserted merely from the amount or difficulty of Lean code. The foundational
libraries serve this development and remain reusable work toward Mathlib;
their research interest is not asserted as separate registry claims.

### Quadratic transformations: precise relationship to Carlson

The selected formulas adapt Transformation 6.9-3 (1977, p. 161) and
Transformation 6.10-1 (pp. 164–166). Carlson already assumes `Re x > 0` and
`Re y > 0` for the unsquared variables and explicitly allows slit-plane
transformed nodes. Our formulas keep that domain. In particular, `x^2`, `y^2`,
`((x+y)/2)^2`, and `x*y` need not have positive real parts. The broader domain
is relative to our earlier common right-half-plane integral formalization,
not a new node-domain extension beyond Carlson's stated transformations.

The adaptation uses `regR = R / Gamma(sum b)` on the ordinary nonpolar domain
and its analytic continuation elsewhere. Both formulas hold for every complex
`t` and `beta`, with the factor `2^(1-2*beta)*sqrt(pi)/Gamma(beta)` interpreted
using reciprocal Gamma. Carlson's ordinary-R statements impose
`beta + 1/2 ∈ U`, excluding nonpositive integers. The regularized formulas do
not assert finite ordinary-R values at all parameter poles. Their proofs extend
local identities by parameter and joint-node analyticity, paralleling Carlson's
permanence of functional relations and the slit continuation of Section 6.8.
Arbitrary branch components, multiply connected or Riemann-surface continuation,
the contour formula
6.8-7 (proved in the project on `C¹` cycles, but not selected), and complete coverage of the L
article are not claimed.

The simply connected case of Carlson (1969), Theorem 8, is selected as
`simply_connected_average_continuation` (`Dirichlet.Average.SimplyConnected`). For `f`
holomorphic on a simply connected open set `D`, the regularized Dirichlet average continues to
all node tuples in `D`, entire in the Dirichlet parameters. This answers the question Carlson
raises at the bottom of p. 156 of the 1977 book. The proof uses a convex chart from the Riemann mapping
theorem and induction on the number of nodes, not Carlson's contour-adapted branches. The
multiply connected and Riemann-surface cases remain open.

## References

Carlson, B. C. "Special Function of Applied Mathematics." Academic Press, 1977.

Carlson, B. C. "Dirichlet averages of $x^t\log x$."
SIAM Journal on Mathematical Analysis 18, no. 2 (1987): 550-565.
