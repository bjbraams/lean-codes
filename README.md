# Carlson special functions

A Lean 4 formalization of B. C. Carlson's approach to special functions through integration over the standard simplex with respect to complex Dirichlet densities.
The foundational developments are intended as potential Mathlib contributions.

## Organization

There are five main directories.

- `Pochhammer/`.
Support codes. Simplex-independent Pochhammer, gamma/beta and complex-power operations.

- `SeveralComplexVariables/`.
Support codes and more for simplex-independent several-complex-variable analysis.

- `StdSimplexMeasure/`.
Coordinates, aggregation, measure, integration, smooth simplex functions, and moment determination.

- `Dirichlet/`.
Real and complex beta functions, Dirichlet measures and densities, moments, averages, and analytic continuation.

- `Carlson/`.
R-polynomials, R/L/S/T functions, and two-variable specializations.

Dependencies flow from the support libraries and simplex foundations to
`Dirichlet`, then to `Carlson`. The simplex foundation never imports either
application layer; `Dirichlet` never imports `Carlson`. The two support libraries
never import the simplex or application layers.

Each directory has a matching umbrella module. `Main.lean` imports all five.
See the [module structure guide](STRUCTURE.md) for the finer topic splits and import paths.

## Registry statement

[comparator.json](comparator.json) selects **10 Carlson and Dirichlet-average
continuation theorems and one R-function construction** for the proposed Palomar
snapshot. [Statement.lean](Statement.lean) and [Solution.lean](Solution.lean)
remain unchanged: they contain these claims and 11 additional foundational
theorems. Those supporting theorems are no longer separately selected for
registration. The statement module's broader description of its contents is
not the current Comparator selection. Keeping these declarations and all five
libraries does not presume that their supporting theory is already in Mathlib.

Solution connects the statements to project proofs and never imports the
intentional statement placeholders. See [PALOMAR.md](PALOMAR.md) for proof
locations and validation commands. The preceding submission passed Palomar's
mechanical verification, as reported by the maintainer, but was not offered
registration after editorial review. The narrowed selection and revised
provenance require a new submission. This is not yet a registered result.

### Mathematical scope and research interest

The selected subject is Carlson's analytic theory of Dirichlet averages and its
R/L special functions, not a collection of independent elementary identities.
The construction, native agreement, continuation, differential equations, and
transformations together specify how one family of integral-defined functions
behaves beyond the parameters for which the defining integrals converge.

- `joint_average_continuation` gives a jointly holomorphic continuation in all
  complex Dirichlet parameters and nodes lying in a convex open scalar domain,
  for any function holomorphic there (Carlson 1977, 6.3-6).
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
general nonconvex simply connected average continuation, the contour formula
6.8-7, and complete coverage of the L article are not claimed.

## References

Carlson, B. C. "Special Function of Applied Mathematics." Academic Press, 1977.

Carlson, B. C. "Dirichlet averages of $x^t\log x$."
SIAM Journal on Mathematical Analysis 18, no. 2 (1987): 550-565.
