/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basic
public import Carlson.Jacobi.Derivative
public import Carlson.Jacobi.Basis
public import Carlson.Jacobi.Carlson
public import Carlson.Jacobi.Normalization
public import Carlson.Jacobi.Endpoint
public import Carlson.Jacobi.DifferentialEquation
public import Carlson.Jacobi.Weight
public import Carlson.Jacobi.RealOrthogonality
public import Carlson.Jacobi.Expansion
public import Carlson.Jacobi.Rodrigues
public import Carlson.Jacobi.Orthogonality
public import Carlson.Jacobi.Legendre
public import Carlson.Jacobi.Chebyshev
public import Carlson.Jacobi.Gegenbauer
public import Carlson.Jacobi.GegenbauerDerivative
public import Carlson.Jacobi.BetaAverage
public import Carlson.Jacobi.AlgebraicExpansion
public import Carlson.PolynomialAverage
public import Carlson.Jacobi.ComplexAverage
public import Carlson.Jacobi.Endpoints
public import Carlson.Jacobi.FiniteExpansion
public import Carlson.Jacobi.EndpointBridge
public import Carlson.Jacobi.SecondKind
public import Carlson.Jacobi.Contour
public import Carlson.Jacobi.SeriesCoefficients
public import Carlson.Jacobi.Pearson
public import Carlson.Jacobi.SecondKindEquation
public import Carlson.Jacobi.SecondKindInfinity
public import Carlson.Jacobi.SecondKindIntegral
public import Carlson.Jacobi.BoundaryKernel
public import Carlson.Jacobi.SecondKindBoundary
public import Carlson.Jacobi.Ellipse
public import Carlson.Jacobi.ComplexSecondKind
public import Carlson.Jacobi.ComplexOrthogonality
public import Carlson.Jacobi.ComplexRodrigues
public import Carlson.Jacobi.AnalyticRodrigues
public import Carlson.Jacobi.WeightedIntegral
public import Carlson.Jacobi.ComplexWeightedIntegral
public import Carlson.Jacobi.Norm
public import Carlson.Jacobi.Raising

/-!
# Jacobi polynomials and adjoint functions in Carlson's Chapter 7

The polynomial theory of Chapter 7 begins with standard Jacobi polynomials over a
commutative rational algebra. Their shifted coordinate is `Pₙ⁽α,β⁾(1-2X)`.
The Carlson bridge identifies their complex evaluations with the two-node
Pochhammer numerator and relates the standard and monic normalizations. Polynomial
identities include exceptional parameters; degree and basis assertions state the
necessary nonvanishing hypotheses separately. Finite expansions at arbitrary complex
endpoints use continued Dirichlet averages of derivatives. The adjoint second-kind
functions are holomorphic off the endpoint segment and biorthogonal to the
polynomials on `C¹` cycles avoiding that segment, with the winding number as a
factor; coincident endpoints recover Taylor theory. Contour coefficients recover
the coefficients of uniformly convergent Jacobi series and prove their uniqueness
on cycles of nonzero index. This does not yet establish existence of such expansions.
Their parameter-shift differentiation rule and adjoint differential equation hold
off the segment, including exceptional parameters and coincident endpoints.
Their leading normalization at infinity holds in every complex direction. For complex
parameters with real parts greater than `-1`, Cauchy-integral representations yield symmetric
boundary jumps at interior points of any nondegenerate complex segment.
Real-variable Rodrigues formulas, weighted coefficient integrals for `Cⁿ` functions
and squared norms complement the polynomial expansion theory. Complex Rodrigues
formulas hold on the principal branch domain; complex weighted integrals give
bilinear orthogonality and squared integrals. Confocal elliptic disks supply the
geometry for future convergence theorems. Gegenbauer derivatives follow from Jacobi
derivatives, with analytic continuation covering exceptional parameters.

## Main results

* `Polynomial.iterate_derivative_jacobi`: all derivative orders by parameter shifts.
* `Polynomial.jacobi_differential_equation`: the Jacobi differential equation.
* `Polynomial.sum_algebraicJacobiCoefficient`: finite expansions over a
  characteristic-zero field at admissible parameters.
* `Carlson.TwoVariable.sum_carlsonJacobiCoefficient`: complex finite expansions
  at arbitrary endpoints, including coincident endpoints.
* `Carlson.TwoVariable.circleIntegral_jacobiOn_mul_jacobiSecondKind`: circle
  biorthogonality throughout the admissible complex parameter range.
* `Carlson.TwoVariable.cycleIntegral_jacobiOn_mul_jacobiSecondKind`: the extension
  to arbitrary `C¹` cycles avoiding the endpoint segment, with the index explicit.
* `Carlson.TwoVariable.cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq`: contour
  independence for holomorphic functions under the homology condition.
* `Carlson.TwoVariable.jacobiContourCoefficient_eq_of_tendstoUniformlyOn`: extraction
  of coefficients of a Jacobi series uniformly convergent on a cycle.
* `Carlson.TwoVariable.jacobiSeries_coefficients_unique`: uniqueness of these
  coefficients when the cycle has nonzero index.
* `Carlson.TwoVariable.analyticAt_jacobiSecondKind_comp`: joint analytic dependence
  on parameters, endpoints and the exterior evaluation point.
* `Carlson.TwoVariable.jacobiSecondKind_differential_equation`: the adjoint Jacobi
  equation for arbitrary endpoints and complex parameters.
* `Carlson.TwoVariable.hasDerivAt_jacobiSecondKind`: differentiation by an index
  increase and simultaneous parameter decreases.
* `Carlson.TwoVariable.tendsto_pow_mul_jacobiSecondKind`: leading normalization
  at infinity whenever the Gamma factor at the given index is regular.
* `Carlson.TwoVariable.jacobiSecondKind_eq_complexCauchyIntegral`: the weighted
  Cauchy representation off the unit segment, for `re α, re β > -1`.
* `Carlson.TwoVariable.tendsto_jacobiSecondKind_sub_complex_affine`: the symmetric
  boundary jump for these complex parameters and distinct complex endpoints.
* `Carlson.TwoVariable.exists_jacobiClosedEllipseDisk_subset`: every open
  neighborhood of the focal segment contains a nondegenerate closed elliptic disk.
* `Polynomial.integral_mul_shiftedJacobi_eq_zero`: weighted orthogonality against
  every lower-degree polynomial in the full real parameter range.
* `Polynomial.iteratedDeriv_shiftedJacobiWeight`: analytic Rodrigues formula for
  arbitrary real parameters on the open unit interval.
* `Polynomial.iteratedDeriv_complexJacobiWeight`: Rodrigues formula for all complex
  parameters wherever both `z` and `1-z` lie in the principal slit plane.
* `Polynomial.integral_complexJacobiWeight_mul_shiftedJacobi_eq_zero`: bilinear
  orthogonality on the unit interval for `re α, re β > -1`.
* `Polynomial.integral_complexJacobiWeight_sq`: the corresponding squared integral
  as a Pochhammer factor times a Gamma quotient.
* `Polynomial.factorial_mul_integral_mul_shiftedJacobi_of_contDiffOn`: weighted
  coefficient integrals for `Cⁿ` functions on the closed interval.
* `Polynomial.integral_shiftedJacobi_sq_eq_beta`: squared norms throughout the
  real orthogonality range, including all degree-zero cases.
* `Polynomial.shiftedJacobiCoefficient_eq_integral_div_norm`: equality of
  derivative-average and orthogonal projection coefficients.
* `Polynomial.integral_shiftedLegendre_sq`: the shifted Legendre norm by specialization.
* `Polynomial.shiftedJacobi_rodrigues_nat`: polynomial Rodrigues formula for
  nonnegative integer parameters over a commutative rational algebra.
* `Polynomial.shiftedJacobi_zero_zero`, `Polynomial.jacobi_neg_half_eq_chebyshev_T`,
  `Polynomial.jacobi_half_eq_chebyshev_U`: identification with Mathlib's Legendre
  and Chebyshev polynomials.
* `Polynomial.pochhammer_mul_gegenbauer`: the denominator-free Gegenbauer/Jacobi relation.
* `Polynomial.iterate_derivative_gegenbauer`: derivatives of every order at all
  complex parameters, derived from Jacobi derivatives.

Branches adapted to contours crossing the endpoint segment,
separate second-kind boundary values and principal-value formulas, large-degree
asymptotics, the Gegenbauer addition theorem,
existence and convergence of infinite Jacobi expansions, and the Laguerre/Hermite
limits remain further work.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7, especially §§7.1–7.3, 7.5 and 7.8.
-/
