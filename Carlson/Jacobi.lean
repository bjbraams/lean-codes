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
public import Carlson.Jacobi.SecondKindBounds
public import Carlson.Jacobi.SecondKindRayBounds
public import Carlson.Jacobi.SecondKindSeries
public import Carlson.Jacobi.PolynomialBounds
public import Carlson.Jacobi.KernelSeries
public import Carlson.Jacobi.CauchyKernel
public import Carlson.Jacobi.SaddleGeometry
public import Carlson.Jacobi.EllipseCoordinates
public import Carlson.Jacobi.AnalyticExpansion
public import Carlson.Jacobi.ComplexSecondKind
public import Carlson.Jacobi.SecondKindPlemelj
public import Carlson.Jacobi.ComplexOrthogonality
public import Carlson.Jacobi.ComplexRodrigues
public import Carlson.Jacobi.AnalyticRodrigues
public import Carlson.Jacobi.WeightedIntegral
public import Carlson.Jacobi.Norm
public import Carlson.Jacobi.Raising
public import Carlson.Jacobi.Recurrence
public import Carlson.Jacobi.PolynomialGrowth
public import Carlson.Jacobi.SecondKindSaddle
public import Carlson.Jacobi.SaddleLaplace
public import Carlson.Jacobi.SaddleUniform
public import Carlson.Jacobi.SaddleJoint
public import Carlson.Jacobi.AsymptoticZeros
public import Carlson.Jacobi.PolynomialSaddle
public import Carlson.Jacobi.EllipseContour
public import Carlson.Jacobi.EllipticExpansion
public import Carlson.Jacobi.GrowthLimits
public import Carlson.Jacobi.SecondKindLimits
public import Carlson.Jacobi.GrowthMaxima
public import Carlson.Jacobi.PlaneWave
public import Carlson.Jacobi.SegmentOrthogonality
public import Carlson.Jacobi.EndpointRodrigues
public import Carlson.Jacobi.Laguerre
public import Carlson.Jacobi.LaguerreRepresentation
public import Carlson.Jacobi.LaguerreSecondKind
public import Carlson.Jacobi.HermiteSecondKind
public import Carlson.Jacobi.GegenbauerAddition
public import Carlson.Jacobi.ChebyshevSecondKind
public import Carlson.Jacobi.Bessel
public import Carlson.Jacobi.Hermite
public import Carlson.Jacobi.GegenbauerProduct
public import Carlson.Jacobi.HermiteRepresentation
public import Carlson.Jacobi.EllipseCoefficient
public import Carlson.Jacobi.FourierCosine

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
on cycles of nonzero index. Geometric bounds and polynomial approximation establish
expansion existence for holomorphic functions on disks under sufficient separation
conditions. Every entire function has an absolutely and locally uniformly convergent
Jacobi expansion throughout the plane at admissible total parameters, with coefficients
computed on any fixed index-one cycle off the segment.
Their parameter-shift differentiation rule and adjoint differential equation hold
off the segment, including exceptional parameters and coincident endpoints.
Their leading normalization at infinity holds in every complex direction. Second-kind
series with geometrically bounded coefficients converge locally uniformly, with
holomorphic sum, wherever distance from the segment exceeds the coefficient growth
rate. These sufficient distance bounds apply to arbitrary complex parameters and
endpoints. The three-term recurrence of Exercise 7.1-6 is a small perturbation of a
constant-coefficient recurrence whose dominant characteristic root has modulus equal to the
elliptic mean radius, so `‖pₙ(x)‖ ≤ C (ρ + ε)ⁿ` on closed elliptic disks. Deforming the Euler
integral of the second-kind functions onto Carlson's saddle curve, by a real change of
variables and the identity theorem, gives `‖qₙ(y)‖ ≤ C (1/σ + ε)ⁿ` on closed elliptic
exteriors. Consequently the Cauchy-kernel identity holds on Carlson's full domain
`μ(x) < μ(y)`, and every function holomorphic on an open elliptic disk is the sum of its
Jacobi series there, with coefficients computed on any confocal ellipse inside the disk.
Analytic continuation across the pole of the Cauchy kernel, a recurrence for the second-kind
functions derived from the polynomial one, and elementary dichotomies for perturbed
recurrences give the growth limits `‖pₙ(x)‖^{1/n} → μ(x)` and `‖qₙ(y)‖^{1/n} → 1/μ(y)` off the
segment, and with them the ellipses of convergence of Jacobi series of both kinds.
The separate Laplace argument in `SaddleLaplace` gives the pointwise second-kind
asymptotic `qₙ(z) ∼ C (4/Λ(z))ⁿ`, with `C ≠ 0` and `‖Λ(z)‖ = 4μ(z)`, for arbitrary
complex parameters and points off the segment. Its compact-uniform version remains open. The
plane-wave expansion, orthogonality on arbitrary complex segments, and the Laguerre and
Hermite limits with their orthogonality relations complete the main applications. For complex
parameters with real parts greater than `-1`, Cauchy-integral representations yield separate
upper and lower boundary values at interior points of any nondegenerate complex segment.
On the unit segment, their common principal-value term is also the limit of symmetric
real-axis truncations.
Real-variable Rodrigues formulas, weighted coefficient integrals for `Cⁿ` functions
and squared norms complement the polynomial expansion theory. Complex Rodrigues
formulas hold on the principal branch domain; complex weighted integrals give
bilinear orthogonality and squared integrals. At arbitrary complex endpoints, Rodrigues'
formula holds on the principal branch, and the coefficients of a Jacobi series on an
elliptic disk are continued Dirichlet averages of the derivatives of the function
(Carlson's formula 7.6-8). The Laguerre and Hermite polynomials satisfy Rodrigues formulas
and weighted representations obtained by repeated integration by parts. Gegenbauer
derivatives follow from Jacobi derivatives, with analytic continuation covering
exceptional parameters.

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
* `Carlson.TwoVariable.exists_geometric_bound_jacobiOn`: geometric degree bounds
  uniform on compact sets.
* `Carlson.TwoVariable.tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind`: uniform
  convergence of the candidate kernel series on sufficiently separated product sets.
* `Polynomial.eval_jacobiOn_three_term`: Carlson's monic three-term recurrence.
* `Carlson.TwoVariable.exists_bound_norm_eval_jacobiOn_of_le`: sharp growth of the
  polynomials on closed elliptic disks.
* `Carlson.TwoVariable.integral_jacobiMobiusIntegrand_eq`: deformation of the Euler integral
  onto the saddle curve.
* `Carlson.TwoVariable.exists_bound_jacobiSecondKind_exterior`: sharp decay of the
  second-kind functions on closed elliptic exteriors.
* `Carlson.TwoVariable.hasSum_jacobiOn_mul_jacobiSecondKind`: Lemma 7.6-1 on its full domain.
* `Carlson.TwoVariable.hasSum_jacobiContourCoefficient_jacobiEllipseCycle`: Theorem 7.6-2 on
  open elliptic disks.
* `Carlson.TwoVariable.tendsto_norm_eval_jacobiOn_rpow`,
  `Carlson.TwoVariable.tendsto_norm_jacobiSecondKind_rpow`: Theorem 7.5-1.
* `Carlson.TwoVariable.not_summable_jacobiOn`, `Carlson.TwoVariable.not_tendsto_jacobiSecondKind`:
  divergence outside the ellipses of convergence (Theorem 7.5-3).
* `Carlson.TwoVariable.exists_jacobiSecondKind_three_term`: the second-kind recurrence.
* `Carlson.TwoVariable.jacobiContourCoefficient_eq_of_hasSum`: uniqueness of Jacobi expansions
  from boundedness at one point.
* `Carlson.TwoVariable.hasSum_exp_jacobiOn`: the plane-wave expansion (Example 7.7-1).
* `Carlson.TwoVariable.jacobiSegmentIntegral_jacobiOn_mul_jacobiOn`: orthogonality on a
  complex segment (Theorem 7.8-3).
* `Carlson.TwoVariable.jacobiContourCoefficient_jacobiEllipseCycle_eq_average`: the
  coefficient formula (7.6-8) on confocal ellipses.
* `Carlson.TwoVariable.tendsto_jacobiOnMax_rpow`,
  `Carlson.TwoVariable.tendsto_jacobiSecondKindMax_rpow`: Theorem 7.5-2.
* `Carlson.TwoVariable.hasSum_fourier_cosine`: the Fourier cosine expansion (Example 7.7-2).
* `Carlson.TwoVariable.iteratedDeriv_sub_cpow_mul_sub_cpow`: Rodrigues' formula (7.8-1) at
  arbitrary complex endpoints.
* `Carlson.TwoVariable.integral_mul_monicLaguerre_mul_cpow_mul_exp`,
  `Carlson.TwoVariable.integral_mul_monicHermite_mul_exp`: Theorems 7.9-3 and 7.10-3.
* `Carlson.TwoVariable.tendsto_eval_jacobiOn_monicLaguerre`,
  `Carlson.TwoVariable.integral_monicLaguerre_mul_monicLaguerre`: Theorems 7.9-1 and 7.9-4.
* `Carlson.tendsto_laguerreSecondKind`, `Carlson.tendsto_norm_regCarlsonS_pair_neg_atTop`: the
  Laguerre function of the second kind as a limit (7.9-4) and Theorem 7.9-5.
* `Carlson.tendsto_hermiteSecondKind`: the Hermite function of the second kind as a limit (7.10-3).
* `Carlson.TwoVariable.gegenbauer_addition`, `Carlson.TwoVariable.legendre_addition`: the addition
  theorems 7.3-1 and (7.3-11).
* `Carlson.regCarlsonDirichletAverage_chebyshev`: the Chebyshev function of the second kind
  in closed form (Lemma 7.4-1).
* `Carlson.TwoVariable.hasSum_exp_I_mul_mul_legendre`,
  `Carlson.TwoVariable.hasSum_zpow_mul_besselJ`: the Bessel expansions of Section 7.7, including
  the generating function of the Bessel coefficients.
* `Carlson.TwoVariable.tendsto_eval_jacobiOn_monicHermite`,
  `Carlson.TwoVariable.gaussianFunctional_monicHermite_mul_monicHermite`: Theorems 7.10-1 and
  7.10-4.
* `Carlson.TwoVariable.exists_radius_uniform_cauchyKernel`: the Cauchy-kernel
  identity and uniform convergence on initial product domains.
* `Carlson.TwoVariable.eqOn_cauchyKernel_of_tendstoLocallyUniformlyOn`: continuation
  to an elliptic exterior once local uniform convergence there is established.
* `Carlson.TwoVariable.jacobiEllipseRadius_jacobiJoukowski`: the circular coordinate
  modulus equals Carlson's elliptic mean radius.
* `Carlson.TwoVariable.isPreconnected_jacobiEllipse_exterior`: connectedness of
  the exterior convergence domains.
* `Carlson.TwoVariable.hasSum_jacobiContourCoefficient_on_ball`: expansion existence
  under sufficient disk and contour-separation conditions.
* `Carlson.TwoVariable.hasSum_jacobiContourCoefficient_of_entire`: Jacobi expansions
  of entire functions at all complex points.
* `Carlson.TwoVariable.tendstoLocallyUniformlyOn_sum_jacobiContourCoefficient_of_entire`:
  local uniform convergence of those expansions throughout the plane.
* `Carlson.TwoVariable.summable_norm_mul_jacobiSecondKind_on_ray`: second-kind
  series converge at the elliptic upper rate on either exterior focal ray.
* `Carlson.TwoVariable.exists_isEquivalent_jacobiSecondKind_geometric`: the pointwise
  second-kind asymptotic with a nonzero coefficient, for all complex parameters.
* `Carlson.TwoVariable.exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric`:
  the relative second-kind equivalent uniformly on compact sets off the focal
  segment, for arbitrary complex parameters and fixed endpoints, including coincident endpoints.
* `Carlson.TwoVariable.exists_tendstoUniformlyOn_carlsonR_secondKind_div`: Theorem 7.4-3,
  jointly uniform on compact subsets of `W`, for arbitrary complex parameters and
  including coincident square arguments.
* `Carlson.TwoVariable.carlsonRPolynomial_chebyshev`: exact two-term formula (7.4-1),
  including cancellation points; `tendstoUniformlyOn_carlsonRPolynomial_chebyshev_div`
  gives the dominant-term relative limit uniformly on compact subsets of `W`.
* `Carlson.TwoVariable.carlson_polynomial_two_saddle_ratio_counterexample`:
  odd-degree Chebyshev zeros obstruct the literal unextended ratio interpretation
  of Theorem 7.4-2 at `(x,y) = (1,I)`; a formulation accounting for zeros is needed.
* `Carlson.TwoVariable.norm_integral_jacobiSaddleKernel_tail_le`: explicit geometric
  decay of the integral outside a central saddle interval.
* `Carlson.TwoVariable.exists_jacobiEulerSaddle_bound`: the complex saddle curve
  has the required geometric bound.
* `Carlson.TwoVariable.norm_jacobiSecondKind_add_le`: degree-dependent uniform
  bounds from the Euler integral at sufficiently large degrees.
* `Carlson.TwoVariable.tendstoLocallyUniformlyOn_sum_jacobiSecondKind`: local uniform
  convergence of second-kind series under geometric coefficient bounds.
* `Carlson.TwoVariable.analyticOnNhd_tsum_jacobiSecondKind`: holomorphy of their sum
  on the sufficient distance-based convergence region.
* `Carlson.TwoVariable.jacobiSecondKind_eq_complexCauchyIntegral`: the weighted
  Cauchy representation off the unit segment, for `re α, re β > -1`.
* `Carlson.TwoVariable.tendsto_jacobiSecondKind_sub_complex_affine`: the symmetric
  boundary jump for these complex parameters and distinct complex endpoints.
* `Carlson.TwoVariable.tendsto_jacobiSecondKind_upper_affine` and
  `Carlson.TwoVariable.tendsto_jacobiSecondKind_lower_affine`: separate perpendicular
  boundary limits with the normalized principal-value term.
* `Carlson.TwoVariable.tendsto_jacobiSecondKind_principalValue`: the normalized
  symmetric real-axis truncation limit on the unit segment.
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

Branches adapted to contours crossing the endpoint segment, boundary values outside
the integrable-weight range and endpoint finite parts, the polynomial asymptotics
of §7.4 at general parameters with an error formulation accounting for zeros,
compact-uniform root limits, and the Bessel addition
theorem of Example 7.7-4 remain further work.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
-/
