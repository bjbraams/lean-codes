# Carlson (1977), Chapter 7: exercises

Status of the exercises of Chapter 7 of B. C. Carlson, *Special Functions of Applied
Mathematics* (pp. 221–230), against the Lean sources. Chapter 7 theorems and formulas are
tracked in [CarlsonCoverage.md](CarlsonCoverage.md); the Chapter 6 exercises
deferred to this chapter are listed in [CarlsonChapter6Exercises.md](CarlsonChapter6Exercises.md).

Notation as in the coverage file: `pₙ = jacobiOn α β r s n` (monic, foci `r, s`),
`qₙ = jacobiSecondKind α β r s n`. R-polynomial identities are stated for the Pochhammer
numerator `Nₙ = (c)ₙ Rₙ` where that removes exceptional parameters.

Legend:
- **Proved**: the cited declaration states the exercise, possibly in numerator form.
- **Partial**: a closely related or weaker result is proved; what is missing is noted.
- **Open**: not yet formalized.
- **Applied**: a physical application, not targeted.

| Exercise | Status | Lean / remark |
| --- | --- | --- |
| 7.1-1 | Proved | `carlsonRPolynomialNumerator₂_jacobi_eq_sum` (numerator form) |
| 7.1-2 | Proved | `hasSum_bateman` (numerator form; `(1 + α + β + n)ₙ Rₙ = (-1)ⁿ Nₙ`) |
| 7.1-3 | Proved | `factorial_mul_eval_jacobi`; the `₂F₁` forms follow from 6.5-2 |
| 7.1-4 | Open | `Q_n^{(α,β)}` as an R-function |
| 7.1-5 | Proved | `jacobiOn_eq_sum_monomial`, `hasSum_jacobiSecondKind_laurent` (for `\|y\| > \|r\|, \|s\|`, all parameters) |
| 7.1-6 | Proved | `jacobiOn_three_term`; second kind: `jacobiSecondKind_three_term` at every degree and `eval_jacobiOn_one_mul_jacobiSecondKind_zero` (the case `q₋₁ = 1`), when `α + β + 1` is not a nonpositive integer; `exists_jacobiSecondKind_three_term` for large degrees in general |
| 7.1-7 | Proved | `christoffel_second_summation` (`α + β + 1` regular) |
| 7.1-8 | Proved | `jacobi_differential_equation`, `jacobiSecondKind_differential_equation` |
| 7.1-9 | Proved | `hasSum_zeroFOne_mul_zeroFOne` (for `δ, 2δ - 1 ∉ -ℕ`) |
| 7.1-10 | Proved | `hasSum_besselJ_zero_mul_besselI_zero` |
| 7.1-11 | Proved | `jacobiOn_casoratian` (`α + β + 1` regular) |
| 7.1-12 | Proved | `factorial_mul_eval_gegenbauer_two_mul_cos_half`, `factorial_mul_eval_gegenbauer_two_mul_add_one_cos_half` (division-free numerator form) |
| 7.1-13 | Open | Appell `F₄` as a Jacobi series |
| 7.2-1 | Proved | `circleIntegral_gegenbauer_mul_jacobiSecondKind` (circle contour; also assumes `ν` and `2ν` are not nonpositive integers) |
| 7.2-2 | Proved | `affine_pow_eq_sum_jacobiOn` |
| 7.3-1 | Proved | `unsold` |
| 7.3-2 | Proved | `hasSum_inv_dist_spherical` |
| 7.4-1 | Proved | `carlsonRPolynomial_chebyshevU` (`xy ≠ 0`), `regCarlsonDirichletAverage_chebyshevU` (on `W`) |
| 7.4-2 – 7.4-4 | Open | asymptotics; the polynomial parts meet the zeros obstruction of `AsymptoticZeros` |
| 7.5-1 | Proved | `exists_bound_norm_eval_jacobiOn`, `tendsto_norm_eval_jacobiOn_rpow` |
| 7.5-2 | Partial | explicit bounds `exists_bound_norm_eval_jacobiOn_of_le` |
| 7.6-1 | Open | Cauchy formula in the outer region (Jordan curve) |
| 7.6-2 | Proved | `hasSum_gegenbauer_expansion` (for `re (ν + 1/2) > 0`, so that `F⁽ⁿ⁾` is the native average) |
| 7.6-3, 7.6-4 | Open | Gegenbauer product and Laurent expansions |
| 7.7-1 | Proved | `hasSum_exp_I_mul_besselJ_gegenbauer` (prefactor `(λ/2)^{-ν}`; `ν` Gamma-regular, `re (ν + 1/2) > 0`); regularized form `hasSum_exp_I_mul_gegenbauer` |
| 7.7-2 | Proved | `hasSum_neumann` (`(y/2)^ν` form, `y ≠ 0`; `ν` Gamma-regular, `re (ν + 1/2) > 0`), from Sonine's formula at `x = 0` |
| 7.7-3 | Proved | `two_pi_mul_besselJ_eq_integral`, `two_pi_mul_besselJ_eq_integral_cos` |
| 7.7-5 | Proved | `hasSum_regularizedHGFun_add` (regularized `₀F₁`, `c = ν + 1` with `re (c - 1/2) > 0`), from Gegenbauer's addition theorem at `x = 0` |
| 7.7-6 | Proved | `hasSum_besselJ_zero_addition` (`A, B ≠ 0`) |
| 7.7-7 | Proved | `hasSum_besselJ_gegenbauer_sin_half` (`A ≠ 0`, `sin (θ/2) ≠ 0`; prefactors `(A sin (θ/2))^{-ν}`) |
| 7.7-8 | Applied | magnetic dipole |
| 7.7-9 – 7.7-13 | Open | Poisson kernel, `S`-function series, Fourier integrals |
| 7.7-14 | Proved | `hasSum_affine_cpow_jacobiOn` (principal branch: `A - Bw` in the slit plane on the elliptic disk) |
| 7.7-15 | Proved | `hasSum_gegenbauer_dist_cpow` (lengths `a ≠ b`, `x = cos θ ∈ [-1, 1]`; `ν`, `ν + 1/2`, `2ν + 1` regular) |
| 7.8-1 | Proved | `iterate_derivative_X_sq_sub_one_pow` (Legendre), `iteratedDeriv_gegenbauer_rodrigues` (Gegenbauer, with `(x + 1)^a (x - 1)^a` in place of `(x² - 1)^a`, principal branch, `(ν)ₙ, (ν + 1/2)ₙ, (2ν + n)ₙ ≠ 0`) |
| 7.8-2 – 7.8-4 | Open | orthogonality of `Pₙ^m`, Gegenbauer orthogonality, product formula |
| 7.8-5 | Proved | `iteratedDeriv_add_cpow_mul_add_cpow` (`∂/∂x + ∂/∂y` as `d/dt` along the diagonal; slit-plane nodes) |
| 7.8-6 | Proved | `iteratedDeriv_prod_add_cpow` (same conventions) |
| 7.8-7 | Proved | `integral_exp_mul_legendre` |
| 7.8-8 | Proved | `jacobiSecondKind_eq_complexCauchyIntegral` |
| 7.8-9, 7.8-10 | Open | Poisson integral, Gegenbauer coefficient integral |
| 7.9-1 | Proved | `hasSum_laguerre_exp` (for `1 + β ∉ -ℕ`) |
| 7.9-2 | Proved | `hasSum_laguerre_generating` |
| 7.9-3, 7.9-4 | Open | contour and `S`-function generating relations |
| 7.9-5 | Proved | `hasSum_laguerre_exp_zeroFOne` |
| 7.9-6 | Proved | `laguerre_add` (all parameters) |
| 7.9-7 | Open | addition theorem |
| 7.9-8 | Proved | `derivative_laguerre` |
| 7.9-9 | Open | Dirichlet average of `L⁽ᵐ⁾` |
| 7.10-1 | Proved | `gaussianFunctional_X_pow` (density `e^{-x²}`; the `e^{-x²/2}` form is a change of variable) |
| 7.10-2 | Proved | `gaussianFunctional_affine_pow` |
| 7.10-3 | Open | integral with `Rₙ(1/2, 1/2; x ± i√t)` |
| 7.10-4 | Proved | `hasSum_carlsonHermite_generating` (`Hₙ = carlsonHermite n = 2ⁿ p̃ₙ`) |
| 7.10-5 | Proved | `tendsto_gegenbauer_hermite` (real `ν → ∞`), via the Gegenbauer recurrence `gegenbauer_three_term` |
| 7.10-6 | Proved | `carlsonHermite_addition` |
