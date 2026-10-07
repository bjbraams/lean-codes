# Carlson (1977), Chapter 6: exercises

Status of the exercises of Chapter 6 of B. C. Carlson, *Special Functions of Applied
Mathematics* (pp. 177–188), against the Lean sources. Chapter 6 theorems and formulas are
tracked in [CarlsonCoverage.md](CarlsonCoverage.md).

Most R-polynomial identities are stated for the Pochhammer numerator
`Nₙ(b; z) = (c)ₙ Rₙ(b, z)`, `c = ∑ bᵢ`, or for the regularized polynomial `Rₙ(b, z)/Γ(c)`. In those
forms they hold for all parameters. Carlson's normalized statements follow wherever `(c)ₙ ≠ 0`.

Legend:
- **Proved**: the cited declaration states the exercise, possibly in numerator form.
- **Partial**: a closely related or weaker result is proved; what is missing is noted.
- **Open**: not yet formalized, but within reach of the existing theory.
- **Ch. 7**: a special-function identification (Gegenbauer, Legendre, Chebyshev, Stirling,
  Bessel, symmetric functions), deferred until Chapter 7 provides the bridges.
- **Applied**: a numerical computation or physical application, not targeted.

| Exercise | Status | Lean / remark |
| --- | --- | --- |
| 6.2-1 | Proved | `TwoVariable.sum_ascPochhammer_div_factorial_mul_pow` |
| 6.2-2 | Proved | `carlsonRPolynomialNumerator_sumElim_unit` (numerator form) |
| 6.2-3 | Ch. 7 | E_n, C_n recursions; needs (6.2-11), (6.2-12) identified with Mathlib's `esymm`, `hsymm` |
| 6.2-4 | Proved | `TwoVariable.natCast_succ_mul_carlsonRPolynomial₂_one_one` |
| 6.2-5 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_eq_hypergeometric` (Mathlib's `₂F₁`) |
| 6.2-6 | Proved | `isLittleO_regCarlsonRPolynomial_sub` (`Rₙ(b, z)/Γ(c) = ∑ bᵢ zᵢⁿ + o(‖b‖)`) |
| 6.2-7 | Partial | `eventually_norm_carlsonRPolynomial_le` (for `c` not a nonpositive integer) |
| 6.2-8 | Proved | `norm_carlsonRPolynomial_smul_le` |
| 6.2-9 | Proved | `TwoVariable.regRPolynomial_one_neg_nat` (case `m = n`) |
| 6.2-10 | Proved | `norm_carlsonRPolynomialNumerator_const_le` (numerator form), `norm_Gamma_mul_regCarlsonRPolynomial_const_le` |
| 6.2-11 | Proved | `eventually_norm_Gamma_mul_regCarlsonRPolynomial_const_le` (for every `ε > 0`, eventually `\|Γ(β)Rₙ/Γ(kβ)\| ≤ (\|z\| + ε)ⁿ`) |
| 6.2-12 | Proved | `norm_Gamma_mul_regCarlsonRPolynomial_const_le_exp` |
| 6.2-13 | Proved | `carlsonRPolynomialNumerator_two`, `sum_mul_carlsonRPolynomialNumerator_two` |
| 6.2-14 | Proved | the variance identity `sum_mul_sub_mean_sq`; the expansion `exists_carlsonR_cpow_near_diagonal` in the variables `uᵢ = zᵢ/z̄` (the homogeneity step `R_t(cw, z^s) = z̄^{st} R_t(cw, (z/z̄)^s)` is not stated) |
| 6.3-1 | Open | holomorphy on the plane cut along the segment |
| 6.3-2 | Proved | `regCarlsonR_neg_one_one_neg_nat` |
| 6.3-3 | Proved | `TwoVariable.exists_fractionalIntegral_continuation`, `continuedFractionalIntegral_neg_nat` |
| 6.3-4 | Proved | `tendsto_gamma_mul_regCarlsonContinuation_smul` |
| 6.3-5 | Ch. 7 | Appell's `F₁` as `R₋ₐ` |
| 6.3-6 | Partial | `Normalization.EqualParameter` gives joint holomorphy on slit-plane nodes, not on `ℂ \ con(z)` |
| 6.4-1 | Proved | `TwoVariable.ordinaryHypergeometric_neg_natCast_mul` |
| 6.4-2 | Proved | `Appell.isAppell_iff_hasDiagonalDeriv` |
| 6.5-1 | Proved | `carlsonRPolynomialNumerator_transform` |
| 6.5-2 | Proved | the six forms `TwoVariable.carlsonRPolynomialNumerator₂_eq_hypergeometric`, `…'`, `_div`, `_div'`, `_sub`, `_sub'` |
| 6.5-3 | Proved | `TwoVariable.ascPochhammer_mul_ordinaryHypergeometric_inv`, `…_one_sub` |
| 6.6-1 | Proved | `carlsonRPolynomialNumerator_eq_circleIntegral` |
| 6.6-2, 6.6-3 | Ch. 7 | Stirling numbers |
| 6.6-4 | Proved | `TwoVariable.eventually_hasSum_quadratic_generating` (numerator form, for `c` in the slit plane and `t` near `0`) |
| 6.6-5 | Applied | electrical network |
| 6.6-6 | Proved | `carlsonRPolynomialNumerator_sumElim` |
| 6.6-7 | Proved | `carlsonRPolynomialNumerator_add_params` |
| 6.6-8 | Proved | `carlsonRPolynomialNumerator_sq_nodes` |
| 6.6-9 | Partial | on `C¹` cycles: `isRegCarlsonContinuation_cycleIntegral`; the Jordan-curve form is open |
| 6.6-10 | Proved | `TwoVariable.hasSum_ordinaryHypergeometric_neg_natCast` |
| 6.6-11 | Ch. 7 | `∑ (-1)ᵐ Eₘ C_(n-m) = δ_{n0}`; needs (6.2-11), (6.2-12) |
| 6.6-12 | Proved | `carlsonRPolynomialNumerator_addDirichletUnit` |
| 6.6-13 | Proved | Tobey's relation `carlsonRPolynomialNumerator_tobey` |
| 6.6-14 | Ch. 7 | Newton's identities via (6.2-11), (6.2-12) |
| 6.6-15 | Partial | `regCarlsonR_neg_eq_cycleIntegral_log` on `C¹` cycles with prescribed winding numbers, with the regularized resolvent as integrand; the Jordan-curve form is not available |
| 6.6-16 | Proved | `carlsonR_neg_three_halves` (product form `x^(-1/2) y^(-1/2) z^(-1/2)`, valid on the slit plane) |
| 6.6-17 | Proved | `Complex.integral_exp_mul_one_sub_cos_pow` |
| 6.7-1 | Proved | `eval_gegenbauer_one`, `TwoVariable.eval_gegenbauer_neg`, `eval_legendre_one` |
| 6.7-2 | Proved | `TwoVariable.norm_eval_gegenbauer_cos_le` |
| 6.7-3 | Proved | `TwoVariable.chebyshevU_cos_eq_numerator` |
| 6.7-4 | Proved | `TwoVariable.hasSum_chebyshevT_log` (for `\|t e^{±iθ}\| < 1`) |
| 6.7-5 | Proved | `TwoVariable.gegenbauer_christoffel_darboux` (for `(2ν)_N ≠ 0`), from `gegenbauer_three_term` |
| 6.7-6 | Open | contour integral for `2ν ∈ ℕ` |
| 6.7-7 | Proved | `TwoVariable.sum_legendre_cos_mul_legendre_cos` (`sin θ ≠ 0`) |
| 6.7-8 | Proved | `TwoVariable.eval_gegenbauer_cos_two_mul` |
| 6.7-9 | Proved | `TwoVariable.eval_gegenbauer_cos_rainville` (division-free) |
| 6.7-10 | Proved | `TwoVariable.eval_legendre_cos_eq_sum` (`cos θ ≠ 0`), `sin_pow_mul_eval_legendre_sin` |
| 6.7-11 | Proved | `TwoVariable.gegenbauer_tobey` |
| 6.7-12 | Proved | `TwoVariable.hasSum_gegenbauer_dist` (real inner product spaces) |
| 6.7-13 | Proved | `TwoVariable.tendsto_eval_legendre_cos_div`, `tendsto_eval_gegenbauer_cos_div_besselJ` (`t ≠ 0`; `ν + 1/2`, `2ν` regular), `tendsto_eval_gegenbauer_cos_div` (regularized `₀F₁`) |
| 6.8-1 – 6.8-4 | Open | Legendre and Gegenbauer functions of complex degree |
| 6.8-5 | Proved | `TwoVariable.regCarlsonR_pair_one_one_exp`, `cos_pi_mul_div_two_eq`, `regCarlsonR_pair_neg_one_exp`, `log_eq_mul_regCarlsonR_pair`, `arctan_eq_mul_regCarlsonR` (for `|Im z| < 1`); the arccoth form `R₋₁(1, 1; x + 1, x - 1)` is not stated (Mathlib has no arccoth) |
| 6.8-6 | Proved | `TwoVariable.regCarlsonR_pair_neg_one_sq` |
| 6.8-7 | Proved | `carlsonR_neg_three_halves`, `carlsonR_neg_five_halves` (product forms, slit plane) |
| 6.8-8 | Proved | `mellin_carlsonRayProduct_eq_rIntegral` |
| 6.9-1 | Proved | `TwoVariable.eval_gegenbauer_even_zero`, `eval_gegenbauer_odd_zero` |
| 6.9-2 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_odd_two_one`, `_even_two_one`, `ordinaryHypergeometric_two`, `ordinaryHypergeometric_neg_one`, `ordinaryHypergeometric_half` |
| 6.9-3 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_self_eq_sum` |
| 6.9-4 | Proved | `TwoVariable.eval_gegenbauer_eq_sum` |
| 6.9-5 | Proved | `TwoVariable.hasSum_carlsonR_arithmetic` (`₃F₂` series, nodes in a disk about `(x + y)/2` inside the slit plane) |
| 6.9-7 | Proved | `TwoVariable.betaIntegral_mul_carlsonRPolynomial₂` (for `(2β)ₙ, (2β + 2σ)ₙ ≠ 0`) and `TwoVariable.integral_evenBinomialSum` (with the sums of (6.9-6)) |
| 6.9-6 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_add_sub` (division-free) and `TwoVariable.carlsonRPolynomialNumerator₂_add_sub_eq_mul` (Carlson's form) |
| 6.9-8 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_firstQuadratic_even_linear`, `_odd_linear` |
| 6.9-9 | Proved | `TwoVariable.eval_gegenbauer_two_mul_eq_hypergeometric`, `eval_gegenbauer_two_mul_add_one_eq_hypergeometric` |
| 6.9-10 | Proved | `TwoVariable.cos_two_mul_mul_eq_hypergeometric_sin`, `cos_two_mul_mul_eq_hypergeometric_cos`, `cos_two_mul_add_one_mul_eq_hypergeometric_sin`, `cos_two_mul_add_one_mul_eq_hypergeometric_cos` |
| 6.9-11 | Proved | `TwoVariable.sin_two_mul_succ_mul_eq_hypergeometric_sin`, `sin_two_mul_succ_mul_eq_hypergeometric_cos` (written for `2(n + 1)θ`), `sin_two_mul_add_one_mul_eq_hypergeometric_sin`, `sin_two_mul_add_one_mul_eq_hypergeometric_cos` |
| 6.9-12 | Partial | `F_{n+1}` is Mathlib's `Nat.fib_succ_eq_sum_choose`; the Lucas numbers are open |
| 6.9-13 | Proved | `carlsonRPolynomialNumerator_rootsOfUnity` |
| 6.9-14 | Proved | `hasSum_polygon`, `hasSum_carlsonS_polygon`, `hasSum_carlsonR_polygon` (for a disk about `λ` inside the slit plane) |
| 6.9-15 | Proved | `TwoVariable.hasSum_carlsonS_arithmetic` |
| 6.9-16 | Proved | `arcsin_eq_mul_carlsonRC`, `log_eq_mul_carlsonRC` and `TwoVariable.arccos_eq_mul_carlsonRC`, `arctan_eq_mul_carlsonRC`, `arctan_inv_eq_carlsonRC` (arccot), `arsinh_eq_mul_carlsonRC`, `arcosh_eq_mul_carlsonRC`, `artanh_eq_mul_carlsonRC` (`0 < x < 1`), `half_log_eq_carlsonRC` (arcoth) |
| 6.9-17 | Proved | `TwoVariable.carlsonR_cos_sq_eq_sin_div`, `sin_mul_carlsonRC_cos_sq` (complex strip `\|Re θ\| < π/2`), `pi_eq_four_mul_carlsonRC`, `tendsto_two_mul_carlsonRC_zero` (`2R_C(0, 1) = π` as a boundary limit), `carlsonRC_cot_sq_csc_sq_complex` (`0 < Re θ < π/2`), `carlsonRC_coth_sq_csch_sq_complex` (`Re φ > 0`, `\|Im φ\| < π/2`). Correction: the last two relations fail for `Re θ < 0` and `Re φ < 0`, where the printed hypotheses allow them, since `R_C(cot² θ, csc² θ)` and `R_C(coth² φ, csch² φ)` are even in the angle |
| 6.9-18 | Proved | `TwoVariable.exists_carlsonRC_sq_expansion` (complex `x, y` in the right half-plane, uniform in `ε`) |
| 6.9-19 | Partial | Mathlib's `regularizedHGFun` is entire in `x`; joint entire dependence on `c` is not stated |
| 6.9-20 | Proved | (6.9-23) as `Complex.iteratedDeriv_regularizedHGFun_zero_singleton`; `dⁿ/dxⁿ [x^{c-1} F̃₀₁(c; x)] = x^{c-n-1} F̃₀₁(c - n; x)` as `Complex.iteratedDeriv_cpow_mul_regularizedHGFun`; the Bessel forms as `TwoVariable.iterate_besselD_cpow_neg_mul_besselJ`, `iterate_besselD_cpow_mul_besselJ` (all on the slit plane) |
| 6.9-21 | Proved | (6.9-24) as Mathlib's `regularizedHGFun_zero_singleton_neg_nat_add_one` and `Complex.regularizedHGFun_zero_singleton_one_sub_int` (`n ∈ ℤ`, `x ≠ 0`); (6.9-25) as Mathlib's `besselJ_neg_int` and `Complex.besselI_neg_int` |
| 6.10-1 | Proved | `TwoVariable.ordinaryHypergeometric_quadratic` (for `‖z‖, ‖4z(1 - z)‖ < 1`), `regularizedGaussHGFun_quadratic`, and the R-function form `regCarlsonR_quadratic_gauss` on all of `re z < 1/2` |
| 6.10-2 – 6.10-4 | Applied | numerical values, pendulum |
| 6.10-5 | Proved | `legendreK_imaginary_modulus`, `legendreK_landen` |
| 6.10-6 | Proved | `TwoVariable.eventually_hasSum_quadratic_generating_second` (for `(1 - 2ν - 2n)ₙ ≠ 0`) |
| 6.10-7 | Proved | `TwoVariable.ascPochhammer_mul_eval_gegenbauer_reflect` (division-free, for any `S` with `S² = x² - 1`, `S ≠ 0`) |
| 6.10-8 | Proved | `TwoVariable.carlsonRPolynomialNumerator₂_neg_sub_sq` (division-free) |
| 6.10-9 | Partial | Fibonacci numbers: `TwoVariable.carlsonRPolynomial_fib`; the Lucas numbers are open (Mathlib has no Lucas numbers) |
| 6.10-10 | Proved | `TwoVariable.eval_gegenbauer_eq_hypergeometric` (for `(ν + 1/2)ₙ ≠ 0`) |
| 6.10-11 | Proved | `TwoVariable.two_pow_mul_carlsonRPolynomial_cos` |
| 6.10-12 | Proved | `TwoVariable.regCarlsonR_one_half_sub_pair_sq`, `regCarlsonR_neg_one_half_sub_pair_sq` (regularized, all `β`), `carlsonR_one_half_sub_pair_sq` (`re β > 0`) |
| 6.10-13 | Applied | numerical; the algorithm is `exists_borchardtSigma_extrapolation` |
| 6.11-1 | Applied | potential of a charged ring |

The section results Corollary 6.11-3 and Theorem 6.11-4 are now proved in the book's
generality: `TwoVariable.hasSum_ossicini_complex` and
`TwoVariable.gegenbauer_product_formula_complex`.
