/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Equal
public import Carlson.RPolynomial.TaylorContinuation

/-!
# Equal-denominator F₄ as a Gauss-function average

The equal-moment series is the entire continuation in the averaging parameters
of the native Dirichlet average of a Gauss function. On `re c > 1/2` this gives
Carlson (1975), equation (2.4), as an actual integral average, with no restrictions
on the two numerator parameters. The series in `AppellF4Equal` also covers the
removable averaging parameters outside the native integration domain.
-/

open Complex Polynomial Set Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The regularized Gauss function has its prescribed scalar power series on the unit ball. -/
private theorem hasFPowerSeriesOnBall_gauss (a b c : ℂ) :
    HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (FormalMultilinearSeries.ofScalars ℂ (gaussCoeff a b c)) 0 1 := by
  have hseries : regularizedGaussHGFunSeries a b c =
      FormalMultilinearSeries.ofScalars ℂ (gaussCoeff a b c) := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries]
    congr 1
    funext n
    simp only [regularizedHGFunCoeff, gaussCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  have h := (regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le zero_lt_one (radius_regularizedGaussHGFunSeries_ge_one a b c))
  rw [← hseries]
  exact h.mono zero_lt_one (radius_regularizedGaussHGFunSeries_ge_one a b c)

/-- Squared sum and difference nodes lie in the Gauss disk on the F₄ square-root region. -/
private theorem norm_equalF4_nodes_lt_one {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    ‖pair ((x + y) ^ 2) ((x - y) ^ 2)‖ < 1 := by
  have hs : (‖x‖ + ‖y‖) ^ 2 < 1 := by
    nlinarith [norm_nonneg x, norm_nonneg y]
  apply lt_of_le_of_lt _ hs
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change ‖(x + y) ^ 2‖ ≤ (‖x‖ + ‖y‖) ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  · change ‖(x - y) ^ 2‖ ≤ (‖x‖ + ‖y‖) ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2

/-- **Carlson (1975), (2.4), continued average.** The Gauss-average Taylor construction
is the duplication ratio times regularized equal-denominator F₄, at all parameters. -/
theorem regCarlsonTaylorSeries_equalF4 (a b c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regCarlsonTaylorSeries 0 (gaussCoeff a b c)
      (pair ((x + y) ^ 2) ((x - y) ^ 2)) (pair (c - 1 / 2) (c - 1 / 2)) =
      quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  have h := (hasSum_regularizedAppellF4_equalRPolynomial a b c hxy).mul_left
    (quadraticGammaRatio (c - 1 / 2))
  rw [regCarlsonTaylorSeries]
  convert h.tsum_eq using 1
  apply tsum_congr
  intro N
  simp only [sub_zero, regCarlsonRPolynomial_pair_self_eq]
  ring

/-- The Gauss-average Taylor construction is an entire continuation in its averaging
parameters; the node region is precisely the full square-root region for the squared F₄ nodes. -/
theorem isRegCarlsonContinuation_equalF4 (a b c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    IsRegCarlsonContinuation (regularizedGaussHGFun a b c)
      (pair ((x + y) ^ 2) ((x - y) ^ 2))
      (regCarlsonTaylorSeries 0 (gaussCoeff a b c) (pair ((x + y) ^ 2) ((x - y) ^ 2))) := by
  apply isRegCarlsonContinuation_of_hasFPowerSeriesOnBall (hasFPowerSeriesOnBall_gauss a b c)
  simpa only [sub_zero, NNReal.coe_one] using norm_equalF4_nodes_lt_one hxy

/-- The native regularized Gauss average is the duplication ratio times regularized F₄. -/
theorem regCarlsonDirichletAverage_equalF4 (a b c : ℂ) (hc : 1 / 2 < c.re)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regCarlsonDirichletAverage (pair (c - 1 / 2) (c - 1 / 2))
      (pair ((x + y) ^ 2) ((x - y) ^ 2)) (regularizedGaussHGFun a b c) =
      quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [← regCarlsonTaylorSeries_equalF4 a b c hxy]
  symm
  apply (isRegCarlsonContinuation_equalF4 a b c hxy).2
  intro i
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  fin_cases i <;> exact hβ

/-- **Carlson (1975), (2.4); Exercise 7.1-13.** Equal-denominator ordinary F₄ is a native
Dirichlet average of the ordinary Gauss function when the averaging parameters have positive
real parts. Its continuation to all admissible denominator parameters is the equal-moment series. -/
theorem carlsonDirichletAverage_equalF4 (a b c : ℂ) (hc : 1 / 2 < c.re)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    carlsonDirichletAverage (pair (c - 1 / 2) (c - 1 / 2))
      (pair ((x + y) ^ 2) ((x - y) ^ 2))
      (fun z => Gamma c * regularizedGaussHGFun a b c z) =
      appellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [carlsonDirichletAverage, regCarlsonDirichletAverage_const_mul,
    regCarlsonDirichletAverage_equalF4 a b c hc hxy, sum_pair, appellF4]
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hdup := Gamma_mul_quadraticGammaRatio hβ
  rw [show c - 1 / 2 + 1 / 2 = c by ring] at hdup
  rw [mul_left_comm (Gamma c), ← mul_assoc, hdup]
  ring

end Carlson.TwoVariable
