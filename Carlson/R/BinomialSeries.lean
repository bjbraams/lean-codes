/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import ToMathlib.Analysis.SpecialFunctions.ComplexPowerDeriv
public import Carlson.RPolynomial.TaylorContinuation
public import Carlson.RPolynomial.GeneratingIdentities

/-!
# The continued R-function binomial series

The scalar Taylor theorem gives the binomial expansion at every complex
Dirichlet parameter, with the full entry disk about one. The shifted moments
are regularized R-polynomials, including their exceptional parameter values.
-/

open Complex Polynomial Set Dirichlet
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The R-function binomial expansion on the unit node disk, at every Dirichlet parameter. -/
theorem hasSum_regCarlsonR_cpow_neg (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : ∀ i, ‖z i - 1‖ < 1) :
    HasSum (fun n => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
      regCarlsonRPolynomial n b (fun i => 1 - z i)) (regCarlsonR (-a) b z) := by
  have hnode : z ∈ carlsonRVariableDomain := by
    intro i
    have hr := (abs_re_le_norm (z i - 1)).trans_lt (hz i)
    simp only [sub_re, one_re] at hr
    change 0 < (z i).re
    linarith [neg_abs_le ((z i).re - 1)]
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-a)) (Metric.ball 1 1) := by
    intro w hw
    have hr := (abs_re_le_norm (w - 1)).trans_lt (show ‖w - 1‖ < 1 by simpa [dist_eq_norm] using hw)
    simp only [sub_re, one_re] at hr
    have hwre : 0 < w.re := by linarith [neg_abs_le (w.re - 1)]
    exact analyticAt_id.cpow analyticAt_const (Or.inl hwre)
  have hn : ‖fun i => z i - 1‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr hz
  have H := (isRegCarlsonRContinuation_regCarlsonR (-a) hnode).hasSum_taylor hf hn b
  convert H using 1
  funext n
  have hder : iteratedDeriv n (fun w : ℂ => w ^ (-a)) 1 =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval a := by
    rw [Complex.iteratedDeriv_cpow_const _ _ (by simp), one_cpow, mul_one]
    have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) (-a) n
    rw [neg_neg] at h
    rw [h, ← mul_assoc, ← mul_pow]
    simp
  have hshift : (fun i => z i - 1) = fun i => (-1 : ℂ) * (1 - z i) := by
    funext i; ring
  rw [hder, hshift, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, carlsonRPolynomialNumerator_smul]
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  linear_combination
    -(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
      carlsonRPolynomialNumerator n b (fun i => 1 - z i) *
      (Gamma ((∑ i, b i) + n))⁻¹ * hs

end Carlson
