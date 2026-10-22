/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Euler and Weierstrass products for reciprocal Gamma

Carlson (1977), §§3.4, 3.6. David Loeffler's Mathlib complex Euler limit,
combined with Mathlib's harmonic-number limit, gives the canonical product.
The reciprocal limit includes every nonpositive integer: at such a parameter
the finite products are eventually zero.
-/

open Filter Finset
open scoped Topology

public noncomputable section

namespace Complex

/-- The reciprocal Euler approximants converge even at the zeros of reciprocal Gamma. -/
theorem inv_GammaSeq_tendsto_inv_Gamma (z : ℂ) :
    Tendsto (fun n : ℕ => (GammaSeq z n)⁻¹) atTop (𝓝 (Gamma z)⁻¹) := by
  by_cases hz : Gamma z = 0
  · obtain ⟨m, rfl⟩ := (Gamma_eq_zero_iff z).mp hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m] with n hn
    have hp : (∏ j ∈ range (n + 1), (-(m : ℂ) + j)) = 0 :=
      prod_eq_zero (i := m) (mem_range.mpr (by omega)) (by simp)
    simp [GammaSeq, hp, Gamma_neg_nat_eq_zero]
  · exact (GammaSeq_tendsto_Gamma z).inv₀ hz

/-- Finite Euler products of the factors `1 + z/k`. -/
private theorem euler_product_finite (z : ℂ) (n : ℕ) :
    z * (∏ k ∈ range n, (1 + z / (k + 1 : ℂ))) =
      (∏ k ∈ range (n + 1), (z + k)) / (n.factorial : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [prod_range_succ]
    rw [← mul_assoc, ih]
    conv_rhs => rw [prod_range_succ]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The first `n` canonical factors of the Weierstrass product for reciprocal Gamma. -/
def weierstrassGammaProduct (z : ℂ) (n : ℕ) : ℂ :=
  z * exp ((Real.eulerMascheroniConstant : ℂ) * z) *
    ∏ k ∈ range n, ((1 + z / (k + 1 : ℂ)) * exp (-z / (k + 1 : ℂ)))

/-- The harmonic counterterm relates the canonical product to the Euler approximant. -/
private theorem weierstrassGammaProduct_eq (z : ℂ) {n : ℕ} (hn : 0 < n) :
    weierstrassGammaProduct z n = (GammaSeq z n)⁻¹ *
      exp (z * ((Real.eulerMascheroniConstant - (harmonic n : ℝ) + Real.log n : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : (∑ k ∈ range n, -z / (k + 1 : ℂ)) = -z * (harmonic n : ℂ) := by
    rw [harmonic]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl (fun k _ => by rw [div_eq_mul_inv])
  have hlog : log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg n)]
  unfold weierstrassGammaProduct
  rw [prod_mul_distrib, ← exp_sum, hsum]
  have he : z * exp ((Real.eulerMascheroniConstant : ℂ) * z) *
      (∏ k ∈ range n, (1 + z / (k + 1 : ℂ))) * exp (-z * (harmonic n : ℂ)) =
      (z * ∏ k ∈ range n, (1 + z / (k + 1 : ℂ))) *
        exp (z * ((Real.eulerMascheroniConstant : ℂ) - harmonic n)) := by
    calc
      _ = (z * ∏ k ∈ range n, (1 + z / (k + 1 : ℂ))) *
          (exp ((Real.eulerMascheroniConstant : ℂ) * z) * exp (-z * (harmonic n : ℂ))) := by ring
      _ = _ := by rw [← exp_add]; congr 1; congr 1; ring
  rw [← mul_assoc, he, euler_product_finite]
  rw [GammaSeq, inv_div, cpow_def_of_ne_zero hn0]
  push_cast only [ofReal_add, ofReal_sub, ofReal_ratCast]
  rw [← hlog]
  rw [show z * ((Real.eulerMascheroniConstant : ℂ) - (harmonic n : ℂ) +
      log (n : ℂ)) =
      z * ((Real.eulerMascheroniConstant : ℂ) - harmonic n) + log (n : ℂ) * z by ring,
    exp_add]
  field_simp

/-- **Carlson §3.6, Weierstrass product.** The canonical finite products converge
to reciprocal Gamma for every complex parameter, including the Gamma poles. -/
theorem tendsto_weierstrassGammaProduct (z : ℂ) :
    Tendsto (weierstrassGammaProduct z) atTop (𝓝 (Gamma z)⁻¹) := by
  have hc : Tendsto (fun n : ℕ =>
      ((Real.eulerMascheroniConstant - (harmonic n : ℝ) + Real.log n : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => Real.eulerMascheroniConstant -
        ((harmonic n : ℝ) - Real.log n)) atTop
        (𝓝 (Real.eulerMascheroniConstant - Real.eulerMascheroniConstant)) :=
      tendsto_const_nhds.sub Real.tendsto_harmonic_sub_log
    have h := (continuous_ofReal.tendsto _).comp hr
    convert h using 1
    · funext n; congr 1; ring
    · simp
  have h := (inv_GammaSeq_tendsto_inv_Gamma z).mul ((hc.const_mul z).cexp)
  simp only [mul_zero, exp_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (weierstrassGammaProduct_eq z hn).symm

end Complex
