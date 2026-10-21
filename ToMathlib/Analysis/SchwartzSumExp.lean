/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SchwartzExpExp

/-!
# Schwartz functions composed with a sum of exponentials

If `ψ : SchwartzMap ℝ F`, the function `y ↦ ψ (∑ i, exp (y i))` has uniformly
bounded derivatives of every order, hence temperate growth. The derivatives of the inner
function are bounded by the sum of exponentials itself; the decay of the outer derivatives
cancels these powers in Mathlib's Faà di Bruno estimate.

This supplies smooth multipliers for double-exponential Schwartz weights and allows
compactly supported radial profiles in simplex Mellin inversion.
-/

open Real MeasureTheory Set
open scoped ContDiff
@[expose] public noncomputable section
variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composing a one-dimensional Schwartz function with the sum of coordinate exponentials
has bounded derivatives of every order. -/
theorem SchwartzMap.hasTemperateGrowth_comp_sum_exp (ψ : SchwartzMap ℝ F) :
    (fun y : EuclideanSpace ℝ ι => ψ (∑ i, Real.exp (y i))).HasTemperateGrowth := by
  have hinner : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i)) :=
    ContDiff.sum fun i _ => Real.contDiff_exp.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).contDiff
  refine ⟨(ψ.smooth ⊤).comp hinner, fun n => ?_⟩
  let C : ℝ := ∑ j ∈ Finset.range (n + 1),
    (SchwartzMap.seminorm ℝ 0 j ψ + SchwartzMap.seminorm ℝ n j ψ)
  refine ⟨0, (n.factorial : ℝ) * (2 ^ n * C), fun y => ?_⟩
  simp only [pow_zero, mul_one]
  let s : ℝ := ∑ i, Real.exp (y i)
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hD : 1 ≤ 1 + s := by linarith
  have hcomp := norm_iteratedFDeriv_comp_le (ψ.smooth ⊤) hinner
    (show (n : ℕ∞ω) ≤ ∞ by simp) y
    (C := 2 ^ n * C * (1 + s) ^ (-(n : ℝ))) (D := 1 + s) (fun j hj => ?_) (fun j hj _ => ?_)
  · refine hcomp.trans ?_
    apply le_of_eq
    rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    have hne : (1 + s) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp
  · have hbase := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := n) (norm_nonneg s)
      (norm_nonneg (iteratedFDeriv ℝ j ψ s))
      (ψ.norm_iteratedFDeriv_le_seminorm ℝ j s) (by
        simpa only [zero_add] using ψ.le_seminorm ℝ n j s)
    simp only [pow_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hs] at hbase
    apply hbase.trans
    gcongr
    exact Finset.single_le_sum (fun k _ => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (by simp only [Finset.mem_range]; omega)
  · have hfun : (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i)) =
        fun y => -expExpExponent (fun _ : ι => 0) y := by
      funext y
      simp [expExpExponent]
    have hder : ‖iteratedFDeriv ℝ j (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i)) y‖ ≤ s := by
      rw [hfun]
      change ‖iteratedFDeriv ℝ j (-expExpExponent (fun _ : ι => 0)) y‖ ≤ s
      rw [iteratedFDeriv_neg]
      simp only [Pi.neg_apply, norm_neg]
      simpa [s] using norm_iteratedFDeriv_expExpExponent_le (fun _ : ι => 0) hj y
    refine hder.trans ((by linarith : s ≤ 1 + s).trans ?_)
    exact le_self_pow₀ hD (by omega)

end
