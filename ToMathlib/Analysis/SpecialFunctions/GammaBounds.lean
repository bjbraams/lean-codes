/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.GammaRatio
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Slope

/-!
# Elementary bounds for the Gamma function

* `Complex.norm_Gamma_le_Gamma_re`: `|Γ(s)| ≤ Γ(re s)` for `re s > 0`.
* `Real.Gamma_le_Gamma_of_one_le`: `Γ(x) ≤ Γ(y)` for `1 ≤ x ≤ y` and `2 ≤ y`.
* `Real.Gamma_add_div_Gamma_le`: `x ↦ Γ(x + r)/Γ(x)` is nondecreasing on `x > 0` for `r ≥ 0`.
* `Real.Gamma_add_nat_eq`: `Γ(x + n) = (x)ₙ Γ(x)` for `x > 0`.
* `Real.ascPochhammer_eval_le_pow`: `(x)ₙ ≤ (x + n)ⁿ` for `x ≥ 0`.
-/

open Filter Topology Set Finset

@[expose] public noncomputable section

namespace Complex

/-- **`|Γ(s)| ≤ Γ(re s)`** for `re s > 0`, by comparing Euler's limit sequences termwise. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  have hG : ‖Gamma (s.re : ℂ)‖ = Real.Gamma s.re := by
    rw [Gamma_ofReal, norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos hs).le]
  rw [← hG]
  have hcast : ∀ j : ℕ, (s.re : ℂ) + j = ((s.re + j : ℝ) : ℂ) := fun j ↦ by push_cast; ring
  refine le_of_tendsto_of_tendsto (GammaSeq_tendsto_Gamma s).norm
    (GammaSeq_tendsto_Gamma (s.re : ℂ)).norm ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  simp only
  rw [norm_GammaSeq _ (by omega), norm_GammaSeq _ (by omega), ofReal_re]
  have hpos : ∀ j ∈ range (n + 1), 0 < ‖(s.re : ℂ) + j‖ := fun j _ ↦ by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact abs_pos.mpr (by positivity)
  refine div_le_div_of_nonneg_left (by positivity) (prod_pos hpos)
    (prod_le_prod₀ (fun j hj ↦ (hpos j hj).le) fun j _ ↦ ?_)
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc s.re + j = (s + j).re := by simp
    _ ≤ ‖s + j‖ := re_le_norm _

end Complex

namespace Real

/-- `Γ(x) ≤ Γ(y)` for `1 ≤ x ≤ y` and `2 ≤ y`: on `[1, 2]` the Gamma function is at most one by
convexity, and it increases on `[2, ∞)`. -/
theorem Gamma_le_Gamma_of_one_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : 2 ≤ y) :
    Gamma x ≤ Gamma y := by
  rcases le_or_gt 2 x with h2 | h2
  · exact Gamma_strictMonoOn_Ici.monotoneOn h2 (le_trans h2 hxy) hxy
  have h1 : Gamma x ≤ 1 := by
    have hc := convexOn_Gamma
    have ht : x = (2 - x) * 1 + (x - 1) * 2 := by ring
    have := hc.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (by linarith : (0 : ℝ) ≤ 2 - x) (by linarith : (0 : ℝ) ≤ x - 1) (by ring)
    simp only [smul_eq_mul, Gamma_one, Gamma_two, mul_one] at this
    rw [show 2 - x + (x - 1) * 2 = x by ring] at this
    linarith
  have h2' : 1 ≤ Gamma y := by
    rw [← Gamma_two]; exact Gamma_strictMonoOn_Ici.monotoneOn (le_refl 2) hy hy
  linarith

/-- **Increasing differences of `log Γ`**: for `r ≥ 0`, `x ↦ Γ(x + r)/Γ(x)` is nondecreasing on
`x > 0`. -/
theorem Gamma_add_div_Gamma_le {x y r : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hr : 0 ≤ r) :
    Gamma (x + r) / Gamma x ≤ Gamma (y + r) / Gamma y := by
  have hy : 0 < y := hx.trans_le hxy
  rcases hr.eq_or_lt with rfl | hr
  · simp [div_self (Gamma_pos_of_pos hx).ne', div_self (Gamma_pos_of_pos hy).ne']
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  set f := Real.log ∘ Gamma
  have hc := convexOn_log_Gamma
  have hmem : ∀ {t : ℝ}, 0 < t → t ∈ Set.Ioi (0 : ℝ) := fun ht ↦ ht
  -- slope over `[x, x + r]` ≤ slope over `[x, y + r]` ≤ slope over `[y, y + r]`
  have s1 := hc.secant_mono (a := x) (x := x + r) (y := y + r) (hmem hx) (hmem (by linarith))
    (hmem (by linarith)) (by linarith) (by linarith) (by linarith)
  have s2 := hc.secant_mono (a := y + r) (x := x) (y := y) (hmem (by linarith)) (hmem hx)
    (hmem hy) (by linarith) (by linarith) hxy.le
  have hkey : f (x + r) - f x ≤ f (y + r) - f y := by
    have e1 : (f (y + r) - f x) / (y + r - x) = (f x - f (y + r)) / (x - (y + r)) := by
      rw [← neg_div_neg_eq]; ring_nf
    have e2 : (f y - f (y + r)) / (y - (y + r)) = (f (y + r) - f y) / r := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [show x + r - x = r by ring] at s1
    rw [e2] at s2
    have := s1.trans (e1 ▸ s2)
    rwa [div_le_div_iff_of_pos_right hr] at this
  simp only [f, Function.comp_apply] at hkey
  have hp : ∀ {t : ℝ}, 0 < t → 0 < Gamma t := fun ht ↦ Gamma_pos_of_pos ht
  rw [div_le_div_iff₀ (hp hx) (hp hy), ← Real.log_le_log_iff (by
    exact mul_pos (hp (by linarith)) (hp hy)) (mul_pos (hp (by linarith)) (hp hx)),
    Real.log_mul (hp (by linarith)).ne' (hp hy).ne', Real.log_mul (hp (by linarith)).ne'
      (hp hx).ne']
  linarith

/-- `Γ(x + n) = (x)ₙ Γ(x)` for `x > 0`. -/
theorem Gamma_add_nat_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) = (ascPochhammer ℝ n).eval x * Gamma x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one (by positivity), ih, ascPochhammer_succ_eval]
    ring

/-- `(x)ₙ ≤ (x + n)ⁿ` for `x ≥ 0`. -/
theorem ascPochhammer_eval_le_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (x + n) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, pow_succ]
    have h0 : 0 ≤ (ascPochhammer ℝ n).eval x := by
      clear ih
      induction n with
      | zero => simp
      | succ n ihn => rw [ascPochhammer_succ_eval]; positivity
    push_cast
    gcongr
    · exact ih.trans (pow_le_pow_left₀ (by positivity) (by linarith) n)
    · linarith

end Real
