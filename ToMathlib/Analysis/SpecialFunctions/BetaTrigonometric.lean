/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The complex trigonometric beta integral

Carlson (1977), formula (4.2-3), for two parameters of positive real part.
The proof pulls David Loeffler's Mathlib complex beta integral back along
`θ ↦ Real.sin θ ^ 2`, using Sébastien Gouëzel's one-dimensional Jacobian theorem.
All powers use the principal complex logarithm; their bases are positive in
the interior of the interval, so no extra branch restrictions are needed.
-/

open Set Real MeasureTheory

public noncomputable section

namespace Complex

/-- Squared sine parametrizes the open unit interval on the first quadrant. -/
private theorem sin_sq_image :
    (fun θ : ℝ => Real.sin θ ^ 2) '' Ioo 0 (π / 2) = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ⟨sq_pos_of_pos hs, by nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hc]⟩
  · intro ht
    refine ⟨Real.arcsin (Real.sqrt t), ⟨Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ht.1), ?_⟩, ?_⟩
    · apply Real.arcsin_lt_pi_div_two.mpr
      nlinarith [ht.2, Real.sq_sqrt ht.1.le, Real.sqrt_nonneg t]
    · dsimp only
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg t])
        (by nlinarith [ht.2, Real.sq_sqrt ht.1.le, Real.sqrt_nonneg t])]
      exact Real.sq_sqrt ht.1.le

/-- Squared sine is injective in the first quadrant. -/
private theorem sin_sq_injOn : InjOn (fun θ : ℝ => Real.sin θ ^ 2) (Ioo 0 (π / 2)) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  have hs := Real.strictMonoOn_sin
    (show x ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)
    (show y ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩) hxy
  have hx0 := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  nlinarith

/-- The Jacobian of squared sine. -/
private theorem hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
  convert (Real.hasDerivAt_sin θ).pow 2 using 1
  ring

/-- Absorbing the Jacobian factor into a complex power of a positive square. -/
private theorem cpow_sq_mul_self {v : ℝ} (hv : 0 < v) (a : ℂ) :
    ((v : ℂ) ^ 2) ^ (a - 1) * v = (v : ℂ) ^ (2 * a - 1) := by
  have h := cpow_mul_ofReal_nonneg hv.le 2 (a - 1)
  norm_num only [Real.rpow_two, ofReal_pow, ofReal_ofNat] at h
  calc
    _ = (v : ℂ) ^ (2 * (a - 1)) * (v : ℂ) ^ (1 : ℂ) := by rw [← h, cpow_one]
    _ = (v : ℂ) ^ (2 * (a - 1) + 1) := (cpow_add _ _ (ofReal_ne_zero.mpr hv.ne')).symm
    _ = _ := by congr 1; ring

/-- Pullback of the complex beta density along squared sine. -/
private theorem trig_beta_pullback (a b : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    |2 * Real.sin θ * Real.cos θ| •
        (((Real.sin θ ^ 2 : ℝ) : ℂ) ^ (b - 1) * (1 - ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (a - 1)) =
      2 * ((Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have he : 1 - ((Real.sin θ ^ 2 : ℝ) : ℂ) = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast (show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ])
  rw [he, abs_of_pos (by positivity : 0 < 2 * Real.sin θ * Real.cos θ), real_smul]
  push_cast only [ofReal_mul, ofReal_ofNat, ofReal_pow]
  calc
    _ = 2 * ((((Real.cos θ : ℂ) ^ 2) ^ (a - 1) * Real.cos θ) *
        (((Real.sin θ : ℂ) ^ 2) ^ (b - 1) * Real.sin θ)) := by ring
    _ = _ := by rw [cpow_sq_mul_self hc, cpow_sq_mul_self hs]

/-- **Carlson (4.2-3), convergence.** The trigonometric beta density is integrable
for any two complex parameters of positive real part. -/
theorem integrableOn_cos_cpow_mul_sin_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun θ : ℝ => (Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1))
      (Ioo 0 (π / 2)) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => (hasDerivAt_sin_sq θ).hasDerivWithinAt) sin_sq_injOn
    (fun t : ℝ => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (a - 1))).mp
      (by
        rw [sin_sq_image]
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
          (betaIntegral_convergent hb ha))
  have he := h.congr_fun (fun θ hθ => trig_beta_pullback a b hθ) measurableSet_Ioo
  have hi : IntegrableOn (fun θ : ℝ => (1 / 2 : ℂ) *
      (2 * ((Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1))))
      (Ioo 0 (π / 2)) := he.const_mul (1 / 2 : ℂ)
  exact hi.congr_fun (fun θ _ => by ring) measurableSet_Ioo

/-- **Carlson (4.2-3).** Evaluation of the complex trigonometric beta integral. -/
theorem integral_cos_cpow_mul_sin_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ θ : ℝ in Ioo 0 (π / 2),
      (Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1)) =
      Gamma a * Gamma b / (2 * Gamma (a + b)) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => (hasDerivAt_sin_sq θ).hasDerivWithinAt) sin_sq_injOn
    (fun t : ℝ => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (a - 1))
  rw [sin_sq_image] at h
  have he : (∫ θ : ℝ in Ioo 0 (π / 2), |2 * Real.sin θ * Real.cos θ| •
      (((Real.sin θ ^ 2 : ℝ) : ℂ) ^ (b - 1) * (1 - ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (a - 1))) =
      2 * (∫ θ : ℝ in Ioo 0 (π / 2),
        (Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => trig_beta_pullback a b hθ)
  rw [he] at h
  have hbval : (∫ t : ℝ in Ioo 0 1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (a - 1)) =
      Gamma a * Gamma b / Gamma (a + b) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change betaIntegral b a = _
    rw [betaIntegral_symm, betaIntegral_eq_Gamma_mul_div a b ha hb]
  rw [hbval] at h
  linear_combination -h / 2

/-- Interval-integrability version of the convergence in **Carlson (4.2-3)**. -/
theorem intervalIntegrable_cos_cpow_mul_sin_cpow {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    IntervalIntegrable (fun θ : ℝ =>
      (Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1)) volume 0 (π / 2) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)).mpr
    (integrableOn_cos_cpow_mul_sin_cpow ha hb)

/-- **Carlson (4.2-3)** in interval-integral notation. -/
theorem intervalIntegral_cos_cpow_mul_sin_cpow {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ θ : ℝ in 0..(π / 2),
      (Real.cos θ : ℂ) ^ (2 * a - 1) * (Real.sin θ : ℂ) ^ (2 * b - 1)) =
      Gamma a * Gamma b / (2 * Gamma (a + b)) := by
  rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  exact integral_cos_cpow_mul_sin_cpow ha hb

end Complex
