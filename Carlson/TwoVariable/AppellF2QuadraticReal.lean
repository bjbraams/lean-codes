/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF2Quadratic

/-!
# Real angle domains for the quadratic F₂ formulas

The positive-triangle continuation removes the auxiliary absolute reexpansion
bound from Carlson (1976), (2.10) and (2.12), for nonnegative real angles whose
sum is less than π/2. Mathlib's sine and cosine inequalities prove convergence
of every displayed series, including points on either coordinate axis.
-/

open Complex Set Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The two sine/cosine products have a sum below one on the positive angle triangle. -/
private theorem real_angle_products {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (h : θ + φ < Real.pi / 2) :
    0 ≤ Real.sin θ * Real.cos φ ∧ 0 ≤ Real.cos θ * Real.sin φ ∧
      Real.sin θ * Real.cos φ + Real.cos θ * Real.sin φ < 1 := by
  have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcφ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsθ := Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos])
  have hsφ := Real.sin_nonneg_of_nonneg_of_le_pi hφ (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos (θ + φ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
  refine ⟨mul_nonneg hsθ hcφ.le, mul_nonneg hcθ.le hsφ, ?_⟩
  rw [← Real.sin_add]
  nlinarith [Real.sin_sq_add_cos_sq (θ + φ), Real.sin_le_one (θ + φ), sq_pos_of_pos hc]

/-- The squared sines belong to the F₂ diamond throughout the positive angle triangle. -/
private theorem real_angle_squares {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (h : θ + φ < Real.pi / 2) : Real.sin θ ^ 2 + Real.sin φ ^ 2 < 1 := by
  have hp : 0 < Real.cos (θ + φ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
  have hm : 0 < Real.cos (θ - φ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have he : Real.cos (θ + φ) * Real.cos (θ - φ) =
      1 - Real.sin θ ^ 2 - Real.sin φ ^ 2 := by
    rw [Real.cos_add, Real.cos_sub]
    calc
      _ = Real.cos θ ^ 2 * Real.cos φ ^ 2 - Real.sin θ ^ 2 * Real.sin φ ^ 2 := by ring
      _ = _ := by rw [Real.cos_sq', Real.cos_sq']; ring
  have H := mul_pos hp hm
  rw [he] at H
  linarith

/-- Positive centered coordinates give a convergent transformed F₂ series. -/
private theorem centered_real_F2_diamond {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXY : X + Y < 1) :
    ‖2 * (X : ℂ) / (1 + X + Y)‖ + ‖2 * (Y : ℂ) / (1 + X + Y)‖ < 1 := by
  have he (Z : ℝ) (hZ : 0 ≤ Z) :
      ‖2 * (Z : ℂ) / (1 + X + Y)‖ = 2 * Z / (1 + X + Y) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ← ofReal_one, ← ofReal_add, ← ofReal_add,
      ← ofReal_div, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [he X hX, he Y hY, ← add_div]
  exact (div_lt_one (by linarith : 0 < 1 + X + Y)).mpr (by linarith)

/-- The complex norms of the real sine/cosine products satisfy the F₄ square-root bound. -/
private theorem real_angle_complex_bound {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (h : θ + φ < Real.pi / 2) :
    ‖((Real.sin θ * Real.cos φ : ℝ) : ℂ)‖ +
      ‖((Real.cos θ * Real.sin φ : ℝ) : ℂ)‖ < 1 := by
  obtain ⟨hX, hY, hXY⟩ := real_angle_products hθ hφ h
  simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hX, abs_of_nonneg hY] using hXY

/-- **Carlson (1976), (2.12), on the positive angle triangle.** Every complex parameter
is included, with the reciprocal Gamma factor retained at denominator poles. -/
theorem regularizedAppellF2_quadratic_real_sin_F1 (a b : ℂ) {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (h : θ + φ < Real.pi / 2) :
    regularizedAppellF2 (2 * a) b b (a + 1 / 2) (a + 1 / 2)
      ((Real.sin θ : ℂ) ^ 2) ((Real.sin φ : ℂ) ^ 2) =
      (Gamma (a + 1 / 2))⁻¹ * regularizedAppellF1 b a a (a + 1 / 2)
        ((Real.sin (θ + φ) : ℂ) ^ 2) ((Real.sin (θ - φ) : ℂ) ^ 2) := by
  have H := regularizedAppellF4_eq_equalAppellF1 a b (real_angle_complex_bound hθ hφ h)
  have hx : (((Real.sin θ * Real.cos φ : ℝ) : ℂ)) ^ 2 =
      (Real.sin θ : ℂ) ^ 2 * (1 - (Real.sin φ : ℂ) ^ 2) := by
    norm_cast; rw [mul_pow, Real.cos_sq']
  have hy : (((Real.cos θ * Real.sin φ : ℝ) : ℂ)) ^ 2 =
      (Real.sin φ : ℂ) ^ 2 * (1 - (Real.sin θ : ℂ) ^ 2) := by
    norm_cast; rw [mul_pow, Real.cos_sq']; ring
  rw [hx, hy] at H
  have H2 := regularizedAppellF4_eq_F2_of_real_nonneg
    (a := 2 * a) (b := b)
    (show (a + 1 / 2) + (a + 1 / 2) = 2 * a + 1 by ring)
    (sq_nonneg (Real.sin θ)) (sq_nonneg (Real.sin φ)) (real_angle_squares hθ hφ h)
  simp only [ofReal_pow] at H2
  rw [H2] at H
  simpa only [ofReal_pow, ← ofReal_add, ← ofReal_sub, Real.sin_add, Real.sin_sub] using H

/-- **Carlson (1976), (2.12), ordinary form on the positive angle triangle.** -/
theorem appellF2_quadratic_real_sin_F1 (a b : ℂ) {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (h : θ + φ < Real.pi / 2) :
    appellF2 (2 * a) b b (a + 1 / 2) (a + 1 / 2)
      ((Real.sin θ : ℂ) ^ 2) ((Real.sin φ : ℂ) ^ 2) =
      appellF1 b a a (a + 1 / 2)
        ((Real.sin (θ + φ) : ℂ) ^ 2) ((Real.sin (θ - φ) : ℂ) ^ 2) := by
  rw [appellF2, regularizedAppellF2_quadratic_real_sin_F1 a b hθ hφ h, Complex.appellF1]
  by_cases hG : Gamma (a + 1 / 2) = 0
  · simp only [hG, zero_mul, mul_zero, inv_zero]
  · field_simp

/-- **Carlson (1976), (2.10), regularized on the positive angle triangle.** All complex
parameters are allowed and both duplication factors are retained. -/
theorem regularizedAppellF2_quadratic_real_sin_self (a μ : ℂ) {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (h : θ + φ < Real.pi / 2) :
    (quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
      regularizedAppellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2)
        ((Real.sin θ : ℂ) ^ 2) ((Real.sin φ : ℂ) ^ 2) =
      (1 + (Real.sin (θ + φ) : ℂ)) ^ (-(2 * a)) * regularizedAppellF2 (2 * a) μ (a - μ)
        (2 * μ) (2 * a - 2 * μ)
        (2 * (Real.sin θ : ℂ) * Real.cos φ / (1 + (Real.sin (θ + φ) : ℂ)))
        (2 * (Real.cos θ : ℂ) * Real.sin φ / (1 + (Real.sin (θ + φ) : ℂ))) := by
  let X := Real.sin θ * Real.cos φ
  let Y := Real.cos θ * Real.sin φ
  obtain ⟨hX, hY, hXY⟩ := real_angle_products hθ hφ h
  have hb := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_bailey
    a (μ + 1 / 2) (a - μ + 1 / 2) (real_angle_complex_bound hθ hφ h)
  have hx : ((X : ℂ)) ^ 2 = (Real.sin θ : ℂ) ^ 2 * (1 - (Real.sin φ : ℂ) ^ 2) := by
    dsimp [X]; norm_cast; rw [mul_pow, Real.cos_sq']
  have hy : ((Y : ℂ)) ^ 2 = (Real.sin φ : ℂ) ^ 2 * (1 - (Real.sin θ : ℂ) ^ 2) := by
    dsimp [Y]; norm_cast; rw [mul_pow, Real.cos_sq']; ring
  rw [show μ + 1 / 2 - 1 / 2 = μ by ring,
    show a - μ + 1 / 2 - 1 / 2 = a - μ by ring, hx, hy] at hb
  have H2 := regularizedAppellF4_eq_F2_of_real_nonneg (a := a) (b := a + 1 / 2)
    (show μ + 1 / 2 + (a - μ + 1 / 2) = a + 1 by ring)
    (sq_nonneg (Real.sin θ)) (sq_nonneg (Real.sin φ)) (real_angle_squares hθ hφ h)
  simp only [ofReal_pow] at H2
  rw [H2] at hb
  have H := hb.symm.trans (continuedBaileyMatrix_eq_F2 a μ
    (real_angle_complex_bound hθ hφ h) (centered_real_F2_diamond hX hY hXY))
  have hs : 1 + (X : ℂ) + Y = 1 + (Real.sin (θ + φ) : ℂ) := by
    simp only [X, Y, Real.sin_add, ofReal_add]
    ring
  rw [hs] at H
  simpa only [ofReal_pow, X, Y, ofReal_mul, mul_assoc,
    show μ + μ = 2 * μ by ring, show (a - μ) + (a - μ) = 2 * a - 2 * μ by ring] using H

/-- **Carlson (1976), (2.10), ordinary form on the positive angle triangle.** -/
theorem appellF2_quadratic_real_sin_self (a μ : ℂ)
    (hμ : ∀ k : ℕ, 2 * μ ≠ -(k : ℂ)) (hβ : ∀ k : ℕ, 2 * a - 2 * μ ≠ -(k : ℂ))
    {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (h : θ + φ < Real.pi / 2) :
    appellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2)
      ((Real.sin θ : ℂ) ^ 2) ((Real.sin φ : ℂ) ^ 2) =
      (1 + (Real.sin (θ + φ) : ℂ)) ^ (-(2 * a)) * appellF2 (2 * a) μ (a - μ)
        (2 * μ) (2 * a - 2 * μ)
        (2 * (Real.sin θ : ℂ) * Real.cos φ / (1 + (Real.sin (θ + φ) : ℂ)))
        (2 * (Real.cos θ : ℂ) * Real.sin φ / (1 + (Real.sin (θ + φ) : ℂ))) := by
  have hμ' : ∀ k : ℕ, μ ≠ -(k : ℂ) := by
    intro k hk
    exact hμ (k + k) (by push_cast; rw [hk]; ring)
  have hβ' : ∀ k : ℕ, a - μ ≠ -(k : ℂ) := by
    intro k hk
    exact hβ (k + k) (by push_cast; rw [← show 2 * (a - μ) = 2 * a - 2 * μ by ring, hk]; ring)
  have hm := Gamma_mul_quadraticGammaRatio_of_ne hμ'
  have hb := Gamma_mul_quadraticGammaRatio_of_ne hβ'
  have H := regularizedAppellF2_quadratic_real_sin_self a μ hθ hφ h
  rw [show μ + μ = 2 * μ by ring] at hm
  rw [show (a - μ) + (a - μ) = 2 * a - 2 * μ by ring] at hb
  rw [appellF2, appellF2]
  calc
    _ = (Gamma (2 * μ) * Gamma (2 * a - 2 * μ)) *
        ((quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
          regularizedAppellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2)
            ((Real.sin θ : ℂ) ^ 2) ((Real.sin φ : ℂ) ^ 2)) := by
      rw [← hm, ← hb]; ring
    _ = _ := by rw [H]; ring

end Carlson.TwoVariable
