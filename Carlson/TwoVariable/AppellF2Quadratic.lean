/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellQuadraticMatrix

/-!
# The quadratic F₂ transformations

Carlson (1976), (2.10) and (2.12), obtained by comparing the proved F₄
reductions as on page 296 of the article. Absolute convergence permits
coefficient comparison and reassembly. Reciprocal Gamma and duplication
factors retain exceptional parameters; ordinary formulas state the needed
Gamma-cancellation conditions.
-/

open Complex Set Dirichlet Polynomial Finset
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Each F₁ homogeneous term is its two-node numerator times one scalar coefficient. -/
private theorem F1_antidiagonal_eq_numerator (a b c X Y : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, regularizedAppellF1Coeff a b b c p * X ^ p.1 * Y ^ p.2 =
      (ascPochhammer ℂ N).eval a / Gamma (c + N) *
        (carlsonRPolynomialNumerator₂ N b b X Y / (N.factorial : ℂ)) := by
  rw [← carlsonRPolynomialNumerator_pair, numerator_pair_div_factorial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hn := mem_antidiagonal.mp hp
  rw [regularizedAppellF1Coeff_eq, hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Equal-denominator F₄ with numerator `2α` reduces to F₁. Reciprocal Gamma
normalization makes the identity valid at every complex parameter. -/
theorem regularizedAppellF4_eq_equalAppellF1 (α b : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    regularizedAppellF4 (2 * α) b (α + 1 / 2) (α + 1 / 2) (x ^ 2) (y ^ 2) =
      (Gamma (α + 1 / 2))⁻¹ *
        regularizedAppellF1 b α α (α + 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  have hn (z : ℂ) (hz : ‖z‖ ≤ ‖x‖ + ‖y‖) : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have H4 := hasSum_regularizedAppellF4_equalRPolynomial
    (2 * α) b (α + 1 / 2) hxy
  have H1 := (hasSum_regularizedAppellF1_antidiagonal
    (a := b) (b₁ := α) (b₂ := α) (c := α + 1 / 2)
    (hn (x + y) (norm_add_le x y)) (hn (x - y) (norm_sub_le x y))).mul_left
      (Gamma (α + 1 / 2))⁻¹
  apply H4.unique
  convert H1 using 1
  funext N
  rw [F1_antidiagonal_eq_numerator, gaussCoeff,
    show α + 1 / 2 - 1 / 2 = α by ring]
  have hp := ascPochhammer_mul_regEqualRPolynomial N α ((x + y) ^ 2) ((x - y) ^ 2)
  simp only [div_eq_mul_inv, mul_inv_rev] at hp ⊢
  simp only [one_mul] at hp ⊢
  linear_combination ((ascPochhammer ℂ N).eval b * (N.factorial : ℂ)⁻¹ *
    (Gamma (α + (2 : ℂ)⁻¹ + N))⁻¹) * hp

/-- The algebraic F₂-to-F₁ quadratic reduction on a common series domain. -/
theorem regularizedAppellF2_quadratic_F1 (α b : ℂ) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1) (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    regularizedAppellF2 (2 * α) b b (α + 1 / 2) (α + 1 / 2) u v =
      (Gamma (α + 1 / 2))⁻¹ *
        regularizedAppellF1 b α α (α + 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  rw [← regularizedAppellF4_eq_F2
    (show (α + 1 / 2) + (α + 1 / 2) = 2 * α + 1 by ring) hsub, ← hx, ← hy]
  exact regularizedAppellF4_eq_equalAppellF1 α b hxy

/-- Ordinary normalization of the algebraic F₂-to-F₁ reduction. At denominator poles
both named ordinary functions have their specified Gamma-normalized value. -/
theorem appellF2_quadratic_F1 (α b : ℂ) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1) (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    appellF2 (2 * α) b b (α + 1 / 2) (α + 1 / 2) u v =
      appellF1 b α α (α + 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  rw [appellF2, regularizedAppellF2_quadratic_F1 α b hsub hxy hx hy, Complex.appellF1]
  by_cases hG : Gamma (α + 1 / 2) = 0
  · simp only [hG, zero_mul, mul_zero, inv_zero]
  · field_simp

/-- The trigonometric coordinates used in both named quadratic transformations. -/
private theorem trig_quadratic_arguments (θ φ : ℂ) :
    (sin θ * cos φ) ^ 2 = sin θ ^ 2 * (1 - sin φ ^ 2) ∧
      (cos θ * sin φ) ^ 2 = sin φ ^ 2 * (1 - sin θ ^ 2) := by
  constructor
  · rw [mul_pow, cos_sq']
  · rw [mul_pow, cos_sq']; ring

/-- **Carlson (1976), (2.12), regularized.** The explicit convergence bounds account
for all series used in the proof; every complex parameter is retained. -/
theorem regularizedAppellF2_quadratic_sin_F1 (α b θ φ : ℂ)
    (hsub : Real.sqrt (‖sin θ ^ 2‖ * (1 + ‖sin φ ^ 2‖)) +
      Real.sqrt (‖sin φ ^ 2‖ * (1 + ‖sin θ ^ 2‖)) < 1)
    (hxy : ‖sin θ * cos φ‖ + ‖cos θ * sin φ‖ < 1) :
    regularizedAppellF2 (2 * α) b b (α + 1 / 2) (α + 1 / 2) (sin θ ^ 2) (sin φ ^ 2) =
      (Gamma (α + 1 / 2))⁻¹ *
        regularizedAppellF1 b α α (α + 1 / 2) (sin (θ + φ) ^ 2) (sin (θ - φ) ^ 2) := by
  simpa only [sin_add, sin_sub] using regularizedAppellF2_quadratic_F1 α b hsub hxy
    (trig_quadratic_arguments θ φ).1 (trig_quadratic_arguments θ φ).2

/-- **Carlson (1976), (2.12), ordinary form.** -/
theorem appellF2_quadratic_sin_F1 (α b θ φ : ℂ)
    (hsub : Real.sqrt (‖sin θ ^ 2‖ * (1 + ‖sin φ ^ 2‖)) +
      Real.sqrt (‖sin φ ^ 2‖ * (1 + ‖sin θ ^ 2‖)) < 1)
    (hxy : ‖sin θ * cos φ‖ + ‖cos θ * sin φ‖ < 1) :
    appellF2 (2 * α) b b (α + 1 / 2) (α + 1 / 2) (sin θ ^ 2) (sin φ ^ 2) =
      appellF1 b α α (α + 1 / 2) (sin (θ + φ) ^ 2) (sin (θ - φ) ^ 2) := by
  simpa only [sin_add, sin_sub] using appellF2_quadratic_F1 α b hsub hxy
    (trig_quadratic_arguments θ φ).1 (trig_quadratic_arguments θ φ).2

/-- The centered parallelogram is a scalar multiple of the standard F₂ matrix. -/
private theorem baileyMatrix_eq_scaled_F2 (x y : ℂ) (hs : 1 + x + y ≠ 0) :
    appellF4BaileyMatrix x y = fun i j => (1 + x + y) *
      appellF2Matrix (2 * x / (1 + x + y)) (2 * y / (1 + x + y)) i j := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF4BaileyMatrix, appellF2Matrix]
  all_goals simp only [mul_sub, mul_one, mul_div_cancel₀ _ hs]
  all_goals ring

/-- The standard F₂ matrix is in the principal branch on its convergence diamond. -/
theorem appellF2Matrix_mem_rightHalfPlane {u v : ℂ} (huv : ‖u‖ + ‖v‖ < 1) :
    appellF2Matrix u v ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have hr := (abs_re_le_norm (appellF2Matrix u v i j - 1)).trans_lt
    ((norm_appellF2Matrix_sub_one_le u v i j).trans_lt huv)
  simp only [sub_re, one_re] at hr
  change 0 < (appellF2Matrix u v i j).re
  linarith [neg_abs_le ((appellF2Matrix u v i j).re - 1)]

/-- The continued Bailey matrix as a scaled F₂ function, at arbitrary parameters. -/
theorem continuedBaileyMatrix_eq_F2 (a μ : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1)
    (hF2 : ‖2 * x / (1 + x + y)‖ + ‖2 * y / (1 + x + y)‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => z ^ (-(2 * a)))
      (pair μ μ, pair (a - μ) (a - μ)) =
        (1 + x + y) ^ (-(2 * a)) * regularizedAppellF2 (2 * a) μ (a - μ)
          (μ + μ) ((a - μ) + (a - μ)) (2 * x / (1 + x + y)) (2 * y / (1 + x + y)) := by
  have hs : 0 < (1 + x + y).re := appellF4BaileyMatrix_mem_rightHalfPlane hxy 1 1
  have hs0 : 1 + x + y ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hp (b : ℂ) : pair b b = appellF2Parameters b (b + b) := by
    funext i; fin_cases i <;> simp [pair, appellF2Parameters]
  have hscaled : (fun i j => (1 + x + y) *
      appellF2Matrix (2 * x / (1 + x + y)) (2 * y / (1 + x + y)) i j) ∈
        matrixNodeDomain carlsonRightHalfPlane := by
    rw [← baileyMatrix_eq_scaled_F2 x y hs0]
    exact appellF4BaileyMatrix_mem_rightHalfPlane hxy
  rw [baileyMatrix_eq_scaled_F2 x y hs0,
    continuedRegMatrixDirichletAverage_mul_cpow_neg (pair μ μ) (pair (a - μ) (a - μ))
      (appellF2Matrix_mem_rightHalfPlane hF2) hs hscaled (2 * a),
    hp μ, hp (a - μ), continuedRegMatrixDirichletAverage_eq_regularizedAppellF2]
  exact hF2

/-- **Carlson (1976), (2.5), in normalized algebraic coordinates.** Eliminating F₄
retains both duplication ratios, including their zeros. -/
theorem continuedMatrix_fifthQuadratic (a μ : ℂ) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1) (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => z ^ (-(2 * a)))
      (pair μ μ, pair (a - μ) (a - μ)) =
        (quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
          continuedRegMatrixDirichletAverage (appellF2Matrix u v) (fun z => z ^ (-a))
            (appellF2Parameters (a + 1 / 2) (μ + 1 / 2),
              appellF2Parameters (a + 1 / 2) (a - μ + 1 / 2)) := by
  have hd : ‖u‖ + ‖v‖ < 1 := by
    have h := appellF4_reassembly_kernel_bound hsub
    nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 _ _ _ _ _ hd]
  have H := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_bailey
    a (μ + 1 / 2) (a - μ + 1 / 2) hxy
  rw [show μ + 1 / 2 - 1 / 2 = μ by ring,
    show a - μ + 1 / 2 - 1 / 2 = a - μ by ring, hx, hy,
    regularizedAppellF4_eq_F2
      (show μ + 1 / 2 + (a - μ + 1 / 2) = a + 1 by ring) hsub] at H
  exact H

/-- The algebraic F₂-to-F₂ quadratic transformation, with entire normalization. -/
theorem regularizedAppellF2_quadratic_self (a μ : ℂ) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hF2 : ‖2 * x / (1 + x + y)‖ + ‖2 * y / (1 + x + y)‖ < 1)
    (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    (quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
        regularizedAppellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2) u v =
      (1 + x + y) ^ (-(2 * a)) * regularizedAppellF2 (2 * a) μ (a - μ)
        (μ + μ) ((a - μ) + (a - μ)) (2 * x / (1 + x + y)) (2 * y / (1 + x + y)) := by
  have H := continuedMatrix_fifthQuadratic a μ hsub hxy hx hy
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 _ _ _ _ _
    (by have h := appellF4_reassembly_kernel_bound hsub
        nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)])] at H
  exact H.symm.trans (continuedBaileyMatrix_eq_F2 a μ hxy hF2)

/-- Ordinary F₂-to-F₂ transformation away from the two transformed denominator pole sets. -/
theorem appellF2_quadratic_self (a μ : ℂ)
    (hμ : ∀ k : ℕ, μ + μ ≠ -(k : ℂ))
    (hβ : ∀ k : ℕ, (a - μ) + (a - μ) ≠ -(k : ℂ)) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hF2 : ‖2 * x / (1 + x + y)‖ + ‖2 * y / (1 + x + y)‖ < 1)
    (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    appellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2) u v =
      (1 + x + y) ^ (-(2 * a)) * appellF2 (2 * a) μ (a - μ)
        (μ + μ) ((a - μ) + (a - μ)) (2 * x / (1 + x + y)) (2 * y / (1 + x + y)) := by
  have hμ' : ∀ k : ℕ, μ ≠ -(k : ℂ) := by
    intro k hk
    exact hμ (k + k) (by push_cast; rw [hk]; ring)
  have hβ' : ∀ k : ℕ, a - μ ≠ -(k : ℂ) := by
    intro k hk
    exact hβ (k + k) (by push_cast; rw [hk]; ring)
  have hGμ := Gamma_mul_quadraticGammaRatio_of_ne hμ'
  have hGβ := Gamma_mul_quadraticGammaRatio_of_ne hβ'
  have H := regularizedAppellF2_quadratic_self a μ hsub hxy hF2 hx hy
  rw [appellF2, appellF2]
  calc
    _ = (Gamma (μ + μ) * Gamma ((a - μ) + (a - μ))) *
        ((quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
          regularizedAppellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2) u v) := by
      rw [← hGμ, ← hGβ]; ring
    _ = _ := by rw [H]; ring

/-- **Carlson (1976), (2.10), regularized.** Both duplication ratios remain explicit,
so all complex averaging parameters are included. -/
theorem regularizedAppellF2_quadratic_sin_self (a μ θ φ : ℂ)
    (hsub : Real.sqrt (‖sin θ ^ 2‖ * (1 + ‖sin φ ^ 2‖)) +
      Real.sqrt (‖sin φ ^ 2‖ * (1 + ‖sin θ ^ 2‖)) < 1)
    (hxy : ‖sin θ * cos φ‖ + ‖cos θ * sin φ‖ < 1)
    (hF2 : ‖2 * sin θ * cos φ / (1 + sin (θ + φ))‖ +
      ‖2 * cos θ * sin φ / (1 + sin (θ + φ))‖ < 1) :
    (quadraticGammaRatio μ * quadraticGammaRatio (a - μ)) *
        regularizedAppellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2)
          (sin θ ^ 2) (sin φ ^ 2) =
      (1 + sin (θ + φ)) ^ (-(2 * a)) * regularizedAppellF2 (2 * a) μ (a - μ)
        (2 * μ) (2 * a - 2 * μ) (2 * sin θ * cos φ / (1 + sin (θ + φ)))
          (2 * cos θ * sin φ / (1 + sin (θ + φ))) := by
  have hs : 1 + sin θ * cos φ + cos θ * sin φ = 1 + sin (θ + φ) := by
    rw [sin_add]; ring
  have hd : (a - μ) + (a - μ) = 2 * a - 2 * μ := by ring
  simpa only [hs, hd, show μ + μ = 2 * μ by ring, mul_assoc] using
    regularizedAppellF2_quadratic_self a μ hsub hxy
      (by simpa only [hs, mul_assoc] using hF2)
      (trig_quadratic_arguments θ φ).1 (trig_quadratic_arguments θ φ).2

/-- **Carlson (1976), (2.10), ordinary form.** The two transformed denominator
parameters must avoid the nonpositive integers. -/
theorem appellF2_quadratic_sin_self (a μ θ φ : ℂ)
    (hμ : ∀ k : ℕ, 2 * μ ≠ -(k : ℂ)) (hβ : ∀ k : ℕ, 2 * a - 2 * μ ≠ -(k : ℂ))
    (hsub : Real.sqrt (‖sin θ ^ 2‖ * (1 + ‖sin φ ^ 2‖)) +
      Real.sqrt (‖sin φ ^ 2‖ * (1 + ‖sin θ ^ 2‖)) < 1)
    (hxy : ‖sin θ * cos φ‖ + ‖cos θ * sin φ‖ < 1)
    (hF2 : ‖2 * sin θ * cos φ / (1 + sin (θ + φ))‖ +
      ‖2 * cos θ * sin φ / (1 + sin (θ + φ))‖ < 1) :
    appellF2 a (a + 1 / 2) (a + 1 / 2) (μ + 1 / 2) (a - μ + 1 / 2)
      (sin θ ^ 2) (sin φ ^ 2) =
      (1 + sin (θ + φ)) ^ (-(2 * a)) * appellF2 (2 * a) μ (a - μ)
        (2 * μ) (2 * a - 2 * μ) (2 * sin θ * cos φ / (1 + sin (θ + φ)))
          (2 * cos θ * sin φ / (1 + sin (θ + φ))) := by
  have hs : 1 + sin θ * cos φ + cos θ * sin φ = 1 + sin (θ + φ) := by
    rw [sin_add]; ring
  have hd : (a - μ) + (a - μ) = 2 * a - 2 * μ := by ring
  have hm : μ + μ = 2 * μ := by ring
  simpa only [hs, hd, hm, mul_assoc] using appellF2_quadratic_self a μ
    (by simpa only [hm] using hμ) (by simpa only [hd] using hβ) hsub hxy
    (by simpa only [hs, mul_assoc] using hF2)
    (trig_quadratic_arguments θ φ).1 (trig_quadratic_arguments θ φ).2

/-- **Carlson (1976), (2.6), normalized algebraic coordinates.** The regularized
transformation retains the duplication ratio in the column normalization. -/
theorem continuedMatrix_sixthQuadratic (a b : ℂ) {u v x y : ℂ}
    (hsub : Real.sqrt (‖u‖ * (1 + ‖v‖)) + Real.sqrt (‖v‖ * (1 + ‖u‖)) < 1)
    (hxy : ‖x‖ + ‖y‖ < 1) (hx : x ^ 2 = u * (1 - v)) (hy : y ^ 2 = v * (1 - u)) :
    continuedRegMatrixDirichletAverage (appellF4EqualMatrix x y) (fun z => z ^ (-(2 * a)))
      (appellF2Parameters b (a + 1 / 2), pair a a) =
        quadraticGammaRatio a *
          continuedRegMatrixDirichletAverage (appellF2Matrix u v) (fun z => z ^ (-(2 * a)))
            (appellF2Parameters b (a + 1 / 2), appellF2Parameters b (a + 1 / 2)) := by
  have hd : ‖u‖ + ‖v‖ < 1 := by
    have h := appellF4_reassembly_kernel_bound hsub
    nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  have H := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_equal
    (2 * a) b (a + 1 / 2) hxy
  rw [show a + 1 / 2 - 1 / 2 = a by ring, hx, hy,
    regularizedAppellF4_eq_F2
      (show (a + 1 / 2) + (a + 1 / 2) = 2 * a + 1 by ring) hsub] at H
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 _ _ _ _ _ hd]
  exact H

end Carlson.TwoVariable
