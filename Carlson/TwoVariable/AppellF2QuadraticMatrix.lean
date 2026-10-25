/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF2Quadratic

/-!
# Explicit matrices in the fifth and sixth Appell quadratic transformations

Carlson (1976), (2.5) and (2.6). Polynomial coordinate identities identify
the original matrices with the normalized F₄ comparisons. The local matrix
homogeneity theorem accounts for the principal-power branch at each scale.
-/

open Complex Set Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The squared-node input of Carlson (1976), (2.5). -/
def appellF2F2InputMatrix (x y z w : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![x ^ 2, y ^ 2], ![z ^ 2, w ^ 2]]

/-- The quartic transformed matrix in Carlson (1976), (2.5). -/
def appellF2F2OutputMatrix (x y z w : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![((x ^ 2 + w ^ 2) / 2) ^ 2, ((x * y + z * w) / 2) ^ 2],
    ![((x * z + y * w) / 2) ^ 2, x * y * z * w]]

/-- The two equal diagonal sums give the product identity needed by the coordinate map. -/
private theorem fifth_product_identity {x y z w C : ℂ}
    (hX : 2 * C = x ^ 2 + w ^ 2) (hY : 2 * C = y ^ 2 + z ^ 2) :
    4 * C ^ 2 = (x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2) := by
  calc
    _ = (2 * C) * (2 * C) := by ring
    _ = _ := congrArg₂ (· * ·) hX hY

/-- Normalizing the squared-node parallelogram produces Bailey's matrix. -/
theorem appellF2F2InputMatrix_eq_scaled_bailey {x y z w C : ℂ} (hC : C ≠ 0)
    (hX : 2 * C = x ^ 2 + w ^ 2) (hY : 2 * C = y ^ 2 + z ^ 2) :
    appellF2F2InputMatrix x y z w = fun i j => C *
      appellF4BaileyMatrix ((z ^ 2 - x ^ 2) / (2 * C))
        ((y ^ 2 - x ^ 2) / (2 * C)) i j := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF2F2InputMatrix, appellF4BaileyMatrix]
  all_goals field_simp [hC]
  · linear_combination -hY
  · linear_combination -hY
  · linear_combination -hY
  · linear_combination hY - 2 * hX

/-- Reversing both rows and columns of the quartic matrix gives a scaled F₂ matrix. -/
theorem appellF2F2OutputMatrix_reverse_eq_scaled_F2 {x y z w C : ℂ} (hC : C ≠ 0)
    (hX : 2 * C = x ^ 2 + w ^ 2) (hY : 2 * C = y ^ 2 + z ^ 2) :
    (fun i j => appellF2F2OutputMatrix x y z w ((Equiv.swap 0 1) i) ((Equiv.swap 0 1) j)) =
      fun i j => C ^ 2 * appellF2Matrix ((x * y - z * w) ^ 2 / (4 * C ^ 2))
        ((x * z - y * w) ^ 2 / (4 * C ^ 2)) i j := by
  have H := fifth_product_identity hX hY
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF2F2OutputMatrix, appellF2Matrix]
  all_goals field_simp [hC]
  · linear_combination -H
  · linear_combination -4 * H
  · linear_combination -4 * H
  · rw [← hX]; ring

/-- The quartic coordinate change has precisely the nonlinear F₄ arguments. -/
theorem appellF2F2_quadratic_arguments {x y z w C : ℂ} (hC : C ≠ 0)
    (hX : 2 * C = x ^ 2 + w ^ 2) (hY : 2 * C = y ^ 2 + z ^ 2) :
    ((z ^ 2 - x ^ 2) / (2 * C)) ^ 2 =
        ((x * y - z * w) ^ 2 / (4 * C ^ 2)) *
          (1 - (x * z - y * w) ^ 2 / (4 * C ^ 2)) ∧
      ((y ^ 2 - x ^ 2) / (2 * C)) ^ 2 =
        ((x * z - y * w) ^ 2 / (4 * C ^ 2)) *
          (1 - (x * y - z * w) ^ 2 / (4 * C ^ 2)) := by
  have H := fifth_product_identity hX hY
  have hA : 1 - (x * z - y * w) ^ 2 / (4 * C ^ 2) =
      (x * y + z * w) ^ 2 / (4 * C ^ 2) := by
    field_simp [hC]
    linear_combination H
  have hB : 1 - (x * y - z * w) ^ 2 / (4 * C ^ 2) =
      (x * z + y * w) ^ 2 / (4 * C ^ 2) := by
    field_simp [hC]
    linear_combination H
  have hP : (x * y - z * w) * (x * y + z * w) = 2 * C * (x ^ 2 - z ^ 2) := by
    linear_combination -x ^ 2 * hY + z ^ 2 * hX
  have hQ : (x * z - y * w) * (x * z + y * w) = 2 * C * (x ^ 2 - y ^ 2) := by
    linear_combination -x ^ 2 * hY + y ^ 2 * hX
  constructor
  · rw [hA]
    calc
      _ = ((2 * C * (x ^ 2 - z ^ 2)) / (4 * C ^ 2)) ^ 2 := by field_simp [hC]; ring
      _ = _ := by rw [← hP]; field_simp [hC]
  · rw [hB]
    calc
      _ = ((2 * C * (x ^ 2 - y ^ 2)) / (4 * C ^ 2)) ^ 2 := by field_simp [hC]; ring
      _ = _ := by rw [← hQ]; field_simp [hC]

/-- Reversing both index orders reverses both parameter pairs. -/
private theorem continued_reverseBoth (t r s b c : ℂ) {Z : Fin 2 → Fin 2 → ℂ}
    (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage
      (fun i j => Z ((Equiv.swap 0 1) i) ((Equiv.swap 0 1) j)) (fun z => z ^ t)
      (pair s r, pair c b) =
        continuedRegMatrixDirichletAverage Z (fun z => z ^ t) (pair r s, pair b c) := by
  have hp (a d : ℂ) : pair a d ∘ Equiv.swap (0 : Fin 2) 1 = pair d a := by
    funext i; fin_cases i <;> simp [pair]
  have hc := continuedRegMatrixDirichletAverage_perm_columns isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane (f := fun z : ℂ => z ^ t)
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) hZ (Equiv.swap 0 1)
    (pair r s) (pair b c)
  have hr := continuedRegMatrixDirichletAverage_perm_rows isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane (f := fun z : ℂ => z ^ t)
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (fun i j => hZ i ((Equiv.swap 0 1) j)) (Equiv.swap 0 1) (pair r s) (pair c b)
  simp only [hp] at hc hr
  exact hr.trans hc

/-- **Carlson (1976), (2.5), explicit matrices.** The diagonal-square sums equal `2C`.
The common series bounds and all principal-power branch conditions are explicit.
All complex averaging parameters are retained by the two duplication ratios. -/
theorem continuedMatrix_fifthQuadratic_explicit (t μ : ℂ) {x y z w C : ℂ}
    (hX : 2 * C = x ^ 2 + w ^ 2) (hY : 2 * C = y ^ 2 + z ^ 2)
    (hC : 0 < C.re) (hC2 : 0 < (C ^ 2).re)
    (hZ : appellF2F2InputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellF2F2OutputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hsub : Real.sqrt (‖(x * y - z * w) ^ 2 / (4 * C ^ 2)‖ *
        (1 + ‖(x * z - y * w) ^ 2 / (4 * C ^ 2)‖)) +
      Real.sqrt (‖(x * z - y * w) ^ 2 / (4 * C ^ 2)‖ *
        (1 + ‖(x * y - z * w) ^ 2 / (4 * C ^ 2)‖)) < 1)
    (hxy : ‖(z ^ 2 - x ^ 2) / (2 * C)‖ + ‖(y ^ 2 - x ^ 2) / (2 * C)‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF2F2InputMatrix x y z w) (fun z => z ^ (2 * t))
      (pair μ μ, pair (-μ - t) (-μ - t)) =
        (quadraticGammaRatio μ * quadraticGammaRatio (-μ - t)) *
          continuedRegMatrixDirichletAverage (appellF2F2OutputMatrix x y z w) (fun z => z ^ t)
            (pair (μ + t) (1 / 2 - t), pair (-μ) (1 / 2 - t)) := by
  let S := (z ^ 2 - x ^ 2) / (2 * C)
  let T := (y ^ 2 - x ^ 2) / (2 * C)
  let U := (x * y - z * w) ^ 2 / (4 * C ^ 2)
  let V := (x * z - y * w) ^ 2 / (4 * C ^ 2)
  have hC0 : C ≠ 0 := fun h => by rw [h] at hC; simp at hC
  have hargs := appellF2F2_quadratic_arguments hC0 hX hY
  have H := continuedMatrix_fifthQuadratic (-t) μ hsub hxy hargs.1 hargs.2
  have hr : appellF2Parameters (-t + 1 / 2) (μ + 1 / 2) =
      pair (1 / 2 - t) (μ + t) := by
    funext i
    fin_cases i <;> simp [appellF2Parameters, pair]
    all_goals ring
  have hb : appellF2Parameters (-t + 1 / 2) (-μ - t + 1 / 2) =
      pair (1 / 2 - t) (-μ) := by
    funext i
    fin_cases i <;> simp [appellF2Parameters, pair]
    all_goals ring
  rw [show -(2 * -t) = 2 * t by ring, neg_neg,
    show -t - μ = -μ - t by ring, hr, hb] at H
  have hd : ‖U‖ + ‖V‖ < 1 := by
    have h := appellF4_reassembly_kernel_bound hsub
    dsimp [U, V]
    nlinarith [mul_nonneg (norm_nonneg ((x * y - z * w) ^ 2 / (4 * C ^ 2)))
      (norm_nonneg ((x * z - y * w) ^ 2 / (4 * C ^ 2)))]
  have hIn := appellF2F2InputMatrix_eq_scaled_bailey hC0 hX hY
  have hOut := appellF2F2OutputMatrix_reverse_eq_scaled_F2 hC0 hX hY
  have hL := continuedRegMatrixDirichletAverage_mul_cpow_neg
    (pair μ μ) (pair (-μ - t) (-μ - t)) (appellF4BaileyMatrix_mem_rightHalfPlane hxy)
    hC (by rw [← hIn]; exact hZ) (-(2 * t))
  have hR := continuedRegMatrixDirichletAverage_mul_cpow_neg
    (pair (1 / 2 - t) (μ + t)) (pair (1 / 2 - t) (-μ))
    (appellF2Matrix_mem_rightHalfPlane hd) hC2 (by
      rw [← hOut]; exact fun i j => hW ((Equiv.swap 0 1) i) ((Equiv.swap 0 1) j)) (-t)
  simp only [neg_neg] at hL hR
  have hp := continued_reverseBoth t (μ + t) (1 / 2 - t) (-μ) (1 / 2 - t) hW
  rw [hOut] at hp
  have he : C ^ (2 * t) = (C ^ 2) ^ t := by
    rw [show (2 : ℂ) * t = t + t by ring, cpow_add _ _ hC0,
      show C ^ 2 = C * C by ring, mul_cpow_of_re_pos hC hC]
  rw [hIn, hL, H, ← hp, hR, he]
  ring

/-- The input matrix of Carlson (1976), (2.6). -/
def appellF2F1InputMatrix (x y z w : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![x ^ 2, y ^ 2], ![x ^ 2 + z ^ 2, y ^ 2 + w ^ 2]]

/-- The transformed matrix of Carlson (1976), (2.6). -/
def appellF2F1OutputMatrix (x y z w : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![x * y, ((x + y) / 2) ^ 2 + ((z + w) / 2) ^ 2],
    ![((x + y) / 2) ^ 2 + ((z - w) / 2) ^ 2, x ^ 2 + z ^ 2]]

/-- The input of (2.6) is the equal-denominator F₄ matrix after a common scale. -/
theorem appellF2F1InputMatrix_eq_scaled_equal {x y z w ℓ : ℂ} (hℓ : ℓ ≠ 0)
    (hX : ℓ ^ 2 = x ^ 2 + z ^ 2) (hY : ℓ ^ 2 = y ^ 2 + w ^ 2) :
    appellF2F1InputMatrix x y z w = fun i j => ℓ ^ 2 *
      appellF4EqualMatrix ((z - w) / (2 * ℓ)) ((z + w) / (2 * ℓ)) i j := by
  have hp : (z - w) / (2 * ℓ) + (z + w) / (2 * ℓ) = z / ℓ := by field_simp; ring
  have hm : (z - w) / (2 * ℓ) - (z + w) / (2 * ℓ) = -w / ℓ := by field_simp; ring
  funext i j
  fin_cases i <;> fin_cases j
  · change x ^ 2 = ℓ ^ 2 * (1 - _)
    rw [hp, div_pow, mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hℓ)]
    linear_combination -hX
  · change y ^ 2 = ℓ ^ 2 * (1 - _)
    rw [hm, div_pow, neg_sq, mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hℓ)]
    linear_combination -hY
  · simpa [appellF2F1InputMatrix, appellF4EqualMatrix] using hX.symm
  · simpa [appellF2F1InputMatrix, appellF4EqualMatrix] using hY.symm

/-- The output of (2.6) is a scaled F₂ parallelogram. -/
theorem appellF2F1OutputMatrix_eq_scaled_F2 {x y z w ℓ : ℂ} (hℓ : ℓ ≠ 0)
    (hX : ℓ ^ 2 = x ^ 2 + z ^ 2) (hY : ℓ ^ 2 = y ^ 2 + w ^ 2) :
    appellF2F1OutputMatrix x y z w = fun i j => ℓ ^ 2 *
      appellF2Matrix ((ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2))
        ((ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)) i j := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF2F1OutputMatrix, appellF2Matrix]
  all_goals field_simp [hℓ]
  · ring
  · linear_combination -hX - hY
  · linear_combination -hX - hY
  · linear_combination -hX

/-- The nonlinear coordinate identities for the sixth transformation. -/
theorem appellF2F1_quadratic_arguments {x y z w ℓ : ℂ} (hℓ : ℓ ≠ 0)
    (hX : ℓ ^ 2 = x ^ 2 + z ^ 2) (hY : ℓ ^ 2 = y ^ 2 + w ^ 2) :
    ((z - w) / (2 * ℓ)) ^ 2 =
        ((ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)) *
          (1 - (ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)) ∧
      ((z + w) / (2 * ℓ)) ^ 2 =
        ((ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)) *
          (1 - (ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)) := by
  have H : (ℓ ^ 2 - z ^ 2) * (ℓ ^ 2 - w ^ 2) = x ^ 2 * y ^ 2 := by
    rw [show ℓ ^ 2 - z ^ 2 = x ^ 2 by linear_combination hX,
      show ℓ ^ 2 - w ^ 2 = y ^ 2 by linear_combination hY]
  have hp : (ℓ ^ 2 - x * y - z * w) * (ℓ ^ 2 + x * y - z * w) =
      ℓ ^ 2 * (z - w) ^ 2 := by linear_combination H
  have hm : (ℓ ^ 2 - x * y + z * w) * (ℓ ^ 2 + x * y + z * w) =
      ℓ ^ 2 * (z + w) ^ 2 := by linear_combination H
  constructor
  · calc
      _ = ((ℓ ^ 2 - x * y - z * w) * (ℓ ^ 2 + x * y - z * w)) / (4 * ℓ ^ 4) := by
        rw [hp]; field_simp [hℓ]; ring
      _ = _ := by field_simp [hℓ]; ring
  · calc
      _ = ((ℓ ^ 2 - x * y + z * w) * (ℓ ^ 2 + x * y + z * w)) / (4 * ℓ ^ 4) := by
        rw [hm]; field_simp [hℓ]; ring
      _ = _ := by field_simp [hℓ]; ring

/-- **Carlson (1976), (2.6), explicit matrices.** The square `ℓ²` is the common
bottom-row value. The convergence and matrix branch conditions are stated explicitly;
no averaging parameter is excluded in this regularized form. -/
theorem continuedMatrix_sixthQuadratic_explicit (t μ : ℂ) {x y z w ℓ : ℂ}
    (hX : ℓ ^ 2 = x ^ 2 + z ^ 2) (hY : ℓ ^ 2 = y ^ 2 + w ^ 2)
    (hC : 0 < (ℓ ^ 2).re)
    (hZ : appellF2F1InputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellF2F1OutputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hsub : Real.sqrt (‖(ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)‖ *
        (1 + ‖(ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)‖)) +
      Real.sqrt (‖(ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)‖ *
        (1 + ‖(ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)‖)) < 1)
    (hxy : ‖(z - w) / (2 * ℓ)‖ + ‖(z + w) / (2 * ℓ)‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF2F1InputMatrix x y z w) (fun z => z ^ (2 * t))
      (pair μ (1 / 2 - μ - t), pair (-t) (-t)) =
        quadraticGammaRatio (-t) *
          continuedRegMatrixDirichletAverage (appellF2F1OutputMatrix x y z w)
            (fun z => z ^ (2 * t)) (pair μ (1 / 2 - μ - t), pair μ (1 / 2 - μ - t)) := by
  let U := (ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)
  let V := (ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)
  have hℓ : ℓ ≠ 0 := by intro h; simp [h] at hC
  have hargs := appellF2F1_quadratic_arguments hℓ hX hY
  have H := continuedMatrix_sixthQuadratic (-t) μ hsub hxy hargs.1 hargs.2
  have hr : appellF2Parameters μ (-t + 1 / 2) = pair μ (1 / 2 - μ - t) := by
    funext i
    fin_cases i <;> simp [appellF2Parameters, pair]
    all_goals ring
  rw [show -(2 * -t) = 2 * t by ring, hr] at H
  have hd : ‖U‖ + ‖V‖ < 1 := by
    have h := appellF4_reassembly_kernel_bound hsub
    dsimp [U, V]
    nlinarith [mul_nonneg (norm_nonneg ((ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)))
      (norm_nonneg ((ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)))]
  have hIn := appellF2F1InputMatrix_eq_scaled_equal hℓ hX hY
  have hOut := appellF2F1OutputMatrix_eq_scaled_F2 hℓ hX hY
  have hL := continuedRegMatrixDirichletAverage_mul_cpow_neg
    (pair μ (1 / 2 - μ - t)) (pair (-t) (-t))
    (appellF4EqualMatrix_mem_rightHalfPlane hxy) hC (by rw [← hIn]; exact hZ) (-(2 * t))
  have hR := continuedRegMatrixDirichletAverage_mul_cpow_neg
    (pair μ (1 / 2 - μ - t)) (pair μ (1 / 2 - μ - t))
    (appellF2Matrix_mem_rightHalfPlane hd) hC (by rw [← hOut]; exact hW) (-(2 * t))
  simp only [neg_neg] at hL hR
  rw [hIn, hOut, hL, hR, H]
  ring

/-- **Carlson (1976), (2.6), native normalized form.** This form assumes positive
real parts in both native averaging vectors. -/
theorem matrix_sixthQuadratic_explicit (t μ : ℂ) {x y z w ℓ : ℂ}
    (hX : ℓ ^ 2 = x ^ 2 + z ^ 2) (hY : ℓ ^ 2 = y ^ 2 + w ^ 2)
    (hC : 0 < (ℓ ^ 2).re)
    (hZ : appellF2F1InputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellF2F1OutputMatrix x y z w ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hsub : Real.sqrt (‖(ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)‖ *
        (1 + ‖(ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)‖)) +
      Real.sqrt (‖(ℓ ^ 2 - x * y + z * w) / (2 * ℓ ^ 2)‖ *
        (1 + ‖(ℓ ^ 2 - x * y - z * w) / (2 * ℓ ^ 2)‖)) < 1)
    (hxy : ‖(z - w) / (2 * ℓ)‖ + ‖(z + w) / (2 * ℓ)‖ < 1)
    (hr : pair μ (1 / 2 - μ - t) ∈ mvBetaConvergent) (ht : 0 < (-t).re) :
    matrixDirichletAverage (pair μ (1 / 2 - μ - t)) (pair (-t) (-t))
      (appellF2F1InputMatrix x y z w) (fun z => z ^ (2 * t)) =
        matrixDirichletAverage (pair μ (1 / 2 - μ - t)) (pair μ (1 / 2 - μ - t))
          (appellF2F1OutputMatrix x y z w) (fun z => z ^ (2 * t)) := by
  have hb : pair (-t) (-t) ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> exact ht
  have H := continuedMatrix_sixthQuadratic_explicit t μ hX hY hC hZ hW hsub hxy
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (2 * t)) carlsonRightHalfPlane :=
    fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)
  rw [continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
      convex_carlsonRightHalfPlane hf hZ hr hb,
    continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
      convex_carlsonRightHalfPlane hf hW hr hr] at H
  rw [matrixDirichletAverage, matrixDirichletAverage, H]
  simp only [sum_pair]
  rw [show μ + (1 / 2 - μ - t) = -t + 1 / 2 by ring]
  have hG := Gamma_mul_quadraticGammaRatio ht
  linear_combination Gamma (-t + 1 / 2) *
    regMatrixDirichletAverage (pair μ (1 / 2 - μ - t)) (pair μ (1 / 2 - μ - t))
      (appellF2F1OutputMatrix x y z w) (fun z => z ^ (2 * t)) * hG

end Carlson.TwoVariable
