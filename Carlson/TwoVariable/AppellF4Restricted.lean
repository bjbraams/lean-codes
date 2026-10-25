/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Reassembly

/-!
# Restricted two-by-two matrices for Appell F₄

Carlson (1975), equations (4.1)–(4.3). Explicit polynomial moments identify
the matrices at every parameter, including zero column parameters and Gamma
poles. Native normalized forms are separated from their entire continuations.
-/

open Complex Polynomial Finset Set Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The product-of-Gauss matrix in Carlson (1975), equation (4.1). -/
def appellF4ProductMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(1 - x) * (1 - y), 1 - x], ![1 - y, 1]]

/-- The F₁ matrix in Carlson (1975), equation (4.2), in the paper's column order. -/
def appellF4F1Matrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![1 - x - y, (1 - x) * (1 - y)], ![1 - y, 1 - y]]

/-- Shifted kernel of the product-of-Gauss matrix. -/
theorem matrixAffineForm_appellF4Product (x y : ℂ) {u v : Fin 2 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    1 - matrixAffineForm (appellF4ProductMatrix x y) u v =
      (x * (u 0 : ℂ)) * (1 - y * (v 0 : ℂ)) + y * (v 0 : ℂ) := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv1 : (v 1 : ℂ) = 1 - (v 0 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF4ProductMatrix, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hu1, hv1]
  ring

/-- Shifted kernel of the F₁ matrix, with its nonconstant column coordinate last. -/
theorem matrixAffineForm_appellF4F1 (x y : ℂ) {u v : Fin 2 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    1 - matrixAffineForm (appellF4F1Matrix x y) u v =
      (x * (u 0 : ℂ)) * (1 - y * (v 1 : ℂ)) + y := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv0 : (v 0 : ℂ) = 1 - (v 1 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF4F1Matrix, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hu1, hv0]
  ring

/-- Entire polynomial moments of the product-of-Gauss matrix. -/
def appellF4ProductMoment (x y : ℂ) (N : ℕ)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 *
    ((ascPochhammer ℂ q.1).eval (p.1 0) / Gamma (p.1 0 + p.1 1 + q.1)) *
    ∑ k ∈ antidiagonal q.1, (q.1.choose k.1 : ℂ) * (-y) ^ k.1 * y ^ q.2 *
      ((ascPochhammer ℂ (k.1 + q.2)).eval (p.2 0) /
        Gamma (p.2 0 + p.2 1 + (k.1 + q.2 : ℕ)))

/-- Entire polynomial moments of the repeated-row F₁ matrix. -/
def appellF4F1Moment (x y : ℂ) (N : ℕ)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 *
    ((ascPochhammer ℂ q.1).eval (p.1 0) / Gamma (p.1 0 + p.1 1 + q.1)) *
    ∑ k ∈ antidiagonal q.1, (q.1.choose k.1 : ℂ) * (-y) ^ k.1 * y ^ q.2 *
      ((ascPochhammer ℂ k.1).eval (p.2 1) / Gamma (p.2 0 + p.2 1 + k.1))

/-- The product matrix moments on the native row and column parameter region. -/
private theorem native_productMoment {r β : Fin 2 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage r β (appellF4ProductMatrix x y) (fun z => (1 - z) ^ N) =
      appellF4ProductMoment x y N (r, β) := by
  rw [regMatrixDirichletAverage_binomial_moment hr hβ (appellF4ProductMatrix x y)
    (fun u => x * (u 0 : ℂ)) (fun _ => 1)
    (fun v => 1 - y * (v 0 : ℂ)) (fun v => y * (v 0 : ℂ))
    (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
    (fun u hu v hv => by rw [matrixAffineForm_appellF4Product x y hu hv]; ring)]
  unfold appellF4ProductMoment
  apply Finset.sum_congr rfl
  intro q _
  simp only [one_pow, mul_one]
  rw [show (fun u : Fin 2 → ℝ => (x * (u 0 : ℂ)) ^ q.1) =
    (fun u => x ^ q.1 * (u 0 : ℂ) ^ q.1) by funext u; rw [mul_pow]]
  rw [regDirichletIntegral_smul, regDirichletIntegral_fin_two_pow hr,
    regDirichletIntegral_fin_two_one_sub_pow_mul_pow hβ]
  ring

/-- The repeated-row matrix moments on the native row and column parameter region. -/
private theorem native_F1Moment {r β : Fin 2 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage r β (appellF4F1Matrix x y) (fun z => (1 - z) ^ N) =
      appellF4F1Moment x y N (r, β) := by
  rw [regMatrixDirichletAverage_binomial_moment hr hβ (appellF4F1Matrix x y)
    (fun u => x * (u 0 : ℂ)) (fun _ => 1)
    (fun v => 1 - y * (v 1 : ℂ)) (fun _ => y)
    (by fun_prop) continuous_const (by fun_prop) continuous_const
    (fun u hu v hv => by rw [matrixAffineForm_appellF4F1 x y hu hv]; ring)]
  unfold appellF4F1Moment
  apply Finset.sum_congr rfl
  intro q _
  simp only [mul_pow, one_pow, mul_one]
  rw [regDirichletIntegral_smul, regDirichletIntegral_fin_two_pow hr]
  have hc : regDirichletIntegral β (fun v => (1 - y * (v 1 : ℂ)) ^ q.1) =
      ∑ k ∈ antidiagonal q.1, (q.1.choose k.1 : ℂ) * (-y) ^ k.1 *
        ((ascPochhammer ℂ k.1).eval (β 1) / Gamma (β 0 + β 1 + k.1)) := by
    simpa only [pow_zero, mul_one, add_zero] using
      regDirichletIntegral_fin_two_one_sub_pow_mul_pow hβ 1 y q.1 0
  have he : (fun v : Fin 2 → ℝ => (1 - y * (v 1 : ℂ)) ^ q.1 * y ^ q.2) =
      fun v => y ^ q.2 * (1 - y * (v 1 : ℂ)) ^ q.1 := by funext v; ring
  rw [he, regDirichletIntegral_smul, hc, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

/-- Holomorphic dependence of a coordinate beta moment under parameter substitutions. -/
private theorem analyticAt_coordinate_moment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {s v : E → ℂ} {p : E}
    (hs : AnalyticAt ℂ s p) (hv : AnalyticAt ℂ v p) (n : ℕ) :
    AnalyticAt ℂ (fun q => (ascPochhammer ℂ n).eval (s q) / Gamma (v q + n)) p := by
  simpa only [ascPochhammer_zero, Polynomial.eval_one, mul_one] using
    analyticAt_appellF4_moment_factor (t := fun _ => 0) hs analyticAt_const hv n 0 n

/-- Both restricted polynomial moment families are entire in independent row and column vectors. -/
private theorem analyticOnNhd_restrictedMoment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (appellF4ProductMoment x y N) univ ∧
      AnalyticOnNhd ℂ (appellF4F1Moment x y N) univ := by
  constructor <;> intro p _
  all_goals
    have hr (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.1 i) p :=
      (analyticAt_pi_iff.mp analyticAt_fst) i
    have hc (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.2 i) p :=
      (analyticAt_pi_iff.mp analyticAt_snd) i
  · unfold appellF4ProductMoment
    apply Finset.analyticAt_fun_sum
    intro q _
    apply AnalyticAt.mul
    · exact analyticAt_const.mul (analyticAt_coordinate_moment (hr 0) ((hr 0).add (hr 1)) q.1)
    · apply Finset.analyticAt_fun_sum
      intro k _
      exact analyticAt_const.mul
        (analyticAt_coordinate_moment (hc 0) ((hc 0).add (hc 1)) (k.1 + q.2))
  · unfold appellF4F1Moment
    apply Finset.analyticAt_fun_sum
    intro q _
    apply AnalyticAt.mul
    · exact analyticAt_const.mul (analyticAt_coordinate_moment (hr 0) ((hr 0).add (hr 1)) q.1)
    · apply Finset.analyticAt_fun_sum
      intro k _
      exact analyticAt_const.mul (analyticAt_coordinate_moment (hc 1) ((hc 0).add (hc 1)) k.1)

/-- The product matrix moment formula holds at all independent complex parameters. -/
theorem continuedRegMatrixDirichletAverage_appellF4Product_moment
    (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4ProductMatrix x y) (fun z => (1 - z) ^ N)
      (r, β) = appellF4ProductMoment x y N (r, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF4ProductMatrix x y) N).1
    (analyticOnNhd_restrictedMoment x y N).1 ?_) (r, β)
  intro s γ hs hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF4ProductMatrix x y) N).2 s γ hs hγ]
  exact native_productMoment hs hγ x y N

/-- The repeated-row matrix moment formula holds at all independent complex parameters. -/
theorem continuedRegMatrixDirichletAverage_appellF4F1_moment
    (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4F1Matrix x y) (fun z => (1 - z) ^ N)
      (r, β) = appellF4F1Moment x y N (r, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF4F1Matrix x y) N).1
    (analyticOnNhd_restrictedMoment x y N).2 ?_) (r, β)
  intro s γ hs hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF4F1Matrix x y) N).2 s γ hs hγ]
  exact native_F1Moment hs hγ x y N

/-- Deleting the middle zero column parameter gives the product matrix moments. -/
theorem appellF4MatrixMoment_zero_middle (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    appellF4MatrixMoment x y N (r, ![β 0, 0, β 1]) = appellF4ProductMoment x y N (r, β) := by
  simp only [appellF4MatrixMoment, appellF4ColumnMoment, appellF4ProductMoment,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_zero,
    ← ascPochhammer_add_eval]

/-- Deleting the last zero column parameter gives the F₁ moments in the paper's column order. -/
theorem appellF4MatrixMoment_zero_last (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    appellF4MatrixMoment x y N (r, ![β 1, β 0, 0]) = appellF4F1Moment x y N (r, β) := by
  unfold appellF4MatrixMoment appellF4F1Moment
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  unfold appellF4ColumnMoment
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_zero]
  have hG := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat
    (β 0 + β 1 + k.1) q.2
  rw [show β 1 + β 0 + (k.1 + q.2 : ℕ) = β 0 + β 1 + k.1 + q.2 by push_cast; ring,
    show β 1 + β 0 + k.1 = β 0 + β 1 + k.1 by ring]
  simp only [div_eq_mul_inv] at hG ⊢
  linear_combination
    -((q.1.choose k.1 : ℂ) * (-y) ^ k.1 * y ^ q.2 * (ascPochhammer ℂ k.1).eval (β 1)) * hG

/-- Both restricted matrices use entries of the unrestricted matrix. -/
private theorem restricted_entry_bounds (x y : ℂ) (i j : Fin 2) :
    ‖appellF4ProductMatrix x y i j - 1‖ ≤ appellF4MatrixRadius x y ∧
      ‖appellF4F1Matrix x y i j - 1‖ ≤ appellF4MatrixRadius x y := by
  have hp : appellF4ProductMatrix x y =
      fun i j => appellF4Matrix x y i (if j = 0 then 0 else 2) := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hf : appellF4F1Matrix x y =
      fun i j => appellF4Matrix x y i (if j = 0 then 1 else 0) := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hp, hf]
  exact ⟨norm_appellF4Matrix_sub_one_le x y _ _, norm_appellF4Matrix_sub_one_le x y _ _⟩

/-- The unrestricted matrix with a zero middle column parameter is exactly the product matrix. -/
theorem continuedRegMatrixDirichletAverage_appellF4_zero_middle (a : ℂ) (r β : Fin 2 → ℂ)
    {x y : ℂ} (hxy : appellF4MatrixRadius x y < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (r, ![β 0, 0, β 1]) =
        continuedRegMatrixDirichletAverage (appellF4ProductMatrix x y) (fun z => z ^ (-a))
          (r, β) := by
  have hL := hasSum_appellF4Matrix_moments a r ![β 0, 0, β 1] hxy
  have hR := hasSum_continuedRegMatrixDirichletAverage_cpow_neg r β
    (appellF4ProductMatrix x y) a ((norm_nonneg _).trans (le_max_left _ _)) hxy
    (fun i j => (restricted_entry_bounds x y i j).1)
  simp only [appellF4MatrixMoment_zero_middle] at hL
  simp only [continuedRegMatrixDirichletAverage_appellF4Product_moment] at hR
  exact hL.unique hR

/-- The unrestricted matrix with a zero final column parameter is exactly the F₁ matrix. -/
theorem continuedRegMatrixDirichletAverage_appellF4_zero_last (a : ℂ) (r β : Fin 2 → ℂ)
    {x y : ℂ} (hxy : appellF4MatrixRadius x y < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (r, ![β 1, β 0, 0]) =
        continuedRegMatrixDirichletAverage (appellF4F1Matrix x y) (fun z => z ^ (-a)) (r, β) := by
  have hL := hasSum_appellF4Matrix_moments a r ![β 1, β 0, 0] hxy
  have hR := hasSum_continuedRegMatrixDirichletAverage_cpow_neg r β
    (appellF4F1Matrix x y) a ((norm_nonneg _).trans (le_max_left _ _)) hxy
    (fun i j => (restricted_entry_bounds x y i j).2)
  simp only [appellF4MatrixMoment_zero_last] at hL
  simp only [continuedRegMatrixDirichletAverage_appellF4F1_moment] at hR
  exact hL.unique hR

/-- **Carlson (1975), (4.1), continued regularized matrix form.**
The explicit two-by-two product matrix represents balanced F₄ at every parameter. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_product
    {a b c d : ℂ} (h : c + d = a + b + 1) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    continuedRegMatrixDirichletAverage (appellF4ProductMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters b d) =
        regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  have hp : appellF4ColumnParameters a b c d =
      ![appellF2Parameters b d 0, 0, appellF2Parameters b d 1] := by
    funext i
    fin_cases i
    · simp [appellF4ColumnParameters, appellF2Parameters]
      linear_combination h
    · simp [appellF4ColumnParameters, appellF2Parameters]
      linear_combination -h
    · simp [appellF4ColumnParameters, appellF2Parameters]
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4 a b c d hxy, hp,
    continuedRegMatrixDirichletAverage_appellF4_zero_middle a _ _
      ((appellF4MatrixRadius_le_sum_norm x y).trans_lt (appellF4_reassembly_kernel_bound hxy))]

/-- **Carlson (1975), (4.2), continued regularized matrix form.**
The repeated-row two-by-two matrix represents F₄ with `d=b`, also at denominator poles. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1
    (a b c : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    continuedRegMatrixDirichletAverage (appellF4F1Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters (1 + a - c) b) =
        regularizedAppellF4 a b c b (x * (1 - y)) (y * (1 - x)) := by
  have hp : appellF4ColumnParameters a b c b =
      ![appellF2Parameters (1 + a - c) b 1, appellF2Parameters (1 + a - c) b 0, 0] := by
    funext i
    fin_cases i <;> simp [appellF4ColumnParameters, appellF2Parameters] <;> ring
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4 a b c b hxy, hp,
    continuedRegMatrixDirichletAverage_appellF4_zero_last a _ _
      ((appellF4MatrixRadius_le_sum_norm x y).trans_lt (appellF4_reassembly_kernel_bound hxy))]

/-- **Carlson (1975), (4.3), continued regularized matrix form.**
The explicit F₂ parallelogram represents F₄ when `c+d=a+1`. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F2
    {a b c d : ℂ} (h : c + d = a + 1) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    continuedRegMatrixDirichletAverage (appellF2Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters b d) =
        regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  have hreg := appellF4_reassembly_kernel_bound hxy
  have hd : ‖x‖ + ‖y‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 a b b c d hd,
    regularizedAppellF4_eq_F2 h hxy]

/-- Native and continued power-kernel matrix averages coincide on the unit entry disk. -/
private theorem continued_eq_native_entry_disk {r β : Fin 2 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : Fin 2 → Fin 2 → ℂ) (a : ℂ) (hZ : ∀ i j, ‖Z i j - 1‖ < 1) :
    continuedRegMatrixDirichletAverage Z (fun z => z ^ (-a)) (r, β) =
      regMatrixDirichletAverage r β Z (fun z => z ^ (-a)) := by
  apply continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) _ hr hβ
  intro i j
  have hre := (abs_re_le_norm (Z i j - 1)).trans_lt (hZ i j)
  simp only [sub_re, one_re] at hre
  change 0 < (Z i j).re
  linarith [neg_abs_le ((Z i j).re - 1)]

/-- Native normalized form of the product-matrix representation (4.1). -/
theorem matrixDirichletAverage_eq_appellF4_product {a b c d : ℂ}
    (h : c + d = a + b + 1)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters b d ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b d)
      (appellF4ProductMatrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  have hn := ((appellF4MatrixRadius_le_sum_norm x y).trans_lt
    (appellF4_reassembly_kernel_bound hxy))
  rw [matrixDirichletAverage, sum_appellF2Parameters, sum_appellF2Parameters,
    ← continued_eq_native_entry_disk hr hβ _ a
      (fun i j => ((restricted_entry_bounds x y i j).1).trans_lt hn),
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_product h hxy, appellF4]

/-- Native normalized form of the repeated-row F₁ matrix representation (4.2). -/
theorem matrixDirichletAverage_eq_appellF4_F1 (a b c : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters (1 + a - c) b ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters (1 + a - c) b)
      (appellF4F1Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c b (x * (1 - y)) (y * (1 - x)) := by
  have hn := ((appellF4MatrixRadius_le_sum_norm x y).trans_lt
    (appellF4_reassembly_kernel_bound hxy))
  rw [matrixDirichletAverage, sum_appellF2Parameters, sum_appellF2Parameters,
    ← continued_eq_native_entry_disk hr hβ _ a
      (fun i j => ((restricted_entry_bounds x y i j).2).trans_lt hn),
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1 a b c hxy, appellF4]

/-- Native normalized form of the F₂ matrix representation (4.3). -/
theorem matrixDirichletAverage_eq_appellF4_F2 {a b c d : ℂ} (h : c + d = a + 1)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters b d ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b d)
      (appellF2Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  have hreg := appellF4_reassembly_kernel_bound hxy
  have hd : ‖x‖ + ‖y‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  rw [matrixDirichletAverage_eq_appellF2 a b b c d hr hβ hd,
    appellF2, ← regularizedAppellF4_eq_F2 h hxy, appellF4]

end Carlson.TwoVariable
