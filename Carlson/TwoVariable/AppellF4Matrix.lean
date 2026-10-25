/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Equal
public import Carlson.TwoVariable.MatrixTaylor

/-!
# The equal-denominator F₄ matrix representation

Carlson (1975), equations (2.6)–(2.8). The two-by-two matrix has entries
`1-(x+y)², 1-(x-y)²` in its first row and ones in its second row.
Its binomial moments separate into a beta coordinate moment and a two-node
R-polynomial. Entire parameter continuation proves the regularized identity
without parameter exclusions. A duplication ratio records the normalization
and its zeros explicitly.
-/

open Complex Polynomial Dirichlet Set Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The two-by-two matrix for equal-denominator F₄ at the squared arguments. -/
def appellF4EqualMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![1 - (x + y) ^ 2, 1 - (x - y) ^ 2], ![1, 1]]

/-- The shifted affine kernel separates into a row coordinate and a column affine form. -/
theorem matrixAffineForm_appellF4Equal (x y : ℂ) {u v : Fin 2 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    1 - matrixAffineForm (appellF4EqualMatrix x y) u v =
      (u 0 : ℂ) * carlsonAffineForm (pair ((x + y) ^ 2) ((x - y) ^ 2)) v := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv1 : (v 1 : ℂ) = 1 - (v 0 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF4EqualMatrix, carlsonAffineForm, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pair_zero, pair_one,
    hu1, hv1]
  ring

/-- **Carlson (1975), (2.6).** The native shifted matrix moments factor into two moments. -/
theorem regMatrixDirichletAverage_appellF4Equal_moment
    {r β : Fin 2 → ℂ} (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage r β (appellF4EqualMatrix x y) (fun z => (1 - z) ^ N) =
      ((ascPochhammer ℂ N).eval (r 0) / Gamma (r 0 + r 1 + N)) *
        regCarlsonRPolynomial N β (pair ((x + y) ^ 2) ((x - y) ^ 2)) := by
  rw [regMatrixDirichletAverage_eq_sum_separated hr hβ (appellF4EqualMatrix x y)
    (by fun_prop) ({()} : Finset Unit) (fun _ => 1) (fun _ u => (u 0 : ℂ) ^ N)
    (fun _ v => carlsonAffineForm (pair ((x + y) ^ 2) ((x - y) ^ 2)) v ^ N)
    (fun _ _ => by fun_prop) (fun _ _ => (continuous_carlsonAffineForm _).pow N |>.continuousOn)
    (fun u hu v hv => by
      simp only [sum_singleton, one_mul]
      rw [matrixAffineForm_appellF4Equal x y hu hv, mul_pow])]
  simp only [sum_singleton, one_mul]
  rw [regDirichletIntegral_fin_two_pow hr]
  congr 1
  exact regCarlsonDirichletAverage_pow N _ hβ

/-- The explicit moment factor is entire in the independent row and column parameters. -/
private theorem analyticOnNhd_appellF4Equal_moment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
      ((ascPochhammer ℂ N).eval (p.1 0) / Gamma (p.1 0 + p.1 1 + N)) *
        regCarlsonRPolynomial N p.2 (pair ((x + y) ^ 2) ((x - y) ^ 2))) univ := by
  intro p _
  have hr (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.1 i) p :=
    (analyticAt_pi_iff.mp analyticAt_fst) i
  have hc (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.2 i) p :=
    (analyticAt_pi_iff.mp analyticAt_snd) i
  apply AnalyticAt.mul
  · simp only [div_eq_mul_inv]
    apply AnalyticAt.mul
    · exact ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ N)) _ (mem_univ _)).comp (hr 0)
    · exact (differentiable_one_div_Gamma.analyticAt _).comp
        (f := fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.1 0 + q.1 1 + N)
        (((hr 0).add (hr 1)).add analyticAt_const)
  · exact analyticAt_regCarlsonRPolynomial_comp
      (b := fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.2)
      (z := fun _ => pair ((x + y) ^ 2) ((x - y) ^ 2)) hc (fun _ => analyticAt_const) N

/-- The equal-denominator matrix moment formula continues to all independent parameters. -/
theorem continuedRegMatrixDirichletAverage_appellF4Equal_moment
    (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4EqualMatrix x y) (fun z => (1 - z) ^ N)
      (r, β) = ((ascPochhammer ℂ N).eval (r 0) / Gamma (r 0 + r 1 + N)) *
        regCarlsonRPolynomial N β (pair ((x + y) ^ 2) ((x - y) ^ 2)) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF4EqualMatrix x y) N).1
    (analyticOnNhd_appellF4Equal_moment x y N) ?_) (r, β)
  intro s γ hs hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF4EqualMatrix x y) N).2 s γ hs hγ]
  exact regMatrixDirichletAverage_appellF4Equal_moment hs hγ x y N

/-- The equal-denominator matrix lies in the full binomial disk allowed by the squared nodes. -/
theorem norm_appellF4EqualMatrix_sub_one_le (x y : ℂ) (i j : Fin 2) :
    ‖appellF4EqualMatrix x y i j - 1‖ ≤ (‖x‖ + ‖y‖) ^ 2 := by
  fin_cases i <;> fin_cases j
  · change ‖(1 - (x + y) ^ 2) - 1‖ ≤ _
    rw [sub_sub_cancel_left, norm_neg, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  · change ‖(1 - (x - y) ^ 2) - 1‖ ≤ _
    rw [sub_sub_cancel_left, norm_neg, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  · change ‖(1 : ℂ) - 1‖ ≤ _
    simp only [sub_self, norm_zero]; positivity
  · change ‖(1 : ℂ) - 1‖ ≤ _
    simp only [sub_self, norm_zero]; positivity

/-- **Carlson (1975), (2.8), continued and division-free.** Equal-denominator F₄ has its
restricted two-by-two matrix representation at every parameter. The duplication ratio
records the removable normalization at exceptional averaging parameters. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_equal
    (a b c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4EqualMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair (c - 1 / 2) (c - 1 / 2)) =
        quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  have hr : (‖x‖ + ‖y‖) ^ 2 < 1 := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hL := hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (appellF2Parameters b c) (pair (c - 1 / 2) (c - 1 / 2)) (appellF4EqualMatrix x y) a
    (by positivity) hr (norm_appellF4EqualMatrix_sub_one_le x y)
  have hR := (hasSum_regularizedAppellF4_equalRPolynomial a b c hxy).mul_left
    (quadraticGammaRatio (c - 1 / 2))
  apply hL.unique
  convert hR using 1
  funext N
  rw [continuedRegMatrixDirichletAverage_appellF4Equal_moment,
    regCarlsonRPolynomial_pair_self_eq]
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_sub_cancel, gaussCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The equal-denominator F₄ matrix has all entries in the right half-plane on its full region. -/
theorem appellF4EqualMatrix_mem_rightHalfPlane {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    appellF4EqualMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have hr : (‖x‖ + ‖y‖) ^ 2 < 1 := by nlinarith [norm_nonneg x, norm_nonneg y]
  have h := (abs_re_le_norm (appellF4EqualMatrix x y i j - 1)).trans
    (norm_appellF4EqualMatrix_sub_one_le x y i j)
  change 0 < (appellF4EqualMatrix x y i j).re
  simp only [sub_re, one_re] at h
  linarith [neg_abs_le ((appellF4EqualMatrix x y i j).re - 1)]

/-- The native regularized equal-denominator matrix average equals regularized F₄
with its explicit duplication ratio. -/
theorem regMatrixDirichletAverage_eq_regularizedAppellF4_equal (a b c : ℂ)
    (hb : appellF2Parameters b c ∈ mvBetaConvergent) (hc : 1 / 2 < c.re)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regMatrixDirichletAverage (appellF2Parameters b c) (pair (c - 1 / 2) (c - 1 / 2))
      (appellF4EqualMatrix x y) (fun z => z ^ (-a)) =
        quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_equal a b c hxy]
  symm
  apply continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (appellF4EqualMatrix_mem_rightHalfPlane hxy) hb
  intro i
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  fin_cases i <;> exact hβ

/-- **Carlson (1975), (2.8), native normalized form.** The ordinary equal-denominator
F₄ is the two-by-two double average, with positive real parts of the averaging parameters. -/
theorem matrixDirichletAverage_eq_appellF4_equal (a b c : ℂ)
    (hb : appellF2Parameters b c ∈ mvBetaConvergent) (hc : 1 / 2 < c.re)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (pair (c - 1 / 2) (c - 1 / 2))
      (appellF4EqualMatrix x y) (fun z => z ^ (-a)) = appellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [matrixDirichletAverage, sum_appellF2Parameters, sum_pair,
    regMatrixDirichletAverage_eq_regularizedAppellF4_equal a b c hb hc hxy, appellF4]
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hdup := Gamma_mul_quadraticGammaRatio hβ
  rw [show c - 1 / 2 + 1 / 2 = c by ring] at hdup
  calc
    _ = Gamma c * (Gamma ((c - 1 / 2) + (c - 1 / 2)) *
        quadraticGammaRatio (c - 1 / 2)) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by ring
    _ = _ := by rw [hdup]

end Carlson.TwoVariable
