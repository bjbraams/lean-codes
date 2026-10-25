/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellContinuation
public import Pochhammer.Vandermonde

/-!
# Polynomial moments of the unrestricted F₄ matrix

The matrix in Carlson (1975), equation (3.5), has two rows and three columns.
Its shifted affine kernel is a sum of two separated products. The column
moments involve overlapping coordinate blocks; Chu–Vandermonde evaluates them.
The resulting finite formulas continue to arbitrary independent row and
column parameters. This module supplies the matrix side of (3.5).
`AppellF4Coefficients` and `AppellF4Reassembly` prove the nonlinear F₄
identification and its analytic continuation on verified scaling domains.
-/

open Complex Polynomial Dirichlet Set Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The unrestricted two-by-three matrix in Carlson (1975), equation (3.5). -/
def appellF4Matrix (x y : ℂ) : Fin 2 → Fin 3 → ℂ :=
  ![![(1 - x) * (1 - y), 1 - x - y, 1 - x], ![1 - y, 1 - y, 1]]

/-- The three column parameters in the unrestricted F₄ representation. -/
def appellF4ColumnParameters (a b c d : ℂ) : Fin 3 → ℂ :=
  ![c + d - a - 1, 1 + a + b - c - d, d - b]

/-- The unrestricted column parameters have total `d`. -/
@[simp] theorem sum_appellF4ColumnParameters (a b c d : ℂ) :
    ∑ j, appellF4ColumnParameters a b c d j = d := by
  simp [appellF4ColumnParameters, Fin.sum_univ_three]
  ring

/-- The first two column parameters add to the first row parameter. -/
theorem appellF4ColumnParameters_add (a b c d : ℂ) :
    appellF4ColumnParameters a b c d 0 + appellF4ColumnParameters a b c d 1 = b := by
  simp [appellF4ColumnParameters]
  ring

/-- The shifted matrix kernel separates into a row coordinate and a column block. -/
theorem matrixAffineForm_appellF4 (x y : ℂ) {u : Fin 2 → ℝ} {v : Fin 3 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :
    1 - matrixAffineForm (appellF4Matrix x y) u v =
      (x * (u 0 : ℂ)) * (1 - y * (v 0 : ℂ)) + y * ((v 0 : ℂ) + v 1) := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv2 : (v 2 : ℂ) = 1 - (v 0 : ℂ) - v 1 := by
    have h : (v 0 : ℂ) + v 1 + v 2 = 1 := by
      exact_mod_cast (by simpa [Fin.sum_univ_three] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF4Matrix, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hu1, hv2]
  ring

/-- The finite overlapping-block moment for the unrestricted column parameters. -/
def appellF4ColumnMoment (β : Fin 3 → ℂ) (y : ℂ) (m n : ℕ) : ℂ :=
  ∑ q ∈ antidiagonal m, (m.choose q.1 : ℂ) * (-y) ^ q.1 * y ^ n *
    ((ascPochhammer ℂ q.1).eval (β 0) * (ascPochhammer ℂ n).eval (β 0 + β 1 + q.1) /
      Gamma (β 0 + β 1 + β 2 + (q.1 + n : ℕ)))

/-- The explicit unrestricted matrix moment, before imposing any Appell parameter relations. -/
def appellF4MatrixMoment (x y : ℂ) (N : ℕ)
    (p : (Fin 2 → ℂ) × (Fin 3 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 *
    ((ascPochhammer ℂ q.1).eval (p.1 0) / Gamma (p.1 0 + p.1 1 + q.1)) *
      appellF4ColumnMoment p.2 y q.1 q.2

/-- Native polynomial moments of the unrestricted F₄ matrix have an explicit finite formula. -/
theorem regMatrixDirichletAverage_appellF4_moment {r : Fin 2 → ℂ} {β : Fin 3 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage r β (appellF4Matrix x y) (fun z => (1 - z) ^ N) =
      appellF4MatrixMoment x y N (r, β) := by
  rw [regMatrixDirichletAverage_binomial_moment hr hβ (appellF4Matrix x y)
    (fun u => x * (u 0 : ℂ)) (fun _ => 1)
    (fun v => 1 - y * (v 0 : ℂ)) (fun v => y * ((v 0 : ℂ) + v 1))
    (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
    (fun u hu v hv => by rw [matrixAffineForm_appellF4 x y hu hv]; ring)]
  unfold appellF4MatrixMoment appellF4ColumnMoment
  apply Finset.sum_congr rfl
  intro q _
  simp only [one_pow, mul_one]
  rw [show (fun u : Fin 2 → ℝ => (x * (u 0 : ℂ)) ^ q.1) =
    (fun u => x ^ q.1 * (u 0 : ℂ) ^ q.1) by funext u; rw [mul_pow]]
  rw [regDirichletIntegral_smul, regDirichletIntegral_fin_two_pow hr,
    regDirichletIntegral_fin_three_one_sub_pow_mul_block_pow hβ]
  ring

/-- Polynomial factors and reciprocal Gamma remain analytic under parameter substitution. -/
theorem analyticAt_appellF4_moment_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E} {s t v : E → ℂ}
    (hs : AnalyticAt ℂ s p) (ht : AnalyticAt ℂ t p) (hv : AnalyticAt ℂ v p) (m n k : ℕ) :
    AnalyticAt ℂ (fun q => (ascPochhammer ℂ m).eval (s q) *
      (ascPochhammer ℂ n).eval (t q) / Gamma (v q + k)) p := by
  simp only [div_eq_mul_inv]
  apply AnalyticAt.mul
  · exact (((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ m)) _ (mem_univ _)).comp hs).mul
      (((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n)) _ (mem_univ _)).comp ht)
  · exact (differentiable_one_div_Gamma.analyticAt _).comp
      (f := fun q => v q + k) (hv.add analyticAt_const)

/-- Every unrestricted matrix moment is entire in both independent parameter vectors. -/
theorem analyticOnNhd_appellF4MatrixMoment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (appellF4MatrixMoment x y N) univ := by
  intro p _
  have hr (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 3 → ℂ) => q.1 i) p :=
    (analyticAt_pi_iff.mp analyticAt_fst) i
  have hc (i : Fin 3) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 3 → ℂ) => q.2 i) p :=
    (analyticAt_pi_iff.mp analyticAt_snd) i
  unfold appellF4MatrixMoment
  apply Finset.analyticAt_fun_sum
  intro q _
  apply AnalyticAt.mul
  · apply AnalyticAt.mul analyticAt_const
    simpa only [ascPochhammer_zero, Polynomial.eval_one, mul_one] using
      analyticAt_appellF4_moment_factor
        (s := fun t : (Fin 2 → ℂ) × (Fin 3 → ℂ) => t.1 0) (t := fun _ => 0)
        (v := fun t => t.1 0 + t.1 1)
        (hr 0) analyticAt_const ((hr 0).add (hr 1)) q.1 0 q.1
  · unfold appellF4ColumnMoment
    apply Finset.analyticAt_fun_sum
    intro s _
    apply AnalyticAt.mul analyticAt_const
    exact analyticAt_appellF4_moment_factor (hc 0)
      (((hc 0).add (hc 1)).add analyticAt_const) (((hc 0).add (hc 1)).add (hc 2))
      s.1 q.2 (s.1 + q.2)

/-- The unrestricted polynomial moment formula holds at arbitrary complex row and column
parameters, including zeros and exceptional total parameters. -/
theorem continuedRegMatrixDirichletAverage_appellF4_moment
    (r : Fin 2 → ℂ) (β : Fin 3 → ℂ) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => (1 - z) ^ N) (r, β) =
      appellF4MatrixMoment x y N (r, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF4Matrix x y) N).1
    (analyticOnNhd_appellF4MatrixMoment x y N) ?_) (r, β)
  intro s γ hs hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF4Matrix x y) N).2 s γ hs hγ]
  exact regMatrixDirichletAverage_appellF4_moment hs hγ x y N

/-- A zero first column parameter deletes that coordinate from every polynomial moment.
This identity also holds at exceptional total parameters. -/
theorem appellF4ColumnMoment_zero_first {β : Fin 3 → ℂ} (hβ : β 0 = 0)
    (y : ℂ) (m n : ℕ) :
    appellF4ColumnMoment β y m n =
      y ^ n * (ascPochhammer ℂ n).eval (β 1) / Gamma (β 1 + β 2 + n) := by
  unfold appellF4ColumnMoment
  rw [Finset.sum_eq_single (0, m)]
  · simp only [hβ, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      ascPochhammer_zero, Polynomial.eval_one, one_mul, Nat.cast_zero, zero_add,
      add_zero, mul_div_assoc]
  · intro q hq hne
    have hq0 : q.1 ≠ 0 := by
      intro h
      apply hne
      have hsum := mem_antidiagonal.mp hq
      exact Prod.ext h (by omega)
    rw [hβ, ascPochhammer_ne_zero_eval_zero ℂ hq0]
    simp
  · simp

/-- The zero first column parameter reduces the unrestricted polynomial moments to the
parallelogram moment formula underlying F₂. No argument or parameter exclusions are needed. -/
theorem continuedRegMatrixDirichletAverage_appellF4_zero_first_moment
    (r : Fin 2 → ℂ) {β : Fin 3 → ℂ} (hβ : β 0 = 0) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => (1 - z) ^ N) (r, β) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) * x ^ p.1 * y ^ p.2 *
        ((ascPochhammer ℂ p.1).eval (r 0) / Gamma (r 0 + r 1 + p.1)) *
        ((ascPochhammer ℂ p.2).eval (β 1) / Gamma (β 1 + β 2 + p.2)) := by
  rw [continuedRegMatrixDirichletAverage_appellF4_moment, appellF4MatrixMoment]
  apply Finset.sum_congr rfl
  intro p _
  rw [appellF4ColumnMoment_zero_first hβ]
  ring

/-- The exact radius of the unrestricted matrix entries about one. -/
def appellF4MatrixRadius (x y : ℂ) : ℝ :=
  max ‖x + y - x * y‖ (max ‖x + y‖ (max ‖x‖ ‖y‖))

/-- Every matrix entry lies in the closed disk with its explicit maximum radius. -/
theorem norm_appellF4Matrix_sub_one_le (x y : ℂ) (i : Fin 2) (j : Fin 3) :
    ‖appellF4Matrix x y i j - 1‖ ≤ appellF4MatrixRadius x y := by
  have hx : ‖x‖ ≤ appellF4MatrixRadius x y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hy : ‖y‖ ≤ appellF4MatrixRadius x y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  fin_cases i <;> fin_cases j
  · change ‖(1 - x) * (1 - y) - 1‖ ≤ _
    rw [show (1 - x) * (1 - y) - 1 = -(x + y - x * y) by ring, norm_neg]
    exact le_max_left _ _
  · change ‖(1 - x - y) - 1‖ ≤ _
    rw [show (1 - x - y) - 1 = -(x + y) by ring, norm_neg]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · change ‖(1 - x) - 1‖ ≤ _
    simpa only [sub_sub_cancel_left, norm_neg] using hx
  · change ‖(1 - y) - 1‖ ≤ _
    simpa only [sub_sub_cancel_left, norm_neg] using hy
  · change ‖(1 - y) - 1‖ ≤ _
    simpa only [sub_sub_cancel_left, norm_neg] using hy
  · change ‖(1 : ℂ) - 1‖ ≤ _
    simpa only [sub_self, norm_zero] using (norm_nonneg x).trans hx

/-- The explicit unrestricted moment series converges on the full matrix entry disk,
at arbitrary independent row and column parameters. -/
theorem hasSum_appellF4Matrix_moments (a : ℂ) (r : Fin 2 → ℂ) (β : Fin 3 → ℂ)
    {x y : ℂ} (hxy : appellF4MatrixRadius x y < 1) :
    HasSum (fun N => (ascPochhammer ℂ N).eval a / (N.factorial : ℂ) *
      appellF4MatrixMoment x y N (r, β))
      (continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a)) (r, β)) := by
  simpa only [continuedRegMatrixDirichletAverage_appellF4_moment] using
    hasSum_continuedRegMatrixDirichletAverage_cpow_neg r β (appellF4Matrix x y) a
      ((norm_nonneg _).trans (le_max_left _ _)) hxy (norm_appellF4Matrix_sub_one_le x y)

/-- Deleting the zero first column reduces the continued matrix to F₂ on the common series
region. This is the matrix reduction used in (4.3), proved directly from its moments. -/
theorem continuedRegMatrixDirichletAverage_appellF4_zero_first_eq_F2 (a b b' c d : ℂ)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) (hmat : appellF4MatrixRadius x y < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, ![0, b', d - b']) = regularizedAppellF2 a b b' c d x y := by
  have hL := hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (appellF2Parameters b c) ![0, b', d - b'] (appellF4Matrix x y) a
    ((norm_nonneg _).trans (le_max_left _ _)) hmat (norm_appellF4Matrix_sub_one_le x y)
  have hR := hasSum_regularizedAppellF2_antidiagonal a b b' c d hxy
  apply hL.unique
  convert hR using 1
  funext N
  rw [continuedRegMatrixDirichletAverage_appellF4_zero_first_moment
    (appellF2Parameters b c) (β := ![0, b', d - b']) rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := mem_antidiagonal.mp hp
  rcases p with ⟨m, n⟩
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, add_sub_cancel, regularizedAppellF2Coeff_eq]
  rw [← hdeg, Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero]

end Carlson.TwoVariable
