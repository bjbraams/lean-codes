/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF2F3
public import Dirichlet.Average.MatrixMoments
public import Pochhammer.BinomialSeries

/-!
# Appell functions as matrix double averages

Carlson (1971), equations (3.1) and (5.6). The second Appell function is an
average over a two-by-two parallelogram; the third is the bare three-by-three
average with two nonconstant diagonal entries. The proof expands the scalar
power kernel and evaluates the separated mixed moments of the two Dirichlet laws.
-/

open Complex Polynomial Dirichlet Set Finset ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Carlson

/-- A scalar binomial series may be averaged on any matrix inside its convergence disk. -/
theorem hasSum_regMatrixDirichletAverage_cpow_neg
    {ι κ : Type*} [Fintype ι] [Fintype κ] {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (a : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hZ : ∀ i j, ‖Z i j - 1‖ ≤ r) :
    HasSum (fun N => (ascPochhammer ℂ N).eval a / (N.factorial : ℂ) *
      regMatrixDirichletAverage b β Z (fun z => (1 - z) ^ N))
      (regMatrixDirichletAverage b β Z (fun z => z ^ (-a))) := by
  have hball : convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) ⊆
      Metric.closedBall (1 : ℂ) r := by
    apply convexHull_min _ (convex_closedBall 1 r)
    rintro z ⟨⟨i, j⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hZ i j
  have hre (z : ℂ) (hz : z ∈ convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))) :
      0 < z.re := by
    have hn : ‖z - 1‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hball hz
    have he := (abs_re_le_norm (z - 1)).trans hn
    simp only [sub_re, one_re] at he
    linarith [neg_abs_le (z.re - 1)]
  have hf : ContinuousOn (fun z : ℂ => z ^ (-a))
      (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))) :=
    (show AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-a)) _ from
      fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl (hre z hz))).continuousOn
  have hM := summable_norm_ascPochhammer_mul_pow_div_factorial a (r : ℂ)
    (by simpa [abs_of_nonneg hr0] using hr1)
  have hM' : Summable (fun N => ‖(ascPochhammer ℂ N).eval a / (N.factorial : ℂ)‖ * r ^ N) := by
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hM
  have h := hasSum_regMatrixDirichletAverage hb hβ Z
    (fun N z => (ascPochhammer ℂ N).eval a / (N.factorial : ℂ) * (1 - z) ^ N)
    (fun z => z ^ (-a)) _ (fun N => by fun_prop) hf hM' (fun N z hz => by
      rw [norm_mul, norm_pow]
      have hn : ‖1 - z‖ ≤ r := by
        rw [norm_sub_rev]
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hball hz
      gcongr) (fun z hz => by
      have hn : ‖1 - z‖ < 1 := by
        rw [norm_sub_rev]
        exact lt_of_le_of_lt (by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hball hz) hr1
      simpa only [(show (1 : ℂ) - (1 - z) = z by ring), cpow_neg, one_div] using
        hasSum_ascPochhammer_mul_pow_div_factorial a (1 - z) hn)
  simpa only [regMatrixDirichletAverage_smul] using h

namespace TwoVariable

/-- The two beta parameters associated with an Appell `F₂` variable. -/
def appellF2Parameters (b c : ℂ) : Fin 2 → ℂ := ![b, c - b]

/-- The parallelogram matrix in Carlson (1971), (3.1). -/
def appellF2Matrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![1 - x - y, 1 - x], ![1 - y, 1]]

/-- The three Dirichlet parameters in the bare matrix representation of `F₃`. -/
def appellF3Parameters (a a' c : ℂ) : Fin 3 → ℂ := ![a, a', c - a - a']

/-- The bare three-by-three matrix in Carlson (1971), (5.6). -/
def appellF3Matrix (x y : ℂ) : Fin 3 → Fin 3 → ℂ :=
  ![![1 - x, 1, 1], ![1, 1 - y, 1], ![1, 1, 1]]

/-- The `F₂` matrix has the expected affine kernel on the product simplex. -/
theorem matrixAffineForm_appellF2 (x y : ℂ) {u v : Fin 2 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    1 - matrixAffineForm (appellF2Matrix x y) u v = (u 0 : ℂ) * x + (v 0 : ℂ) * y := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv1 : (v 1 : ℂ) = 1 - (v 0 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF2Matrix, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hu1, hv1]
  ring

/-- The `F₃` matrix has two diagonal product coordinates. -/
theorem matrixAffineForm_appellF3 (x y : ℂ) {u v : Fin 3 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :
    1 - matrixAffineForm (appellF3Matrix x y) u v =
      (u 0 : ℂ) * (v 0 : ℂ) * x + (u 1 : ℂ) * (v 1 : ℂ) * y := by
  have hu2 : (u 2 : ℂ) = 1 - (u 0 : ℂ) - (u 1 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 + u 2 = 1 := by
      exact_mod_cast (by simpa [Fin.sum_univ_three, add_assoc] using hu.2)
    linear_combination h
  have hv2 : (v 2 : ℂ) = 1 - (v 0 : ℂ) - (v 1 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 + v 2 = 1 := by
      exact_mod_cast (by simpa [Fin.sum_univ_three, add_assoc] using hv.2)
    linear_combination h
  simp [matrixAffineForm, appellF3Matrix, Fin.sum_univ_three, hu2, hv2]
  ring

/-- The `F₂` moment formula, before summing the binomial kernel series. -/
theorem regMatrixDirichletAverage_appellF2_moment (b b' c c' x y : ℂ)
    (hb : appellF2Parameters b c ∈ mvBetaConvergent)
    (hb' : appellF2Parameters b' c' ∈ mvBetaConvergent) (N : ℕ) :
    regMatrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b' c')
      (appellF2Matrix x y) (fun z => (1 - z) ^ N) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) * x ^ p.1 * y ^ p.2 *
        ((ascPochhammer ℂ p.1).eval b / Gamma (c + p.1)) *
        ((ascPochhammer ℂ p.2).eval b' / Gamma (c' + p.2)) := by
  rw [regMatrixDirichletAverage_binomial_moment hb hb' (appellF2Matrix x y)
    (fun u => x * (u 0 : ℂ)) (fun _ => 1) (fun _ => 1) (fun v => y * (v 0 : ℂ))
    (by fun_prop) continuous_const continuous_const (by fun_prop)
    (fun u hu v hv => by rw [matrixAffineForm_appellF2 x y hu hv]; ring)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mul_pow, one_pow, mul_one, one_mul, regDirichletIntegral_smul]
  rw [regDirichletIntegral_fin_two_pow hb, regDirichletIntegral_fin_two_pow hb']
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_sub_cancel]
  ring

/-- The `F₃` mixed moment formula, before summing its scalar kernel. -/
theorem regMatrixDirichletAverage_appellF3_moment (a a' b b' c x y : ℂ)
    (ha : appellF3Parameters a a' c ∈ mvBetaConvergent)
    (hb : appellF3Parameters b b' c ∈ mvBetaConvergent) (N : ℕ) :
    regMatrixDirichletAverage (appellF3Parameters a a' c) (appellF3Parameters b b' c)
      (appellF3Matrix x y) (fun z => (1 - z) ^ N) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) * x ^ p.1 * y ^ p.2 *
        ((ascPochhammer ℂ p.1).eval a * (ascPochhammer ℂ p.2).eval a' / Gamma (c + N)) *
        ((ascPochhammer ℂ p.1).eval b * (ascPochhammer ℂ p.2).eval b' / Gamma (c + N)) := by
  rw [regMatrixDirichletAverage_binomial_moment ha hb (appellF3Matrix x y)
    (fun u => x * (u 0 : ℂ)) (fun u => y * (u 1 : ℂ))
    (fun v => (v 0 : ℂ)) (fun v => (v 1 : ℂ))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun u hu v hv => by rw [matrixAffineForm_appellF3 x y hu hv]; ring)]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  have he : (fun u : Fin 3 → ℝ => (x * (u 0 : ℂ)) ^ p.1 * (y * (u 1 : ℂ)) ^ p.2) =
      fun u => (x ^ p.1 * y ^ p.2) * ((u 0 : ℂ) ^ p.1 * (u 1 : ℂ) ^ p.2) := by
    funext u
    rw [mul_pow, mul_pow]
    ring
  rw [he, regDirichletIntegral_smul, regDirichletIntegral_fin_three_pow_mul ha,
    regDirichletIntegral_fin_three_pow_mul hb, hdeg]
  have hs (s t : ℂ) : appellF3Parameters s t c 0 + appellF3Parameters s t c 1 +
      appellF3Parameters s t c 2 = c := by simp [appellF3Parameters]
  rw [hs, hs]
  simp only [appellF3Parameters, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The two Appell beta parameters have total `c`. -/
@[simp] theorem sum_appellF2Parameters (b c : ℂ) : ∑ i, appellF2Parameters b c i = c := by
  simp [appellF2Parameters, Fin.sum_univ_two]

/-- The three parameters in the bare Appell matrix have total `c`. -/
@[simp] theorem sum_appellF3Parameters (a a' c : ℂ) : ∑ i, appellF3Parameters a a' c i = c := by
  simp [appellF3Parameters, Fin.sum_univ_three]

/-- The parallelogram matrix lies in the binomial disk of radius `‖x‖ + ‖y‖`. -/
theorem norm_appellF2Matrix_sub_one_le (x y : ℂ) (i j : Fin 2) :
    ‖appellF2Matrix x y i j - 1‖ ≤ ‖x‖ + ‖y‖ := by
  fin_cases i <;> fin_cases j <;> simp [appellF2Matrix]
  · calc
      ‖1 - x - y - 1‖ = ‖-(x + y)‖ := congrArg norm (by ring)
      _ = ‖x + y‖ := norm_neg _
      _ ≤ _ := norm_add_le x y
  · positivity

/-- The bare `F₃` matrix lies in the binomial disk of radius `max ‖x‖ ‖y‖`. -/
theorem norm_appellF3Matrix_sub_one_le (x y : ℂ) (i j : Fin 3) :
    ‖appellF3Matrix x y i j - 1‖ ≤ max ‖x‖ ‖y‖ := by
  fin_cases i <;> fin_cases j <;> simp [appellF3Matrix,
    le_trans (norm_nonneg x) (le_max_left ‖x‖ ‖y‖)]

/-- **Carlson (1971), (3.1), regularized.** The `F₂` series is the two-by-two
matrix average in its native parameter region and full argument diamond. -/
theorem regMatrixDirichletAverage_eq_regularizedAppellF2 (a b b' c c' : ℂ)
    (hb : appellF2Parameters b c ∈ mvBetaConvergent)
    (hb' : appellF2Parameters b' c' ∈ mvBetaConvergent)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regMatrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b' c')
      (appellF2Matrix x y) (fun z => z ^ (-a)) = regularizedAppellF2 a b b' c c' x y := by
  have hL := hasSum_regMatrixDirichletAverage_cpow_neg hb hb' (appellF2Matrix x y) a
    (‖x‖ + ‖y‖) (by positivity) hxy (norm_appellF2Matrix_sub_one_le x y)
  have hR := hasSum_regularizedAppellF2_antidiagonal a b b' c c' hxy
  apply hL.unique
  convert hR using 1
  funext N
  rw [regMatrixDirichletAverage_appellF2_moment b b' c c' x y hb hb', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  rw [regularizedAppellF2Coeff_eq, ← hdeg, Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero]

/-- **Carlson (1971), (3.1).** The normalized parallelogram average is Appell `F₂`. -/
theorem matrixDirichletAverage_eq_appellF2 (a b b' c c' : ℂ)
    (hb : appellF2Parameters b c ∈ mvBetaConvergent)
    (hb' : appellF2Parameters b' c' ∈ mvBetaConvergent)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b' c')
      (appellF2Matrix x y) (fun z => z ^ (-a)) = appellF2 a b b' c c' x y := by
  simp only [matrixDirichletAverage, sum_appellF2Parameters, appellF2,
    regMatrixDirichletAverage_eq_regularizedAppellF2 a b b' c c' hb hb' hxy]

/-- **Carlson (1971), (5.6), regularized.** One total Gamma factor cancels
when the exponent equals the negative common row and column parameter total. -/
theorem Gamma_mul_regMatrixDirichletAverage_eq_regularizedAppellF3
    (a a' b b' c : ℂ) (ha : appellF3Parameters a a' c ∈ mvBetaConvergent)
    (hb : appellF3Parameters b b' c ∈ mvBetaConvergent)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Gamma c * regMatrixDirichletAverage (appellF3Parameters a a' c)
      (appellF3Parameters b b' c) (appellF3Matrix x y) (fun z => z ^ (-c)) =
        regularizedAppellF3 a a' b b' c x y := by
  have hc : 0 < c.re := by
    simpa only [sum_appellF3Parameters] using sum_re_pos_of_mem_mvBetaConvergent ha
  have hG : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have hL := (hasSum_regMatrixDirichletAverage_cpow_neg ha hb (appellF3Matrix x y) c
    (max ‖x‖ ‖y‖) (le_trans (norm_nonneg _) (le_max_left _ _))
    (max_lt hx hy) (norm_appellF3Matrix_sub_one_le x y)).mul_left (Gamma c)
  have hR := hasSum_regularizedAppellF3_antidiagonal a a' b b' c hx hy
  apply hL.unique
  convert hR using 1
  funext N
  rw [regMatrixDirichletAverage_appellF3_moment a a' b b' c x y ha hb,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  have hGN : Gamma (c + N) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
  have hcN : (ascPochhammer ℂ N).eval c = Gamma (c + N) / Gamma c :=
    (Gamma_add_nat_div_Gamma_eq c (fun k hk => by
      have he := congrArg Complex.re hk
      simp only [neg_re, natCast_re] at he
      linarith [Nat.cast_nonneg (α := ℝ) k])).symm
  rw [hcN, regularizedAppellF3Coeff_eq, ← hdeg, Nat.cast_add_choose ℂ]
  have hGN' : Gamma (c + (p.1 + p.2 : ℕ)) ≠ 0 := by rw [hdeg]; exact hGN
  field_simp [hG, hGN', Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero]

/-- **Carlson (1971), (5.6).** The normalized bare matrix average is Appell `F₃`.
The full argument bidisk is retained, with positive real parts of both parameter vectors. -/
theorem matrixDirichletAverage_eq_appellF3 (a a' b b' c : ℂ)
    (ha : appellF3Parameters a a' c ∈ mvBetaConvergent)
    (hb : appellF3Parameters b b' c ∈ mvBetaConvergent)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    matrixDirichletAverage (appellF3Parameters a a' c) (appellF3Parameters b b' c)
      (appellF3Matrix x y) (fun z => z ^ (-c)) = appellF3 a a' b b' c x y := by
  rw [matrixDirichletAverage, sum_appellF3Parameters, sum_appellF3Parameters, appellF3]
  rw [mul_assoc, Gamma_mul_regMatrixDirichletAverage_eq_regularizedAppellF3 a a' b b' c ha hb hx hy]

end TwoVariable
end Carlson
