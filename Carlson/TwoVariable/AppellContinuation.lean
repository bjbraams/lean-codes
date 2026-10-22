/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.MatrixTaylor
public import Pochhammer.Gamma

/-!
# Appell matrix identifications at arbitrary parameters

Carlson (1971), equations (3.1) and (5.6), continued in the independent matrix
parameters. The entire polynomial moments and the continued binomial expansion
identify the Appell series on their full convergence diamond and bidisk.

For `F₃` the identity is division-free: the continued regularized matrix average
is `regularizedAppellF3 / Gamma c`, including at nonpositive integral `c`.
Gamma's reciprocal recurrence, rather than division by a nonzero Gamma value,
justifies the cancellation at exceptional parameters.
-/

open Complex Polynomial Dirichlet Set Finset ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- A polynomial moment divided by a shifted Gamma factor is entire under analytic substitutions. -/
private theorem analyticAt_pochhammer_div_Gamma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a c : E → ℂ} {p : E} (ha : AnalyticAt ℂ a p) (hc : AnalyticAt ℂ c p) (m n : ℕ) :
    AnalyticAt ℂ (fun q => (ascPochhammer ℂ m).eval (a q) / Gamma (c q + n)) p := by
  have hP := ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ m)) _ (mem_univ _)).comp ha
  have hG := (differentiable_one_div_Gamma.analyticAt (c p + n)).comp
    (f := fun q => c q + n) (hc.add analyticAt_const)
  simp only [div_eq_mul_inv]
  apply AnalyticAt.mul
  · exact hP
  · simpa only [Function.comp_def, one_div] using hG

/-- The explicit continued moment of the parallelogram matrix. -/
private def appellF2Moment (x y : ℂ) (N : ℕ)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 * y ^ q.2 *
    ((ascPochhammer ℂ q.1).eval (p.1 0) / Gamma (p.1 0 + p.1 1 + q.1)) *
    ((ascPochhammer ℂ q.2).eval (p.2 0) / Gamma (p.2 0 + p.2 1 + q.2))

/-- Each parallelogram moment is entire in the two independent parameter vectors. -/
private theorem analyticOnNhd_appellF2Moment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (appellF2Moment x y N) univ := by
  intro p _
  have hr : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.1) p := analyticAt_fst
  have hc : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.2) p := analyticAt_snd
  unfold appellF2Moment
  apply Finset.analyticAt_fun_sum
  intro q _
  exact (analyticAt_const.mul (analyticAt_pochhammer_div_Gamma
    ((analyticAt_pi_iff.mp hr) 0)
    (((analyticAt_pi_iff.mp hr) 0).add ((analyticAt_pi_iff.mp hr) 1)) q.1 q.1)).mul
      (analyticAt_pochhammer_div_Gamma ((analyticAt_pi_iff.mp hc) 0)
        (((analyticAt_pi_iff.mp hc) 0).add ((analyticAt_pi_iff.mp hc) 1)) q.2 q.2)

/-- The two native beta coordinates reconstruct their own Appell parameter vector. -/
private theorem appellF2Parameters_reconstruct (b : Fin 2 → ℂ) :
    appellF2Parameters (b 0) (b 0 + b 1) = b := by
  funext i
  fin_cases i <;> simp [appellF2Parameters]

/-- The continued parallelogram moments have their explicit formula at all parameters. -/
private theorem continued_appellF2Moment (x y : ℂ) (N : ℕ)
    (b β : Fin 2 → ℂ) :
    continuedRegMatrixDirichletAverage (appellF2Matrix x y) (fun z => (1 - z) ^ N) (b, β) =
      appellF2Moment x y N (b, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF2Matrix x y) N).1
    (analyticOnNhd_appellF2Moment x y N) ?_) (b, β)
  intro c γ hc hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF2Matrix x y) N).2 c γ hc hγ]
  have h := regMatrixDirichletAverage_appellF2_moment
    (c 0) (γ 0) (c 0 + c 1) (γ 0 + γ 1) x y
    (by simpa only [appellF2Parameters_reconstruct] using hc)
    (by simpa only [appellF2Parameters_reconstruct] using hγ) N
  simpa only [appellF2Parameters_reconstruct, appellF2Moment] using h

/-- **Carlson (1971), (3.1), continued.** The regularized `F₂` series is the
continued matrix average for arbitrary complex parameters on the full diamond. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF2
    (a b b' c c' : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF2Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters b' c') =
        regularizedAppellF2 a b b' c c' x y := by
  have hL := hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (appellF2Parameters b c) (appellF2Parameters b' c') (appellF2Matrix x y) a
    (by positivity) hxy (norm_appellF2Matrix_sub_one_le x y)
  have hR := hasSum_regularizedAppellF2_antidiagonal a b b' c c' hxy
  apply hL.unique
  convert hR using 1
  funext N
  rw [continued_appellF2Moment, appellF2Moment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_sub_cancel]
  rw [regularizedAppellF2Coeff_eq, ← hdeg, Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero]

/-- The mixed bare-matrix moment allows independent row and column parameter totals. -/
theorem regMatrixDirichletAverage_appellF3_moment_independent
    {b β : Fin 3 → ℂ} (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage b β (appellF3Matrix x y) (fun z => (1 - z) ^ N) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) * x ^ p.1 * y ^ p.2 *
        ((ascPochhammer ℂ p.1).eval (b 0) * (ascPochhammer ℂ p.2).eval (b 1) /
          Gamma (b 0 + b 1 + b 2 + N)) *
        ((ascPochhammer ℂ p.1).eval (β 0) * (ascPochhammer ℂ p.2).eval (β 1) /
          Gamma (β 0 + β 1 + β 2 + N)) := by
  rw [regMatrixDirichletAverage_binomial_moment hb hβ (appellF3Matrix x y)
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
  rw [he, regDirichletIntegral_smul, regDirichletIntegral_fin_three_pow_mul hb,
    regDirichletIntegral_fin_three_pow_mul hβ, hdeg]
  ring

/-- The explicit continued moment for the bare three-by-three matrix. -/
private def appellF3Moment (x y : ℂ) (N : ℕ)
    (p : (Fin 3 → ℂ) × (Fin 3 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 * y ^ q.2 *
    ((ascPochhammer ℂ q.1).eval (p.1 0) * (ascPochhammer ℂ q.2).eval (p.1 1) /
      Gamma (p.1 0 + p.1 1 + p.1 2 + N)) *
    ((ascPochhammer ℂ q.1).eval (p.2 0) * (ascPochhammer ℂ q.2).eval (p.2 1) /
      Gamma (p.2 0 + p.2 1 + p.2 2 + N))

/-- Each bare-matrix moment is entire in both independent parameter vectors. -/
private theorem analyticOnNhd_appellF3Moment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (appellF3Moment x y N) univ := by
  intro p _
  have hr : AnalyticAt ℂ (fun q : (Fin 3 → ℂ) × (Fin 3 → ℂ) => q.1) p := analyticAt_fst
  have hc : AnalyticAt ℂ (fun q : (Fin 3 → ℂ) × (Fin 3 → ℂ) => q.2) p := analyticAt_snd
  have hfactor {d : ((Fin 3 → ℂ) × (Fin 3 → ℂ)) → Fin 3 → ℂ}
      (hd : AnalyticAt ℂ d p) (m n : ℕ) :
      AnalyticAt ℂ (fun q => (ascPochhammer ℂ m).eval (d q 0) *
        (ascPochhammer ℂ n).eval (d q 1) / Gamma (d q 0 + d q 1 + d q 2 + N)) p := by
    have hP := ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n)) _ (mem_univ _)).comp
      ((analyticAt_pi_iff.mp hd) 1)
    have hQ := analyticAt_pochhammer_div_Gamma ((analyticAt_pi_iff.mp hd) 0)
      ((((analyticAt_pi_iff.mp hd) 0).add ((analyticAt_pi_iff.mp hd) 1)).add
        ((analyticAt_pi_iff.mp hd) 2)) m N
    have h : AnalyticAt ℂ (fun q =>
        ((ascPochhammer ℂ m).eval (d q 0) / Gamma (d q 0 + d q 1 + d q 2 + N)) *
          (ascPochhammer ℂ n).eval (d q 1)) p := by
      apply AnalyticAt.mul
      · exact hQ
      · exact hP
    apply h.congr
    filter_upwards with q
    ring
  unfold appellF3Moment
  apply Finset.analyticAt_fun_sum
  intro q _
  exact (analyticAt_const.mul (hfactor hr q.1 q.2)).mul (hfactor hc q.1 q.2)

/-- The bare-matrix mixed moments continue to arbitrary independent complex parameters. -/
private theorem continued_appellF3Moment (x y : ℂ) (N : ℕ)
    (b β : Fin 3 → ℂ) :
    continuedRegMatrixDirichletAverage (appellF3Matrix x y) (fun z => (1 - z) ^ N) (b, β) =
      appellF3Moment x y N (b, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF3Matrix x y) N).1
    (analyticOnNhd_appellF3Moment x y N) ?_) (b, β)
  intro c γ hc hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF3Matrix x y) N).2 c γ hc hγ]
  exact regMatrixDirichletAverage_appellF3_moment_independent hc hγ x y N

/-- **Carlson (1971), (5.6), division-free continuation.** This identity includes
nonpositive integral `c`; it does not multiply a zero matrix value by totalized Gamma. -/
theorem continuedRegMatrixDirichletAverage_eq_inv_Gamma_mul_regularizedAppellF3
    (a a' b b' c : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF3Matrix x y) (fun z => z ^ (-c))
      (appellF3Parameters a a' c, appellF3Parameters b b' c) =
        (Gamma c)⁻¹ * regularizedAppellF3 a a' b b' c x y := by
  have hL := hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (appellF3Parameters a a' c) (appellF3Parameters b b' c) (appellF3Matrix x y) c
    (le_trans (norm_nonneg _) (le_max_left _ _)) (max_lt hx hy)
    (norm_appellF3Matrix_sub_one_le x y)
  have hR := (hasSum_regularizedAppellF3_antidiagonal a a' b b' c hx hy).mul_left ((Gamma c)⁻¹)
  apply hL.unique
  convert hR using 1
  funext N
  rw [continued_appellF3Moment, appellF3Moment, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  simp only [appellF3Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  have hs (s t : ℂ) : s + t + (c - s - t) = c := by ring
  rw [hs, hs, regularizedAppellF3Coeff_eq, ← hdeg, Nat.cast_add_choose ℂ,
    one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat c (p.1 + p.2)]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero]

/-- Away from denominator poles the Gamma-normalized continued matrix is regularized `F₃`. -/
theorem Gamma_mul_continuedRegMatrixDirichletAverage_eq_regularizedAppellF3
    (a a' b b' c : ℂ) (hc : ∀ m : ℕ, c ≠ -(m : ℂ))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Gamma c * continuedRegMatrixDirichletAverage (appellF3Matrix x y) (fun z => z ^ (-c))
      (appellF3Parameters a a' c, appellF3Parameters b b' c) =
        regularizedAppellF3 a a' b b' c x y := by
  rw [continuedRegMatrixDirichletAverage_eq_inv_Gamma_mul_regularizedAppellF3 a a' b b' c hx hy,
    ← mul_assoc, mul_inv_cancel₀ (Gamma_ne_zero hc), one_mul]

/-- At an exceptional common total parameter the regularized bare matrix vanishes. -/
theorem continuedRegMatrixDirichletAverage_appellF3_neg_nat
    (a a' b b' : ℂ) (m : ℕ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF3Matrix x y) (fun z => z ^ (m : ℂ))
      (appellF3Parameters a a' (-(m : ℂ)), appellF3Parameters b b' (-(m : ℂ))) = 0 := by
  simpa only [neg_neg, Gamma_neg_nat_eq_zero, inv_zero, zero_mul] using
    continuedRegMatrixDirichletAverage_eq_inv_Gamma_mul_regularizedAppellF3
      a a' b b' (-(m : ℂ)) hx hy

end Carlson.TwoVariable
