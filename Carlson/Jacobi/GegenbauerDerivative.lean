/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Gegenbauer
public import Carlson.Jacobi.BetaAverage
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Gegenbauer derivatives from Jacobi derivatives

The derivative identity is obtained from the general Jacobi identity and the
Gegenbauer/Jacobi normalization. Analytic dependence on the Gegenbauer parameter
extends the result across all exceptional complex parameters. This is the
parameter-shift derivative formula used in Carlson's proof of the addition theorem.

## Main results

* `analyticAt_eval_iterate_derivative_shiftedGegenbauer_parameter`: entire parameter dependence.
* `derivative_shiftedGegenbauer_succ`: the shifted derivative formula at every complex parameter.
* `derivative_gegenbauer_succ`: the standard formula `Cₙ₊₁' = 2ρ Cₙ^(ρ+1)`.
* `iterate_derivative_gegenbauer`: every derivative order by a parameter shift.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.3, equation (2).
-/

public noncomputable section
namespace Polynomial
open Complex Set

/-- Every derivative evaluation of a shifted Gegenbauer polynomial is entire
in its parameter. This includes parameters where the degree drops. -/
theorem analyticAt_eval_iterate_derivative_shiftedGegenbauer_parameter
    (n k : ℕ) (x ρ : ℂ) :
    AnalyticAt ℂ (fun v => (derivative^[k] (shiftedGegenbauer v n)).eval x) ρ := by
  simp only [shiftedGegenbauer, iterate_derivative_sum, iterate_derivative_C_mul,
    eval_finsetSum, eval_mul, eval_C]
  apply Finset.analyticAt_fun_sum
  intro ij hij
  apply AnalyticAt.mul _ analyticAt_const
  apply AnalyticAt.mul
  · exact analyticAt_const.mul ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ ij.2)) ρ (mem_univ _))
  · simpa only [Function.comp_def] using
      ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ ij.1))
        (2 * ρ + 2 * (ij.2 : ℂ)) (mem_univ _)).comp
        (f := fun v : ℂ => 2 * v + 2 * (ij.2 : ℂ))
        ((analyticAt_const.fun_mul analyticAt_id).fun_add analyticAt_const)

/-- Away from zeros of the normalization, Gegenbauer differentiation is a direct
specialization of the Jacobi derivative identity. -/
private theorem derivative_shiftedGegenbauer_succ_of_ne_zero {ρ : ℂ} (n : ℕ)
    (hρ : (ascPochhammer ℂ (n + 1)).eval (ρ + 1 / 2) ≠ 0) :
    derivative (shiftedGegenbauer ρ (n + 1)) = C (-4 * ρ) * shiftedGegenbauer (ρ + 1) n := by
  apply mul_left_cancel₀ (show C ((ascPochhammer ℂ (n + 1)).eval (ρ + 1 / 2)) ≠ 0 by
    simpa using hρ)
  rw [← derivative_C_mul, pochhammer_mul_shiftedGegenbauer, derivative_C_mul,
    derivative_shiftedJacobi_succ]
  have hA : (ascPochhammer ℂ (n + 1)).eval (ρ + 1 / 2) =
      (ρ + 1 / 2) * (ascPochhammer ℂ n).eval (ρ + 1 + 1 / 2) := by
    rw [ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
    congr 2
    ring
  have hB : (ascPochhammer ℂ (n + 1)).eval (2 * ρ) * (2 * ρ + n + 1) =
      (2 * ρ) * (2 * ρ + 1) * (ascPochhammer ℂ n).eval (2 * (ρ + 1)) := by
    calc
      _ = (ascPochhammer ℂ (n + 2)).eval (2 * ρ) := by
        rw [ascPochhammer_succ_eval (n + 1)]
        congr 1
        push_cast
        ring
      _ = _ := by
        rw [ascPochhammer_succ_left]
        simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
        rw [ascPochhammer_succ_left]
        simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
        rw [show 2 * ρ + 1 + 1 = 2 * (ρ + 1) by ring]
        ring
  rw [hA, C_mul]
  have h := pochhammer_mul_shiftedGegenbauer (ρ + 1) n
  rw [show ρ - 1 / 2 + 1 = ρ + 1 - 1 / 2 by ring,
    show ρ - 1 / 2 + (ρ - 1 / 2) + n + 2 = 2 * ρ + n + 1 by ring]
  calc
    _ = C (-((ascPochhammer ℂ (n + 1)).eval (2 * ρ) * (2 * ρ + n + 1))) *
        shiftedJacobi (ρ + 1 - 1 / 2) (ρ + 1 - 1 / 2) n := by rw [← mul_assoc, ← C_mul]; congr 1; congr 1; ring
    _ = _ := by
      rw [hB, show -(2 * ρ * (2 * ρ + 1) * (ascPochhammer ℂ n).eval (2 * (ρ + 1))) =
        ((ρ + 1 / 2) * (-4 * ρ)) * (ascPochhammer ℂ n).eval (2 * (ρ + 1)) by ring,
        C_mul, mul_assoc, ← h, C_mul]
      ring

/-- Differentiating a shifted Gegenbauer polynomial lowers its degree and raises
its parameter, with no exclusions at exceptional complex parameters. -/
theorem derivative_shiftedGegenbauer_succ (ρ : ℂ) (n : ℕ) :
    derivative (shiftedGegenbauer ρ (n + 1)) = C (-4 * ρ) * shiftedGegenbauer (ρ + 1) n := by
  apply Polynomial.funext
  intro x
  have hf : AnalyticOnNhd ℂ (fun v => (derivative (shiftedGegenbauer v (n + 1))).eval x) univ :=
    fun v _ => by simpa using analyticAt_eval_iterate_derivative_shiftedGegenbauer_parameter (n + 1) 1 x v
  have hg : AnalyticOnNhd ℂ (fun v => -4 * v * (shiftedGegenbauer (v + 1) n).eval x) univ := by
    intro v hv
    apply (analyticAt_const.mul analyticAt_id).mul
    simpa only [Function.iterate_zero_apply, Function.comp_def] using
      (analyticAt_eval_iterate_derivative_shiftedGegenbauer_parameter n 0 x (v + 1)).comp
        (f := fun w : ℂ => w + 1) (analyticAt_id.fun_add analyticAt_const)
  have he : ∀ᶠ v : ℂ in nhds (1 : ℂ),
      (derivative (shiftedGegenbauer v (n + 1))).eval x =
        -4 * v * (shiftedGegenbauer (v + 1) n).eval x := by
    filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with v hv
    have hn : (ascPochhammer ℂ (n + 1)).eval (v + 1 / 2) ≠ 0 := by
      apply ascPochhammer_ne_zero_of_add_nat_ne_zero
      intro k hk
      have h := congrArg re hk
      simp at h
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    simpa only [eval_mul, eval_C] using
      congrArg (eval x) (derivative_shiftedGegenbauer_succ_of_ne_zero n hn)
  have h := congrFun (hf.eq_of_frequently_eq hg
    ((he.filter_mono nhdsWithin_le_nhds).frequently)) ρ
  simpa only [eval_mul, eval_C] using h

/-- The classical Gegenbauer derivative formula, derived from Jacobi and valid
at every complex parameter. -/
theorem derivative_gegenbauer_succ (ρ : ℂ) (n : ℕ) :
    derivative (gegenbauer ρ (n + 1)) = C (2 * ρ) * gegenbauer (ρ + 1) n := by
  rw [gegenbauer, derivative_comp, derivative_shiftedGegenbauer_succ]
  simp only [mul_comp, C_comp, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_sub, derivative_one, derivative_X, zero_sub, mul_neg, mul_one, gegenbauer]
  norm_num only [map_div₀, map_one, map_ofNat]
  rw [← mul_assoc, ← C_neg, ← C_mul]
  congr 1
  congr 1
  ring

/-- Every Gegenbauer derivative is obtained by shifting the parameter and lowering
the degree. The coefficient is `2^k (ρ)ₖ`, including its exceptional zeros. -/
theorem iterate_derivative_gegenbauer (ρ : ℂ) (n k : ℕ) :
    derivative^[k] (gegenbauer ρ (n + k)) =
      C ((2 : ℂ) ^ k * (ascPochhammer ℂ k).eval ρ) * gegenbauer (ρ + k) n := by
  induction k generalizing ρ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Nat.add_succ, derivative_gegenbauer_succ,
      iterate_derivative_C_mul, ih, ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one, pow_succ, Nat.cast_add,
      Nat.cast_one, ← mul_assoc, ← C_mul]
    rw [show ρ + 1 + k = ρ + (k + 1) by ring]
    congr 2
    ring

end Polynomial
