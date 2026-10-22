/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.LogarithmicMean
public import ToMathlib.Algebra.Polynomial.PochhammerIdentities
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The half-integer Pochhammer remainder in Stirling's formula

Carlson (1977), Theorem 2.7-1. The proof sums the strict logarithmic-mean
bounds over `n ≤ k < 2n`. Mathlib's Stirling sequence packages the telescoping
factorial and logarithm terms; no asymptotic estimate is needed for the remainder.
-/

open Polynomial Real Finset

public noncomputable section

namespace Stirling

/-- A successive logarithmic Stirling difference is the relative mean error. -/
private theorem log_stirlingSeq_sdiff_eq_mean {n : ℕ} (hn : 0 < n) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) =
      ((n : ℝ) + 1 + n) / 2 * (log ((n : ℝ) + 1) - log n) - 1 := by
  simp (disch := positivity) only [log_stirlingSeq_formula, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, log_mul, log_div, log_exp]
  ring

/-- The strict stepwise Robbins bound, with a strict positive lower bound. -/
theorem log_stirlingSeq_sdiff_pos_lt {n : ℕ} (hn : 0 < n) :
    0 < log (stirlingSeq n) - log (stirlingSeq (n + 1)) ∧
      log (stirlingSeq n) - log (stirlingSeq (n + 1)) <
        1 / (12 * (n : ℝ) * (n + 1)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := arithmetic_logarithmicMean_ratio_bounds
    (show 0 < (n : ℝ) + 1 by positivity) hn' (by linarith : (n : ℝ) + 1 ≠ n)
  rw [log_stirlingSeq_sdiff_eq_mean hn]
  have hden : (n : ℝ) + 1 - n = 1 := by ring
  simp only [hden, one_pow, div_one] at h
  constructor
  · have hp : 0 < 1 / (3 * ((n : ℝ) + 1 + n) ^ 2) := by positivity
    linarith [h.1]
  · have hu : ((n : ℝ) + 1 + n) / 2 * (log ((n : ℝ) + 1) - log n) - 1 <
        1 / (12 * ((n : ℝ) + 1) * n) := by linarith [h.2]
    convert hu using 1; ring

/-- Summing the strict Robbins bound from `n` to `2n` gives Carlson's remainder interval. -/
theorem log_stirlingSeq_double_bounds {n : ℕ} (hn : 0 < n) :
    0 < log (stirlingSeq n) - log (stirlingSeq (2 * n)) ∧
      log (stirlingSeq n) - log (stirlingSeq (2 * n)) < 1 / (24 * (n : ℝ)) := by
  let f := fun k : ℕ => log (stirlingSeq (n + k))
  let g := fun k : ℕ => 1 / (12 * ((n + k : ℕ) : ℝ))
  have he : (∑ k ∈ range n, (f k - f (k + 1))) =
      log (stirlingSeq n) - log (stirlingSeq (2 * n)) := by
    rw [sum_range_sub']
    simp only [f, Nat.add_zero, two_mul]
  have hg : (∑ k ∈ range n, (g k - g (k + 1))) = 1 / (24 * (n : ℝ)) := by
    rw [sum_range_sub']
    dsimp [g]
    push_cast
    field_simp
    ring
  have hstep (k : ℕ) : 0 < f k - f (k + 1) ∧ f k - f (k + 1) < g k - g (k + 1) := by
    have hnk : 0 < n + k := by omega
    have h := log_stirlingSeq_sdiff_pos_lt hnk
    dsimp [f, g]
    rw [← Nat.add_assoc]
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    push_cast
    field_simp
    ring
  constructor
  · rw [← he]
    exact sum_pos (fun k _ => (hstep k).1) (nonempty_range_iff.mpr hn.ne')
  · rw [← he, ← hg]
    exact sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hn.ne') (fun k _ => (hstep k).2)

end Stirling

namespace Real

/-- Duplication expresses the half-integer rising factorial through two factorials. -/
theorem ascPochhammer_half_eq_factorial_ratio (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2) =
      ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ)) := by
  have h := ascPochhammer_eval_double (R := ℝ) (1 / 2) n
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ascPochhammer_eval_one] at h
  apply (eq_div_iff (by positivity)).mpr
  linear_combination -h

/-- The logarithmic error of the half-integer rising factorial is a Stirling difference. -/
private theorem log_ascPochhammer_half_error {n : ℕ} (hn : 0 < n) :
    log ((ascPochhammer ℝ n).eval (1 / 2)) -
        (log (sqrt 2) + (n : ℝ) * log n - n) =
      log (Stirling.stirlingSeq (2 * n)) - log (Stirling.stirlingSeq n) := by
  rw [ascPochhammer_half_eq_factorial_ratio]
  simp (disch := positivity) only [Stirling.log_stirlingSeq_formula,
    log_div, log_mul, log_pow, log_exp, log_sqrt, Nat.cast_mul, Nat.cast_ofNat]
  have h4 : log (4 : ℝ) = 2 * log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  rw [h4]
  ring

/-- **Carlson Theorem 2.7-1.** The half-integer rising factorial has a strict
remainder of the form `θ / (24 n)`, with `0 < θ < 1`, for every positive `n`. -/
theorem ascPochhammer_half_stirling_remainder {n : ℕ} (hn : 0 < n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (ascPochhammer ℝ n).eval (1 / 2) =
        sqrt 2 * (n : ℝ) ^ n * exp (-(n : ℝ) - θ / (24 * n)) := by
  let e := log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq (2 * n))
  have hb := Stirling.log_stirlingSeq_double_bounds hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hepos : 0 < e := hb.1
  refine ⟨24 * n * e, by dsimp [e]; positivity, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_left hb.2 (show 0 < 24 * (n : ℝ) by positivity)
    have he : 24 * (n : ℝ) * (1 / (24 * n)) = 1 := by field_simp
    rwa [he] at h
  · have he := log_ascPochhammer_half_error hn
    have hp : 0 < (ascPochhammer ℝ n).eval (1 / 2) := ascPochhammer_pos n (1 / 2 : ℝ) (by norm_num)
    have hh : log ((ascPochhammer ℝ n).eval (1 / 2)) =
        log (sqrt 2) + (n : ℝ) * log n - n - e := by dsimp [e]; linarith
    apply log_injOn_pos hp (by change 0 < _; positivity)
    rw [show 24 * (n : ℝ) * e / (24 * n) = e by field_simp]
    simp (disch := positivity) only [log_mul, log_pow, log_exp]
    linarith [hh]

end Real
