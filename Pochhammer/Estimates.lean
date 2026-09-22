/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Elementary bounds for ascending Pochhammer symbols
-/

public noncomputable section

namespace Complex

/-- The sharp elementary Pochhammer bound, retaining the rising factorial rather
than replacing every factor by the largest one. -/
theorem norm_ascPochhammer_eval_le_ascPochhammer (a : ℂ) (n : ℕ) {B : ℝ}
    (ha : ‖a‖ ≤ B) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ (ascPochhammer ℝ n).eval B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul, ascPochhammer_succ_eval]
    apply mul_le_mul ih
      ((norm_add_le a (n : ℂ)).trans (by simpa using add_le_add_right ha (n : ℝ)))
      (norm_nonneg _)
    exact (norm_nonneg _).trans ih

/-- An ascending Pochhammer symbol is bounded by a power of a uniform bound on the argument. -/
theorem norm_ascPochhammer_eval_le (a : ℂ) (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ‖a‖ ≤ B) :
    ‖(ascPochhammer ℂ k).eval a‖ ≤ (B + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, norm_mul]
    have h1 : ‖(ascPochhammer ℂ k).eval a‖ ≤ (B + k + 1) ^ k :=
      ih.trans <| pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : ‖a + (k : ℂ)‖ ≤ B + k + 1 := by
      calc
        ‖a + (k : ℂ)‖ ≤ ‖a‖ + ‖(k : ℂ)‖ := norm_add_le _ _
        _ = ‖a‖ + k := by simp
        _ ≤ B + k := by gcongr
        _ ≤ B + k + 1 := by linarith
    calc
      ‖(ascPochhammer ℂ k).eval a‖ * ‖a + k‖ ≤ (B + k + 1) ^ k * (B + k + 1) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (B + k + 1) ^ (k + 1) := (pow_succ _ _).symm
      _ = (B + (k + 1 : ℕ)) ^ (k + 1) := by simp [Nat.cast_succ, add_assoc]

/-- Ascending Pochhammer symbols do not vanish in the open right half-plane. -/
theorem ascPochhammer_eval_ne_zero_of_re_pos {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval c ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨k, _, hk⟩
  have h := congrArg Complex.re hk
  simp only [natCast_re, neg_re] at h
  linarith

/-- A geometric bound for binomial coefficients, uniform in the degree. -/
theorem norm_ascPochhammer_eval_le_factorial_mul_pow (a : ℂ) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ (n.factorial : ℝ) * (‖a‖ + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul]
    have h : ‖a + (n : ℂ)‖ ≤ (n + 1) * (‖a‖ + 1) := by
      have h₀ := norm_add_le a (n : ℂ)
      simp only [norm_natCast] at h₀
      nlinarith [norm_nonneg a, Nat.cast_nonneg (α := ℝ) n]
    calc
      _ ≤ ((n.factorial : ℝ) * (‖a‖ + 1) ^ n) * ((n + 1) * (‖a‖ + 1)) :=
        mul_le_mul ih h (norm_nonneg _) (by positivity)
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- The half-integer Pochhammer factors are a lower bound for the denominator. -/
theorem norm_ascPochhammer_half_le {c : ℂ} (hc : 1 / 2 ≤ c.re) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval (1 / 2)‖ ≤ ‖(ascPochhammer ℂ n).eval c‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [ascPochhammer_succ_eval, norm_mul]
    apply mul_le_mul ih _ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖(1 / 2 : ℂ) + n‖ = 1 / 2 + (n : ℝ) := by
        rw [show (1 / 2 : ℂ) + n = ((1 / 2 + (n : ℝ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (c + n).re := by simp only [add_re, natCast_re]; linarith
      _ ≤ ‖c + n‖ := re_le_norm _

end Complex

end
