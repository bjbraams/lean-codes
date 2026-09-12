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

end Complex

end
