/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The coefficients in Carlson's logarithmic elliptic expansion

Formula (8.3-15) evaluates the digamma difference occurring in the logarithmic series
(8.3-13) and (8.3-14). We use Mathlib's digamma values and recurrence; the expansion
itself is a separate statement.
-/

open Complex

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **Carlson (8.3-15), initial coefficient**: `ψ(1) - ψ(1/2) = 2 log 2`. -/
theorem digamma_one_sub_half :
    digamma 1 - digamma (1 / 2) = 2 * log 2 := by
  rw [digamma_one, digamma_one_half]
  ring

/-- **Carlson (8.3-15)**: all logarithmic-series coefficients, with an empty sum
at `n = 0`. The summand is `1/((k+1)(2k+1))`. -/
theorem digamma_nat_sub_half (n : ℕ) :
    digamma (1 + n) - digamma (1 / 2 + n) =
      2 * log 2 - ∑ k ∈ Finset.range n, ((k + 1 : ℂ) * (2 * k + 1))⁻¹ := by
  have hi (m : ℕ) : (1 : ℂ) ≠ -m := by
    intro h
    have := congrArg re h
    simp only [one_re, neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hh (m : ℕ) : (1 / 2 : ℂ) ≠ -m := by
    intro h
    have := congrArg re h
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [digamma_apply_add_nat hi n, digamma_apply_add_nat hh n,
    show digamma 1 + ∑ k ∈ Finset.range n, (1 + (k : ℂ))⁻¹ -
        (digamma (1 / 2) + ∑ k ∈ Finset.range n, (1 / 2 + (k : ℂ))⁻¹) =
        (digamma 1 - digamma (1 / 2)) +
          ∑ k ∈ Finset.range n, ((1 + (k : ℂ))⁻¹ - (1 / 2 + (k : ℂ))⁻¹) by
      rw [Finset.sum_sub_distrib]; ring,
    digamma_one_sub_half]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h1 : (1 + (k : ℂ)) ≠ 0 := by
    intro h
    have := congrArg re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h2 : (1 / 2 + (k : ℂ)) ≠ 0 := by
    intro h
    have := congrArg re h
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h3 : (2 * (k : ℂ) + 1) ≠ 0 := by
    intro h
    apply h2
    linear_combination h / 2
  have h4 : ((k : ℂ) + 1) ≠ 0 := by simpa [add_comm] using h1
  have h5 : (1 + (k : ℂ) * 2) ≠ 0 := by simpa [add_comm, mul_comm] using h3
  field_simp [h1, h2, h3, h4, h5]
  ring_nf
  field_simp [h5]
  ring

end Carlson.TwoVariable
