/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Strict weighted geometric-mean inequality for sums

Positive weights give strict Hölder interpolation unless the two positive vectors
are proportional. The weights need not sum to one.
-/

public section
namespace Real
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Weighted geometric interpolation is strictly submultiplicative under summation
unless the two positive vectors are proportional. -/
theorem sum_mul_rpow_mul_rpow_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {w x y : ι → ℝ} (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    (∑ i, w i * (x i ^ a * y i ^ c)) < (∑ i, w i * x i) ^ a * (∑ i, w i * y i) ^ c := by
  let A := ∑ i, w i * x i
  let B := ∑ i, w i * y i
  have hA : 0 < A := Finset.sum_pos (fun i _ ↦ mul_pos (hw i) (hx i)) Finset.univ_nonempty
  have hB : 0 < B := Finset.sum_pos (fun i _ ↦ mul_pos (hw i) (hy i)) Finset.univ_nonempty
  have hn : ∃ i, x i / A ≠ y i / B := by
    by_contra! he
    apply hne
    refine ⟨B / A, div_pos hB hA, fun i ↦ ?_⟩
    have hi := (div_eq_div_iff hA.ne' hB.ne').mp (he i)
    calc
      y i = B * x i / A := (eq_div_iff hA.ne').mpr (by nlinarith)
      _ = B / A * x i := by ring
  have hle i := geom_mean_le_arith_mean2_weighted ha.le hc.le
    (div_pos (hx i) hA).le (div_pos (hy i) hB).le hac
  have hsum : (∑ i, w i * ((x i / A) ^ a * (y i / B) ^ c)) <
      ∑ i, w i * (a * (x i / A) + c * (y i / B)) := by
    obtain ⟨i, hi⟩ := hn
    exact Finset.sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (hle j) (hw j).le)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left
        ((geom_mean_lt_arith_mean2_weighted_iff_of_pos ha hc
          (div_pos (hx i) hA).le (div_pos (hy i) hB).le hac).mpr hi) (hw i)⟩
  have he : (∑ i, w i * (a * (x i / A) + c * (y i / B))) = 1 := by
    simp_rw [mul_add, Finset.sum_add_distrib,
      show ∀ i, w i * (a * (x i / A)) = a * (w i * x i) / A by intro i; ring,
      show ∀ i, w i * (c * (y i / B)) = c * (w i * y i) / B by intro i; ring,
      ← Finset.sum_div, ← Finset.mul_sum]
    rw [show ∑ i, w i * x i = A from rfl, show ∑ i, w i * y i = B from rfl,
      mul_div_cancel_right₀ _ hA.ne', mul_div_cancel_right₀ _ hB.ne', hac]
  rw [he] at hsum
  simp_rw [div_rpow (hx _).le hA.le, div_rpow (hy _).le hB.le,
    div_mul_div_comm, ← mul_div_assoc, ← Finset.sum_div] at hsum
  exact (div_lt_one (mul_pos (rpow_pos_of_pos hA a) (rpow_pos_of_pos hB c))).mp hsum

end Real
