/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Components of a perturbed second-order complex recurrence

Reconstruction from two characteristic roots bounds two successive sequence values.
A small common error preserves the cone in which the component of the larger root
is dominant. These elementary estimates are extracted from the Jacobi growth proofs
and shared by their upper and lower bounds.
-/

public section

namespace Complex

/-- Reconstruction from the two characteristic-root components controls two
successive values of a sequence. -/
theorem norm_le_root_component_sum {u v y₀ y₁ : ℂ} (huv : u ≠ v) (hvu : ‖v‖ ≤ ‖u‖) :
    ‖y₀‖ ≤ (‖y₁ - u * y₀‖ + ‖y₁ - v * y₀‖) / ‖u - v‖ ∧
      ‖y₁‖ ≤ ‖u‖ * (‖y₁ - u * y₀‖ + ‖y₁ - v * y₀‖) / ‖u - v‖ := by
  have hw : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  constructor
  · rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖(y₁ - v * y₀) - (y₁ - u * y₀)‖ := by congr 1; ring
      _ ≤ _ := (norm_sub_le _ _).trans_eq (add_comm _ _)
  · rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖u * (y₁ - v * y₀) - v * (y₁ - u * y₀)‖ := by congr 1; ring
      _ ≤ ‖u‖ * ‖y₁ - v * y₀‖ + ‖v‖ * ‖y₁ - u * y₀‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖u‖ * ‖y₁ - v * y₀‖ + ‖u‖ * ‖y₁ - u * y₀‖ := by gcongr
      _ = _ := by ring

/-- A small common perturbation preserves the cone in which the component
of the larger characteristic root dominates, and gives its growth in one step. -/
theorem perturbed_recurrence_cone_step {a b d g e : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ‖a‖ + 2 * δ ≤ ‖b‖ - 2 * δ) (hcone : ‖g‖ ≤ ‖d‖)
    (he : ‖e‖ ≤ δ * (‖d‖ + ‖g‖)) :
    ‖a * g + e‖ ≤ ‖b * d + e‖ ∧ (‖b‖ - 2 * δ) * ‖d‖ ≤ ‖b * d + e‖ := by
  have heb : ‖e‖ ≤ 2 * δ * ‖d‖ := by
    calc ‖e‖ ≤ δ * (‖d‖ + ‖g‖) := he
      _ ≤ δ * (‖d‖ + ‖d‖) := by gcongr
      _ = _ := by ring
  have hdn : (‖b‖ - 2 * δ) * ‖d‖ ≤ ‖b * d + e‖ := by
    have := norm_sub_norm_le (b * d) (-e)
    simp only [sub_neg_eq_add, norm_neg, norm_mul] at this
    nlinarith
  have hgn : ‖a * g + e‖ ≤ (‖a‖ + 2 * δ) * ‖d‖ := by
    calc
      _ ≤ ‖a‖ * ‖g‖ + ‖e‖ := (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ ‖a‖ * ‖d‖ + 2 * δ * ‖d‖ := by gcongr
      _ = _ := by ring
  exact ⟨hgn.trans ((mul_le_mul_of_nonneg_right hgap (norm_nonneg _)).trans hdn), hdn⟩

end Complex
