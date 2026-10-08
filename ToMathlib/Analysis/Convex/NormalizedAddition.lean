/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Convexity under normalized addition

For `A, B > 0` the normalized sum `(A + B)⁻¹ • (x + y)` is the convex combination of the rescaled
vectors `A⁻¹ • x` and `B⁻¹ • y` with weights `A / (A + B)` and `B / (A + B)`. Hence a convex
function `F` satisfies
`F ((A + B)⁻¹ • (x + y)) ≤ A / (A + B) * F (A⁻¹ • x) + B / (A + B) * F (B⁻¹ • y)`,
strictly for a strictly convex function when the rescaled vectors differ. For positive vectors in
`ι → ℝ` this holds in particular unless the vectors are proportional; the index type need not be
finite or nonempty.

## Main results

* `ConvexOn.map_add_smul_le`, `StrictConvexOn.map_add_smul_lt`: the inequalities in a real
  vector space; `ConcaveOn.le_map_add_smul`, `StrictConcaveOn.lt_map_add_smul`: the concave
  versions.
* `StrictConvexOn.map_normalized_add_lt`, `StrictConcaveOn.lt_map_normalized_add`: the strict
  inequalities for positive vectors in `ι → ℝ`.
* `inv_mul_ne_inv_mul_of_not_proportional`: non-proportional vectors have distinct rescalings.
-/

public section

section VectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {F : E → ℝ} {x y : E} {A B : ℝ}

/-- The normalized sum is the convex combination of the rescaled vectors. -/
private theorem normalized_add_eq (hA : 0 < A) (hB : 0 < B) :
    (A / (A + B)) • A⁻¹ • x + (B / (A + B)) • B⁻¹ • y = (A + B)⁻¹ • (x + y) := by
  have hS := add_pos hA hB
  rw [smul_smul, smul_smul, smul_add]
  congr 2 <;> field_simp

/-- **Convexity under normalized addition.** -/
theorem ConvexOn.map_add_smul_le (hF : ConvexOn ℝ s F) (hA : 0 < A) (hB : 0 < B)
    (hx : A⁻¹ • x ∈ s) (hy : B⁻¹ • y ∈ s) :
    F ((A + B)⁻¹ • (x + y)) ≤ A / (A + B) * F (A⁻¹ • x) + B / (A + B) * F (B⁻¹ • y) := by
  have hS := add_pos hA hB
  have h := hF.2 hx hy (div_pos hA hS).le (div_pos hB hS).le (by rw [← add_div, div_self hS.ne'])
  rwa [normalized_add_eq hA hB, smul_eq_mul, smul_eq_mul] at h

/-- **Strict convexity under normalized addition**: the inequality is strict when the rescaled
vectors differ. -/
theorem StrictConvexOn.map_add_smul_lt (hF : StrictConvexOn ℝ s F) (hA : 0 < A) (hB : 0 < B)
    (hx : A⁻¹ • x ∈ s) (hy : B⁻¹ • y ∈ s) (hxy : A⁻¹ • x ≠ B⁻¹ • y) :
    F ((A + B)⁻¹ • (x + y)) < A / (A + B) * F (A⁻¹ • x) + B / (A + B) * F (B⁻¹ • y) := by
  have hS := add_pos hA hB
  have h := hF.2 hx hy hxy (div_pos hA hS) (div_pos hB hS) (by rw [← add_div, div_self hS.ne'])
  rwa [normalized_add_eq hA hB, smul_eq_mul, smul_eq_mul] at h

/-- **Concavity under normalized addition.** -/
theorem ConcaveOn.le_map_add_smul (hF : ConcaveOn ℝ s F) (hA : 0 < A) (hB : 0 < B)
    (hx : A⁻¹ • x ∈ s) (hy : B⁻¹ • y ∈ s) :
    A / (A + B) * F (A⁻¹ • x) + B / (A + B) * F (B⁻¹ • y) ≤ F ((A + B)⁻¹ • (x + y)) := by
  simpa only [Pi.neg_apply, mul_neg, ← neg_add, neg_le_neg_iff] using
    hF.neg.map_add_smul_le hA hB hx hy

/-- **Strict concavity under normalized addition.** -/
theorem StrictConcaveOn.lt_map_add_smul (hF : StrictConcaveOn ℝ s F) (hA : 0 < A) (hB : 0 < B)
    (hx : A⁻¹ • x ∈ s) (hy : B⁻¹ • y ∈ s) (hxy : A⁻¹ • x ≠ B⁻¹ • y) :
    A / (A + B) * F (A⁻¹ • x) + B / (A + B) * F (B⁻¹ • y) < F ((A + B)⁻¹ • (x + y)) := by
  simpa only [Pi.neg_apply, mul_neg, ← neg_add, neg_lt_neg_iff] using
    hF.neg.map_add_smul_lt hA hB hx hy hxy

end VectorSpace

section Positive

variable {ι : Type*}

/-- Positive rescalings of two positive vectors that are not proportional are distinct. -/
theorem inv_mul_ne_inv_mul_of_not_proportional {x y : ι → ℝ}
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (fun i ↦ A⁻¹ * x i) ≠ (fun i ↦ B⁻¹ * y i) := by
  intro he
  apply hne
  refine ⟨B / A, div_pos hB hA, fun i ↦ ?_⟩
  have hi := congrFun he i
  field_simp at hi ⊢
  nlinarith

/-- Normalized addition of positive vectors is a strict convex combination of the rescaled
vectors when these are distinct. -/
theorem StrictConvexOn.map_normalized_add_lt {F : (ι → ℝ) → ℝ}
    (hF : StrictConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} F)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) {A B : ℝ}
    (hxy : (fun i ↦ A⁻¹ * x i) ≠ (fun i ↦ B⁻¹ * y i)) (hA : 0 < A) (hB : 0 < B) :
    F (fun i ↦ (A + B)⁻¹ * (x i + y i)) <
      A / (A + B) * F (fun i ↦ A⁻¹ * x i) +
      B / (A + B) * F (fun i ↦ B⁻¹ * y i) :=
  hF.map_add_smul_lt hA hB (fun i ↦ mul_pos (inv_pos.mpr hA) (hx i))
    (fun i ↦ mul_pos (inv_pos.mpr hB) (hy i)) hxy

/-- The concave version of normalized addition of positive vectors. -/
theorem StrictConcaveOn.lt_map_normalized_add {F : (ι → ℝ) → ℝ}
    (hF : StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} F)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) {A B : ℝ}
    (hxy : (fun i ↦ A⁻¹ * x i) ≠ (fun i ↦ B⁻¹ * y i)) (hA : 0 < A) (hB : 0 < B) :
    A / (A + B) * F (fun i ↦ A⁻¹ * x i) +
      B / (A + B) * F (fun i ↦ B⁻¹ * y i) <
      F (fun i ↦ (A + B)⁻¹ * (x i + y i)) :=
  hF.lt_map_add_smul hA hB (fun i ↦ mul_pos (inv_pos.mpr hA) (hx i))
    (fun i ↦ mul_pos (inv_pos.mpr hB) (hy i)) hxy

end Positive
