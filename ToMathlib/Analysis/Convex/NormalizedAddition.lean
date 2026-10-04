/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic

/-!
# Convexity under normalized addition

Dividing two positive vectors by positive scales expresses their normalized sum as
a convex combination. Strict convexity gives a strict inequality unless the vectors
are proportional. The index type need not be finite or nonempty.
-/

public section
variable {ι : Type*}

/-- Normalized addition is a strict convex combination unless the original positive
vectors are proportional. -/
theorem StrictConvexOn.map_normalized_add_lt {F : (ι → ℝ) → ℝ}
    (hF : StrictConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} F)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    F (fun i => (A + B)⁻¹ * (x i + y i)) <
      A / (A + B) * F (fun i => A⁻¹ * x i) +
      B / (A + B) * F (fun i => B⁻¹ * y i) := by
  have hS := add_pos hA hB
  have hxy : (fun i => A⁻¹ * x i) ≠ (fun i => B⁻¹ * y i) := by
    intro he
    apply hne
    refine ⟨B / A, div_pos hB hA, fun i => ?_⟩
    have hi := congrFun he i
    field_simp at hi ⊢
    nlinarith
  have hab : A / (A + B) + B / (A + B) = 1 := by
    rw [← add_div, div_self hS.ne']
  have h := hF.2 (fun i => mul_pos (inv_pos.mpr hA) (hx i))
    (fun i => mul_pos (inv_pos.mpr hB) (hy i)) hxy
    (div_pos hA hS) (div_pos hB hS) hab
  have he : (A / (A + B)) • (fun i => A⁻¹ * x i) +
      (B / (A + B)) • (fun i => B⁻¹ * y i) =
      (fun i => (A + B)⁻¹ * (x i + y i)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  simpa only [he, smul_eq_mul] using h

/-- The concave version of normalized addition. -/
theorem StrictConcaveOn.lt_map_normalized_add {F : (ι → ℝ) → ℝ}
    (hF : StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} F)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A / (A + B) * F (fun i => A⁻¹ * x i) +
      B / (A + B) * F (fun i => B⁻¹ * y i) <
      F (fun i => (A + B)⁻¹ * (x i + y i)) := by
  simpa only [Pi.neg_apply, mul_neg, ← neg_add, neg_lt_neg_iff] using
    hF.neg.map_normalized_add_lt hx hy hne hA hB

