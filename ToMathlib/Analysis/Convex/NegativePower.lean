/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Convexity of negative real powers

The power function is strictly convex on the positive half-line for a negative
exponent. This complements Mathlib's convexity theorem for exponents at least one.
-/

open Set
public section
namespace Real

/-- Negative powers are strictly convex on the positive half-line. -/
theorem strictConvexOn_rpow_of_neg {t : ℝ} (ht : t < 0) :
    StrictConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x ^ t) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hp : 0 < a • x + b • y := (convex_Ioi (0 : ℝ)) hx hy ha.le hb.le hab
  change (a • x + b • y) ^ t < a • x ^ t + b • y ^ t
  rw [rpow_def_of_pos hp, rpow_def_of_pos hx, rpow_def_of_pos hy]
  have hlog := strictConcaveOn_log_Ioi.2 hx hy hxy ha hb hab
  calc
    exp (log (a • x + b • y) * t) < exp ((a • log x + b • log y) * t) :=
      exp_lt_exp.mpr (mul_lt_mul_of_neg_right hlog ht)
    _ = exp (a • (log x * t) + b • (log y * t)) := by congr 1; simp only [smul_eq_mul]; ring
    _ ≤ a • exp (log x * t) + b • exp (log y * t) :=
      convexOn_exp.2 (mem_univ _) (mem_univ _) ha.le hb.le hab

/-- Nonpositive powers are convex on the positive half-line. -/
theorem convexOn_rpow_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x ^ t) := by
  rcases ht.eq_or_lt with h | h
  · subst t; simpa using convexOn_const (c := (1 : ℝ)) (convex_Ioi (0 : ℝ))
  · exact (strictConvexOn_rpow_of_neg h).convexOn

end Real
