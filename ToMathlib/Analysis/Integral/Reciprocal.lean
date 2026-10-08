/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Compactifying a positive half-line by inversion

The substitution `x = u⁻¹` identifies integration on `(a, ∞)`, for positive `a`,
with a weighted integral on `(0, a⁻¹)`. Both Bochner integrals and integrability
are preserved with the Jacobian `u⁻²`. The results follow from Mathlib's
one-dimensional change-of-variables theorem and do not assume continuity.

## Main results

* `MeasureTheory.integrableOn_Ioi_iff_integrableOn_Ioo_inv`: Inversion converts integrability on
  a positive half-line into weighted integrability on a bounded interval.
* `MeasureTheory.integral_Ioi_eq_integral_Ioo_inv`: Inversion changes a half-line integral into
  an integral over a bounded interval, including its inverse-square Jacobian.
-/

public section
open Set
open scoped Pointwise
namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℝ}

/-- Inversion changes integrability on a measurable set avoiding zero, with its Jacobian. -/
theorem integrableOn_inv_iff {s : Set ℝ} (hs : MeasurableSet s) (h0 : 0 ∉ s) (f : ℝ → F) :
    IntegrableOn f s⁻¹ ↔ IntegrableOn (fun u ↦ (u ^ 2)⁻¹ • f u⁻¹) s := by
  simpa only [image_inv_eq_inv, abs_neg, abs_inv, abs_pow, sq_abs] using
    integrableOn_image_iff_integrableOn_abs_deriv_smul hs
      (fun u hu ↦ (hasDerivAt_inv (by rintro rfl; exact h0 hu)).hasDerivWithinAt)
      inv_injective.injOn f

/-- Inversion on a measurable set avoiding zero has inverse-square Jacobian. -/
theorem integral_inv_eq {s : Set ℝ} (hs : MeasurableSet s) (h0 : 0 ∉ s) (f : ℝ → F) :
    ∫ x in s⁻¹, f x = ∫ u in s, (u ^ 2)⁻¹ • f u⁻¹ := by
  simpa only [image_inv_eq_inv, abs_neg, abs_inv, abs_pow, sq_abs] using
    integral_image_eq_integral_abs_deriv_smul hs
      (fun u hu ↦ (hasDerivAt_inv (by rintro rfl; exact h0 hu)).hasDerivWithinAt)
      inv_injective.injOn f

/-- Inversion converts integrability on a positive half-line into weighted integrability
on a bounded interval. -/
theorem integrableOn_Ioi_iff_integrableOn_Ioo_inv (ha : 0 < a) (f : ℝ → F) :
    IntegrableOn f (Ioi a) ↔
      IntegrableOn (fun u : ℝ ↦ (u ^ 2)⁻¹ • f u⁻¹) (Ioo 0 a⁻¹) := by
  simpa only [inv_Ioo_0_left (inv_pos.mpr ha), inv_inv] using
    integrableOn_inv_iff (s := Ioo 0 a⁻¹) measurableSet_Ioo (by simp) f

/-- Inversion changes a half-line integral into an integral over a bounded interval,
including its inverse-square Jacobian. -/
theorem integral_Ioi_eq_integral_Ioo_inv (ha : 0 < a) (f : ℝ → F) :
    ∫ x in Ioi a, f x = ∫ u in Ioo 0 a⁻¹, (u ^ 2)⁻¹ • f u⁻¹ := by
  simpa only [inv_Ioo_0_left (inv_pos.mpr ha), inv_inv] using
    integral_inv_eq (s := Ioo 0 a⁻¹) measurableSet_Ioo (by simp) f

end MeasureTheory
