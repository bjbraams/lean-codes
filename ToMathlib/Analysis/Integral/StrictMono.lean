/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Strict comparison of real integrals

If `f ≤ g` almost everywhere for integrable real functions and `f < g` on a set of positive
measure, then `∫ f < ∫ g`. In particular an almost everywhere strict inequality gives a strict
inequality of integrals for a nonzero measure.

## Main results

* `MeasureTheory.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero`: the strict
  comparison; the interval-integral analogue is Mathlib's
  `intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero`.
* `MeasureTheory.integral_lt_integral_of_ae_lt`: the case of an almost everywhere strict
  inequality.
-/

public section
namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

/-- If `f ≤ g` almost everywhere and `f < g` on a set of positive measure, then the integral of
`f` is strictly less than the integral of `g`, for integrable real functions. -/
theorem integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (hf : Integrable f μ)
    (hg : Integrable g μ) (hle : f ≤ᵐ[μ] g) (hlt : μ {x | f x < g x} ≠ 0) :
    (∫ x, f x ∂μ) < ∫ x, g x ∂μ := by
  refine lt_of_le_of_ne (integral_mono_ae hf hg hle) fun heq ↦ hlt ?_
  have he := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  exact measure_mono_null (fun x (hx : f x < g x) ↦ hx.ne) (ae_iff.mp he)

/-- Integrating an almost everywhere strict inequality preserves strictness for a nonzero
measure, provided both real functions are integrable. -/
theorem integral_lt_integral_of_ae_lt [NeZero μ] (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x < g x) : (∫ x, f x ∂μ) < ∫ x, g x ∂μ := by
  refine integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hf hg
    (hfg.mono fun _ h ↦ h.le) fun h0 ↦ NeZero.ne μ ?_
  rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self {x | f x < g x}]
  exact measure_union_null h0 (ae_iff.mp hfg)

end MeasureTheory
