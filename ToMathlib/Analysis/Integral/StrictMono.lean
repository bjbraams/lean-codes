/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Strict comparison of real integrals

For a nonzero measure, an almost everywhere strict comparison between integrable
real functions gives a strict comparison of their integrals.
-/

public section
namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [NeZero μ]

/-- Integrating an almost everywhere strict inequality preserves strictness for a nonzero
measure, provided both real functions are integrable. -/
theorem integral_lt_integral_of_ae_lt {f g : α → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : ∀ᵐ x ∂μ, f x < g x) :
    (∫ x, f x ∂μ) < ∫ x, g x ∂μ := by
  have hle := hfg.mono fun _ h ↦ h.le
  apply lt_of_le_of_ne (integral_mono_ae hf hg hle)
  intro heq
  have he := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  obtain ⟨x, hx, hlt⟩ := (he.and hfg).exists
  exact hlt.ne hx

end MeasureTheory
