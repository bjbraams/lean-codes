/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product integrals over measurable sets by slices

This file provides Tonelli and Fubini formulas for integration over an arbitrary measurable
subset of a product. It is a temporary home for results intended respectively for
`Mathlib.MeasureTheory.Measure.Prod` and `Mathlib.MeasureTheory.Integral.Prod`.
-/

open MeasureTheory

public noncomputable section

namespace MeasureTheory

/-! ## Nonnegative integrals -/

/-- Tonelli's theorem for a nonnegative integral restricted to a measurable subset of a product.
Unlike `setIntegral_prod_slices`, this result requires no integrability hypothesis. -/
lemma setLIntegral_prod_slices
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → ENNReal) (hf : Measurable f) :
    ∫⁻ p in T, f p ∂μ.prod ν =
      ∫⁻ x, ∫⁻ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν ∂μ := by
  rw [← lintegral_indicator hT]
  rw [lintegral_prod _ (hf.indicator hT).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← lintegral_indicator (measurable_prodMk_left hT)]
  apply lintegral_congr
  intro y
  rfl

/-! ## Bochner integrals -/

/-- Fubini's theorem for an integral restricted to a measurable subset of a product. -/
lemma setIntegral_prod_slices
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → E) (hf : IntegrableOn f T (μ.prod ν)) :
    ∫ p in T, f p ∂μ.prod ν =
      ∫ x, ∫ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hT]
  rw [integral_prod _ (hf.integrable_indicator hT)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_indicator (measurable_prodMk_left hT)]
  apply integral_congr_ae
  filter_upwards [] with y
  rfl

end MeasureTheory

end
