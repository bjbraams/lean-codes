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
subset of a product, together with the specialization to a region between two graphs of real
functions. It is a temporary home for results intended respectively for
`Mathlib.MeasureTheory.Measure.Prod` and `Mathlib.MeasureTheory.Integral.Prod`.
-/

open MeasureTheory Set
open scoped Classical

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

/-! ## Regions between graphs of real functions -/

variable {α : Type*} [MeasurableSpace α]

/-- Pairs `(x, t)` with `x ∈ s` and `t` in the closed interval from `lo x` to `hi x`. -/
lemma measurableSet_prod_Icc_slice {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi) :
    MeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)} := by
  refine (measurable_fst hs).inter ?_
  exact (measurableSet_le (hlo.comp measurable_fst) measurable_snd).inter
    (measurableSet_le measurable_snd (hhi.comp measurable_fst))

omit [MeasurableSpace α] in
lemma prod_Icc_slice_preimage (s : Set α) (lo hi : α → ℝ) (x : α) :
    Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)} =
      {t | x ∈ s ∧ t ∈ Icc (lo x) (hi x)} := by
  ext t
  simp [mem_Icc]

/-- Tonelli's theorem for the region between two graphs, in the closed-interval convention. -/
lemma setLIntegral_prod_Icc_slice {μ : Measure α} [SFinite μ]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p ∂μ.prod volume =
      ∫⁻ x in s, ∫⁻ t in Icc (lo x) (hi x), f (x, t) ∂volume ∂μ := by
  have hT := measurableSet_prod_Icc_slice hs hlo hhi
  rw [setLIntegral_prod_slices _ hT f hf, ← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  rw [prod_Icc_slice_preimage]
  by_cases hx : x ∈ s
  · simp [hx, Icc]
  · simp [hx]

/-- Fubini's theorem for the region between two graphs, in the closed-interval convention. -/
lemma setIntegral_prod_Icc_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → E)
    (hf : IntegrableOn f {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)} (μ.prod volume)) :
    ∫ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p ∂μ.prod volume =
      ∫ x in s, ∫ t in Icc (lo x) (hi x), f (x, t) ∂volume ∂μ := by
  have hT := measurableSet_prod_Icc_slice hs hlo hhi
  rw [setIntegral_prod_slices _ hT f hf, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [prod_Icc_slice_preimage]
  by_cases hx : x ∈ s
  · simp [hx, Icc]
  · simp [hx]

omit [MeasurableSpace α] in
/-- Volume form of `setIntegral_prod_Icc_slice`, matching the product `MeasureSpace`
instance on `α × ℝ`. -/
lemma setIntegral_prod_Icc_slice_volume
    {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → E)
    (hf : IntegrableOn f {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}) :
    ∫ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p =
      ∫ x in s, ∫ t in Icc (lo x) (hi x), f (x, t) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod_Icc_slice hs hlo hhi f hf

end MeasureTheory

end
