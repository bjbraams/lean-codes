/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Analytic dependence of integrals on several complex parameters

This file is the proposed home for analytic versions of Mathlib's differentiation-under-the-
integral theorems.  The intended results combine the existing dominated Fréchet derivative API
with finite-dimensional complex analyticity from `SeveralComplexVariables.Basic`.

This is a temporary project home for material ultimately intended near
`Mathlib.Analysis.Calculus.ParametricIntegral`, rather than in a simplex- or Carlson-specific
namespace.

## Main result

`analyticOnNhd_integral_of_dominated_of_fderiv_le` packages the existing local dominated
Fréchet-derivative criterion at every point of an open finite-dimensional parameter domain.

Companion theorems should identify the Fréchet derivative with the integral of the pointwise
Fréchet derivative and, when useful, handle set integrals and finite measures over compact
domains.  The public theorem names should remain in the root namespace, consistently with the
existing parametric-integral API.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace SeveralComplexVariables

/-! Shared predicates describing local integrable domination may live here if spelling out the
same hypotheses in each public theorem proves unwieldy. -/

end SeveralComplexVariables

/-- The derivative of a holomorphic function is uniformly bounded on a sufficiently small
closed thickening of any compact subset of its open domain. -/
theorem AnalyticOnNhd.exists_cthickening_deriv_bound
    {Ω K : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hΩopen : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.cthickening δ K, ‖deriv f w‖ ≤ C := by
  obtain ⟨δ₁, hδ₁, hδ₁compact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hδ₂Ω⟩ := hK.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hcompact : IsCompact (Metric.cthickening δ K) :=
    hδ₁compact.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono (min_le_left _ _) K)
  have hsub : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hδ₂Ω
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hf.deriv.continuousOn.mono hsub).norm
  exact ⟨δ, lt_min hδ₁ hδ₂, hsub, max C 0, le_max_right _ _,
    fun w hw => (hC (Set.mem_image_of_mem _ hw)).trans (le_max_left _ _)⟩

variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An integral depending on finitely many complex parameters is analytic if, locally at every
parameter, its pointwise Fréchet derivatives have an integrable uniform bound.  The hypotheses
are grouped pointwise so that the dominating function and neighborhood may depend on the base
parameter. -/
theorem analyticOnNhd_integral_of_dominated_of_fderiv_le
    {μ : Measure α} {U : Set (ι → ℂ)} {F : (ι → ℂ) → α → E}
    (hU : IsOpen U)
    (hdom : ∀ x ∈ U, ∃ (s : Set (ι → ℂ)) (bound : α → ℝ)
        (F' : (ι → ℂ) → α → (ι → ℂ) →L[ℂ] E),
      s ∈ nhds x ∧
      (∀ᶠ y in nhds x, AEStronglyMeasurable (F y) μ) ∧
      Integrable (F x) μ ∧ AEStronglyMeasurable (F' x) μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, ‖F' y a‖ ≤ bound a) ∧ Integrable bound μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, HasFDerivAt (F · a) (F' y a) y)) :
    AnalyticOnNhd ℂ (fun x ↦ ∫ a, F x a ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd_pi _ hU
  intro x hx
  obtain ⟨s, bound, F', hs, hmeas, hint, hF'meas, hbound, hboundInt, hdiff⟩ := hdom x hx
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hmeas hint hF'meas
    hbound hboundInt hdiff).differentiableAt.differentiableWithinAt

end
