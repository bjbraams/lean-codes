/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Integral.CompactSupport

/-!
# Differentiation of weighted compact integrals

Joint continuity of a kernel and its Fréchet derivative supplies local domination on
compact integration sets. The scalar weight need only be integrable; in particular it
may be singular on the boundary. Parameters may lie in any real or complex normed space.

## Main results

* `hasFDerivAt_integral_smul_of_continuousOn_compact`: Fréchet differentiation under a compact
  integral with a fixed integrable scalar weight. Joint continuity of the kernel and derivative
  supplies all domination and measurability.
-/

public noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

variable {𝕜 α E P : Type*} [RCLike 𝕜]
  [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- Fréchet differentiation under a compact integral with a fixed integrable scalar weight.
Joint continuity of the kernel and derivative supplies all domination and measurability. -/
theorem hasFDerivAt_integral_smul_of_continuousOn_compact
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → 𝕜} (hg : IntegrableOn g K μ)
    {U : Set P} (hU : IsOpen U) {x : P} (hx : x ∈ U)
    {F : P → α → E} {F' : P → α → P →L[𝕜] E}
    (hF : ContinuousOn (fun p : P × α ↦ F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : P × α ↦ F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasFDerivAt (fun w ↦ F w a) (F' z a) z) :
    HasFDerivAt (fun z ↦ ∫ a in K, g a • F z a ∂μ)
      (∫ a in K, g a • F' x a ∂μ) x := by
  have hslice {z : P} (hz : z ∈ U) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  have hslice' {z : P} (hz : z ∈ U) : ContinuousOn (F' z) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hslice' hx).norm
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hbound : ∀ᶠ z in 𝓝 x, ∀ a : K, ‖F' z a‖ ≤ M + 1 := by
    suffices ∀ᶠ z in 𝓝 x, ∀ a ∈ (univ : Set K), ‖F' z a‖ ≤ M + 1 by
      simpa only [mem_univ, forall_true_left] using this
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro a _
    have hc : ContinuousAt (fun p : P × K ↦ F' p.1 p.2) (x, a) := by
      change Tendsto ((fun p : P × α ↦ F' p.1 p.2) ∘
        (fun p : P × K ↦ (p.1, (p.2 : α)))) (𝓝 (x, a)) _
      apply Filter.Tendsto.comp (hF' (x, a) ⟨hx, a.property⟩)
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).tendsto _, ?_⟩
      filter_upwards [continuous_fst.continuousAt.eventually (hU.mem_nhds hx)] with p hp
      exact ⟨hp, p.2.property⟩
    exact (hc.norm.eventually
      (gt_mem_nhds ((hM ⟨a, a.property, rfl⟩).trans_lt (lt_add_one M)))).mono
      (fun _ hz ↦ hz.le)
  let V := {z | (∀ a : K, ‖F' z a‖ ≤ M + 1) ∧ z ∈ U}
  have hV : V ∈ 𝓝 x := inter_mem hbound (hU.mem_nhds hx)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (F := fun z a ↦ g a • F z a)
    (F' := fun z a ↦ g a • F' z a) (bound := fun a ↦ ‖g a‖ * (M + 1))
    hV ?_ (hg.smul_continuousOn_of_isCompact (hslice hx) hK)
    (hg.smul_continuousOn_of_isCompact (hslice' hx) hK).aestronglyMeasurable ?_
    (hg.norm.mul_const (M + 1)) ?_
  · filter_upwards [hU.eventually_mem hx] with z hz
    exact (hg.smul_continuousOn_of_isCompact (hslice hz) hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hz.1 ⟨a, ha⟩) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact (hd z hz.2 a ha).const_smul (g a)

end
