/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Deforming path integrals with singular endpoints

Let `ω` be holomorphic on a convex open set `U ⊆ ℂ`, and let `γ₁`, `γ₂` be paths on `[0, 1]`
whose interiors lie in `U`. Their endpoints need not lie in `U`, and `ω` may be singular there,
provided the two path integrals exist. If the two paths approach each endpoint so that the
segment joining `γ₁ ε` and `γ₂ ε` stays in `U` and its length times a bound for `ω` on it tends to
zero, then the two path integrals coincide.

The proof uses a primitive of `ω` on `U` (`Convex.exists_forall_hasDerivWithinAt`): on
`[ε, 1 - ε]` each integral is a difference of values of the primitive, and the mean value
inequality compares those values along the joining segments. No Cauchy theorem at the
endpoints is needed.

## Main results

* `intervalIntegral_mul_comp_eq_of_endpoint`: equality of the two path integrals.
-/

public section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace Complex

/-- The interior values of a path integral are differences of a primitive. -/
private theorem integral_Icc_eq_sub_of_primitive {U : Set ℂ} {P ω : ℂ → ℂ}
    (hP : ∀ z ∈ U, HasDerivAt P (ω z) z) {γ γ' : ℝ → ℂ}
    (hγ : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' v) v) (hγU : ∀ v ∈ Ioo (0 : ℝ) 1, γ v ∈ U)
    (hi : IntervalIntegrable (fun v ↦ ω (γ v) * γ' v) volume 0 1) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ v in a..b, ω (γ v) * γ' v = P (γ b) - P (γ a) := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    rw [uIcc_of_le hab]
    exact fun v hv ↦ ⟨ha.trans_le hv.1, hv.2.trans_lt hb⟩
  apply integral_eq_sub_of_hasDerivAt
  · intro v hv
    have h := ((hP _ (hγU v (hsub hv))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt v
      (hγ v (hsub hv))
    simpa [mul_comm, Function.comp_def] using h
  · exact hi.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ha.le hb.le)

/-- A primitive moves by at most the length of a segment times a bound for its derivative. -/
private theorem norm_sub_le_of_segment {U : Set ℂ} {P ω : ℂ → ℂ}
    (hP : ∀ z ∈ U, HasDerivAt P (ω z) z) {x y : ℂ} {M : ℝ} (hseg : segment ℝ x y ⊆ U)
    (hM : ∀ w ∈ segment ℝ x y, ‖ω w‖ ≤ M) :
    ‖P y - P x‖ ≤ M * ‖y - x‖ :=
  (convex_segment x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw ↦ (hP w (hseg hw)).hasDerivWithinAt) hM (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)

/-- **Endpoint deformation of path integrals.** Two paths through a convex open domain of
holomorphy of `ω`, with possibly singular common endpoints, give the same integral, provided
both integrals exist and the paths approach each endpoint compatibly: the segment between
`γ₁ ε` and `γ₂ ε` (respectively `γ₁ (1 - ε)` and `γ₂ (1 - ε)`) lies in `U`, `ω` is bounded on it
by `M ε` (respectively `M' ε`), and the bound times the segment length tends to zero. -/
theorem intervalIntegral_mul_comp_eq_of_endpoint {U : Set ℂ} (hUo : IsOpen U)
    (hUc : Convex ℝ U) {ω : ℂ → ℂ} (hω : DifferentiableOn ℂ ω U)
    {γ₁ γ₁' γ₂ γ₂' : ℝ → ℂ}
    (hγ₁ : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt γ₁ (γ₁' v) v)
    (hγ₂ : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt γ₂ (γ₂' v) v)
    (hU₁ : ∀ v ∈ Ioo (0 : ℝ) 1, γ₁ v ∈ U) (hU₂ : ∀ v ∈ Ioo (0 : ℝ) 1, γ₂ v ∈ U)
    (hi₁ : IntervalIntegrable (fun v ↦ ω (γ₁ v) * γ₁' v) volume 0 1)
    (hi₂ : IntervalIntegrable (fun v ↦ ω (γ₂ v) * γ₂' v) volume 0 1)
    {M M' : ℝ → ℝ}
    (h₀ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), segment ℝ (γ₁ ε) (γ₂ ε) ⊆ U ∧
      ∀ w ∈ segment ℝ (γ₁ ε) (γ₂ ε), ‖ω w‖ ≤ M ε)
    (h₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), segment ℝ (γ₁ (1 - ε)) (γ₂ (1 - ε)) ⊆ U ∧
      ∀ w ∈ segment ℝ (γ₁ (1 - ε)) (γ₂ (1 - ε)), ‖ω w‖ ≤ M' ε)
    (ht₀ : Tendsto (fun ε ↦ M ε * ‖γ₂ ε - γ₁ ε‖) (𝓝[>] 0) (𝓝 0))
    (ht₁ : Tendsto (fun ε ↦ M' ε * ‖γ₂ (1 - ε) - γ₁ (1 - ε)‖) (𝓝[>] 0) (𝓝 0)) :
    ∫ v in (0 : ℝ)..1, ω (γ₁ v) * γ₁' v = ∫ v in (0 : ℝ)..1, ω (γ₂ v) * γ₂' v := by
  obtain ⟨P, hP⟩ := hUc.exists_forall_hasDerivWithinAt (E := ℂ) hω
  have hP' : ∀ z ∈ U, HasDerivAt P (ω z) z := fun z hz ↦
    (hP z hz).hasDerivAt (hUo.mem_nhds hz)
  -- Integrals over `[ε, 1 - ε]` converge to the full integrals.
  have hlim {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
      Tendsto (fun ε ↦ ∫ v in ε..(1 - ε), f v) (𝓝[>] 0) (𝓝 (∫ v in (0 : ℝ)..1, f v)) := by
    have hc : ContinuousOn (fun t ↦ ∫ v in (0 : ℝ)..t, f v) (uIcc 0 1) :=
      continuousOn_primitive_interval' hf left_mem_uIcc
    have hmem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ uIcc (0 : ℝ) 1 ∧ 1 - ε ∈ uIcc (0 : ℝ) 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      rw [uIcc_of_le zero_le_one]
      exact ⟨⟨hε.1.le, hε.2.le⟩, ⟨by linarith [hε.2], by linarith [hε.1]⟩⟩
    have hA : Tendsto (fun ε ↦ ∫ v in (0 : ℝ)..ε, f v) (𝓝[>] 0)
        (𝓝 (∫ v in (0 : ℝ)..0, f v)) := by
      have h := (hc 0 left_mem_uIcc).tendsto
      refine (h.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
      · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      · filter_upwards [hmem] with ε hε using hε.1
    have hB : Tendsto (fun ε ↦ ∫ v in (0 : ℝ)..(1 - ε), f v) (𝓝[>] 0)
        (𝓝 (∫ v in (0 : ℝ)..1, f v)) := by
      have h := (hc 1 right_mem_uIcc).tendsto
      refine (h.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
      · have : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝 0) (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [hmem] with ε hε using hε.2
    have hsplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ v in ε..(1 - ε), f v =
        (∫ v in (0 : ℝ)..(1 - ε), f v) - ∫ v in (0 : ℝ)..ε, f v := by
      filter_upwards [hmem] with ε hε
      rw [integral_interval_sub_left (hf.mono_set (uIcc_subset_uIcc left_mem_uIcc hε.2))
        (hf.mono_set (uIcc_subset_uIcc left_mem_uIcc hε.1))]
    have := hB.sub hA
    simp only [integral_same, sub_zero] at this
    exact this.congr' (hsplit.mono fun ε h ↦ h.symm)
  -- The difference of the truncated integrals is a difference of primitive increments.
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 - ε ∧ 1 - ε < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact ⟨hε.1, by linarith [hε.2], by linarith [hε.1]⟩
  have hdiff : Tendsto (fun ε ↦ (∫ v in ε..(1 - ε), ω (γ₂ v) * γ₂' v) -
      ∫ v in ε..(1 - ε), ω (γ₁ v) * γ₁' v) (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ‖(∫ v in ε..(1 - ε), ω (γ₂ v) * γ₂' v) - ∫ v in ε..(1 - ε), ω (γ₁ v) * γ₁' v‖ ≤
          M' ε * ‖γ₂ (1 - ε) - γ₁ (1 - ε)‖ + M ε * ‖γ₂ ε - γ₁ ε‖ := by
      filter_upwards [hsmall, h₀, h₁] with ε hε hε₀ hε₁
      rw [integral_Icc_eq_sub_of_primitive hP' hγ₂ hU₂ hi₂ hε.1 hε.2.1 hε.2.2,
        integral_Icc_eq_sub_of_primitive hP' hγ₁ hU₁ hi₁ hε.1 hε.2.1 hε.2.2]
      have e1 := norm_sub_le_of_segment hP' hε₁.1 hε₁.2
      have e0 := norm_sub_le_of_segment hP' hε₀.1 hε₀.2
      calc _ = ‖(P (γ₂ (1 - ε)) - P (γ₁ (1 - ε))) - (P (γ₂ ε) - P (γ₁ ε))‖ := by
              congr 1; ring
        _ ≤ ‖P (γ₂ (1 - ε)) - P (γ₁ (1 - ε))‖ + ‖P (γ₂ ε) - P (γ₁ ε)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add e1 e0
    have hz := ht₁.add ht₀
    rw [add_zero] at hz
    exact squeeze_zero_norm' hbound hz
  have h2 := (hlim hi₂).sub (hlim hi₁)
  exact (sub_eq_zero.mp (tendsto_nhds_unique h2 hdiff)).symm

end Complex
