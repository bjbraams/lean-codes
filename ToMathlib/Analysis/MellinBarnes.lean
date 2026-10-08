/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import ToMathlib.Analysis.Integral.Tail
public import Mathlib.Basic.Real.Sign

/-!
# Mellin–Barnes integrals

Tools for moving vertical lines of integration, as in Mellin–Barnes integrals. Functions take
values in a complex normed space `E`; completeness is needed only where a residue term appears.

* `Complex.integral_vertical_eq_of_tendstoUniformlyOn`: Cauchy's theorem on a vertical strip. A
  function holomorphic on the open strip `a < Re s < b` and continuous on its closure, integrable
  on the two boundary lines, and tending to zero as `|t| → ∞` uniformly in the strip, has the same
  integral along both boundary lines.
* `Complex.integral_vertical_eq_of_tail_bound`, `Complex.integral_vertical_eq_of_bound`: the case
  of a function holomorphic on the closed strip and `O((1 + |t|)^(-2))` there.
* `Complex.integral_vertical_sub_eq_of_simplePole`: crossing a simple pole with residue `r`
  changes the line integral `∫ f (σ + t I) dt` by `2π r`, under the same hypotheses away from the
  pole. The proof subtracts the comparison function `((s - s₀)⁻¹ + (L - (s - s₀))⁻¹) • r`, which
  has the same pole and is integrable on vertical lines. Its line integrals
  `π (sign α + sign (L - α)) r` come from `∫_{-T}^{T} dτ / (α + τ I) = 2 arctan (T / α)`
  (`Complex.integral_inv_add_mul_I`, `Complex.integral_inv_add_inv_sub`).
  `Complex.integral_vertical_sub_eq_of_simplePole_of_tail_bound` is the version with a bound
  `O((1 + |t|)^(-2))`.
* `mellin_mellinInv_eq`: the Mellin transform of an inverse Mellin transform. It is the
  counterpart of Mathlib's `mellinInv_mellin_eq` and follows from Fourier inversion in the
  other order.

The private change-of-variables lemmas are adapted from `Mathlib.Analysis.MellinInversion`, where
they are private.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Topology Real FourierTransform

namespace Complex

section LineShift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Shifting a vertical line of integration.** Let `f` be holomorphic on the open strip
`a < Re s < b` and continuous on its closure, integrable on the two boundary lines, and let
`f (σ + t I) → 0` as `|t| → ∞`, uniformly for `σ ∈ [a, b]`. Then
`∫ f (a + t I) dt = ∫ f (b + t I) dt`. The target need not be complete. -/
theorem integral_vertical_eq_of_tendstoUniformlyOn {f : ℂ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (ha : Integrable fun t : ℝ ↦ f (a + t * I)) (hb : Integrable fun t : ℝ ↦ f (b + t * I))
    (hdecay : TendstoUniformlyOn (fun t σ : ℝ ↦ f (σ + t * I)) 0 (cocompact ℝ) (Icc a b)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  rcases hab.eq_or_lt with rfl | hab'
  · rfl
  have hc : ContinuousOn f (re ⁻¹' Icc a b) := by
    simpa only [closure_preimage_re, closure_Ioo hab'.ne] using hf.continuousOn
  -- The horizontal sides tend to zero.
  have hH : Tendsto (fun y : ℝ ↦ ∫ x in a..b, f (x + y * I)) (cocompact ℝ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hba : 0 < b - a := sub_pos.mpr hab'
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hdecay _ (div_pos hε (mul_pos two_pos hba))]
      with y hy
    rw [dist_zero_right]
    calc ‖∫ x in a..b, f (x + y * I)‖ ≤ ε / (2 * (b - a)) * |b - a| := by
          refine norm_integral_le_of_norm_le_const fun x hx ↦ ?_
          rw [uIoc_of_le hab] at hx
          simpa only [Pi.zero_apply, dist_zero_left] using (hy x ⟨hx.1.le, hx.2⟩).le
      _ = ε / 2 := by rw [abs_of_pos hba]; field_simp
      _ < ε := half_lt_self hε
  -- Cauchy's theorem on the rectangle `[a, b] × [-R, R]`.
  have hrect : ∀ R : ℝ, (∫ x in a..b, f (x + ((-R : ℝ) : ℂ) * I)) -
      (∫ x in a..b, f (x + (R : ℂ) * I)) +
      I • (∫ y in -R..R, f (b + y * I)) - I • (∫ y in -R..R, f (a + y * I)) = 0 := by
    intro R
    refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
      ⟨a, -R⟩ ⟨b, R⟩ (hc.mono fun s hs ↦ ?_) (hf.differentiableOn.mono fun s hs ↦ ?_)
    · rw [mem_reProdIm, uIcc_of_le hab] at hs
      exact hs.1
    · rw [mem_reProdIm, min_eq_left hab, max_eq_right hab] at hs
      exact hs.1
  have hTa : Tendsto (fun R : ℝ ↦ ∫ y in -R..R, f (a + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (a + t * I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hTb : Tendsto (fun R : ℝ ↦ ∫ y in -R..R, f (b + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (b + t * I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hTot := (((hH.comp (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)).sub
    (hH.comp (tendsto_id.mono_right atTop_le_cocompact))).add (hTb.const_smul I)).sub
      (hTa.const_smul I)
  have := tendsto_nhds_unique hTot (tendsto_const_nhds.congr fun R ↦ (hrect R).symm)
  simp only [sub_self, zero_add] at this
  rw [← smul_sub, smul_eq_zero] at this
  exact (sub_eq_zero.mp (this.resolve_left I_ne_zero)).symm

omit [NormedSpace ℂ E] in
/-- A bound `C (1 + |t|)^(-2)` on the strip `a ≤ Re s ≤ b` for large `|t|` gives uniform decay
as `|t| → ∞`. -/
theorem tendstoUniformlyOn_of_tail_bound {f : ℂ → E} {a b C T₀ : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    TendstoUniformlyOn (fun t σ : ℝ ↦ f (σ + t * I)) 0 (cocompact ℝ) (Icc a b) := by
  have hcoc : Tendsto (fun t : ℝ ↦ |t|) (cocompact ℝ) atTop :=
    tendsto_norm_cocompact_atTop.congr fun t ↦ Real.norm_eq_abs t
  have hg : Tendsto (fun t : ℝ ↦ C * (1 + |t|) ^ (-2 : ℝ)) (cocompact ℝ) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_atTop_add_const_left _ 1 hcoc)).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually (gt_mem_nhds hε), hcoc.eventually (eventually_ge_atTop T₀)]
    with t ht hT σ hσ
  rw [Pi.zero_apply, dist_zero_left]
  exact (hC σ t hσ.1 hσ.2 hT).trans_lt ht

omit [NormedSpace ℂ E] in
/-- A bound `C (1 + |t|)^(-2)` for large `|t|` extends, with another constant, to the whole closed
strip `a ≤ Re s ≤ b` for a function continuous there. -/
theorem exists_bound_of_tail_bound {f : ℂ → E} {a b C T₀ : ℝ}
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ContinuousAt f s)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    ∃ C', ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ C' * (1 + |t|) ^ (-2 : ℝ) := by
  set T₁ := max T₀ 0
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ Icc a b ×ˢ Icc (-T₁) T₁, ‖f (p.1 + p.2 * I)‖ ≤ M := by
    refine (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn fun p hp ↦ ?_
    have hp1 := (mem_prod.mp hp).1
    exact ((hf _ (by simpa using hp1.1) (by simpa using hp1.2)).comp
      (by fun_prop : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) p)).continuousWithinAt
  refine ⟨max (max M 0 * (1 + T₁) ^ 2) C, fun σ t h1 h2 ↦ ?_⟩
  have hpos : 0 < (1 + |t|) ^ (-2 : ℝ) := by positivity
  rcases le_or_gt T₁ |t| with ht | ht
  · exact (hC σ t h1 h2 ((le_max_left _ _).trans ht)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)
  · have hb := hM (σ, t) ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩
    have hle : (1 + |t|) ^ 2 ≤ (1 + T₁) ^ 2 := by gcongr
    calc ‖f (σ + t * I)‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ = max M 0 * (1 + T₁) ^ 2 * ((1 + T₁) ^ 2)⁻¹ := by
          have : (1 + T₁) ^ 2 ≠ (0 : ℝ) := by positivity
          rw [mul_assoc, mul_inv_cancel₀ this, mul_one]
      _ ≤ max M 0 * (1 + T₁) ^ 2 * ((1 + |t|) ^ 2)⁻¹ := by gcongr
      _ = max M 0 * (1 + T₁) ^ 2 * (1 + |t|) ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le

/-- **Shifting a vertical line of integration** for a function holomorphic at every point of the
closed strip `a ≤ Re s ≤ b` with a bound `C (1 + |t|)^(-2)` there for large `|t|`. -/
theorem integral_vertical_eq_of_tail_bound {f : ℂ → E} {a b C T₀ : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  obtain ⟨C', hC'⟩ := exists_bound_of_tail_bound (fun s h1 h2 ↦ (hf s h1 h2).continuousAt) hC
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable fun t : ℝ ↦ f (σ + t * I) := fun σ h1 h2 ↦
    (integrable_one_add_abs_rpow_neg_two.const_mul C').mono'
      (continuous_iff_continuousAt.mpr fun t ↦ (hf _ (by simpa using h1)
        (by simpa using h2)).continuousAt.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ hC' σ t h1 h2)
  refine integral_vertical_eq_of_tendstoUniformlyOn hab ?_ (hint a le_rfl hab) (hint b hab le_rfl)
    (tendstoUniformlyOn_of_tail_bound hC)
  refine DifferentiableOn.diffContOnCl fun s hs ↦ ?_
  rw [closure_preimage_re] at hs
  have hs' := closure_minimal Ioo_subset_Icc_self isClosed_Icc hs
  exact (hf s hs'.1 hs'.2).differentiableWithinAt

/-- **Shifting a vertical line of integration.** If `f` is holomorphic at every point of the
closed strip `a ≤ Re s ≤ b` and `‖f (σ + t I)‖ ≤ C (1 + |t|)^(-2)` there, then
`∫ f (a + t I) dt = ∫ f (b + t I) dt`. -/
theorem integral_vertical_eq_of_bound {f : ℂ → E} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) :=
  integral_vertical_eq_of_tail_bound (T₀ := 0) hab hf fun σ t h1 h2 _ ↦ hC σ t h1 h2

end LineShift

/-- `∫_{-T}^{T} dτ / (α + τ I) = 2 arctan (T / α)` for real `α ≠ 0`. -/
theorem integral_inv_add_mul_I {α : ℝ} (hα : α ≠ 0) (T : ℝ) :
    ∫ τ in -T..T, 1 / ((α : ℂ) + τ * I) = 2 * Real.arctan (T / α) := by
  set G : ℝ → ℂ := fun τ ↦
    (Real.arctan (τ / α) : ℂ) - I * ((Real.log (α ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ)
  have hpos : ∀ τ : ℝ, 0 < α ^ 2 + τ ^ 2 := fun τ ↦ by positivity
  have hne : ∀ τ : ℝ, (α : ℂ) + τ * I ≠ 0 := fun τ h ↦ by
    have := congrArg re h
    simp at this
    exact hα this
  have hderiv : ∀ τ : ℝ, HasDerivAt G (1 / ((α : ℂ) + τ * I)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ ↦ Real.arctan (τ / α)) (1 / (1 + (τ / α) ^ 2) * (1 / α)) τ :=
      ((hasDerivAt_id' τ).div_const α).arctan
    have h2 : HasDerivAt (fun τ : ℝ ↦ Real.log (α ^ 2 + τ ^ 2) / 2)
        ((2 * τ) / (α ^ 2 + τ ^ 2) / 2) τ := by
      have := ((hasDerivAt_pow 2 τ).const_add (α ^ 2)).log (hpos τ).ne'
      refine (this.div_const 2).congr_deriv ?_
      simp
    have h3 := (h1.ofReal_comp).sub (h2.ofReal_comp.const_mul I)
    refine h3.congr_deriv ?_
    have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα
    have hsq : ((α ^ 2 + τ ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos τ).ne'
    have hfac : ((α ^ 2 + τ ^ 2 : ℝ) : ℂ) = ((α : ℂ) + τ * I) * ((α : ℂ) - τ * I) := by
      push_cast; ring_nf; rw [I_sq]; ring
    push_cast at hsq hfac ⊢
    field_simp
    rw [hfac]
    field_simp [hne τ]
  have hcont : Continuous fun τ : ℝ ↦ 1 / ((α : ℂ) + τ * I) :=
    continuous_iff_continuousAt.mpr fun τ ↦
      (continuousAt_const.div (by fun_prop) (hne τ))
  rw [integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hderiv τ) (hcont.intervalIntegrable _ _)]
  simp only [G, neg_div, Real.arctan_neg, neg_sq]
  push_cast
  ring

/-- `arctan (T / α) → (π / 2) sign α` as `T → ∞`. -/
theorem _root_.Real.tendsto_arctan_div {α : ℝ} (hα : α ≠ 0) :
    Tendsto (fun T : ℝ ↦ Real.arctan (T / α)) atTop (𝓝 (π / 2 * Real.sign α)) := by
  rcases hα.lt_or_gt with h | h
  · rw [Real.sign_of_neg h, mul_neg_one]
    exact (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const_of_neg h)
  · rw [Real.sign_of_pos h, mul_one]
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const h)

/-- A lower bound for `‖α + τ I‖`, linear in `1 + |τ|`. -/
theorem norm_ofReal_add_mul_I_ge (α τ : ℝ) :
    min |α| 1 / 2 * (1 + |τ|) ≤ ‖(α : ℂ) + τ * I‖ := by
  have h1 : |α| ≤ ‖(α : ℂ) + τ * I‖ := by
    simpa using abs_re_le_norm ((α : ℂ) + τ * I)
  have h2 : |τ| ≤ ‖(α : ℂ) + τ * I‖ := by
    simpa using abs_im_le_norm ((α : ℂ) + τ * I)
  have hm1 : min |α| 1 ≤ |α| := min_le_left _ _
  have hm2 : min |α| 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min |α| 1 := le_min (abs_nonneg _) zero_le_one
  rcases le_total |τ| 1 with h | h
  · nlinarith
  · nlinarith

/-- **The comparison integral.** For real `α, β ≠ 0`,
`t ↦ 1 / (α + (t - y₀) I) + 1 / (β - (t - y₀) I)` is integrable with integral
`π (sign α + sign β)`. -/
theorem integral_inv_add_inv_sub {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (y₀ : ℝ) :
    Integrable (fun t : ℝ ↦ 1 / ((α : ℂ) + (t - y₀) * I) + 1 / ((β : ℂ) - (t - y₀) * I)) ∧
      ∫ t : ℝ, (1 / ((α : ℂ) + (t - y₀) * I) + 1 / ((β : ℂ) - (t - y₀) * I)) =
        π * (Real.sign α + Real.sign β) := by
  set h : ℝ → ℂ := fun τ ↦ 1 / ((α : ℂ) + τ * I) + 1 / ((β : ℂ) - τ * I)
  have hne : ∀ (γ τ : ℝ), γ ≠ 0 → (γ : ℂ) + τ * I ≠ 0 := fun γ τ hγ h ↦ by
    have := congrArg re h; simp at this; exact hγ this
  have hneg : ∀ τ : ℝ, (β : ℂ) - τ * I = (β : ℂ) + ((-τ : ℝ) : ℂ) * I := fun τ ↦ by
    push_cast; ring
  have hcont : Continuous h :=
    (continuous_const.div (by fun_prop) fun τ ↦ hne α τ hα).add
      (continuous_const.div (by fun_prop) fun τ ↦ by rw [hneg]; exact hne β (-τ) hβ)
  -- Integrability from `h = (α + β) / ((α + τ I) (β - τ I))`.
  set mα := min |α| 1 / 2
  set mβ := min |β| 1 / 2
  have hmα : 0 < mα := by simp only [mα]; positivity
  have hmβ : 0 < mβ := by simp only [mβ]; positivity
  have hbound : ∀ τ : ℝ, ‖h τ‖ ≤ (|α + β| / (mα * mβ)) * (1 + |τ|) ^ (-2 : ℝ) := by
    intro τ
    have hβτ : ‖(β : ℂ) - τ * I‖ = ‖(β : ℂ) + ((-τ : ℝ) : ℂ) * I‖ := by rw [hneg]
    have e1 := norm_ofReal_add_mul_I_ge α τ
    have e2 := norm_ofReal_add_mul_I_ge β (-τ)
    rw [abs_neg, ← hβτ] at e2
    have hprod : h τ = ((α + β : ℝ) : ℂ) / (((α : ℂ) + τ * I) * ((β : ℂ) - τ * I)) := by
      simp only [h]
      rw [div_add_div _ _ (hne α τ hα) (by rw [hneg]; exact hne β (-τ) hβ)]
      push_cast; ring
    have this : mα * (1 + |τ|) * (mβ * (1 + |τ|)) ≤ ‖(α : ℂ) + τ * I‖ * ‖(β : ℂ) - τ * I‖ :=
      mul_le_mul e1 e2 (by positivity) (norm_nonneg _)
    rw [hprod, norm_div, norm_mul, norm_real, Real.norm_eq_abs,
      Real.rpow_neg (by positivity), Real.rpow_two]
    calc |α + β| / (‖(α : ℂ) + τ * I‖ * ‖(β : ℂ) - τ * I‖)
        ≤ |α + β| / (mα * (1 + |τ|) * (mβ * (1 + |τ|))) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) this
      _ = _ := by field_simp
  have hint : Integrable h :=
    (integrable_one_add_abs_rpow_neg_two.const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hshift : (fun t : ℝ ↦ 1 / ((α : ℂ) + (t - y₀) * I) + 1 / ((β : ℂ) - (t - y₀) * I)) =
      fun t ↦ h (t - y₀) := by
    funext t; simp only [h]; push_cast; ring_nf
  rw [hshift]
  refine ⟨hint.comp_sub_right y₀, ?_⟩
  rw [integral_sub_right_eq_self (fun τ ↦ h τ) y₀]
  -- The symmetric truncations.
  have htrunc : ∀ T : ℝ, ∫ τ in -T..T, h τ = 2 * Real.arctan (T / α) + 2 * Real.arctan (T / β) := by
    intro T
    have hi1 : IntervalIntegrable (fun τ : ℝ ↦ 1 / ((α : ℂ) + τ * I)) volume (-T) T :=
      (continuous_iff_continuousAt.mpr fun τ ↦
        continuousAt_const.div (by fun_prop) (hne α τ hα)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun τ : ℝ ↦ 1 / ((β : ℂ) - τ * I)) volume (-T) T := by
      refine (continuous_iff_continuousAt.mpr fun τ ↦ continuousAt_const.div
        (by fun_prop : ContinuousAt (fun τ : ℝ ↦ (β : ℂ) - τ * I) τ) ?_).intervalIntegrable _ _
      rw [hneg]; exact hne β (-τ) hβ
    simp only [h]
    rw [intervalIntegral.integral_add hi1 hi2, integral_inv_add_mul_I hα]
    have hsub : ∫ τ in -T..T, 1 / ((β : ℂ) - τ * I) = ∫ τ in -T..T, 1 / ((β : ℂ) + τ * I) := by
      have := intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun τ : ℝ ↦ 1 / ((β : ℂ) + τ * I))
      simp only [neg_neg] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun τ _ ↦ ?_
      push_cast; ring_nf
    rw [hsub, integral_inv_add_mul_I hβ]
  have hlim : Tendsto (fun T : ℝ ↦ ∫ τ in -T..T, h τ) atTop (𝓝 (∫ τ, h τ)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  rw [show (fun T : ℝ ↦ ∫ τ in -T..T, h τ) = fun T : ℝ ↦
    ((2 * Real.arctan (T / α) + 2 * Real.arctan (T / β) : ℝ) : ℂ) from
    funext fun T ↦ by rw [htrunc]; push_cast; ring] at hlim
  have hlim2 : Tendsto (fun T : ℝ ↦
      ((2 * Real.arctan (T / α) + 2 * Real.arctan (T / β) : ℝ) : ℂ))
      atTop (𝓝 ((2 * (π / 2 * Real.sign α) + 2 * (π / 2 * Real.sign β) : ℝ) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp
      (((Real.tendsto_arctan_div hα).const_mul 2).add ((Real.tendsto_arctan_div hβ).const_mul 2))
  rw [tendsto_nhds_unique hlim hlim2]
  push_cast; ring

section SimplePole

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Crossing a simple pole.** Let `f` be continuous on the closed strip `a ≤ Re s ≤ b` and
holomorphic on the open strip, except for a simple pole at `s₀` (`a < Re s₀ < b`) with residue
`r`: `f s = (s - s₀)⁻¹ • r + k s` near `s₀` with `k` holomorphic at `s₀`. If `f` is integrable on
the two boundary lines and `f (σ + t I) → 0` as `|t| → ∞` uniformly for `σ ∈ [a, b]`, then
`∫ f (b + t I) dt - ∫ f (a + t I) dt = 2π r`.

The proof subtracts the comparison function `((s - s₀)⁻¹ + (L - (s - s₀))⁻¹) • r`, which has the
same pole and is integrable on vertical lines, and shifts the line for the difference. -/
theorem integral_vertical_sub_eq_of_simplePole {f k : ℂ → E} {a b : ℝ} {s₀ : ℂ} {r : E}
    (ha : a < s₀.re) (hb : s₀.re < b)
    (hfc : ContinuousOn f (re ⁻¹' Icc a b \ {s₀}))
    (hfd : DifferentiableOn ℂ f (re ⁻¹' Ioo a b \ {s₀}))
    (hk : DifferentiableAt ℂ k s₀) (hpole : ∀ᶠ s in 𝓝[≠] s₀, f s = (s - s₀)⁻¹ • r + k s)
    (hia : Integrable fun t : ℝ ↦ f (a + t * I)) (hib : Integrable fun t : ℝ ↦ f (b + t * I))
    (hdecay : TendstoUniformlyOn (fun t σ : ℝ ↦ f (σ + t * I)) 0 (cocompact ℝ) (Icc a b)) :
    (∫ t : ℝ, f (b + t * I)) - ∫ t : ℝ, f (a + t * I) = (2 * π : ℂ) • r := by
  have hab : a < b := ha.trans hb
  set L : ℝ := b - a + 1
  have hL : 0 < L := by simp only [L]; linarith
  set φ : ℂ → ℂ := fun s ↦ (s - s₀)⁻¹ + ((L : ℂ) - (s - s₀))⁻¹
  set G : ℂ → E := fun s ↦ if s = s₀ then k s₀ - (L : ℂ)⁻¹ • r else f s - φ s • r
  have hGe : ∀ s, s ≠ s₀ → G s = f s - φ s • r := fun s hs ↦ by simp [G, hs]
  have hLne : ∀ s : ℂ, s.re ≤ b → (L : ℂ) - (s - s₀) ≠ 0 := by
    intro s hs h
    have := congrArg re h
    simp only [sub_re, ofReal_re, zero_re] at this
    simp only [L] at this
    linarith
  have hφd : ∀ s : ℂ, s ≠ s₀ → s.re ≤ b → DifferentiableAt ℂ φ s := fun s hs hs2 ↦
    ((differentiableAt_id.sub_const s₀).inv (sub_ne_zero.mpr hs)).add
      (((differentiableAt_const _).sub (differentiableAt_id.sub_const s₀)).inv (hLne s hs2))
  -- Regularity of `G`: the singularity at `s₀` is removable.
  have hGd : ∀ s : ℂ, a < s.re → s.re < b → DifferentiableAt ℂ G s := by
    intro s hs1 hs2
    by_cases hss : s = s₀
    · rw [hss]
      have hev : G =ᶠ[𝓝 s₀] fun z ↦ k z - ((L : ℂ) - (z - s₀))⁻¹ • r := by
        filter_upwards [eventually_nhdsWithin_iff.mp hpole] with z hz
        by_cases hzs : z = s₀
        · subst hzs; simp [G]
        · rw [hGe z hzs, hz hzs]
          simp only [φ, add_smul]
          abel
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact hk.sub ((((differentiableAt_const _).sub (differentiableAt_id.sub_const s₀)).inv
        (hLne s₀ hb.le)).smul_const r)
    · have hev : G =ᶠ[𝓝 s] fun z ↦ f z - φ z • r := by
        filter_upwards [isOpen_ne.mem_nhds hss] with z hz using hGe z hz
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      have hmem : re ⁻¹' Ioo a b \ {s₀} ∈ 𝓝 s :=
        ((isOpen_Ioo.preimage continuous_re).sdiff isClosed_singleton).mem_nhds ⟨⟨hs1, hs2⟩, hss⟩
      exact (hfd.differentiableAt hmem).sub ((hφd s hss hs2.le).smul_const r)
  have hGc : ContinuousOn G (re ⁻¹' Icc a b) := by
    intro s hs
    by_cases hss : s = s₀
    · rw [hss]
      exact (hGd s₀ ha hb).continuousAt.continuousWithinAt
    · have hfs : ContinuousWithinAt f (re ⁻¹' Icc a b) s :=
        (continuousWithinAt_sdiff_singleton (y := s₀)).mp (hfc s ⟨hs, hss⟩)
      refine (hfs.sub ((hφd s hss hs.2).continuousAt.continuousWithinAt.smul
        continuousWithinAt_const)).congr_of_eventuallyEq ?_ (hGe s hss)
      filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hss)] with z hz using hGe z hz
  have hGdc : DiffContOnCl ℂ G (re ⁻¹' Ioo a b) :=
    ⟨fun s hs ↦ (hGd s hs.1 hs.2).differentiableWithinAt, by
      rw [closure_preimage_re, closure_Ioo hab.ne]; exact hGc⟩
  -- The comparison function on vertical lines avoiding `s₀`.
  have hline : ∀ σ : ℝ, σ ≤ b → σ ≠ s₀.re → Integrable (fun t : ℝ ↦ φ (σ + t * I)) ∧
      ∫ t : ℝ, φ (σ + t * I) =
        π * (Real.sign (σ - s₀.re) + Real.sign (L - (σ - s₀.re))) := by
    intro σ h2 hσ
    have hα : σ - s₀.re ≠ 0 := sub_ne_zero.mpr hσ
    have hβ : L - (σ - s₀.re) ≠ 0 := by simp only [L]; linarith
    obtain ⟨hqi, hqv⟩ := integral_inv_add_inv_sub hα hβ s₀.im
    have hqe : ∀ t : ℝ, φ (σ + t * I) = 1 / (((σ - s₀.re : ℝ) : ℂ) + (t - s₀.im) * I) +
        1 / (((L - (σ - s₀.re) : ℝ) : ℂ) - (t - s₀.im) * I) := by
      intro t
      have hs₀ : s₀ = (s₀.re : ℂ) + s₀.im * I := (re_add_im s₀).symm
      have e1 : (σ : ℂ) + t * I - s₀ = ((σ - s₀.re : ℝ) : ℂ) + (t - s₀.im) * I := by
        rw [hs₀]; push_cast; ring_nf; simp
      have e2 : (L : ℂ) - ((σ : ℂ) + t * I - s₀) =
          ((L - (σ - s₀.re) : ℝ) : ℂ) - (t - s₀.im) * I := by
        rw [e1]; push_cast; ring
      simp only [φ]
      rw [e2, e1, one_div, one_div]
    exact ⟨by simp_rw [hqe]; exact hqi, by simp_rw [hqe]; exact hqv⟩
  have hfline : ∀ σ : ℝ, σ ≤ b → σ ≠ s₀.re → (Integrable fun t : ℝ ↦ f (σ + t * I)) →
      (Integrable fun t : ℝ ↦ G (σ + t * I)) ∧ ∫ t : ℝ, f (σ + t * I) =
        (∫ t : ℝ, G (σ + t * I)) +
          (π * (Real.sign (σ - s₀.re) + Real.sign (L - (σ - s₀.re))) : ℂ) • r := by
    intro σ h2 hσ hfi
    have hne : ∀ t : ℝ, (σ : ℂ) + t * I ≠ s₀ := fun t h ↦ hσ (by rw [← h]; simp)
    have hGe' : (fun t : ℝ ↦ G (σ + t * I)) = fun t : ℝ ↦ f (σ + t * I) - φ (σ + t * I) • r :=
      funext fun t ↦ hGe _ (hne t)
    obtain ⟨hφi, hφv⟩ := hline σ h2 hσ
    have hφr : Integrable fun t : ℝ ↦ φ (σ + t * I) • r := hφi.smul_const r
    refine ⟨by rw [hGe']; exact hfi.sub hφr, ?_⟩
    rw [hGe', integral_sub hfi hφr, _root_.integral_smul_const, hφv]
    abel
  -- Uniform decay of `G`.
  have hGdecay : TendstoUniformlyOn (fun t σ : ℝ ↦ G (σ + t * I)) 0 (cocompact ℝ) (Icc a b) := by
    have hcoc : Tendsto (fun t : ℝ ↦ |t|) (cocompact ℝ) atTop :=
      tendsto_norm_cocompact_atTop.congr fun t ↦ Real.norm_eq_abs t
    have h1 : Tendsto (fun t : ℝ ↦ 4 * ‖r‖ / (1 + |t|)) (cocompact ℝ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 hcoc)
    rw [Metric.tendstoUniformlyOn_iff] at hdecay ⊢
    intro ε hε
    filter_upwards [hdecay (ε / 2) (half_pos hε), h1.eventually (gt_mem_nhds (half_pos hε)),
      hcoc.eventually (eventually_ge_atTop (2 * |s₀.im| + 2))] with t hft hq ht σ hσ
    have hf' := hft σ hσ
    simp only [Pi.zero_apply, dist_zero_left] at hf' ⊢
    have hne : (σ : ℂ) + t * I ≠ s₀ := by
      intro h
      have := congrArg im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        zero_add] at this
      simp only [add_zero] at this
      rw [this] at ht
      linarith [abs_nonneg s₀.im]
    rw [hGe _ hne]
    have hφb : ‖φ (σ + t * I)‖ ≤ 4 / (1 + |t|) := by
      set u : ℂ := (σ : ℂ) + t * I - s₀
      have hlow : ∀ v : ℂ, |t - s₀.im| ≤ ‖v‖ → (1 + |t|) / 2 ≤ ‖v‖ := fun v hv ↦ by
        have h3 : |t| - |s₀.im| ≤ |t - s₀.im| := abs_sub_abs_le_abs_sub _ _
        linarith
      have hu : (1 + |t|) / 2 ≤ ‖u‖ := hlow u (by simpa [u] using abs_im_le_norm u)
      have hLu : (1 + |t|) / 2 ≤ ‖(L : ℂ) - u‖ :=
        hlow _ (by simpa [u, abs_sub_comm] using abs_im_le_norm ((L : ℂ) - u))
      have hpos : 0 < (1 + |t|) / 2 := by positivity
      calc ‖φ (σ + t * I)‖ ≤ ‖u‖⁻¹ + ‖(L : ℂ) - u‖⁻¹ := by
            simpa only [φ, norm_inv] using norm_add_le u⁻¹ ((L : ℂ) - u)⁻¹
        _ ≤ ((1 + |t|) / 2)⁻¹ + ((1 + |t|) / 2)⁻¹ := by gcongr
        _ = 4 / (1 + |t|) := by field_simp; ring
    calc ‖f (σ + t * I) - φ (σ + t * I) • r‖ ≤ ‖f (σ + t * I)‖ + ‖φ (σ + t * I)‖ * ‖r‖ := by
          simpa only [norm_smul] using norm_sub_le (f (σ + t * I)) (φ (σ + t * I) • r)
      _ ≤ ‖f (σ + t * I)‖ + 4 / (1 + |t|) * ‖r‖ := by gcongr
      _ < ε / 2 + ε / 2 := by
          rw [show 4 / (1 + |t|) * ‖r‖ = 4 * ‖r‖ / (1 + |t|) by ring]
          exact add_lt_add hf' hq
      _ = ε := add_halves ε
  obtain ⟨hGa, hva⟩ := hfline a hab.le ha.ne hia
  obtain ⟨hGb, hvb⟩ := hfline b le_rfl hb.ne' hib
  have hshift := integral_vertical_eq_of_tendstoUniformlyOn hab.le hGdc hGa hGb hGdecay
  rw [Real.sign_of_neg (by linarith : a - s₀.re < 0),
    Real.sign_of_pos (by simp only [L]; linarith : 0 < L - (a - s₀.re))] at hva
  rw [Real.sign_of_pos (by linarith : 0 < b - s₀.re),
    Real.sign_of_pos (by simp only [L]; linarith : 0 < L - (b - s₀.re))] at hvb
  rw [hva, hvb, hshift, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

/-- **Crossing a simple pole**, for a function holomorphic at every point of the closed strip
`a ≤ Re s ≤ b` except `s₀`, with a bound `C (1 + |t|)^(-2)` for large `|t|`. The integrability
on the boundary lines is part of the conclusion. -/
theorem integral_vertical_sub_eq_of_simplePole_of_tail_bound {f k : ℂ → E} {a b : ℝ} {s₀ : ℂ}
    {r : E} (ha : a < s₀.re) (hb : s₀.re < b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ s₀ → DifferentiableAt ℂ f s)
    (hk : DifferentiableAt ℂ k s₀) (hpole : ∀ᶠ s in 𝓝[≠] s₀, f s = (s - s₀)⁻¹ • r + k s)
    {C T₀ : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    Integrable (fun t : ℝ ↦ f (a + t * I)) ∧ Integrable (fun t : ℝ ↦ f (b + t * I)) ∧
      (∫ t : ℝ, f (b + t * I)) - ∫ t : ℝ, f (a + t * I) = (2 * π : ℂ) • r := by
  have hline : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ≠ s₀.re → Integrable fun t : ℝ ↦ f (σ + t * I) := by
    intro σ h1 h2 hσ
    have hfσ : ∀ s : ℂ, s.re = σ → DifferentiableAt ℂ f s := fun s hs ↦
      hf s (hs ▸ h1) (hs ▸ h2) fun h ↦ hσ (by rw [← hs, h])
    obtain ⟨C', hC'⟩ := exists_bound_of_tail_bound (a := σ) (b := σ) (C := C) (T₀ := T₀)
      (fun s hs1 hs2 ↦ (hfσ s (le_antisymm hs2 hs1)).continuousAt)
      (fun σ' t hs1 hs2 ht ↦ hC σ' t (h1.trans hs1) (hs2.trans h2) ht)
    exact (integrable_one_add_abs_rpow_neg_two.const_mul C').mono'
      (continuous_iff_continuousAt.mpr fun t ↦ (hfσ _ (by simp)).continuousAt.comp
        (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ hC' σ t le_rfl le_rfl)
  have hia := hline a le_rfl (ha.trans hb).le ha.ne
  have hib := hline b (ha.trans hb).le le_rfl hb.ne'
  exact ⟨hia, hib, integral_vertical_sub_eq_of_simplePole ha hb
    (fun s hs ↦ (hf s hs.1.1 hs.1.2 hs.2).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hf s hs.1.1.le hs.1.2.le hs.2).differentiableWithinAt) hk hpole hia hib
    (tendstoUniformlyOn_of_tail_bound hC)⟩

end SimplePole

end Complex

section MellinInverse

/-- The derivative of `x ↦ exp (-x)` (adapted from `Mathlib.Analysis.MellinInversion`). -/
private theorem rexp_neg_deriv_aux' :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

/-- The image of `x ↦ exp (-x)` is `(0, ∞)`. -/
private theorem rexp_neg_image_aux' : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

/-- `x ↦ exp (-x)` is injective. -/
private theorem rexp_neg_injOn_aux' : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- The Mellin weight after the substitution `t = exp (-x)`. -/
private theorem rexp_cexp_aux' (x : ℝ) (s : ℂ) (f : ℂ) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  simp only [Complex.real_smul, smul_eq_mul]
  rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg), ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Mellin transform of an inverse Mellin transform.** If `Ψ` is continuous and integrable on the
vertical line `Re s = σ` and `ℳ⁻¹_σ Ψ` is Mellin convergent at `σ`, then
`ℳ (ℳ⁻¹_σ Ψ) s = Ψ s` on that line. -/
theorem mellin_mellinInv_eq {Ψ : ℂ → ℂ} {σ : ℝ}
    (hcont : Continuous fun y : ℝ ↦ Ψ (σ + y * I))
    (hint : Integrable fun y : ℝ ↦ Ψ (σ + y * I))
    (hconv : MellinConvergent (mellinInv σ Ψ) σ) {s : ℂ} (hs : s.re = σ) :
    mellin (mellinInv σ Ψ) s = Ψ s := by
  set F := mellinInv σ Ψ
  set ψ : ℝ → ℂ := fun y ↦ Ψ (σ + 2 * π * y * I)
  set g : ℝ → ℂ := fun u ↦ Real.exp (-σ * u) • F (Real.exp (-u))
  have hψc : Continuous ψ := by
    have : ψ = (fun y : ℝ ↦ Ψ (σ + y * I)) ∘ fun y ↦ 2 * π * y := by
      funext y; simp only [ψ, Function.comp_apply]; push_cast; ring_nf
    rw [this]; exact hcont.comp (by fun_prop)
  have hψi : Integrable ψ := by
    have h2π : (2 * π : ℝ) ≠ 0 := by positivity
    have := hint.comp_mul_left' h2π
    refine this.congr (Eventually.of_forall fun y ↦ ?_)
    simp only [ψ]; push_cast; ring_nf
  have hg : g = 𝓕⁻ ψ := by
    funext u
    have hx : 0 < Real.exp (-u) := Real.exp_pos _
    simp only [g, F]
    rw [mellinInv_eq_fourierInv σ Ψ hx, Real.log_exp, neg_neg]
    rw [← smul_assoc]
    have h1 : (Real.exp (-σ * u) : ℝ) • ((Real.exp (-u) : ℝ) : ℂ) ^ (-(σ : ℂ)) = 1 := by
      rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul, Complex.real_smul, ← ofReal_mul,
        ← Real.exp_add]
      rw [show -σ * u + -u * -σ = 0 by ring, Real.exp_zero, ofReal_one]
    rw [h1, one_smul]
  have hgi : Integrable g := by
    have hf := hconv
    rw [MellinConvergent, ← rexp_neg_image_aux', integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux' rexp_neg_injOn_aux'] at hf
    rw [IntegrableOn, Measure.restrict_univ] at hf
    replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • F (rexp (-x)) := by
      refine hf.congr (Eventually.of_forall fun x ↦ ?_)
      simp only [Function.comp_apply, abs_neg, Real.abs_exp, ofReal_exp, ofReal_neg]
      exact rexp_cexp_aux' x σ _
    refine hf.congr (Eventually.of_forall fun u ↦ ?_)
    simp only [g]
    rw [smul_eq_mul, Complex.real_smul, ofReal_exp]
    push_cast
    ring_nf
  rw [mellin_eq_fourier, hs]
  have : (fun u : ℝ ↦ Real.exp (-σ * u) • F (Real.exp (-u))) = 𝓕⁻ ψ := hg
  have hFi : Integrable (𝓕 ψ) := by
    rw [hg] at hgi
    refine hgi.comp_neg.congr (Eventually.of_forall fun v ↦ ?_)
    simp [Real.fourierInv_eq_fourier_neg]
  rw [this, hψc.fourier_fourierInv_eq hψi hFi]
  simp only [ψ]
  congr 1
  conv_rhs => rw [← re_add_im s]
  rw [hs]
  push_cast
  field_simp

end MellinInverse
