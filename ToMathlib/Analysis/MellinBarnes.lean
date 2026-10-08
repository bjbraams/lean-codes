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

Tools for moving vertical lines of integration, as in Mellin–Barnes integrals.

* `Complex.integral_vertical_eq_of_bound`, `Complex.integral_vertical_eq_of_tail_bound`: Cauchy's
  theorem on a vertical strip. A function holomorphic on the closed strip `a ≤ Re s ≤ b` and
  `O((1 + |t|)^(-2))` there has the same integral along both boundary lines.
* `Complex.integral_vertical_sub_eq_of_simplePole`: crossing a simple pole with residue `r`
  changes the line integral `∫ f (σ + t I) dt` by `2π r`. The proof subtracts the comparison
  function `r / (s - s₀) + r / (L - (s - s₀))`, which has the same pole and is integrable on
  vertical lines. Its line integrals `π r (sign α + sign (L - α))` come from
  `∫_{-T}^{T} dτ / (α + τ I) = 2 arctan (T / α)` (`Complex.integral_inv_add_mul_I`,
  `Complex.integral_inv_add_inv_sub`).
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

/-- **Shifting a vertical line of integration.** If `f` is holomorphic at every point of the
closed strip `a ≤ Re s ≤ b` and `‖f (σ + t I)‖ ≤ C (1 + |t|)^(-2)` there, then
`∫ f (a + t I) dt = ∫ f (b + t I) dt`. -/
theorem integral_vertical_eq_of_bound {f : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hcont : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Continuous fun t : ℝ ↦ f (σ + t * I) := by
    intro σ h1 h2
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    exact ((hf _ (by simpa using h1) (by simpa using h2)).continuousAt).comp (by fun_prop)
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable fun t : ℝ ↦ f (σ + t * I) := fun σ h1 h2 ↦
    (integrable_one_add_abs_rpow_neg_two.const_mul C).mono'
      (hcont σ h1 h2).aestronglyMeasurable (Eventually.of_forall fun t ↦ hC σ t h1 h2)
  -- The horizontal sides.
  have hside : ∀ R : ℝ, 0 ≤ R → ∀ y : ℝ, |y| = R →
      ‖∫ x in a..b, f (x + y * I)‖ ≤ C * (1 + R) ^ (-2 : ℝ) * |b - a| := by
    intro R _ y hy
    refine norm_integral_le_of_norm_le_const fun x hx ↦ ?_
    rw [uIoc_of_le hab] at hx
    simpa [hy] using hC x y hx.1.le hx.2
  have hlim : Tendsto (fun R : ℝ ↦ C * (1 + R) ^ (-2 : ℝ) * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ ↦ (1 + R) ^ (-2 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp
        (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using (h1.const_mul C).mul_const |b - a|
  have hH : ∀ s : ℝ → ℝ, (∀ R, 0 ≤ R → |s R| = R) →
      Tendsto (fun R ↦ ∫ x in a..b, f (x + s R * I)) atTop (𝓝 0) := by
    intro s hs
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact hside R hR (s R) (hs R hR)
  -- Cauchy's theorem on the rectangle `[a, b] × [-R, R]`.
  have hrect : ∀ R : ℝ, 0 ≤ R → (∫ x in a..b, f (x + ((-R : ℝ) : ℂ) * I)) -
      (∫ x in a..b, f (x + (R : ℂ) * I)) +
      I • (∫ y in -R..R, f (b + y * I)) - I • (∫ y in -R..R, f (a + y * I)) = 0 := by
    intro R hR
    have hR' : -R ≤ R := by linarith
    refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
      ⟨a, -R⟩ ⟨b, R⟩ ?_ ?_
    · intro s hs
      rw [mem_reProdIm, uIcc_of_le hab] at hs
      exact (hf s hs.1.1 hs.1.2).continuousAt.continuousWithinAt
    · intro s hs
      rw [mem_reProdIm, min_eq_left hab, max_eq_right hab] at hs
      exact (hf s hs.1.1.le hs.1.2.le).differentiableWithinAt
  have hTa : Tendsto (fun R : ℝ ↦ ∫ y in -R..R, f (a + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (a + t * I))) :=
    intervalIntegral_tendsto_integral (hint a le_rfl hab) tendsto_neg_atTop_atBot tendsto_id
  have hTb : Tendsto (fun R : ℝ ↦ ∫ y in -R..R, f (b + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (b + t * I))) :=
    intervalIntegral_tendsto_integral (hint b hab le_rfl) tendsto_neg_atTop_atBot tendsto_id
  have hTot := (((hH (fun R ↦ -R) fun R hR ↦ by rw [abs_neg, abs_of_nonneg hR]).sub
    (hH (fun R ↦ R) fun R hR ↦ abs_of_nonneg hR)).add (hTb.const_smul I)).sub (hTa.const_smul I)
  have hzero : Tendsto (fun R : ℝ ↦ (∫ x in a..b, f (x + ((-R : ℝ) : ℂ) * I)) -
      (∫ x in a..b, f (x + R * I)) + I • (∫ y in -R..R, f (b + y * I)) -
      I • (∫ y in -R..R, f (a + y * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 0] with R hR using (hrect R hR).symm)
  have := tendsto_nhds_unique hTot hzero
  simp only [sub_self, zero_add, smul_eq_mul] at this
  have h2 : I * ((∫ t : ℝ, f (b + t * I)) - ∫ t : ℝ, f (a + t * I)) = 0 := by
    rw [mul_sub]; simpa [sub_eq_zero] using this
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-- A bound `C (1 + |t|)^(-2)` for large `|t|` extends, with another constant, to the whole closed
strip `a ≤ Re s ≤ b` for a function continuous there. -/
theorem exists_bound_of_tail_bound {f : ℂ → ℂ} {a b C T₀ : ℝ}
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

/-- **Shifting a vertical line of integration**, with a bound only for large `|t|`. -/
theorem integral_vertical_eq_of_tail_bound {f : ℂ → ℂ} {a b C T₀ : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  obtain ⟨C', hC'⟩ := exists_bound_of_tail_bound (fun s h1 h2 ↦ (hf s h1 h2).continuousAt) hC
  exact integral_vertical_eq_of_bound hab hf hC'

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
theorem tendsto_arctan_div {α : ℝ} (hα : α ≠ 0) :
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
      (((tendsto_arctan_div hα).const_mul 2).add ((tendsto_arctan_div hβ).const_mul 2))
  rw [tendsto_nhds_unique hlim hlim2]
  push_cast; ring

/-- **Crossing a simple pole.** Let `f` be holomorphic on the closed strip `a ≤ Re s ≤ b` except
for a simple pole at `s₀` (`a < Re s₀ < b`) with residue `r`, `f s = r / (s - s₀) + k s` near `s₀`
with `k` holomorphic at `s₀`, and let `‖f (σ + t I)‖ ≤ C (1 + |t|)^(-2)` for `|t| ≥ T₀`. Then the
integrals of `f` along the two boundary lines differ by `2π r`:
`∫ f (b + t I) dt - ∫ f (a + t I) dt = 2π r`. -/
theorem integral_vertical_sub_eq_of_simplePole {f k : ℂ → ℂ} {a b : ℝ} {s₀ r : ℂ}
    (ha : a < s₀.re) (hb : s₀.re < b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ s₀ → DifferentiableAt ℂ f s)
    (hk : DifferentiableAt ℂ k s₀) (hpole : ∀ᶠ s in 𝓝[≠] s₀, f s = r / (s - s₀) + k s)
    {C T₀ : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₀ ≤ |t| → ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    Integrable (fun t : ℝ ↦ f (a + t * I)) ∧ Integrable (fun t : ℝ ↦ f (b + t * I)) ∧
      (∫ t : ℝ, f (b + t * I)) - ∫ t : ℝ, f (a + t * I) = 2 * π * r := by
  set L : ℝ := b - a + 1
  have hL : 0 < L := by simp only [L]; linarith
  set q : ℂ → ℂ := fun s ↦ r / (s - s₀) + r / ((L : ℂ) - (s - s₀))
  set G : ℂ → ℂ := fun s ↦ if s = s₀ then k s₀ - r / (L : ℂ) else f s - q s
  have hLne : ∀ s : ℂ, s.re ≤ b → (L : ℂ) - (s - s₀) ≠ 0 := by
    intro s hs h
    have := congrArg re h
    simp only [sub_re, ofReal_re, zero_re] at this
    simp only [L] at this
    linarith
  -- Regularity of `G`.
  have hGd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ G s := by
    intro s hs1 hs2
    by_cases hss : s = s₀
    · subst hss
      have hev : G =ᶠ[𝓝 s] fun z ↦ k z - r / ((L : ℂ) - (z - s)) := by
        filter_upwards [eventually_nhdsWithin_iff.mp hpole] with z hz
        by_cases hzs : z = s
        · subst hzs; simp [G]
        · have hz' := hz hzs
          have hsub : z - s ≠ 0 := sub_ne_zero.mpr hzs
          simp only [G, hzs, ite_false, q, hz']
          ring
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact hk.sub ((differentiableAt_const r).div ((differentiableAt_const _).sub
        (differentiableAt_id.sub (differentiableAt_const _))) (by simpa using
        (ofReal_ne_zero.mpr hL.ne')))
    · have hev : G =ᶠ[𝓝 s] fun z ↦ f z - q z := by
        filter_upwards [isOpen_ne.mem_nhds hss] with z hz
        simp only [G, show z ≠ s₀ from hz, ite_false]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ z - s₀) s := by fun_prop
      have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ (L : ℂ) - (z - s₀)) s := by fun_prop
      exact (hf s hs1 hs2 hss).sub (((differentiableAt_const r).div h1 (sub_ne_zero.mpr hss)).add
        ((differentiableAt_const r).div h2 (hLne s hs2)))
  -- A global bound for `G`.
  set T₁ : ℝ := max T₀ (2 * |s₀.im| + 2)
  have hT₁ : 0 ≤ T₁ := le_max_of_le_right (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ Icc a b ×ˢ Icc (-T₁) T₁, ‖G (p.1 + p.2 * I)‖ ≤ M := by
    refine (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn fun p hp ↦ ?_
    have hp1 := (mem_prod.mp hp).1
    refine ContinuousAt.continuousWithinAt ?_
    exact (hGd _ (by simpa using hp1.1) (by simpa using hp1.2)).continuousAt.comp (by fun_prop)
  set M' : ℝ := max M 0
  have hq : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T₁ ≤ |t| →
      ‖q (σ + t * I)‖ ≤ 4 * ‖r‖ * L * (1 + |t|) ^ (-2 : ℝ) := by
    intro σ t _ hσb ht
    set u : ℂ := (σ : ℂ) + t * I - s₀
    have hu : (1 + |t|) / 2 ≤ ‖u‖ := by
      have h1 : |t - s₀.im| ≤ ‖u‖ := by simpa [u] using abs_im_le_norm u
      have h2 : 2 * |s₀.im| + 2 ≤ |t| := (le_max_right _ _).trans ht
      have h3 : |t| - |s₀.im| ≤ |t - s₀.im| := abs_sub_abs_le_abs_sub _ _
      linarith
    have hLu : (1 + |t|) / 2 ≤ ‖(L : ℂ) - u‖ := by
      have h1 : |t - s₀.im| ≤ ‖(L : ℂ) - u‖ := by
        have := abs_im_le_norm ((L : ℂ) - u)
        simpa [u, abs_sub_comm] using this
      have h2 : 2 * |s₀.im| + 2 ≤ |t| := (le_max_right _ _).trans ht
      have h3 : |t| - |s₀.im| ≤ |t - s₀.im| := abs_sub_abs_le_abs_sub _ _
      linarith
    have hu0 : u ≠ 0 := fun h ↦ by rw [h, norm_zero] at hu; linarith [abs_nonneg t]
    have hLu0 : (L : ℂ) - u ≠ 0 := fun h ↦ by rw [h, norm_zero] at hLu; linarith [abs_nonneg t]
    have hqe : q (σ + t * I) = r * L / (u * ((L : ℂ) - u)) := by
      simp only [q]
      rw [div_add_div _ _ hu0 hLu0]
      ring
    rw [hqe, norm_div, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hL.le,
      Real.rpow_neg (by positivity), Real.rpow_two]
    rw [div_le_iff₀ (mul_pos (lt_of_lt_of_le (by positivity) hu)
      (lt_of_lt_of_le (by positivity) hLu))]
    have hprod : (1 + |t|) ^ 2 / 4 ≤ ‖u‖ * ‖(L : ℂ) - u‖ := by
      have := mul_le_mul hu hLu (by positivity) (norm_nonneg _)
      linarith
    have hpos : 0 < (1 + |t|) ^ 2 := by positivity
    calc ‖r‖ * L = 4 * ‖r‖ * L * ((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) ^ 2 / 4) := by
          field_simp
      _ ≤ 4 * ‖r‖ * L * ((1 + |t|) ^ 2)⁻¹ * (‖u‖ * ‖(L : ℂ) - u‖) := by gcongr
  set CG : ℝ := max (M' * (1 + T₁) ^ 2) (C + 4 * ‖r‖ * L)
  have hGb : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖G (σ + t * I)‖ ≤ CG * (1 + |t|) ^ (-2 : ℝ) := by
    intro σ t h1 h2
    have hpos : 0 < (1 + |t|) ^ (-2 : ℝ) := by positivity
    rcases le_or_gt T₁ |t| with ht | ht
    · have hne : (σ : ℂ) + t * I ≠ s₀ := by
        intro h
        have := congrArg im h
        simp at this
        have h2' : 2 * |s₀.im| + 2 ≤ |t| := (le_max_right _ _).trans ht
        rw [this] at h2'
        linarith [abs_nonneg s₀.im]
      have hGe : G (σ + t * I) = f (σ + t * I) - q (σ + t * I) := by simp [G, hne]
      rw [hGe]
      refine (norm_sub_le _ _).trans ?_
      have e1 := hC σ t h1 h2 ((le_max_left _ _).trans ht)
      have e2 := hq σ t h1 h2 ht
      calc ‖f (σ + t * I)‖ + ‖q (σ + t * I)‖
          ≤ C * (1 + |t|) ^ (-2 : ℝ) + 4 * ‖r‖ * L * (1 + |t|) ^ (-2 : ℝ) := add_le_add e1 e2
        _ = (C + 4 * ‖r‖ * L) * (1 + |t|) ^ (-2 : ℝ) := by ring
        _ ≤ CG * (1 + |t|) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
    · have hb' := hM (σ, t) ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩
      have hle : (1 + |t|) ^ 2 ≤ (1 + T₁) ^ 2 := by gcongr
      calc ‖G (σ + t * I)‖ ≤ M' := hb'.trans (le_max_left _ _)
        _ = M' * (1 + T₁) ^ 2 * ((1 + T₁) ^ 2)⁻¹ := by field_simp
        _ ≤ M' * (1 + T₁) ^ 2 * ((1 + |t|) ^ 2)⁻¹ := by
            gcongr
        _ = M' * (1 + T₁) ^ 2 * (1 + |t|) ^ (-2 : ℝ) := by
            rw [Real.rpow_neg (by positivity), Real.rpow_two]
        _ ≤ CG * (1 + |t|) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le
  have hshift := integral_vertical_eq_of_bound (ha.trans hb).le hGd hGb
  -- On the boundary lines `f = G + q`.
  have hline : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ≠ s₀.re →
      Integrable (fun t : ℝ ↦ f (σ + t * I)) ∧
      ∫ t : ℝ, f (σ + t * I) = (∫ t : ℝ, G (σ + t * I)) +
        r * (π * (Real.sign (σ - s₀.re) + Real.sign (L - (σ - s₀.re)))) := by
    intro σ h1 h2 hσ
    have hα : σ - s₀.re ≠ 0 := sub_ne_zero.mpr hσ
    have hβ : L - (σ - s₀.re) ≠ 0 := by simp only [L]; linarith
    obtain ⟨hqi, hqv⟩ := integral_inv_add_inv_sub hα hβ s₀.im
    have hqe : ∀ t : ℝ, q (σ + t * I) = r * (1 / (((σ - s₀.re : ℝ) : ℂ) + (t - s₀.im) * I) +
        1 / (((L - (σ - s₀.re) : ℝ) : ℂ) - (t - s₀.im) * I)) := by
      intro t
      have hs₀ : s₀ = (s₀.re : ℂ) + s₀.im * I := (re_add_im s₀).symm
      have e1 : (σ : ℂ) + t * I - s₀ = ((σ - s₀.re : ℝ) : ℂ) + (t - s₀.im) * I := by
        rw [hs₀]; push_cast; ring_nf; simp
      have e2 : (L : ℂ) - ((σ : ℂ) + t * I - s₀) =
          ((L - (σ - s₀.re) : ℝ) : ℂ) - (t - s₀.im) * I := by
        rw [e1]; push_cast; ring
      simp only [q, e1]
      push_cast
      ring
    have hGi : Integrable fun t : ℝ ↦ G (σ + t * I) := by
      refine (integrable_one_add_abs_rpow_neg_two.const_mul CG).mono' ?_
        (Eventually.of_forall fun t ↦ hGb σ t h1 h2)
      refine (continuous_iff_continuousAt.mpr fun t ↦ ?_).aestronglyMeasurable
      exact (hGd _ (by simpa using h1) (by simpa using h2)).continuousAt.comp (by fun_prop)
    have hfe : (fun t : ℝ ↦ f (σ + t * I)) = fun t : ℝ ↦ G (σ + t * I) + q (σ + t * I) := by
      funext t
      have hne : (σ : ℂ) + t * I ≠ s₀ := fun h ↦ hσ (by rw [← h]; simp)
      simp [G, hne]
    have hqi' : Integrable fun t : ℝ ↦ q (σ + t * I) := by
      simp_rw [hqe]; exact hqi.const_mul r
    refine ⟨by rw [hfe]; exact hGi.add hqi', ?_⟩
    rw [hfe, integral_add hGi hqi']
    congr 1
    simp_rw [hqe]
    rw [MeasureTheory.integral_const_mul, hqv]
  have hσa : a ≠ s₀.re := ha.ne
  have hσb : b ≠ s₀.re := hb.ne'
  obtain ⟨hfa, hva⟩ := hline a le_rfl (ha.trans hb).le hσa
  obtain ⟨hfb, hvb⟩ := hline b (ha.trans hb).le le_rfl hσb
  refine ⟨hfa, hfb, ?_⟩
  rw [Real.sign_of_neg (by linarith : a - s₀.re < 0), Real.sign_of_pos (by simp only [L]; linarith :
      0 < L - (a - s₀.re))] at hva
  rw [Real.sign_of_pos (by linarith : 0 < b - s₀.re),
    Real.sign_of_pos (by simp only [L]; linarith : 0 < L - (b - s₀.re))] at hvb
  push_cast at hva hvb
  linear_combination hvb - hva - hshift

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
