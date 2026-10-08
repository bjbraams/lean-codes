/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Slope
public import ToMathlib.Analysis.Integral.StrictMono

/-!
# Integral comparison for a kernel with two sign changes

A signed kernel which is positive between two crossings and negative outside, and annihilates
constants and linear functions, has negative integral against any strictly convex function; with
nonstrict signs it has nonpositive integral against any convex function. This is the
secant-line argument used by Carlson–Tobey (1968), Lemma 1. The results allow any convex domain,
with the sign and support assumptions stated almost everywhere; the strict version needs a
nonzero measure that does not charge the two crossings.

## Main results

* `StrictConvexOn.integral_mul_neg_of_two_crossings`,
  `StrictConcaveOn.integral_mul_pos_of_two_crossings`: the strict comparisons.
* `ConvexOn.integral_mul_nonpos_of_two_crossings`,
  `ConcaveOn.integral_mul_nonneg_of_two_crossings`: the nonstrict comparisons.
-/

open MeasureTheory Set
public section

/-- The secant combination of a two-crossing kernel annihilating constants and linear functions
is integrable with integral zero. -/
private theorem integrable_secant_mul_and_integral_eq_zero {μ : Measure ℝ} {f g : ℝ → ℝ}
    {a b : ℝ} (hg : Integrable g μ) (hug : Integrable (fun u ↦ u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    Integrable (fun u ↦ ((b - u) * f a + (u - a) * f b) * g u) μ ∧
      ∫ u, ((b - u) * f a + (u - a) * f b) * g u ∂μ = 0 := by
  have he (u : ℝ) : ((b - u) * f a + (u - a) * f b) * g u =
      (b * f a - a * f b) * g u + (f b - f a) * (u * g u) := by ring
  simp_rw [he]
  refine ⟨(hg.const_mul _).add (hug.const_mul _), ?_⟩
  rw [integral_add (hg.const_mul _) (hug.const_mul _), integral_const_mul,
    integral_const_mul, h0, h1, mul_zero, mul_zero, add_zero]

/-- A signed kernel with two crossings and vanishing first two moments integrates
 every strictly convex function to a strictly negative value. -/
theorem StrictConvexOn.integral_mul_neg_of_two_crossings
    {μ : Measure ℝ} [NeZero μ] {s : Set ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConvexOn ℝ s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hs : ∀ᵐ u ∂μ, u ∈ s) (hne : ∀ᵐ u ∂μ, u ≠ a ∧ u ≠ b)
    (hpos : ∀ᵐ u ∂μ, u ∈ Ioo a b → 0 < g u)
    (hneg : ∀ᵐ u ∂μ, u < a ∨ b < u → g u < 0)
    (hg : Integrable g μ) (hug : Integrable (fun u ↦ u * g u) μ)
    (hfg : Integrable (fun u ↦ f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    (∫ u, f u * g u ∂μ) < 0 := by
  let L := fun u ↦ ((b - u) * f a + (u - a) * f b) * g u
  obtain ⟨hL, hL0⟩ := integrable_secant_mul_and_integral_eq_zero (f := f) (a := a) (b := b)
    hg hug h0 h1
  have hcmp : ∀ᵐ u ∂μ, (b - a) * (f u * g u) < L u := by
    filter_upwards [hs, hne, hpos, hneg] with u hu hne hpos hneg
    dsimp only [L]
    rcases lt_or_gt_of_ne hne.1 with hua | hau
    · have h := hf.secant_strict_mono_aux1 hu hb hua hab
      have he : (b - u) * f a + (u - a) * f b < (b - a) * f u := by linarith
      simpa only [mul_assoc] using mul_lt_mul_of_neg_right he (hneg (Or.inl hua))
    · rcases lt_or_gt_of_ne hne.2 with hub | hbu
      · have h := hf.secant_strict_mono_aux1 ha hb hau hub
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right h (hpos ⟨hau, hub⟩)
      · have h := hf.secant_strict_mono_aux1 ha hu hab hbu
        have he : (b - u) * f a + (u - a) * f b < (b - a) * f u := by linarith
        simpa only [mul_assoc] using mul_lt_mul_of_neg_right he (hneg (Or.inr hbu))
  have h := integral_lt_integral_of_ae_lt (hfg.const_mul (b - a)) hL hcmp
  rw [integral_const_mul, hL0] at h
  nlinarith

/-- The two-crossing comparison reverses for a strictly concave kernel. -/
theorem StrictConcaveOn.integral_mul_pos_of_two_crossings
    {μ : Measure ℝ} [NeZero μ] {s : Set ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConcaveOn ℝ s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hs : ∀ᵐ u ∂μ, u ∈ s) (hne : ∀ᵐ u ∂μ, u ≠ a ∧ u ≠ b)
    (hpos : ∀ᵐ u ∂μ, u ∈ Ioo a b → 0 < g u)
    (hneg : ∀ᵐ u ∂μ, u < a ∨ b < u → g u < 0)
    (hg : Integrable g μ) (hug : Integrable (fun u ↦ u * g u) μ)
    (hfg : Integrable (fun u ↦ f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    0 < ∫ u, f u * g u ∂μ := by
  have h := hf.neg.integral_mul_neg_of_two_crossings ha hb hab hs hne hpos hneg hg hug
    (by convert hfg.neg using 1; ext u; simp) h0 h1
  simpa only [Pi.neg_apply, neg_mul, integral_neg, neg_lt_zero] using h

/-- A signed kernel which is nonnegative between two points and nonpositive outside, with vanishing
first two moments, integrates every convex function to a nonpositive value. Unlike the strict
version, no condition on the measure is needed. -/
theorem ConvexOn.integral_mul_nonpos_of_two_crossings
    {μ : Measure ℝ} {s : Set ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hs : ∀ᵐ u ∂μ, u ∈ s)
    (hpos : ∀ᵐ u ∂μ, u ∈ Ioo a b → 0 ≤ g u)
    (hneg : ∀ᵐ u ∂μ, u < a ∨ b < u → g u ≤ 0)
    (hg : Integrable g μ) (hug : Integrable (fun u ↦ u * g u) μ)
    (hfg : Integrable (fun u ↦ f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    (∫ u, f u * g u ∂μ) ≤ 0 := by
  let L := fun u ↦ ((b - u) * f a + (u - a) * f b) * g u
  obtain ⟨hL, hL0⟩ := integrable_secant_mul_and_integral_eq_zero (f := f) (a := a) (b := b)
    hg hug h0 h1
  have hcmp : ∀ᵐ u ∂μ, (b - a) * (f u * g u) ≤ L u := by
    filter_upwards [hs, hpos, hneg] with u hu hpos hneg
    dsimp only [L]
    rcases lt_trichotomy u a with hua | rfl | hau
    · have h := hf.secant_mono_aux1 hu hb hua hab
      have he : (b - u) * f a + (u - a) * f b ≤ (b - a) * f u := by linarith
      simpa only [mul_assoc] using mul_le_mul_of_nonpos_right he (hneg (Or.inl hua))
    · exact le_of_eq (by ring)
    · rcases lt_trichotomy u b with hub | rfl | hbu
      · have h := hf.secant_mono_aux1 ha hb hau hub
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h (hpos ⟨hau, hub⟩)
      · exact le_of_eq (by ring)
      · have h := hf.secant_mono_aux1 ha hu hab hbu
        have he : (b - u) * f a + (u - a) * f b ≤ (b - a) * f u := by linarith
        simpa only [mul_assoc] using mul_le_mul_of_nonpos_right he (hneg (Or.inr hbu))
  have h := integral_mono_ae (hfg.const_mul (b - a)) hL hcmp
  rw [integral_const_mul, hL0] at h
  nlinarith

/-- The two-crossing comparison reverses for a concave kernel. -/
theorem ConcaveOn.integral_mul_nonneg_of_two_crossings
    {μ : Measure ℝ} {s : Set ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ConcaveOn ℝ s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hs : ∀ᵐ u ∂μ, u ∈ s)
    (hpos : ∀ᵐ u ∂μ, u ∈ Ioo a b → 0 ≤ g u)
    (hneg : ∀ᵐ u ∂μ, u < a ∨ b < u → g u ≤ 0)
    (hg : Integrable g μ) (hug : Integrable (fun u ↦ u * g u) μ)
    (hfg : Integrable (fun u ↦ f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    0 ≤ ∫ u, f u * g u ∂μ := by
  have h := hf.neg.integral_mul_nonpos_of_two_crossings ha hb hab hs hpos hneg hg hug
    (by convert hfg.neg using 1; ext u; simp) h0 h1
  simpa only [Pi.neg_apply, neg_mul, integral_neg, neg_nonpos] using h
