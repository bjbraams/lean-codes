/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Slope
public import ToMathlib.Analysis.Integral.StrictMono
public import Mathlib.Tactic

/-!
# Strict integral comparison for a kernel with two sign changes

A signed kernel which is positive between two crossings and negative outside,
and annihilates constants and linear functions, has negative integral against
any strictly convex function. This is the secant-line argument used by
Carlson–Tobey (1968), Lemma 1. The result allows any nonzero measure and any convex
domain, with the sign and support assumptions stated almost everywhere.
-/

open MeasureTheory Set
public section

/-- A signed kernel with two crossings and vanishing first two moments integrates
 every strictly convex function to a strictly negative value. -/
theorem StrictConvexOn.integral_mul_neg_of_two_crossings
    {μ : Measure ℝ} [NeZero μ] {s : Set ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConvexOn ℝ s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hs : ∀ᵐ u ∂μ, u ∈ s) (hne : ∀ᵐ u ∂μ, u ≠ a ∧ u ≠ b)
    (hpos : ∀ᵐ u ∂μ, u ∈ Ioo a b → 0 < g u)
    (hneg : ∀ᵐ u ∂μ, u < a ∨ b < u → g u < 0)
    (hg : Integrable g μ) (hug : Integrable (fun u => u * g u) μ)
    (hfg : Integrable (fun u => f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    (∫ u, f u * g u ∂μ) < 0 := by
  let L := fun u => ((b - u) * f a + (u - a) * f b) * g u
  have he (u : ℝ) : L u = (b * f a - a * f b) * g u + (f b - f a) * (u * g u) := by
    dsimp [L]
    ring
  have hL : Integrable L μ := by
    change Integrable (fun u => L u) μ
    simp_rw [he]
    exact (hg.const_mul _).add (hug.const_mul _)
  have hL0 : (∫ u, L u ∂μ) = 0 := by
    simp_rw [he]
    rw [integral_add (hg.const_mul _) (hug.const_mul _), integral_const_mul,
      integral_const_mul, h0, h1, mul_zero, mul_zero, add_zero]
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
    (hg : Integrable g μ) (hug : Integrable (fun u => u * g u) μ)
    (hfg : Integrable (fun u => f u * g u) μ)
    (h0 : ∫ u, g u ∂μ = 0) (h1 : ∫ u, u * g u ∂μ = 0) :
    0 < ∫ u, f u * g u ∂μ := by
  have h := hf.neg.integral_mul_neg_of_two_crossings ha hb hab hs hne hpos hneg hg hug
    (by convert hfg.neg using 1; ext u; simp) h0 h1
  simpa only [Pi.neg_apply, neg_mul, integral_neg, neg_lt_zero] using h
