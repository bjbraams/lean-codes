/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Convex.Continuous
public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# Real beta density integrals and concentration ratios

Real integrability, total mass, and first moment complement Mathlib's nonnegative
beta density integral. The ratio identity isolates the continuous positive-power
kernel responsible for two crossings when concentration increases.

The nonnegativity, beta-law integration and mean results specialize the Tau Ceti contributors'
`TauCeti.Probability.betaPDFReal_nonneg`, `TauCeti.Probability.integral_betaMeasure_eq` and
`TauCeti.Probability.integral_id_betaMeasure` from `TauCeti.Probability.Distributions.Beta.Basic`.
The unit shift of the beta function is their `ProbabilityTheory.beta_add_one_left` from
`TauCeti.Analysis.SpecialFunctions.Beta`, whose hypotheses are weaker than positivity.
-/

open MeasureTheory Set
public noncomputable section
namespace ProbabilityTheory

/-- A beta density with positive parameters is nonnegative everywhere.
Uses `TauCeti.Probability.betaPDFReal_nonneg`. -/
theorem betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    0 ≤ betaPDFReal a b u :=
  TauCeti.Probability.betaPDFReal_nonneg ha hb u

/-- The real beta density is integrable for positive parameters. -/
theorem integrable_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (betaPDFReal a b) := by
  have h := integrable_toReal_of_lintegral_ne_top (μ := volume) (f := betaPDF a b)
    ((ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)).aemeasurable)
    (by rw [lintegral_betaPDF_eq_one ha hb]; exact ENNReal.one_ne_top)
  simpa only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg ha hb _)] using h

/-- The real beta density integrates to one. -/
theorem integral_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u, betaPDFReal a b u) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (betaPDFReal_nonneg ha hb))
    (measurable_betaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ u, betaPDF a b u).toReal = 1
  rw [lintegral_betaPDF_eq_one ha hb, ENNReal.toReal_one]

/-- Multiplying the beta density by its coordinate shifts its first parameter. -/
theorem mul_betaPDFReal_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    u * betaPDFReal a b u = a / (a + b) * betaPDFReal (a + 1) b u := by
  by_cases hu : 0 < u ∧ u < 1
  · rw [betaPDFReal, betaPDFReal, ite_eq_left hu, ite_eq_left hu,
      beta_add_one_left ha.ne' (add_pos ha hb).ne']
    have hpow : u ^ (a + 1 - 1) = u * u ^ (a - 1) := by
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add hu.1, Real.rpow_one, mul_comm]
    rw [hpow]
    have hbeta := (beta_pos ha hb).ne'
    have hab := (add_pos ha hb).ne'
    field_simp
  · simp only [betaPDFReal, hu, ↓reduceIte, mul_zero]

/-- The first moment of a real beta density is its normalized first parameter.
Uses `TauCeti.Probability.integral_betaMeasure_eq` and
`TauCeti.Probability.integral_id_betaMeasure`. -/
theorem integral_mul_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u, u * betaPDFReal a b u) = a / (a + b) := by
  have h := TauCeti.Probability.integral_betaMeasure_eq ha hb (fun u : ℝ ↦ u)
  rw [TauCeti.Probability.integral_id_betaMeasure ha hb] at h
  simpa only [smul_eq_mul, mul_comm] using h.symm

/-- Continuous kernels on the closed unit interval are integrable against the beta density. -/
theorem integrable_betaPDFReal_mul_of_continuousOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Integrable (fun u ↦ betaPDFReal a b u * f u) := by
  have h := (integrable_betaPDFReal ha hb).integrableOn.mul_continuousOn hf isCompact_Icc
  have h := (integrable_indicator_iff measurableSet_Icc).mpr h
  convert h using 1
  ext u
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    have hn : ¬ (0 < u ∧ u < 1) := fun h ↦ hu ⟨h.1.le, h.2.le⟩
    simp only [betaPDFReal, hn, ↓reduceIte, zero_mul]

/-- A function convex on the closed unit interval is integrable against every beta density with
positive parameters. No continuity is needed: a convex function on `[0, 1]` is bounded above by
`max (f 0) (f 1)`, bounded below by midpoint convexity, and continuous on `(0, 1)`. -/
theorem integrable_betaPDFReal_mul_of_convexOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Icc 0 1) f) :
    Integrable (fun u ↦ betaPDFReal a b u * f u) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set M := max (f 0) (f 1)
  have hup : ∀ u ∈ Icc (0 : ℝ) 1, f u ≤ M := fun u hu ↦ hf.le_max_of_mem_Icc h0 h1 hu
  have hlow : ∀ u ∈ Icc (0 : ℝ) 1, 2 * f (1 / 2) - M ≤ f u := by
    intro u hu
    have hu' : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h := hf.2 hu hu' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at h
    rw [show 1 / 2 * u + 1 / 2 * (1 - u) = 1 / 2 by ring] at h
    linarith [hup _ hu']
  set C := max |M| |2 * f (1 / 2) - M|
  have hbd : ∀ u ∈ Icc (0 : ℝ) 1, |f u| ≤ C := fun u hu ↦ abs_le.mpr
    ⟨by linarith [neg_abs_le (2 * f (1 / 2) - M), le_max_right |M| |2 * f (1 / 2) - M|,
        hlow u hu],
      by linarith [le_abs_self M, le_max_left |M| |2 * f (1 / 2) - M|, hup u hu]⟩
  have hmeas : AEStronglyMeasurable (fun u ↦ betaPDFReal a b u * f u) volume := by
    have hc : ContinuousOn f (Ioo 0 1) := by
      simpa only [interior_Icc] using hf.continuousOn_interior
    have heq : (fun u ↦ betaPDFReal a b u * f u) =
        (Ioo (0 : ℝ) 1).indicator (fun u ↦ betaPDFReal a b u * f u) := by
      funext u
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu]
        simp only [betaPDFReal, show ¬ (0 < u ∧ u < 1) from hu, ↓reduceIte, zero_mul]
    rw [heq, aestronglyMeasurable_indicator_iff measurableSet_Ioo]
    exact (measurable_betaPDFReal a b).aestronglyMeasurable.mul
      (hc.aestronglyMeasurable measurableSet_Ioo)
  refine ((integrable_betaPDFReal ha hb).mul_const C).mono' hmeas
    (Filter.Eventually.of_forall fun u ↦ ?_)
  by_cases hu : 0 < u ∧ u < 1
  · rw [norm_mul, Real.norm_of_nonneg (betaPDFReal_nonneg ha hb u), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd u ⟨hu.1.le, hu.2.le⟩) (betaPDFReal_nonneg ha hb u)
  · simp only [betaPDFReal, hu, ↓reduceIte, zero_mul, norm_zero, le_refl]

/-- Increasing concentration multiplies the beta density by a positive-power kernel. -/
theorem betaPDFReal_concentration_ratio {a b c d u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal (d * a) (d * b) u = betaPDFReal (c * a) (c * b) u *
      (beta (c * a) (c * b) / beta (d * a) (d * b) *
        u ^ ((d - c) * a) * (1 - u) ^ ((d - c) * b)) := by
  change 0 < u ∧ u < 1 at hu
  rw [betaPDFReal, betaPDFReal, ite_eq_left hu, ite_eq_left hu]
  have he : d * a - 1 = (c * a - 1) + (d - c) * a := by ring
  have he' : d * b - 1 = (c * b - 1) + (d - c) * b := by ring
  rw [he, he', Real.rpow_add hu.1, Real.rpow_add (sub_pos.mpr hu.2)]
  have hbc := (beta_pos (mul_pos hc ha) (mul_pos hc hb)).ne'
  symm
  calc
    _ = ((beta (c * a) (c * b))⁻¹ * beta (c * a) (c * b)) *
        (1 / beta (d * a) (d * b) * (u ^ (c * a - 1) * u ^ ((d - c) * a)) *
          ((1 - u) ^ (c * b - 1) * (1 - u) ^ ((d - c) * b))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hbc, one_mul]

/-- Beta density integrals can be restricted to the open unit interval without changing them. -/
theorem integral_betaPDFReal_mul_Ioo (a b : ℝ) (f : ℝ → ℝ) :
    (∫ u in Ioo (0 : ℝ) 1, betaPDFReal a b u * f u) = ∫ u, betaPDFReal a b u * f u := by
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    simp only [betaPDFReal, show ¬ (0 < u ∧ u < 1) from hu, ↓reduceIte, zero_mul]

/-- Integration under a beta law agrees with the ordinary real density integral.
Uses `TauCeti.Probability.integral_betaMeasure_eq`. -/
theorem integral_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure a b) = ∫ u, betaPDFReal a b u * f u := by
  simpa only [smul_eq_mul] using TauCeti.Probability.integral_betaMeasure_eq ha hb f

/-- Constant concentration changes preserve the beta mean. -/
theorem integral_mul_betaPDFReal_concentration {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ u, u * betaPDFReal (c * a) (c * b) u) = a / (a + b) := by
  rw [integral_mul_betaPDFReal (mul_pos hc ha) (mul_pos hc hb), ← mul_add,
    mul_div_mul_left _ _ hc.ne']

end ProbabilityTheory
