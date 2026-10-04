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
public import Mathlib.Tactic

/-!
# Real beta density integrals and concentration ratios

Real integrability, total mass, and first moment complement Mathlib's nonnegative
beta density integral. The ratio identity isolates the continuous positive-power
kernel responsible for two crossings when concentration increases.
-/

open MeasureTheory Set
public noncomputable section
namespace ProbabilityTheory

/-- A beta density with positive parameters is nonnegative everywhere. -/
theorem betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    0 ≤ betaPDFReal a b u := by
  by_cases hu : 0 < u ∧ u < 1
  · exact (betaPDFReal_pos hu.1 hu.2 ha hb).le
  · simp only [betaPDFReal, hu, ↓reduceIte, le_refl]

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

/-- A unit shift in the first beta parameter multiplies its normalizing constant by its mean. -/
theorem beta_add_one_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta (a + 1) b = a / (a + b) * beta a b := by
  unfold beta
  rw [show a + 1 + b = (a + b) + 1 by ring, Real.Gamma_add_one ha.ne',
    Real.Gamma_add_one (add_pos ha hb).ne']
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Multiplying the beta density by its coordinate shifts its first parameter. -/
theorem mul_betaPDFReal_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    u * betaPDFReal a b u = a / (a + b) * betaPDFReal (a + 1) b u := by
  by_cases hu : 0 < u ∧ u < 1
  · rw [betaPDFReal, betaPDFReal, ite_eq_left hu, ite_eq_left hu, beta_add_one_left ha hb]
    have hpow : u ^ (a + 1 - 1) = u * u ^ (a - 1) := by
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add hu.1, Real.rpow_one, mul_comm]
    rw [hpow]
    have hbeta := (beta_pos ha hb).ne'
    have hab := (add_pos ha hb).ne'
    field_simp
  · simp only [betaPDFReal, hu, ↓reduceIte, mul_zero]

/-- The first moment of a real beta density is its normalized first parameter. -/
theorem integral_mul_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u, u * betaPDFReal a b u) = a / (a + b) := by
  simp_rw [mul_betaPDFReal_eq ha hb]
  rw [integral_const_mul, integral_betaPDFReal (by positivity) hb, mul_one]

/-- Continuous kernels on the closed unit interval are integrable against the beta density. -/
theorem integrable_betaPDFReal_mul_of_continuousOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Integrable (fun u => betaPDFReal a b u * f u) := by
  have h := (integrable_betaPDFReal ha hb).integrableOn.mul_continuousOn hf isCompact_Icc
  have h := (integrable_indicator_iff measurableSet_Icc).mpr h
  convert h using 1
  ext u
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    have hn : ¬ (0 < u ∧ u < 1) := fun h => hu ⟨h.1.le, h.2.le⟩
    simp only [betaPDFReal, hn, ↓reduceIte, zero_mul]

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

/-- Integration under a beta law agrees with the ordinary real density integral. -/
theorem integral_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure a b) = ∫ u, betaPDFReal a b u * f u := by
  rw [betaMeasure]
  change (∫ u, f u ∂volume.withDensity (ENNReal.ofReal ∘ betaPDFReal a b)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b))
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (betaPDFReal_nonneg ha hb u), smul_eq_mul]

/-- Constant concentration changes preserve the beta mean. -/
theorem integral_mul_betaPDFReal_concentration {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ u, u * betaPDFReal (c * a) (c * b) u) = a / (a + b) := by
  rw [integral_mul_betaPDFReal (mul_pos hc ha) (mul_pos hc hb), ← mul_add,
    mul_div_mul_left _ _ hc.ne']

end ProbabilityTheory
