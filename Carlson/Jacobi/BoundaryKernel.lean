/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# The symmetric boundary jump of a real-line Cauchy integral

For an integrable complex density continuous at a real point, the difference
between the Cauchy integrals evaluated directly above and below that point tends
to `-2πi` times the density. This follows from the approximate-identity theorem
for the real Poisson kernel. No regularity away from the point is required.
The result concerns the difference of the two values; it does not assert the
existence of their separate limits or a principal-value formula.

## Main results

* `integrable_mul_cauchyKernel`: integrability off the real line.
* `tendsto_cauchyIntegral_sub`: the symmetric vertical boundary jump.
* `tendsto_intervalIntegral_cauchy_sub`: the corresponding interval-integral theorem.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7 (boundary values of associated functions).
* `Mathlib.MeasureTheory.Integral.PeakFunction`.
-/

public noncomputable section
namespace Complex
open MeasureTheory Filter Set Bornology
open scoped Topology

/-- An integrable density times a Cauchy kernel is integrable off the real line. -/
theorem integrable_mul_cauchyKernel {ρ : ℝ → ℂ} (hρ : Integrable ρ) {z : ℂ}
    (hz : z.im ≠ 0) : Integrable (fun t : ℝ => ρ t * (z - t)⁻¹) := by
  have hn (t : ℝ) : z - t ≠ 0 := by
    intro h
    apply hz
    simpa using congrArg im h
  apply hρ.mul_bdd ((continuous_const.sub continuous_ofReal).inv₀ hn).aestronglyMeasurable
  filter_upwards with t
  change ‖(z - (t : ℂ))⁻¹‖ ≤ |z.im|⁻¹
  rw [norm_inv, ← one_div]
  simpa only [one_div] using
    one_div_le_one_div_of_le (abs_pos.mpr hz) (by simpa using abs_im_le_norm (z - t))

/-- The real Poisson profile has the decay required by the approximate-identity theorem. -/
private theorem tendsto_norm_mul_poissonProfile :
    Tendsto (fun t : ℝ => ‖t‖ * ((Real.pi)⁻¹ * (1 + t ^ 2)⁻¹))
      (cobounded ℝ) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => (Real.pi)⁻¹ * ‖t⁻¹‖) (cobounded ℝ) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded (α := ℝ)).norm.const_mul ((Real.pi)⁻¹)
  apply squeeze_zero' (Eventually.of_forall (fun t => by positivity)) ?_ hu
  have hn : ∀ᶠ t : ℝ in cobounded ℝ, t ≠ 0 := isBounded_singleton
  filter_upwards [hn] with t ht
  rw [norm_inv, mul_left_comm]
  gcongr
  have hp : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hs : ‖t‖ ^ 2 = t ^ 2 := by simp
  rw [← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith

/-- The difference of upper and lower Cauchy integrals has the Plemelj jump at
every continuity point of an integrable density. The heights are `±1/c`, with
`c → +∞`; existence of separate boundary values is not needed. -/
theorem tendsto_cauchyIntegral_sub {ρ : ℝ → ℂ} (hρ : Integrable ρ) {x : ℝ}
    (hc : ContinuousAt ρ x) :
    Tendsto (fun c : ℝ =>
      (∫ t : ℝ, ρ t * ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) -
      (∫ t : ℝ, ρ t * ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹)) atTop
      (𝓝 (-2 * (Real.pi : ℂ) * I * ρ x)) := by
  have hm : (∫ t : ℝ, (Real.pi)⁻¹ * (1 + t ^ 2)⁻¹) = 1 := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ Real.pi_ne_zero]
  have hp := tendsto_integral_comp_smul_smul_of_integrable'
    (fun t : ℝ => show 0 ≤ (Real.pi)⁻¹ * (1 + t ^ 2)⁻¹ by positivity) hm
    (by simpa using tendsto_norm_mul_poissonProfile) hρ hc
  have h := hp.const_mul (-2 * (Real.pi : ℂ) * I)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcp
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hcp.ne'
  have hplus : ((x : ℂ) + (c⁻¹ : ℝ) * I).im ≠ 0 := by simpa using hci
  have hminus : ((x : ℂ) - (c⁻¹ : ℝ) * I).im ≠ 0 := by simpa using neg_ne_zero.mpr hci
  rw [← integral_sub (integrable_mul_cauchyKernel hρ hplus)
    (integrable_mul_cauchyKernel hρ hminus), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hnplus : (x : ℂ) + (c⁻¹ : ℝ) * I - t ≠ 0 := by
    intro hz; apply hplus; simpa using congrArg im hz
  have hnminus : (x : ℂ) - (c⁻¹ : ℝ) * I - t ≠ 0 := by
    intro hz; apply hminus; simpa using congrArg im hz
  have hden : (1 + (c * (x - t)) ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [Module.finrank_self, pow_one, smul_eq_mul, real_smul, ofReal_mul,
    ofReal_inv, ofReal_add, ofReal_one, ofReal_pow, ofReal_sub]
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcp.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden' : (1 + ((c : ℂ) * (x - t)) ^ 2) ≠ 0 := by exact_mod_cast hden
  simp only [ofReal_inv] at hnplus hnminus
  have hdp : I + (c : ℂ) * x - c * t ≠ 0 := by
    intro hzero
    have hi := congrArg im hzero
    norm_num at hi
  have hdm : -I + (c : ℂ) * x - c * t ≠ 0 := by
    intro hzero
    have hi := congrArg im hzero
    norm_num at hi
  field_simp [hc0, hπ, hnplus, hnminus, hden', hdp, hdm]
  have hd : (1 - (c : ℂ) ^ 2 * x * t * 2 + c ^ 2 * x ^ 2 + c ^ 2 * t ^ 2) ≠ 0 := by
    convert hden' using 1; ring
  ring_nf
  field_simp [hd, hdp, hdm]
  linear_combination 2 * I * ρ t * I_sq

/-- The symmetric vertical jump for an interval Cauchy integral at an interior
continuity point. Endpoint singularities are allowed whenever the density is integrable. -/
theorem tendsto_intervalIntegral_cauchy_sub {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hx : x ∈ Ioo a b)
    (hc : ContinuousAt ρ x) :
    Tendsto (fun c : ℝ =>
      (∫ t in a..b, ρ t * ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) -
      (∫ t in a..b, ρ t * ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹)) atTop
      (𝓝 (-2 * (Real.pi : ℂ) * I * ρ x)) := by
  have hab : a ≤ b := hx.1.le.trans hx.2.le
  let g := (Icc a b).indicator ρ
  have hi : Integrable g := (integrable_indicator_iff measurableSet_Icc).mpr
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hρ)
  have hg : g =ᶠ[𝓝 x] ρ := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact indicator_of_mem (show t ∈ Icc a b from ⟨ht.1.le, ht.2.le⟩) ρ
  have he (z : ℂ) : (∫ t : ℝ, g t * (z - t)⁻¹) =
      ∫ t in a..b, ρ t * (z - t)⁻¹ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Icc a b <;> simp [g, ht]
  have h := tendsto_cauchyIntegral_sub hi (hc.congr_of_eventuallyEq hg)
  simpa only [he, g, indicator_of_mem (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩) ρ] using h

end Complex
