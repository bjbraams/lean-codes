/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-!
# Cauchy boundary values and segment principal values

For an integrable complex density continuous at a real point, the difference
between the Cauchy integrals evaluated directly above and below that point tends
to `-2πi` times the density. This follows from the approximate-identity theorem
for the real Poisson kernel. No regularity away from the point is required.
For a finite interval and an interior point, integrability of the regularized
difference quotient gives separate upper and lower vertical limits. They equal
the Cauchy principal value minus or plus `πi` times the density. The principal
value is characterized by symmetric real-axis truncations, and differentiability
of the density at the point suffices for quotient integrability. No regularity
at the endpoints beyond integrability is required.

Boundary limits are available for heights tending to zero from above and for reciprocal
heights `±1/c` with `c → +∞`. The regularized integral is continuous at height zero,
so its limit can be composed with arbitrary filters. These are vertical limits.

## Main results

* `integrable_mul_cauchyKernel`: integrability off the real line.
* `tendsto_cauchyIntegral_sub`: the symmetric vertical boundary jump.
* `tendsto_intervalIntegral_cauchy_sub`: the corresponding interval-integral theorem.
* `tendsto_intervalIntegral_cauchy_upper` and `tendsto_intervalIntegral_cauchy_lower`:
  separate vertical boundary values with an integrable difference quotient.
* `tendsto_intervalIntegral_cauchy_principalValue`: symmetric real-axis truncations.
* `intervalIntegrable_cauchyDifferenceQuotient`: quotient integrability from
  differentiability at the evaluation point.

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

/-- The sum of the two constant-density kernels is an elementary logarithmic
integral. The sign convention is the kernel `1 / (z - t)`. -/
theorem intervalIntegral_cauchyKernel_add {a b x y : ℝ} (hy : y ≠ 0) :
    (∫ t in a..b, ((x : ℂ) + (y : ℂ) * I - t)⁻¹ +
      ((x : ℂ) - (y : ℂ) * I - t)⁻¹) =
      (Real.log (y ^ 2 + (x - a) ^ 2) - Real.log (y ^ 2 + (x - b) ^ 2) : ℝ) := by
  have he (t : ℝ) : ((x : ℂ) + (y : ℂ) * I - t)⁻¹ +
      ((x : ℂ) - (y : ℂ) * I - t)⁻¹ =
      (2 : ℂ) * ((x - t) / (y ^ 2 + (x - t) ^ 2) : ℝ) := by
    have hp : (x : ℂ) + (y : ℂ) * I - t ≠ 0 := by
      intro h; apply hy; simpa using congrArg im h
    have hm : (x : ℂ) - (y : ℂ) * I - t ≠ 0 := by
      intro h; apply hy; simpa using congrArg im h
    have hd : (y : ℂ) ^ 2 + ((x : ℂ) - t) ^ 2 ≠ 0 := by
      exact_mod_cast (show y ^ 2 + (x - t) ^ 2 ≠ 0 by positivity)
    push_cast
    field_simp
    linear_combination 2 * ((x : ℂ) - t) * (y : ℂ) ^ 2 * I_sq
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t / (y ^ 2 + t ^ 2)),
    integral_id_div_sq_add_sq hy]
  push_cast
  ring

/-- The sum of the upper and lower constant-density Cauchy integrals tends to
twice the real logarithmic term at an interior point. -/
theorem tendsto_intervalIntegral_cauchyKernel_add {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Tendsto (fun c : ℝ =>
      (∫ t in a..b, ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) +
      (∫ t in a..b, ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹)) atTop
      (𝓝 (2 * (Real.log ((x - a) / (b - x)) : ℂ))) := by
  have ht : Tendsto (fun c : ℝ => (c⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0)).pow 2)
  have ha := (ht.add_const ((x - a) ^ 2)).log (by have := sub_pos.mpr hx.1; positivity : (0 : ℝ) + (x - a)^2 ≠ 0)
  have hb := (ht.add_const ((x - b) ^ 2)).log (by
    have : x - b ≠ 0 := sub_ne_zero.mpr hx.2.ne
    positivity : (0 : ℝ) + (x - b)^2 ≠ 0)
  have he : Real.log ((x - a)^2) - Real.log ((x - b)^2) =
      2 * Real.log ((x - a)/(b - x)) := by
    rw [Real.log_div (sub_pos.mpr hx.1).ne' (sub_pos.mpr hx.2).ne',
      Real.log_pow, Real.log_pow, ← Real.log_neg_eq_log (x - b), neg_sub]
    ring
  have h := continuous_ofReal.continuousAt.tendsto.comp (ha.sub hb)
  simp only [zero_add, he, ofReal_mul, ofReal_ofNat] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hp : Continuous (fun t : ℝ => ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t hz
    have := congrArg im hz
    simp [hc.ne'] at this
  have hm : Continuous (fun t : ℝ => ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t hz
    have := congrArg im hz
    simp [hc.ne'] at this
  rw [← intervalIntegral.integral_add (hp.intervalIntegrable a b) (hm.intervalIntegrable a b),
    intervalIntegral_cauchyKernel_add (inv_ne_zero hc.ne')]
  rfl

/-- An integrable regularized density has its expected vertical boundary limit.
The quotient hypothesis permits integrable singularities at the endpoints.
The regularized integral is continuous even at height zero. -/
theorem continuousAt_intervalIntegral_regularized_cauchy {ρ : ℝ → ℂ} {a b x : ℝ}
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    ContinuousAt (fun y : ℝ => ∫ t in a..b,
      (ρ t - ρ x) * ((x : ℂ) + (y : ℂ) * I - t)⁻¹) 0 := by
  let q : ℝ → ℂ := fun t => (ρ t - ρ x) / ((x : ℂ) - t)
  have he {y : ℝ} {t : ℝ} (ht : t ≠ x) :
      (ρ t - ρ x) * ((x : ℂ) + (y : ℂ) * I - t)⁻¹ =
      q t * (((x : ℂ) - t) / ((x : ℂ) + (y : ℂ) * I - t)) := by
    have hxt : (x : ℂ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.symm)
    dsimp [q]
    field_simp
  simp only [ContinuousAt, ofReal_zero, zero_mul, add_zero]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => ‖q t‖)
  · filter_upwards with c
    by_cases hc : c = 0
    · simpa [hc, div_eq_mul_inv] using hq.aestronglyMeasurable_restrict_uIoc
    have hk : Continuous (fun t : ℝ => ((x : ℂ) - t) /
        ((x : ℂ) + (c : ℂ) * I - t)) := by
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro t hz
      apply hc
      simpa using congrArg im hz
    apply (hq.aestronglyMeasurable_restrict_uIoc.mul hk.aestronglyMeasurable).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne x)] with t ht
    exact (he ht).symm
  · filter_upwards with c
    filter_upwards [volume.ae_ne x] with t ht _
    rw [he ht, norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    simpa [← ofReal_sub] using abs_re_le_norm ((x : ℂ) + (c : ℂ) * I - t)
  · exact hq.norm
  · filter_upwards [volume.ae_ne x] with t ht _
    have hxt : (x : ℂ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.symm)
    have h := (tendsto_const_nhds (x := ρ t - ρ x)).mul ((((tendsto_const_nhds (x := (x : ℂ))).add
      ((continuous_ofReal.tendsto (0 : ℝ)).mul_const I)).sub
        (tendsto_const_nhds (x := (t : ℂ)))).inv₀ (by simpa using hxt))
    simpa [q, div_eq_mul_inv] using h

/-- The regularized Cauchy integral converges along every filter of heights tending to zero.
The heights are allowed to vanish; no countability assumption on the filter is needed. -/
theorem tendsto_intervalIntegral_regularized_cauchy {ρ : ℝ → ℂ} {a b x : ℝ}
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b)
    {α : Type*} {l : Filter α} {v : α → ℝ} (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun c => ∫ t in a..b,
      (ρ t - ρ x) * ((x : ℂ) + (v c : ℂ) * I - t)⁻¹) l
      (𝓝 (∫ t in a..b, (ρ t - ρ x) / ((x : ℂ) - t))) := by
  simpa only [Function.comp_def, ofReal_zero, zero_mul, add_zero, div_eq_mul_inv] using
    (continuousAt_intervalIntegral_regularized_cauchy hq).tendsto.comp hv

/-- Interval integrability of a Cauchy integral off the real line. -/
theorem intervalIntegrable_mul_cauchyKernel {ρ : ℝ → ℂ} {a b : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) {z : ℂ} (hz : z.im ≠ 0) :
    IntervalIntegrable (fun t : ℝ => ρ t * (z - t)⁻¹) volume a b := by
  apply hρ.mul_continuousOn
  apply Continuous.continuousOn
  apply Continuous.inv₀ (by fun_prop)
  intro t ht
  apply hz
  simpa using congrArg im ht

/-- The upper boundary value of the constant-density segment kernel. -/
theorem tendsto_intervalIntegral_cauchyKernel_upper {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Tendsto (fun c : ℝ => ∫ t in a..b,
      ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) atTop
      (𝓝 ((Real.log ((x - a)/(b - x)) : ℂ) - (Real.pi : ℂ) * I)) := by
  have hs := tendsto_intervalIntegral_cauchyKernel_add hx
  have hd := tendsto_intervalIntegral_cauchy_sub
    (ρ := fun _ => (1 : ℂ)) intervalIntegrable_const hx continuousAt_const
  simp only [one_mul, mul_one] at hd
  convert (hs.add hd).div_const 2 using 1
  · funext c; ring
  · congr 1; ring

/-- The lower boundary value of the constant-density segment kernel. -/
theorem tendsto_intervalIntegral_cauchyKernel_lower {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Tendsto (fun c : ℝ => ∫ t in a..b,
      ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹) atTop
      (𝓝 ((Real.log ((x - a)/(b - x)) : ℂ) + (Real.pi : ℂ) * I)) := by
  have hs := tendsto_intervalIntegral_cauchyKernel_add hx
  have hd := tendsto_intervalIntegral_cauchy_sub
    (ρ := fun _ => (1 : ℂ)) intervalIntegrable_const hx continuousAt_const
  simp only [one_mul, mul_one] at hd
  convert (hs.sub hd).div_const 2 using 1
  · funext c; ring
  · congr 1; ring

/-- The regularized expression for the principal value of a segment Cauchy
integral. Its interpretation as a symmetric truncation limit requires integrability
of the density and of its difference quotient at the interior point. -/
def cauchyPrincipalValue (ρ : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  (∫ t in a..b, (ρ t - ρ x) / ((x : ℂ) - t)) +
    ρ x * (Real.log ((x - a)/(b - x)) : ℂ)

/-- Subtracting the density at a point isolates the constant-density kernel. -/
private theorem intervalIntegral_cauchy_decompose {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ t in a..b, ρ t * (z - t)⁻¹) =
      (∫ t in a..b, (ρ t - ρ x) * (z - t)⁻¹) +
        ρ x * (∫ t in a..b, (z - t)⁻¹) := by
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      (intervalIntegrable_mul_cauchyKernel (hρ.sub intervalIntegrable_const) hz)
      (intervalIntegrable_mul_cauchyKernel intervalIntegrable_const hz)]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- The upper Plemelj boundary value for a segment. Integrable endpoint
singularities are allowed; the regularized difference quotient must be integrable. -/
theorem tendsto_intervalIntegral_cauchy_upper {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hx : x ∈ Ioo a b)
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    Tendsto (fun c : ℝ => ∫ t in a..b,
      ρ t * ((x : ℂ) + (c⁻¹ : ℝ) * I - t)⁻¹) atTop
      (𝓝 (cauchyPrincipalValue ρ a b x - (Real.pi : ℂ) * I * ρ x)) := by
  have hr := tendsto_intervalIntegral_regularized_cauchy hq tendsto_inv_atTop_zero
  have h := hr.add ((tendsto_intervalIntegral_cauchyKernel_upper hx).const_mul (ρ x))
  have he : (∫ t in a..b, (ρ t - ρ x) / ((x : ℂ) - t)) +
      ρ x * ((Real.log ((x - a)/(b - x)) : ℂ) - (Real.pi : ℂ) * I) =
      cauchyPrincipalValue ρ a b x - (Real.pi : ℂ) * I * ρ x := by
    dsimp [cauchyPrincipalValue]; ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (intervalIntegral_cauchy_decompose hρ (by simp [hc.ne'])).symm

/-- The lower Plemelj boundary value for a segment, with the same regularized
principal value as in the upper boundary formula. -/
theorem tendsto_intervalIntegral_cauchy_lower {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hx : x ∈ Ioo a b)
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    Tendsto (fun c : ℝ => ∫ t in a..b,
      ρ t * ((x : ℂ) - (c⁻¹ : ℝ) * I - t)⁻¹) atTop
      (𝓝 (cauchyPrincipalValue ρ a b x + (Real.pi : ℂ) * I * ρ x)) := by
  have hr := tendsto_intervalIntegral_regularized_cauchy hq
    (show Tendsto (fun c : ℝ => -(c⁻¹)) atTop (𝓝 0) by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0)).neg)
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg] at hr
  have h := hr.add ((tendsto_intervalIntegral_cauchyKernel_lower hx).const_mul (ρ x))
  have he : (∫ t in a..b, (ρ t - ρ x) / ((x : ℂ) - t)) +
      ρ x * ((Real.log ((x - a)/(b - x)) : ℂ) + (Real.pi : ℂ) * I) =
      cauchyPrincipalValue ρ a b x + (Real.pi : ℂ) * I * ρ x := by
    dsimp [cauchyPrincipalValue]; ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (intervalIntegral_cauchy_decompose hρ (by simp [hc.ne'])).symm

/-- The Plemelj jump as the positive vertical height tends to zero. -/
theorem tendsto_cauchyIntegral_sub_nhdsGT {ρ : ℝ → ℂ} (hρ : Integrable ρ) {x : ℝ}
    (hc : ContinuousAt ρ x) :
    Tendsto (fun y : ℝ =>
      (∫ t : ℝ, ρ t * ((x : ℂ) + (y : ℂ) * I - t)⁻¹) -
      (∫ t : ℝ, ρ t * ((x : ℂ) - (y : ℂ) * I - t)⁻¹)) (𝓝[>] 0)
      (𝓝 (-2 * (Real.pi : ℂ) * I * ρ x)) := by
  simpa only [Function.comp_def, inv_inv] using
    (tendsto_cauchyIntegral_sub hρ hc).comp tendsto_inv_nhdsGT_zero

/-- The upper vertical boundary value, parameterized by height tending to zero. -/
theorem tendsto_intervalIntegral_cauchy_upper_nhdsGT {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hx : x ∈ Ioo a b)
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    Tendsto (fun y : ℝ => ∫ t in a..b,
      ρ t * ((x : ℂ) + (y : ℂ) * I - t)⁻¹) (𝓝[>] 0)
      (𝓝 (cauchyPrincipalValue ρ a b x - (Real.pi : ℂ) * I * ρ x)) := by
  simpa only [Function.comp_def, inv_inv] using
    (tendsto_intervalIntegral_cauchy_upper hρ hx hq).comp tendsto_inv_nhdsGT_zero

/-- The lower vertical boundary value, parameterized by positive height tending to zero. -/
theorem tendsto_intervalIntegral_cauchy_lower_nhdsGT {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hx : x ∈ Ioo a b)
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    Tendsto (fun y : ℝ => ∫ t in a..b,
      ρ t * ((x : ℂ) - (y : ℂ) * I - t)⁻¹) (𝓝[>] 0)
      (𝓝 (cauchyPrincipalValue ρ a b x + (Real.pi : ℂ) * I * ρ x)) := by
  simpa only [Function.comp_def, inv_inv] using
    (tendsto_intervalIntegral_cauchy_lower hρ hx hq).comp tendsto_inv_nhdsGT_zero

/-- Evaluation of the real Cauchy kernel on an interval avoiding its pole. -/
theorem intervalIntegral_cauchyKernel_real {a b x : ℝ} (hx : x ∉ uIcc a b) :
    (∫ t in a..b, ((x : ℂ) - t)⁻¹) =
      (Real.log ((x - a)/(x - b)) : ℂ) := by
  have hzero : (0 : ℝ) ∉ uIcc (x - b) (x - a) := by
    simpa [mem_uIcc, sub_nonneg, sub_nonpos, and_comm, or_comm] using hx
  simp_rw [← ofReal_sub, ← ofReal_inv]
  rw [intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹), integral_inv hzero]

/-- Regularization on a closed interval which avoids the pole. -/
private theorem intervalIntegral_cauchy_real_decompose {ρ : ℝ → ℂ} {a b x : ℝ}
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b)
    (hx : x ∉ uIcc a b) :
    (∫ t in a..b, ρ t * ((x : ℂ) - t)⁻¹) =
      (∫ t in a..b, (ρ t - ρ x) / ((x : ℂ) - t)) +
        ρ x * (Real.log ((x - a)/(x - b)) : ℂ) := by
  have hk : ContinuousOn (fun t : ℝ => ((x : ℂ) - t)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht hz
    have : x = t := ofReal_injective (sub_eq_zero.mp hz)
    exact hx (this ▸ ht)
  rw [← intervalIntegral_cauchyKernel_real hx, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hq (hk.intervalIntegrable.const_mul (ρ x))]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [div_eq_mul_inv]
  ring

/-- The regularized principal value equals the limit of symmetric real-axis
truncations at the pole. Only the difference quotient needs to be integrable. -/
theorem tendsto_intervalIntegral_cauchy_principalValue {ρ : ℝ → ℂ} {a b x : ℝ}
    (hx : x ∈ Ioo a b)
    (hq : IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b) :
    Tendsto (fun c : ℝ =>
      (∫ t in a..x - c⁻¹, ρ t * ((x : ℂ) - t)⁻¹) +
      (∫ t in x + c⁻¹..b, ρ t * ((x : ℂ) - t)⁻¹)) atTop
      (𝓝 (cauchyPrincipalValue ρ a b x)) := by
  let q : ℝ → ℂ := fun t => (ρ t - ρ x) / ((x : ℂ) - t)
  have hab : a ≤ b := hx.1.le.trans hx.2.le
  have hxn : uIcc a b ∈ 𝓝 x := by
    rw [uIcc_of_le hab]
    exact Icc_mem_nhds hx.1 hx.2
  have hxc : x ∈ uIcc a b := by simpa [uIcc_of_le hab] using ⟨hx.1.le, hx.2.le⟩
  have hl := ((intervalIntegral.continuousOn_primitive_interval' hq left_mem_uIcc) x hxc).continuousAt hxn
  have hr := ((intervalIntegral.continuousOn_primitive_interval' hq right_mem_uIcc) x hxc).continuousAt hxn
  have hv : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hleft := hl.tendsto.comp (show Tendsto (fun c : ℝ => x - c⁻¹) atTop (𝓝 x) by simpa using hv.const_sub x)
  have hright := (hr.tendsto.comp (show Tendsto (fun c : ℝ => x + c⁻¹) atTop (𝓝 x) by simpa using hv.const_add x)).neg
  simp only [Function.comp_def, ← intervalIntegral.integral_symm] at hleft hright
  have hi : (∫ t in a..x, q t) + (∫ t in x..b, q t) = ∫ t in a..b, q t := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact hq.mono_set (uIcc_subset_uIcc left_mem_uIcc hxc)
    · exact hq.mono_set (uIcc_subset_uIcc hxc right_mem_uIcc)
  have h := (hleft.add hright).add_const (ρ x * (Real.log ((x - a)/(b - x)) : ℂ))
  change Tendsto _ atTop (𝓝 ((∫ t in a..x, q t) + (∫ t in x..b, q t) + _)) at h
  rw [hi] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hv.eventually (gt_mem_nhds (sub_pos.mpr hx.1)),
    hv.eventually (gt_mem_nhds (sub_pos.mpr hx.2))] with c hc hca hcb
  have he : 0 < c⁻¹ := inv_pos.mpr hc
  have hal : a ≤ x - c⁻¹ := by linarith
  have hrb : x + c⁻¹ ≤ b := by linarith
  have hxl : x - c⁻¹ ∈ uIcc a b := by
    simp only [uIcc_of_le hab, mem_Icc]; constructor <;> linarith [hx.2]
  have hxr : x + c⁻¹ ∈ uIcc a b := by
    simp only [uIcc_of_le hab, mem_Icc]; constructor <;> linarith [hx.1]
  rw [intervalIntegral_cauchy_real_decompose
      (hq.mono_set (uIcc_subset_uIcc left_mem_uIcc hxl)) (by
        simp only [uIcc_of_le hal, mem_Icc, not_and]; intro _; linarith),
    intervalIntegral_cauchy_real_decompose
      (hq.mono_set (uIcc_subset_uIcc hxr right_mem_uIcc)) (by
        simp only [uIcc_of_le hrb, mem_Icc, not_and]; intro hbad; linarith)]
  have heq : Real.log ((x - a)/(x - (x - c⁻¹))) + Real.log ((x - (x + c⁻¹))/(x - b)) =
      Real.log ((x - a)/(b - x)) := by
    have hxb : x - b ≠ 0 := sub_ne_zero.mpr hx.2.ne
    rw [Real.log_div (sub_pos.mpr hx.1).ne' (by linarith),
      Real.log_div (by linarith) hxb,
      Real.log_div (sub_pos.mpr hx.1).ne' (sub_pos.mpr hx.2).ne']
    rw [show x - (x - c⁻¹) = c⁻¹ by ring, show x - (x + c⁻¹) = -(c⁻¹) by ring,
      Real.log_neg_eq_log, ← Real.log_neg_eq_log (x - b), neg_sub]
    ring
  have heq' := congrArg ofReal heq
  push_cast at heq'
  linear_combination -ρ x * heq'

/-- A local linear bound on the density's increment makes its regularized
Cauchy quotient integrable; no endpoint continuity is required. -/
theorem intervalIntegrable_cauchyDifferenceQuotient_of_bound {ρ : ℝ → ℂ} {a b x δ L : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hlocal : ∀ t ∈ uIcc a b, |t - x| < δ → ‖ρ t - ρ x‖ ≤ L * |t - x|) :
    IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b := by
  have hi : IntervalIntegrable (fun t => L + (‖ρ t‖ + ‖ρ x‖) / δ) volume a b :=
    intervalIntegrable_const.add ((hρ.norm.add intervalIntegrable_const).div_const δ)
  apply hi.mono_fun'
  · exact (hρ.aestronglyMeasurable_restrict_uIoc.sub aestronglyMeasurable_const).div₀
      ((continuous_const.sub continuous_ofReal).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [norm_div, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm x t]
    by_cases htx : t = x
    · subst t; simp; positivity
    have hp : 0 < |t - x| := abs_pos.mpr (sub_ne_zero.mpr htx)
    by_cases hnear : |t - x| < δ
    · calc
        ‖ρ t - ρ x‖ / |t - x| ≤ L := (div_le_iff₀ hp).mpr
          (hlocal t (uIoc_subset_uIcc ht) hnear)
        _ ≤ L + (‖ρ t‖ + ‖ρ x‖) / δ := le_add_of_nonneg_right (by positivity)
    · calc
        ‖ρ t - ρ x‖ / |t - x| ≤ (‖ρ t‖ + ‖ρ x‖) / δ :=
          div_le_div₀ (by positivity) (norm_sub_le _ _) hδ (le_of_not_gt hnear)
        _ ≤ L + (‖ρ t‖ + ‖ρ x‖) / δ := le_add_of_nonneg_left hL

/-- Differentiability at the interior evaluation point suffices for integrability
of the regularized Cauchy quotient of an integrable density. -/
theorem intervalIntegrable_cauchyDifferenceQuotient {ρ : ℝ → ℂ} {a b x : ℝ}
    (hρ : IntervalIntegrable ρ volume a b) (hd : DifferentiableAt ℝ ρ x) :
    IntervalIntegrable (fun t : ℝ => (ρ t - ρ x) / ((x : ℂ) - t)) volume a b := by
  obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hC
  apply intervalIntegrable_cauchyDifferenceQuotient_of_bound hρ hδ (abs_nonneg C)
  intro t _ ht
  have h := hball (show t ∈ Metric.ball x δ by simpa [Real.dist_eq] using ht)
  have h' : ‖ρ t - ρ x‖ ≤ C * |t - x| := by simpa [Real.norm_eq_abs] using h
  exact h'.trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg (t - x)))

end Complex
