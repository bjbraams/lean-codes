/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gamma-ratio asymptotics on the positive real axis

The real-parameter version of David Loeffler's Mathlib beta approximation to
Euler's Gamma integral. This is the analytic ingredient in Carlson (1977),
Theorem 3.4-1. The approximation parameter is real, not restricted to integers.
-/

open Filter Set MeasureTheory
open scoped Topology

@[expose] public noncomputable section

namespace Complex

/-- The beta approximation to the Gamma integrand with a real cutoff. -/
private def gammaRealApprox (s : ℂ) (x : ℝ) : ℝ → ℂ :=
  (Ioo 0 x).indicator (fun t : ℝ => ((1 - t / x) ^ x : ℝ) * (t : ℂ) ^ (s - 1))

/-- A real beta cutoff is bounded by the exponential Gamma weight. -/
private theorem rpow_one_sub_div_le_exp {t x : ℝ} (ht : 0 < t) (htx : t < x) :
    (1 - t / x) ^ x ≤ Real.exp (-t) := by
  have hx : 0 < x := ht.trans htx
  have hp : 0 < 1 - t / x := sub_pos.mpr ((div_lt_one hx).mpr htx)
  rw [Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hp) hx.le
  have he : (1 - t / x - 1) * x = -t := by field_simp; ring
  rwa [he] at h

/-- A pointwise integrable majorant for the real-cutoff Gamma approximation. -/
private theorem norm_gammaRealApprox_le (s : ℂ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖gammaRealApprox s x t‖ ≤ Real.exp (-t) * t ^ (s.re - 1) := by
  by_cases htx : t < x
  · have hbase : 0 ≤ 1 - t / x := sub_nonneg.mpr ((div_le_one (ht.trans htx)).mpr htx.le)
    rw [gammaRealApprox, indicator_of_mem (show t ∈ Ioo (0 : ℝ) x from ⟨ht, htx⟩), norm_mul,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hbase _),
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
    exact mul_le_mul_of_nonneg_right (rpow_one_sub_div_le_exp ht htx) (Real.rpow_nonneg ht.le _)
  · rw [gammaRealApprox, indicator_of_notMem (show t ∉ Ioo (0 : ℝ) x from fun h => htx h.2),
    norm_zero]
    positivity

/-- The real-cutoff beta approximation tends to the Gamma integral. -/
private theorem tendsto_gammaRealApprox_integral {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => ∫ t in Ioi (0 : ℝ), gammaRealApprox s x t) atTop (𝓝 (Gamma s)) := by
  have hmeas (x : ℝ) : AEStronglyMeasurable (gammaRealApprox s x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ioo
    fun_prop
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖gammaRealApprox s x t‖ ≤ Real.exp (-t) * t ^ (s.re - 1) := by
    filter_upwards with x
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact norm_gammaRealApprox_le s x ht
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun x : ℝ => gammaRealApprox s x t) atTop
        (𝓝 ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hh := ((continuous_ofReal.tendsto _).comp
      (Real.tendsto_one_add_div_rpow_exp (-t))).mul_const ((t : ℂ) ^ (s - 1))
    apply hh.congr'
    filter_upwards [eventually_gt_atTop t] with x hx
    simp only [Function.comp_apply, gammaRealApprox,
      indicator_of_mem (show t ∈ Ioo (0 : ℝ) x from ⟨ht, hx⟩),
      neg_div, ← sub_eq_add_neg]
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => Real.exp (-t) * t ^ (s.re - 1)) (Eventually.of_forall hmeas) hbound
    (Real.GammaIntegral_convergent hs) hlim
  simpa only [Gamma_eq_integral hs, GammaIntegral] using h

/-- Rescaling the real-cutoff approximation gives a beta integral. -/
private theorem integral_gammaRealApprox {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), gammaRealApprox s x t) = (x : ℂ) ^ s * betaIntegral s ((x : ℂ) + 1) := by
  rw [gammaRealApprox, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
  have hc := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => (((1 - t / x) ^ x : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
    (a := 0) (b := 1) x
  rw [mul_zero, mul_one] at hc
  rw [← hc, betaIntegral, real_smul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxs : (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * x := by
    conv_lhs => rw [show s = s - 1 + 1 by ring, cpow_add _ _ hxC, cpow_one]
  rw [show x * u / x = u by field_simp, ofReal_cpow (sub_nonneg.mpr hu.2),
    ofReal_mul, mul_cpow_ofReal_nonneg hx.le hu.1.le, hxs,
    show (x : ℂ) + 1 - 1 = x by ring]
  push_cast only [ofReal_sub, ofReal_one]
  ring

/-- A scaled beta integral tends to Gamma as its second parameter tends along the
positive real axis. The cutoff parameter is an arbitrary real number. -/
theorem tendsto_cpow_mul_betaIntegral {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * betaIntegral s ((x : ℂ) + 1))
      atTop (𝓝 (Gamma s)) := by
  apply (tendsto_gammaRealApprox_integral hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact integral_gammaRealApprox hx

/-- Uniform domination of the scaled beta approximants by a real Gamma value. -/
theorem norm_cpow_mul_betaIntegral_le_Gamma_re {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ s * betaIntegral s ((x : ℂ) + 1)‖ ≤ Real.Gamma s.re := by
  rw [← integral_gammaRealApprox hx, Real.Gamma_eq_integral hs]
  apply norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hs)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact norm_gammaRealApprox_le s x ht

/-- Reciprocals of positive real arguments tend to zero after complexification. -/
private theorem tendsto_ofReal_inv :
    Tendsto (fun x : ℝ => (x : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := (continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
  simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using h

/-- A fixed complex additive shift does not change the leading real variable. -/
private theorem tendsto_ofReal_div_add (s : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) / ((x : ℂ) + s)) atTop (𝓝 1) := by
  have h := ((tendsto_ofReal_inv.const_mul s).const_add 1).inv₀ (by simp)
  simp only [mul_zero, add_zero, inv_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  field_simp

/-- Gamma-ratio asymptotics for a shift in the right half-plane. -/
private theorem tendsto_Gamma_normalized_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => Gamma ((x : ℂ) + s) / (Gamma (x : ℂ) * (x : ℂ) ^ s))
      atTop (𝓝 1) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have h := (tendsto_cpow_mul_betaIntegral hs).div_const (Gamma s)
  rw [div_self hG] at h
  have hh := (h.inv₀ one_ne_zero).mul (tendsto_ofReal_div_add s)
  simp only [inv_one, one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxs : 0 < ((x : ℂ) + s).re := by simp only [add_re, ofReal_re]; linarith
  have hxΓ : Gamma (x : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx)
  have hxsΓ : Gamma ((x : ℂ) + s) ≠ 0 := Gamma_ne_zero_of_re_pos hxs
  have hx1 : 0 < ((x : ℂ) + 1).re := by
    simpa only [add_re, ofReal_re, one_re] using add_pos hx zero_lt_one
  rw [betaIntegral_eq_Gamma_mul_div _ _ hs hx1,
    show s + ((x : ℂ) + 1) = ((x : ℂ) + s) + 1 by ring,
    Gamma_add_one _ (ne_zero_of_re_pos hxs), Gamma_add_one _ hxC]
  field_simp [hG, hxΓ, hxsΓ, ne_zero_of_re_pos hxs, cpow_ne_zero_iff.mpr (Or.inl hxC)]

/-- A normalized rising factorial is a product of factors tending to one. -/
private theorem ascPochhammer_ofReal_add (s : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (ascPochhammer ℂ n).eval ((x : ℂ) + s) =
      (x : ℂ) ^ n * ∏ k ∈ Finset.range n, (1 + (s + k) / (x : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ, pow_succ]
    have he : (x : ℂ) + s + n = (x : ℂ) * (1 + (s + n) / (x : ℂ)) := by
      field_simp [ofReal_ne_zero.mpr hx.ne']
      ring
    rw [he]
    ring

/-- **Carlson Theorem 3.4-1 with one zero shift.** The normalized Gamma ratio
tends to one for every fixed complex shift and an arbitrary real variable at infinity. -/
theorem tendsto_Gamma_add_div_Gamma_cpow (s : ℂ) :
    Tendsto (fun x : ℝ => Gamma ((x : ℂ) + s) / (Gamma (x : ℂ) * (x : ℂ) ^ s))
      atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-s.re)
  have hsN : 0 < (s + N).re := by simp only [add_re, natCast_re]; linarith
  let P : ℝ → ℂ := fun x => ∏ k ∈ Finset.range N, (1 + (s + k) / (x : ℂ))
  have hP : Tendsto P atTop (𝓝 1) := by
    have h := tendsto_finsetProd (Finset.range N) (fun k _ =>
      (tendsto_ofReal_inv.const_mul (s + k)).const_add 1)
    simpa only [mul_zero, add_zero, Finset.prod_const_one, div_eq_mul_inv, P] using h
  have H := (tendsto_Gamma_normalized_of_re_pos hsN).mul (hP.inv₀ one_ne_zero)
  simp only [inv_one, mul_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-s.re)),
    hP.eventually (eventually_ne_nhds one_ne_zero)] with x hx hp
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hxs : 0 < ((x : ℂ) + s).re := by
    simp only [add_re, ofReal_re]
    have hx' := (le_max_right _ _).trans_lt hx
    linarith
  have hreg : ∀ k : ℕ, (x : ℂ) + s ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg Complex.re hk
    simp only [add_re, ofReal_re, neg_re, natCast_re] at he
    simp only [add_re, ofReal_re] at hxs
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hΓ : Gamma ((x : ℂ) + s + N) =
      (ascPochhammer ℂ N).eval ((x : ℂ) + s) * Gamma ((x : ℂ) + s) :=
    (div_eq_iff (Gamma_ne_zero hreg)).mp (Gamma_add_nat_div_Gamma_eq _ hreg)
  rw [show (x : ℂ) + (s + N) = (x : ℂ) + s + N by ring, hΓ,
    ascPochhammer_ofReal_add s N hx0, cpow_add _ _ hxC, cpow_natCast]
  change ((x : ℂ) ^ N * P x * Gamma ((x : ℂ) + s)) /
    (Gamma (x : ℂ) * ((x : ℂ) ^ s * (x : ℂ) ^ N)) * (P x)⁻¹ = _
  have hxΓ : Gamma (x : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx0)
  field_simp [hp, hxΓ,
    cpow_ne_zero_iff.mpr (Or.inl hxC)]

/-- **Carlson Theorem 3.4-1.** The Gamma ratio with arbitrary fixed complex
shifts, along a real variable tending to positive infinity. -/
theorem tendsto_Gamma_add_div_Gamma_add_mul_cpow (a b : ℂ) :
    Tendsto (fun x : ℝ => Gamma ((x : ℂ) + a) / Gamma ((x : ℂ) + b) *
      (x : ℂ) ^ (b - a)) atTop (𝓝 1) := by
  have H := (tendsto_Gamma_add_div_Gamma_cpow a).div
    (tendsto_Gamma_add_div_Gamma_cpow b) one_ne_zero
  simp only [div_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-b.re))] with x hx
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hb : 0 < ((x : ℂ) + b).re := by
    simp only [add_re, ofReal_re]
    have hx' := (le_max_right _ _).trans_lt hx
    linarith
  have hxΓ : Gamma (x : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx0)
  simp only [Pi.div_apply]
  rw [cpow_sub _ _ hxC]
  field_simp [hxΓ, Gamma_ne_zero_of_re_pos hb,
    cpow_ne_zero_iff.mpr (Or.inl hxC)]

end Complex
