/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The positive-power beta kernel

The kernel `K * u^a * (1-u)^b`, for positive `K`, `a`, and `b`, is strictly
increasing up to `a / (a+b)` and strictly decreasing afterwards. Its level-one
crossings provide the sign pattern needed for comparisons of beta densities.
-/

open Set
public noncomputable section
namespace Real

/-- The derivative of the positive-power beta kernel inside the unit interval. -/
theorem hasDerivAt_betaKernel (K a b : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v : ℝ ↦ K * v ^ a * (1 - v) ^ b)
      (K * u ^ a * (1 - u) ^ b * (a / u - b / (1 - u))) u := by
  have h1 : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  have h := ((hasDerivAt_rpow_const (p := a) (Or.inl hu.1.ne')).const_mul K).mul
    (((hasDerivAt_id u).const_sub 1).rpow_const (p := b) (Or.inl h1))
  convert h using 1
  · rfl
  · simp only [id_eq, Real.rpow_sub hu.1, Real.rpow_sub (sub_pos.mpr hu.2), Real.rpow_one]
    field_simp
    ring

/-- The positive-power beta kernel is strictly increasing to its unique maximum. -/
theorem strictMonoOn_betaKernel {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (fun u : ℝ ↦ K * u ^ a * (1 - u) ^ b) (Icc 0 (a / (a + b))) := by
  have hm0 : 0 < a / (a + b) := div_pos ha (add_pos ha hb)
  have hm1 : a / (a + b) < 1 := (div_lt_one (add_pos ha hb)).mpr (by linarith)
  apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    ((continuous_const.mul (continuous_rpow_const ha.le)).mul
      ((continuous_rpow_const hb.le).comp (continuous_const.sub continuous_id))).continuousOn
  rw [interior_Icc]
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hm1⟩
  change 0 < deriv (fun v : ℝ ↦ K * v ^ a * (1 - v) ^ b) u
  rw [(hasDerivAt_betaKernel K a b hu').deriv]
  apply mul_pos (mul_pos (mul_pos hK (rpow_pos_of_pos hu.1 _))
    (rpow_pos_of_pos (sub_pos.mpr hu'.2) _))
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (sub_pos.mpr hu'.2) hu.1).mpr
  have h := (lt_div_iff₀ (add_pos ha hb)).mp hu.2
  nlinarith

/-- The positive-power beta kernel is strictly decreasing after its unique maximum. -/
theorem strictAntiOn_betaKernel {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : 0 < b) :
    StrictAntiOn (fun u : ℝ ↦ K * u ^ a * (1 - u) ^ b) (Icc (a / (a + b)) 1) := by
  have hm0 : 0 < a / (a + b) := div_pos ha (add_pos ha hb)
  apply strictAntiOn_of_deriv_neg (convex_Icc ..)
    ((continuous_const.mul (continuous_rpow_const ha.le)).mul
      ((continuous_rpow_const hb.le).comp (continuous_const.sub continuous_id))).continuousOn
  rw [interior_Icc]
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hm0.trans hu.1, hu.2⟩
  change deriv (fun v : ℝ ↦ K * v ^ a * (1 - v) ^ b) u < 0
  rw [(hasDerivAt_betaKernel K a b hu').deriv]
  apply mul_neg_of_pos_of_neg (mul_pos (mul_pos hK (rpow_pos_of_pos hu'.1 _))
    (rpow_pos_of_pos (sub_pos.mpr hu.2) _))
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ hu'.1 (sub_pos.mpr hu.2)).mpr
  have h := (div_lt_iff₀ (add_pos ha hb)).mp hu.1
  nlinarith

/-- If the beta kernel's maximum exceeds one, it has exactly two level-one crossings,
with positive excess between them and negative excess outside. -/
theorem exists_betaKernel_crossings {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : 0 < b)
    (hmax : 1 < K * (a / (a + b)) ^ a * (1 - a / (a + b)) ^ b) :
    ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < 1 ∧
      (∀ u ∈ Ioo l r, 1 < K * u ^ a * (1 - u) ^ b) ∧
      (∀ u ∈ Ioo (0 : ℝ) 1, u < l ∨ r < u → K * u ^ a * (1 - u) ^ b < 1) := by
  let f := fun u : ℝ ↦ K * u ^ a * (1 - u) ^ b
  let m := a / (a + b)
  have hm0 : 0 < m := div_pos ha (add_pos ha hb)
  have hm1 : m < 1 := (div_lt_one (add_pos ha hb)).mpr (by linarith)
  have hf : Continuous f := (continuous_const.mul (continuous_rpow_const ha.le)).mul
    ((continuous_rpow_const hb.le).comp (continuous_const.sub continuous_id))
  have hf0 : f 0 = 0 := by simp [f, zero_rpow ha.ne']
  have hf1 : f 1 = 0 := by simp [f, zero_rpow hb.ne']
  have hfm : 1 < f m := hmax
  obtain ⟨l, hl, hfl⟩ := intermediate_value_Icc hm0.le hf.continuousOn
    (show 1 ∈ Icc (f 0) (f m) by rw [hf0]; exact ⟨zero_le_one, hfm.le⟩)
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' hm1.le hf.continuousOn
    (show 1 ∈ Icc (f 1) (f m) by rw [hf1]; exact ⟨zero_le_one, hfm.le⟩)
  have hl0 : 0 < l := hl.1.lt_of_ne (by intro he; subst l; simp [hf0] at hfl)
  have hlm : l < m := hl.2.lt_of_ne (by intro he; rw [he] at hfl; linarith)
  have hmr : m < r := hr.1.lt_of_ne (by intro he; rw [← he] at hfr; linarith)
  have hr1 : r < 1 := hr.2.lt_of_ne (by intro he; rw [he, hf1] at hfr; norm_num at hfr)
  have hmono := strictMonoOn_betaKernel hK ha hb
  have hanti := strictAntiOn_betaKernel hK ha hb
  refine ⟨l, r, hl0, hlm.trans hmr, hr1, ?_, ?_⟩
  · intro u hu
    rcases le_total u m with hum | hmu
    · have h := hmono hl ⟨hl0.le.trans hu.1.le, hum⟩ hu.1
      change f l < f u at h
      rwa [hfl] at h
    · have h := hanti ⟨hmu, hu.2.le.trans hr1.le⟩ hr hu.2
      change f r < f u at h
      rwa [hfr] at h
  · intro u hu hout
    rcases hout with hul | hru
    · have h := hmono ⟨hu.1.le, hul.le.trans hl.2⟩ hl hul
      change f u < f l at h
      rwa [hfl] at h
    · have h := hanti hr ⟨hr.1.trans hru.le, hu.2.le⟩ hru
      change f u < f r at h
      rwa [hfr] at h

end Real
