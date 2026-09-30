/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.ZeroVariable
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic asymptotics of elliptic integrals

For positive real nodes, comparison of the real integral for `R_F` with the
elementary integral `R_C` gives the leading logarithmic asymptotic of Carlson
(9.2-10). The comparison uses monotonicity in the nodes, so it does not require
the general hypergeometric connection formula. Zero-variable duplication and
positive homogeneity then give the complete-integral equivalent (8.3-16) as
the second node tends to zero through positive reals.

## Main results

* `carlsonRF_re_antitone`: comparison on positive real node triples.
* `isEquivalent_carlsonRF_atTop`: (9.2-10) for fixed positive first two nodes.
* `isEquivalent_carlsonRK_zero`: (8.3-16) for a fixed positive first node.
* `tendsto_carlsonRF_re_mul_sqrt_div_log`, `tendsto_carlsonRK_re_div_log`:
  the normalized logarithmic limits.

These equivalents do not assert the constant term of an additive expansion.
The full logarithmic series and complex-sector extension remain separate work.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, §§8.3 and 9.2.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-- On positive real nodes `R_F` is the real half-line integral. -/
theorem carlsonRF_ofReal_eq_integral {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) :
    carlsonRF x y z = ((1 / 2 * ∫ t in Ioi 0, rfKernel x y z t : ℝ) : ℂ) := by
  simpa using carlsonRF_add_eq_integral hx hy hz (l := 0) le_rfl

/-- Increasing positive real nodes decreases the real value of `R_F`. -/
theorem carlsonRF_re_antitone {x y z X Y Z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hX : x ≤ X) (hY : y ≤ Y) (hZ : z ≤ Z) :
    (carlsonRF X Y Z).re ≤ (carlsonRF x y z).re := by
  rw [carlsonRF_ofReal_eq_integral (hx.trans_le hX) (hy.trans_le hY) (hz.trans_le hZ),
    carlsonRF_ofReal_eq_integral hx hy hz]
  simp only [ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_on (integrableOn_rfKernel (hx.trans_le hX) (hy.trans_le hY)
    (hz.trans_le hZ)) (integrableOn_rfKernel hx hy hz) measurableSet_Ioi
  intro t ht
  have ht : 0 < t := ht
  apply inv_anti₀ (Real.sqrt_pos.mpr (rfCubic_pos hx hy hz ht.le))
  apply Real.sqrt_le_sqrt
  unfold rfCubic
  have hX0 : 0 < X := hx.trans_le hX
  have hY0 : 0 < Y := hy.trans_le hY
  gcongr

/-- The square-root ratio used in the elementary logarithmic comparison tends to one. -/
private theorem tendsto_sqrt_sub_div_sqrt (y : ℝ) :
    Tendsto (fun z : ℝ => √(z - y) / √z) atTop (𝓝 1) := by
  have h : Tendsto (fun z : ℝ => 1 - y / z) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := y)).div_atTop (tendsto_id : Tendsto (fun z : ℝ => z) atTop atTop))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simp only [Real.sqrt_one] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (max y 0)] with z hz
  have hz0 : 0 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hzy : y < z := lt_of_le_of_lt (le_max_left _ _) hz
  dsimp only [Function.comp_def]
  rw [show 1 - y / z = (z - y) / z by field_simp,
    Real.sqrt_div (sub_nonneg.mpr hzy.le)]

/-- For fixed positive `y`, `sqrt z R_C(z,y) / log z` tends to `1/2`. -/
theorem tendsto_carlsonRC_re_mul_sqrt_div_log {y : ℝ} (hy : 0 < y) :
    Tendsto (fun z : ℝ => (TwoVariable.carlsonRC z y).re * √z / Real.log z)
      atTop (𝓝 (1 / 2)) := by
  have hr := tendsto_sqrt_sub_div_sqrt y
  have hlog : Tendsto (fun z : ℝ => Real.log ((1 + √(z - y) / √z) / √y))
      atTop (𝓝 (Real.log (2 / √y))) := by
    apply (Real.continuousAt_log (by positivity : (2 / √y : ℝ) ≠ 0)).tendsto.comp
    convert (tendsto_const_nhds.add hr).div_const (√y) using 1
    norm_num
  have hsmall := hlog.div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto (fun z : ℝ =>
      (1 / 2 + Real.log ((1 + √(z - y) / √z) / √y) / Real.log z) /
        (√(z - y) / √z)) atTop (𝓝 (1 / 2)) := by
    convert (tendsto_const_nhds.add hsmall).div hr one_ne_zero using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (max y 1)] with z hz
  have hz1 : 1 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz0 : 0 < z := zero_lt_one.trans hz1
  have hzy : y < z := lt_of_le_of_lt (le_max_left _ _) hz
  have hs : √z ≠ 0 := (Real.sqrt_pos.mpr hz0).ne'
  have hsy : √y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsd : √(z - y) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hzy)).ne'
  have hl : Real.log z ≠ 0 := (Real.log_pos hz1).ne'
  rw [TwoVariable.carlsonRC_of_gt hy hzy, ofReal_re]
  have he : (√z + √(z - y)) / √y = √z * ((1 + √(z - y) / √z) / √y) := by
    field_simp
  rw [he, Real.log_mul hs (by positivity), Real.log_sqrt hz0.le]
  field_simp

/-- For fixed positive `x,y`, `sqrt z R_F(x,y,z) / log z` tends to `1/2`. -/
theorem tendsto_carlsonRF_re_mul_sqrt_div_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun z : ℝ => (carlsonRF x y z).re * √z / Real.log z)
      atTop (𝓝 (1 / 2)) := by
  have hmin : 0 < min x y := lt_min hx hy
  have hmax : 0 < max x y := hx.trans_le (le_max_left _ _)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_carlsonRC_re_mul_sqrt_div_log hmax)
    (tendsto_carlsonRC_re_mul_sqrt_div_log hmin)
  all_goals
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    have hz0 : 0 < z := zero_lt_one.trans hz
    have he (u : ℝ) (hu : 0 < u) :
        TwoVariable.carlsonRC z u = carlsonRF u u z := by
      rw [← carlsonRF_self_right (ofReal_mem_slitPlane.mpr hz0) (ofReal_mem_slitPlane.mpr hu),
        carlsonRF_comm_left (ofReal_mem_slitPlane.mpr hu) (ofReal_mem_slitPlane.mpr hz0)
          (ofReal_mem_slitPlane.mpr hu),
        carlsonRF_comm_right (ofReal_mem_slitPlane.mpr hu) (ofReal_mem_slitPlane.mpr hu)
          (ofReal_mem_slitPlane.mpr hz0)]
    first
    | rw [he _ hmax]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (carlsonRF_re_antitone hx hy hz0 (le_max_left _ _) (le_max_right _ _) le_rfl)
        (Real.sqrt_nonneg _)) (Real.log_pos hz).le
    | rw [he _ hmin]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (carlsonRF_re_antitone hmin hmin hz0 (min_le_left _ _) (min_le_right _ _) le_rfl)
        (Real.sqrt_nonneg _)) (Real.log_pos hz).le

/-- Multiplying the square-root argument of a logarithm by a positive constant does not
change its leading ratio to `log z`. -/
private theorem tendsto_log_mul_sqrt_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℝ => Real.log (c * √z) / Real.log z) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun z : ℝ => Real.log c / Real.log z + 1 / 2) atTop (𝓝 (1 / 2)) := by
    simpa using ((tendsto_const_nhds (x := Real.log c)).div_atTop
      Real.tendsto_log_atTop).add_const (1 / 2 : ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  rw [Real.log_mul hc.ne' (Real.sqrt_pos.mpr (zero_lt_one.trans hz)).ne',
    Real.log_sqrt (zero_lt_one.trans hz).le]
  field_simp [(Real.log_pos hz).ne']

/-- **Carlson's (9.2-10)** for fixed positive `x,y`: as `z → ∞`,
`R_F(x,y,z) ∼ log(4 sqrt z / (sqrt x + sqrt y)) / sqrt z`.
This is an asymptotic equivalent, not an assertion about the additive constant in
`sqrt z R_F(x,y,z) - log(sqrt z)`. -/
theorem isEquivalent_carlsonRF_atTop {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Asymptotics.IsEquivalent atTop (fun z : ℝ => carlsonRF x y z)
      (fun z : ℝ => ((Real.log (4 * √z / (√x + √y)) / √z : ℝ) : ℂ)) := by
  have hc : 0 < 4 / (√x + √y) := by positivity
  have hlog := tendsto_log_mul_sqrt_div_log hc
  have h := (tendsto_carlsonRF_re_mul_sqrt_div_log hx hy).div hlog
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simp only [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
  have hr : Tendsto (fun z : ℝ => (carlsonRF x y z).re /
      (Real.log (4 * √z / (√x + √y)) / √z)) atTop (𝓝 1) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    simp only [Pi.div_apply]
    rw [div_mul_eq_mul_div]
    field_simp [(Real.log_pos hz).ne', (Real.sqrt_pos.mpr (zero_lt_one.trans hz)).ne']
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hcomplex := (continuous_ofReal.tendsto (1 : ℝ)).comp hr
  simp only [ofReal_one] at hcomplex
  apply hcomplex.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  simp only [Function.comp_def, Pi.div_apply, ofReal_div]
  rw [carlsonRF_ofReal_eq_integral hx hy hz, ofReal_re]

/-- The normalized `R_F` limit is unchanged when its large argument is translated by one. -/
private theorem tendsto_carlsonRF_re_add_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun t : ℝ => (carlsonRF x y ((t + 1 : ℝ) : ℂ)).re * √t / Real.log t)
      atTop (𝓝 (1 / 2)) := by
  have ht : Tendsto (fun t : ℝ => t + 1) atTop atTop :=
    tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hs : Tendsto (fun t : ℝ => √t / √(t + 1)) atTop (𝓝 1) := by
    simpa [sub_neg_eq_add] using (tendsto_sqrt_sub_div_sqrt (-1)).inv₀ one_ne_zero
  have hl : Tendsto (fun t : ℝ => Real.log (t + 1) / Real.log t) atTop (𝓝 1) := by
    have h := ((Real.tendsto_log_comp_add_sub_log 1).div_atTop Real.tendsto_log_atTop).add_const
      (1 : ℝ)
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    field_simp [(Real.log_pos ht).ne']
    ring
  have h := (((tendsto_carlsonRF_re_mul_sqrt_div_log hx hy).comp ht).mul hs).mul hl
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  dsimp only [Function.comp_def]
  field_simp [(Real.sqrt_pos.mpr (show 0 < t + 1 by linarith)).ne',
    (Real.log_pos (show 1 < t + 1 by linarith)).ne']

/-- A specialization of zero-variable duplication and homogeneity, with all factors real. -/
theorem carlsonRK_sq_one_eq_rf {t : ℝ} (ht : 0 < t) :
    TwoVariable.carlsonRK ((t ^ 2 : ℝ) : ℂ) 1 =
      ((4 / (π * √t) : ℝ) : ℂ) * carlsonRF 1 ((1 + 1 / t : ℝ) : ℂ) ((t + 1 : ℝ) : ℂ) := by
  have hsl (r : ℝ) (hr : 0 < r) : (r : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hr
  have ht1 : 0 < t + 1 := by positivity
  have hi : 0 < 1 + 1 / t := by positivity
  have hd := carlsonRK_duplication_ofReal (pow_pos ht 2) zero_lt_one
  rw [Real.sqrt_sq ht.le, Real.sqrt_one, mul_one, ofReal_one] at hd
  have hm := carlsonRF_mul_of_pos ht (hsl (t + 1) ht1) (hsl (1 + 1 / t) hi) (hsl 1 zero_lt_one)
  have hp : (t : ℂ) ^ (-1 / 2 : ℂ) = (((√t)⁻¹ : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow ht.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  have h1 : (t : ℂ) * (t + 1 : ℝ) = ((t ^ 2 + t : ℝ) : ℂ) := by push_cast; ring
  have h2 : (t : ℂ) * (1 + 1 / t : ℝ) = ((1 + t : ℝ) : ℂ) := by
    push_cast
    field_simp [ofReal_ne_zero.mpr ht.ne']
    ring
  rw [h1, h2, ofReal_one, mul_one, hp] at hm
  have hone : (1 : ℂ) ∈ slitPlane := by simp
  rw [hm, carlsonRF_comm_left (hsl (1 + 1 / t) hi) (hsl (t + 1) ht1) hone,
    carlsonRF_comm_right (hsl (1 + 1 / t) hi) hone (hsl (t + 1) ht1),
    carlsonRF_comm_left hone (hsl (1 + 1 / t) hi) (hsl (t + 1) ht1)] at hd
  push_cast at hd ⊢
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (√t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  field_simp at hd ⊢
  linear_combination hd

/-- The complete elliptic integral has logarithmic growth:
`t R_K(t²,1) / log t → 2/π` along positive real `t → ∞`. -/
theorem tendsto_carlsonRK_sq_one_re_mul_div_log :
    Tendsto (fun t : ℝ => (TwoVariable.carlsonRK ((t ^ 2 : ℝ) : ℂ) 1).re * t / Real.log t)
      atTop (𝓝 (2 / π)) := by
  have h : Tendsto (fun t : ℝ =>
      (carlsonRF 1 ((1 + 1 / t : ℝ) : ℂ) ((t + 1 : ℝ) : ℂ)).re * √t / Real.log t)
      atTop (𝓝 (1 / 2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_carlsonRF_re_add_one (x := 1) (y := 2) (by norm_num) (by norm_num))
      (tendsto_carlsonRF_re_add_one (x := 1) (y := 1) (by norm_num) (by norm_num))
    all_goals
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hi : 0 < 1 + 1 / t := by positivity
      have hi1 : 1 ≤ 1 + 1 / t := by linarith [one_div_pos.mpr ht0]
      have hi2 : 1 + 1 / t ≤ 2 := by
        have h : 1 / t ≤ (1 : ℝ) := (one_div_le_one_div_of_le zero_lt_one ht.le).trans_eq (by norm_num)
        linarith
      apply div_le_div_of_nonneg_right _ (Real.log_pos ht).le
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      first
      | simpa only [ofReal_one, ofReal_ofNat] using
          (carlsonRF_re_antitone (x := 1) (X := 1) (y := 1 + 1 / t) (Y := 2)
            (z := t + 1) (Z := t + 1) zero_lt_one hi (by positivity) le_rfl hi2 le_rfl)
      | simpa only [ofReal_one] using
          (carlsonRF_re_antitone (x := 1) (X := 1) (y := 1) (Y := 1 + 1 / t)
            (z := t + 1) (Z := t + 1) zero_lt_one zero_lt_one (by positivity) le_rfl hi1 le_rfl)
  have hlim := h.const_mul (4 / π)
  have he : (4 / π : ℝ) * (1 / 2) = 2 / π := by ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [carlsonRK_sq_one_eq_rf ht, re_ofReal_mul]
  have hs := Real.sq_sqrt ht.le
  field_simp
  rw [hs]
  ring

/-- The complete elliptic integral has real values at positive real nodes. -/
theorem ofReal_re_carlsonRK {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((TwoVariable.carlsonRK x y).re : ℂ) = TwoVariable.carlsonRK x y := by
  have hd := carlsonRK_duplication_ofReal hx hy
  rw [carlsonRF_ofReal_eq_integral (by positivity) (by positivity) (by positivity)] at hd
  have hi := congrArg Complex.im hd
  simp only [mul_im, div_ofNat_re, ofReal_re, ofReal_im, div_ofNat_im, zero_div,
    zero_mul, zero_add, mul_zero, add_zero] at hi
  norm_num at hi
  apply Complex.ext
  · simp
  · simp only [ofReal_im]
    nlinarith [Real.pi_pos]

/-- `sqrt z R_K(z,1) / log z → 1/π` as `z → ∞` on the real axis. -/
theorem tendsto_carlsonRK_re_mul_sqrt_div_log_one :
    Tendsto (fun z : ℝ => (TwoVariable.carlsonRK z 1).re * √z / Real.log z)
      atTop (𝓝 (1 / π)) := by
  have h := (tendsto_carlsonRK_sq_one_re_mul_div_log.comp Real.tendsto_sqrt_atTop).div_const 2
  have he : (2 / π : ℝ) / 2 = 1 / π := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  dsimp only [Function.comp_def]
  rw [Real.sq_sqrt (zero_lt_one.trans hz).le, Real.log_sqrt (zero_lt_one.trans hz).le]
  ring

/-- Scaling relates the small positive variable of `R_K(1,y)` to a large variable. -/
theorem carlsonRK_one_eq_inv_sqrt_mul {y : ℝ} (hy : 0 < y) :
    TwoVariable.carlsonRK 1 y = (((√y)⁻¹ : ℝ) : ℂ) * TwoVariable.carlsonRK ((y⁻¹ : ℝ) : ℂ) 1 := by
  have h := carlsonRK_mul_of_pos hy (x := ((y⁻¹ : ℝ) : ℂ)) (y := 1)
    (ofReal_mem_slitPlane.mpr (inv_pos.mpr hy)) (by simp)
  rw [ofReal_inv, mul_inv_cancel₀ (ofReal_ne_zero.mpr hy.ne'), mul_one] at h
  rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num,
    ← ofReal_cpow hy.le, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow] at h
  simpa only [ofReal_inv] using h

/-- The logarithmic singularity at zero: `R_K(1,y) / log(1/y) → 1/π`
as `y → 0` through positive reals. -/
theorem tendsto_carlsonRK_one_re_div_log_inv :
    Tendsto (fun y : ℝ => (TwoVariable.carlsonRK 1 y).re / Real.log (y⁻¹))
      (𝓝[>] 0) (𝓝 (1 / π)) := by
  have h := tendsto_carlsonRK_re_mul_sqrt_div_log_one.comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  dsimp only [Function.comp_def]
  rw [carlsonRK_one_eq_inv_sqrt_mul hy, re_ofReal_mul, Real.sqrt_inv]
  ring

/-- For fixed positive `x`, the logarithmic coefficient of `R_K(x,y)` at `y=0`
is `1/(π sqrt x)`. -/
theorem tendsto_carlsonRK_re_div_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (TwoVariable.carlsonRK x y).re / Real.log (x / y))
      (𝓝[>] 0) (𝓝 (1 / (π * √x))) := by
  have hm : Tendsto (fun y : ℝ => y / x) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)).mono_right
        nhdsWithin_le_nhds).div_const x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
      exact div_pos hy hx
  have h := (tendsto_carlsonRK_one_re_div_log_inv.comp hm).const_mul (√x)⁻¹
  have he : (√x)⁻¹ * (1 / π) = 1 / (π * √x) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  have hmul := carlsonRK_mul_of_pos hx (x := 1) (y := ((y / x : ℝ) : ℂ)) (by simp)
    (ofReal_mem_slitPlane.mpr (div_pos hy hx))
  have hxy : (x : ℂ) * ((y / x : ℝ) : ℂ) = y := by
    push_cast
    field_simp [ofReal_ne_zero.mpr hx.ne']
  rw [mul_one, hxy, show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num,
    ← ofReal_cpow hx.le, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow] at hmul
  dsimp only [Function.comp_def]
  rw [hmul, re_ofReal_mul, inv_div]
  ring

/-- Multiplying `x/y` by 16 inside its logarithm does not change the leading singularity. -/
private theorem tendsto_log_sixteen_div_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => Real.log (16 * x / y) / Real.log (x / y))
      (𝓝[>] 0) (𝓝 1) := by
  have hxy : Tendsto (fun y : ℝ => x / y) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hx
  have h := ((tendsto_const_nhds (x := Real.log 16)).div_atTop
    (Real.tendsto_log_atTop.comp hxy)).add_const (1 : ℝ)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds]
    with y (hy : 0 < y) hyx
  have hlog : Real.log (x / y) ≠ 0 := (Real.log_pos ((one_lt_div hy).mpr hyx)).ne'
  rw [show 16 * x / y = 16 * (x / y) by ring,
    Real.log_mul (by norm_num) (div_pos hx hy).ne']
  dsimp only [Function.comp_def]
  field_simp

/-- **Carlson's (8.3-16)** on the positive real axis: for fixed `x > 0`,
`R_K(x,y) ∼ log(16x/y)/(π sqrt x)` as `y → 0+`.
The full logarithmic series and complex-sector version are separate statements. -/
theorem isEquivalent_carlsonRK_zero {x : ℝ} (hx : 0 < x) :
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun y : ℝ => TwoVariable.carlsonRK x y)
      (fun y : ℝ => ((Real.log (16 * x / y) / (π * √x) : ℝ) : ℂ)) := by
  have hc : (1 / (π * √x) : ℝ) ≠ 0 := by positivity
  have h := (tendsto_carlsonRK_re_div_log hx).div
    ((tendsto_log_sixteen_div_log hx).div_const (π * √x)) hc
  simp only [div_self hc] at h
  have hr : Tendsto (fun y : ℝ => (TwoVariable.carlsonRK x y).re /
      (Real.log (16 * x / y) / (π * √x))) (𝓝[>] 0) (𝓝 1) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds]
      with y (hy : 0 < y) hyx
    have hlog : Real.log (x / y) ≠ 0 := (Real.log_pos ((one_lt_div hy).mpr hyx)).ne'
    simp only [Pi.div_apply]
    field_simp
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hcomplex := (continuous_ofReal.tendsto (1 : ℝ)).comp hr
  simp only [ofReal_one] at hcomplex
  apply hcomplex.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [Function.comp_def, Pi.div_apply, ofReal_div, ofReal_re_carlsonRK hx hy]

end Carlson
