/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.ChapterNineExercises
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Linear independence of `R_H` (part of Carlson's Theorem 9.2-1)

For fixed positive `x, y, z`, the representation (9.2-3) and the substitution `t = ρs` give
`√ρ R_H(x, y, z, ρ) → (3/4) ∫₀^∞ s^{-1/2} (1 + s)⁻¹ ds > 0` as `ρ → ∞` (dominated convergence).
A function with this half-integral power behaviour is not a rational function of `ρ`, so in any
relation `p₀ (xyz)^{-1/2} + p₁ R_F + p₂ R_G + p₃ R_H = 0` with coefficients polynomial in `ρ`, the
coefficient `p₃` vanishes. The independence of `(xyz)^{-1/2}`, `R_F`, `R_G` among themselves (the
rest of Theorem 9.2-1) is not formalized; Carlson's argument from the leading asymptotics (9.2-7),
(9.2-10) needs the full logarithmic expansions to be made rigorous.

## Main results

* `Carlson.tendsto_sqrt_mul_carlsonRH`: `√ρ R_H(x, y, z, ρ)` has a nonzero limit.
* `Carlson.eq_zero_of_mul_eq_eval`: such a function is not rational in `ρ`.
* `Carlson.coeff_carlsonRH_eq_zero`: the `R_H` part of Theorem 9.2-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.2.
-/

open Complex MeasureTheory Set Filter Polynomial
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

/-- The bound `s^{-1/2} (1 + s)⁻¹`, integrable on the positive ray. -/
private def hBound (s : ℝ) : ℝ := (Real.sqrt s)⁻¹ * (1 + s)⁻¹

private theorem continuousOn_hBound : ContinuousOn hBound (Ioi 0) := by
  intro s hs
  have hs : 0 < s := hs
  have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  exact (ContinuousAt.mul (continuousAt_inv₀ this.ne' |>.comp
    Real.continuous_sqrt.continuousAt) (continuousAt_inv₀ (by linarith : (1 + s) ≠ 0) |>.comp
      (continuousAt_const.add continuousAt_id))).continuousWithinAt

private theorem integrableOn_hBound : IntegrableOn hBound (Ioi 0) := by
  have h1 : IntegrableOn hBound (Ioc 0 1) := by
    have hr0 : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by norm_num)
    have hr : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) (Ioc 0 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hr0
    refine hr.mono' ((continuousOn_hBound.mono fun s hs => hs.1).aestronglyMeasurable
      measurableSet_Ioc) ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_of_nonneg (by unfold hBound; positivity), Real.rpow_neg hs0.le,
      ← Real.sqrt_eq_rpow]
    unfold hBound
    have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have h2 : IntegrableOn hBound (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1) one_pos).mono'
      ((continuousOn_hBound.mono fun s (hs : 1 < s) => (by
        show (0 : ℝ) < s; linarith)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 1 < s) => ?_)
    have hs0 : 0 < s := by linarith
    have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    rw [Real.norm_of_nonneg (by unfold hBound; positivity), Real.rpow_neg hs0.le,
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    unfold hBound
    rw [← mul_inv, mul_comm]
    exact inv_anti₀ (by positivity) (by nlinarith)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

/-- `(c + t)^{-1/2} = 1/√(c + t)` for `c + t > 0`. -/
private theorem cpow_neg_half_eq' {c t : ℝ} (h : 0 < c + t) :
    ((c : ℂ) + t) ^ (-1 / 2 : ℂ) = ((1 / Real.sqrt (c + t) : ℝ) : ℂ) := by
  rw [show (c : ℂ) + t = ((c + t : ℝ) : ℂ) by push_cast; ring,
    show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h.le,
    Real.rpow_neg h.le, ← Real.sqrt_eq_rpow, one_div]

/-- The real integrand of `R_H` on the positive ray. -/
private def hKernel (x y z ρ t : ℝ) : ℝ :=
  t / (Real.sqrt (x + t) * Real.sqrt (y + t) * Real.sqrt (z + t) * (ρ + t))

/-- `R_H(x, y, z, ρ) = (3/4) ∫₀^∞ t [(t + x)(t + y)(t + z)]^{-1/2} (t + ρ)⁻¹ dt` for positive
real arguments. -/
private theorem carlsonRH_eq_real_integral {x y z ρ : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hρ : 0 < ρ) :
    carlsonRH x y z ρ = 3 / 4 * ((∫ t in Ioi (0 : ℝ), hKernel x y z ρ t : ℝ) : ℂ) := by
  have h := carlsonRH_add_eq_integral (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hρ)
    (le_refl (0 : ℝ))
  simp only [ofReal_zero, add_zero] at h
  rw [h, ← integral_complex_ofReal]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := ht
  rw [cpow_neg_half_eq' (by linarith), cpow_neg_half_eq' (by linarith),
    cpow_neg_half_eq' (by linarith), cpow_neg_one]
  simp only [hKernel, sub_zero]
  have h1 : 0 < Real.sqrt (x + t) := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.sqrt (y + t) := Real.sqrt_pos.mpr (by linarith)
  have h3 : 0 < Real.sqrt (z + t) := Real.sqrt_pos.mpr (by linarith)
  have h4 : (ρ : ℂ) + t ≠ 0 := by
    rw [show (ρ : ℂ) + t = ((ρ + t : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by linarith)
  push_cast
  field_simp

/-- **Theorem 9.2-1, analytic input**: for fixed `x, y, z > 0`,
`√ρ R_H(x, y, z, ρ) → (3/4) ∫₀^∞ s^{-1/2} (1 + s)⁻¹ ds > 0` as `ρ → ∞`. -/
theorem tendsto_sqrt_mul_carlsonRH {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun ρ : ℝ => (Real.sqrt ρ : ℂ) * carlsonRH x y z ρ) atTop (𝓝 L) := by
  set G : ℝ → ℝ → ℝ := fun ρ s =>
    s / (Real.sqrt (x / ρ + s) * Real.sqrt (y / ρ + s) * Real.sqrt (z / ρ + s) * (1 + s))
  -- the substitution `t = ρ s`
  have hsub : ∀ ρ : ℝ, 0 < ρ →
      Real.sqrt ρ * ∫ t in Ioi (0 : ℝ), hKernel x y z ρ t = ∫ s in Ioi (0 : ℝ), G ρ s := by
    intro ρ hρ
    have hc := integral_comp_mul_left_Ioi (hKernel x y z ρ) 0 hρ
    rw [mul_zero, smul_eq_mul] at hc
    rw [show ∫ t in Ioi (0 : ℝ), hKernel x y z ρ t =
        ρ * ∫ s in Ioi (0 : ℝ), hKernel x y z ρ (ρ * s) by rw [hc]; field_simp,
      ← mul_assoc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs : 0 < s := hs
    have hq := Real.sqrt_pos.mpr hρ
    have e : ∀ c : ℝ, 0 < c → Real.sqrt (c + ρ * s) = Real.sqrt ρ * Real.sqrt (c / ρ + s) :=
      fun c hc => by
        rw [← Real.sqrt_mul hρ.le, show ρ * (c / ρ + s) = c + ρ * s by field_simp]
    simp only [hKernel, G]
    rw [e x hx, e y hy, e z hz, show ρ + ρ * s = ρ * (1 + s) by ring]
    have : 0 < Real.sqrt (x / ρ + s) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (y / ρ + s) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (z / ρ + s) := Real.sqrt_pos.mpr (by positivity)
    have hρs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
    field_simp
    linarith [hρs]
  -- dominated convergence
  have hlim : Tendsto (fun ρ => ∫ s in Ioi (0 : ℝ), G ρ s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), hBound s)) := by
    refine tendsto_integral_filter_of_dominated_convergence hBound ?_ ?_ integrableOn_hBound ?_
    · filter_upwards [eventually_gt_atTop 0] with ρ hρ
      refine ContinuousOn.aestronglyMeasurable (fun s (hs : 0 < s) => ?_) measurableSet_Ioi
      have : 0 < Real.sqrt (x / ρ + s) := Real.sqrt_pos.mpr (by positivity)
      have : 0 < Real.sqrt (y / ρ + s) := Real.sqrt_pos.mpr (by positivity)
      have : 0 < Real.sqrt (z / ρ + s) := Real.sqrt_pos.mpr (by positivity)
      exact (continuousAt_id.div (by fun_prop) (by positivity)).continuousWithinAt
    · filter_upwards [eventually_gt_atTop 0] with ρ hρ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      have hq := Real.sqrt_pos.mpr hs
      have le : ∀ c : ℝ, 0 < c → Real.sqrt s ≤ Real.sqrt (c / ρ + s) := fun c hc =>
        Real.sqrt_le_sqrt (by have := div_pos hc hρ; linarith)
      rw [Real.norm_of_nonneg (by simp only [G]; positivity)]
      simp only [G, hBound]
      have hss : s = Real.sqrt s ^ 2 := (Real.sq_sqrt hs.le).symm
      calc s / (Real.sqrt (x / ρ + s) * Real.sqrt (y / ρ + s) * Real.sqrt (z / ρ + s) * (1 + s))
          ≤ s / (Real.sqrt s * Real.sqrt s * Real.sqrt s * (1 + s)) := by
            gcongr
            · have := div_pos hx hρ; linarith
            · have := div_pos hy hρ; linarith
            · have := div_pos hz hρ; linarith
        _ = (Real.sqrt s)⁻¹ * (1 + s)⁻¹ := by
            rw [Real.mul_self_sqrt hs.le]; field_simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      have hq := Real.sqrt_pos.mpr hs
      have hc : ∀ c : ℝ, Tendsto (fun ρ : ℝ => Real.sqrt (c / ρ + s)) atTop
          (𝓝 (Real.sqrt s)) := fun c => by
        have := ((tendsto_const_nhds (x := c)).div_atTop tendsto_id).add_const s
        have h2 := (Real.continuous_sqrt.tendsto _).comp this
        simpa [Function.comp_def] using h2
      have := (tendsto_const_nhds (x := s)).div ((((hc x).mul (hc y)).mul (hc z)).mul
        (tendsto_const_nhds (x := 1 + s))) (by positivity)
      refine this.congr' (Eventually.of_forall fun ρ => rfl) |>.trans ?_
      apply le_of_eq
      simp only [hBound]
      rw [Real.mul_self_sqrt hs.le]; field_simp
  -- the limit is positive
  have hpos : 0 < ∫ s in Ioi (0 : ℝ), hBound s := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => by
        simp only [Pi.zero_apply, hBound]; have := Real.sqrt_pos.mpr hs; positivity)
      integrableOn_hBound]
    have : Ioi (0 : ℝ) ⊆ Function.support hBound ∩ Ioi 0 := fun s (hs : 0 < s) =>
      ⟨by simp only [Function.mem_support, hBound]; have := Real.sqrt_pos.mpr hs; positivity, hs⟩
    exact lt_of_lt_of_le (by simp) (measure_mono this)
  refine ⟨3 / 4 * ((∫ s in Ioi (0 : ℝ), hBound s : ℝ) : ℂ), by
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hpos.ne'), ?_⟩
  have hc := ((continuous_ofReal.tendsto _).comp hlim).const_mul (3 / 4 : ℂ)
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  simp only [Function.comp_apply]
  rw [carlsonRH_eq_real_integral hx hy hz hρ, ← hsub ρ hρ]
  push_cast
  ring

/-- `P(ρ)/ρ^{deg P} → lead(P)` as `ρ → ∞` along the reals. -/
theorem tendsto_eval_div_pow_natDegree (P : ℂ[X]) :
    Tendsto (fun ρ : ℝ => P.eval (ρ : ℂ) / (ρ : ℂ) ^ P.natDegree) atTop (𝓝 P.leadingCoeff) := by
  set n := P.natDegree
  have hinv : Tendsto (fun ρ : ℝ => ((ρ : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have hsum : Tendsto (fun ρ : ℝ => ∑ i ∈ Finset.range (n + 1),
      P.coeff i * ((ρ : ℂ))⁻¹ ^ (n - i)) atTop
      (𝓝 (∑ i ∈ Finset.range (n + 1), P.coeff i * (0 : ℂ) ^ (n - i))) :=
    tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (hinv.pow _)
  have hval : ∑ i ∈ Finset.range (n + 1), P.coeff i * (0 : ℂ) ^ (n - i) = P.leadingCoeff := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.sum_eq_zero, zero_add]
    · rfl
    intro i hi
    rw [zero_pow (by have := Finset.mem_range.mp hi; omega), mul_zero]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  have hρ0 : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  rw [eval_eq_sum_range, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [inv_pow, mul_div_assoc]
  congr 1
  rw [show n = i + (n - i) by omega, pow_add, Nat.add_sub_cancel_left]
  field_simp

/-- A function `h` with `√ρ h(ρ) → L ≠ 0` is not a rational function of `ρ`: if
`q(ρ) h(ρ) = r(ρ)` for all `ρ > 0` with polynomials `q, r`, then `q = 0`. -/
theorem eq_zero_of_mul_eq_eval {h : ℝ → ℂ} {L : ℂ} (hL : L ≠ 0)
    (hh : Tendsto (fun ρ : ℝ => (Real.sqrt ρ : ℂ) * h ρ) atTop (𝓝 L)) {q r : ℂ[X]}
    (hqr : ∀ ρ : ℝ, 0 < ρ → q.eval (ρ : ℂ) * h ρ = r.eval (ρ : ℂ)) : q = 0 := by
  by_contra hq
  set d := q.natDegree
  have ha : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  -- `F(ρ) = r(ρ) √ρ / ρ^d → lead(q) L`
  have hF : Tendsto (fun ρ : ℝ => r.eval (ρ : ℂ) * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d) atTop
      (𝓝 (q.leadingCoeff * L)) := by
    refine ((tendsto_eval_div_pow_natDegree q).mul hh).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    rw [← hqr ρ hρ]
    ring
  have hlim0 : q.leadingCoeff * L ≠ 0 := mul_ne_zero ha hL
  by_cases hr : r = 0
  · subst hr
    simp only [eval_zero, zero_mul, zero_div] at hF
    exact hlim0 (tendsto_nhds_unique hF tendsto_const_nhds)
  set m := r.natDegree
  have hb : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr
  have hR := tendsto_eval_div_pow_natDegree r
  have hsplit : ∀ ρ : ℝ, 0 < ρ → r.eval (ρ : ℂ) * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d =
      (r.eval (ρ : ℂ) / (ρ : ℂ) ^ m) * ((ρ : ℂ) ^ m * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d) := by
    intro ρ hρ
    have : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
    field_simp
  rcases lt_or_ge m d with hmd | hmd
  · -- the factor `ρ^m √ρ / ρ^d → 0`
    have hu : Tendsto (fun ρ : ℝ => (ρ : ℂ) ^ m * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun ρ : ℝ => (Real.sqrt ρ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
      filter_upwards [eventually_ge_atTop 1] with ρ hρ
      have hρ0 : 0 < ρ := by linarith
      have hq0 := Real.sqrt_pos.mpr hρ0
      rw [norm_div, norm_mul, norm_pow, norm_pow, norm_real, norm_real,
        Real.norm_of_nonneg hρ0.le, Real.norm_of_nonneg hq0.le]
      rw [div_le_iff₀ (by positivity)]
      have e : (Real.sqrt ρ)⁻¹ * ρ ^ d = Real.sqrt ρ * ρ ^ (d - 1) := by
        rw [show d = d - 1 + 1 by omega, pow_succ, inv_mul_eq_div, mul_div_assoc, Real.div_sqrt,
          Nat.add_sub_cancel]
        ring
      rw [e]
      have := pow_le_pow_right₀ hρ (show m ≤ d - 1 by omega)
      nlinarith [hq0]
    have h0 := hR.mul hu
    rw [mul_zero] at h0
    refine hlim0 (tendsto_nhds_unique hF (h0.congr' ?_))
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    exact (hsplit ρ hρ).symm
  · -- the factor grows like `√ρ`, so `F` is unbounded
    have hnorm := hF.norm
    have hbig : Tendsto (fun ρ : ℝ => ‖r.eval (ρ : ℂ) * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d‖)
        atTop atTop := by
      have hb2 : 0 < ‖r.leadingCoeff‖ / 2 := by have := norm_pos_iff.mpr hb; positivity
      have hev := (hR.norm.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hb))))
      refine tendsto_atTop_mono' atTop ?_
        ((Real.tendsto_sqrt_atTop).const_mul_atTop hb2)
      filter_upwards [hev, eventually_ge_atTop 1] with ρ h1 hρ
      have hρ0 : 0 < ρ := by linarith
      have hq0 := Real.sqrt_pos.mpr hρ0
      rw [hsplit ρ hρ0, norm_mul]
      have hu : Real.sqrt ρ ≤ ‖(ρ : ℂ) ^ m * (Real.sqrt ρ : ℂ) / (ρ : ℂ) ^ d‖ := by
        rw [norm_div, norm_mul, norm_pow, norm_pow, norm_real, norm_real,
          Real.norm_of_nonneg hρ0.le, Real.norm_of_nonneg hq0.le,
          le_div_iff₀ (by positivity)]
        nlinarith [pow_le_pow_right₀ hρ hmd, hq0]
      calc ‖r.leadingCoeff‖ / 2 * Real.sqrt ρ ≤
          ‖r.eval (ρ : ℂ) / (ρ : ℂ) ^ m‖ * Real.sqrt ρ := by gcongr
        _ ≤ _ := by gcongr
    exact not_tendsto_nhds_of_tendsto_atTop hbig _ hnorm

/-- **Carlson's Theorem 9.2-1**, the part concerning `R_H`: `R_H(x, y, z, ρ)` is linearly
independent of `(xyz)^{-1/2}`, `R_F(x, y, z)`, `R_G(x, y, z)` with respect to coefficients that are
polynomial in `ρ` (and arbitrary in `x, y, z`). If the relation holds for all positive real
arguments, the coefficient of `R_H` vanishes. -/
theorem coeff_carlsonRH_eq_zero (p : Fin 4 → ℝ → ℝ → ℝ → ℂ[X])
    (hrel : ∀ x y z ρ : ℝ, 0 < x → 0 < y → 0 < z → 0 < ρ →
      (p 0 x y z).eval (ρ : ℂ) * ((x : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-1 / 2 : ℂ) *
          (z : ℂ) ^ (-1 / 2 : ℂ)) +
        (p 1 x y z).eval (ρ : ℂ) * carlsonRF x y z + (p 2 x y z).eval (ρ : ℂ) * carlsonRG x y z +
        (p 3 x y z).eval (ρ : ℂ) * carlsonRH x y z ρ = 0)
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : p 3 x y z = 0 := by
  obtain ⟨L, hL, hlim⟩ := tendsto_sqrt_mul_carlsonRH hx hy hz
  refine eq_zero_of_mul_eq_eval hL hlim (r := -(p 0 x y z * C ((x : ℂ) ^ (-1 / 2 : ℂ) *
    (y : ℂ) ^ (-1 / 2 : ℂ) * (z : ℂ) ^ (-1 / 2 : ℂ)) + p 1 x y z * C (carlsonRF x y z) +
      p 2 x y z * C (carlsonRG x y z))) fun ρ hρ => ?_
  have := hrel x y z ρ hx hy hz hρ
  simp only [eval_neg, eval_add, eval_mul, eval_C]
  linear_combination this

end Carlson
