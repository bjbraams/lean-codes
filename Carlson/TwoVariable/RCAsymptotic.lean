/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Borchardt
public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.TwoVariable.ParameterSymmetry
public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.R.Homogeneity

/-!
# Asymptotic behaviour of `R_C` (Exercise 6.9-18)

Exercise 6.9-18 asks for `((x + 2y)/3) R_C(x², y²) = 1 + (1/5)((x - y)/(x + 2y))² + O(ε³)` with
`ε = |1 - x/y|`, for `x, y` in the right half-plane. By homogeneity this is a statement about
`u = x/y` near `1`, and `R_C(u², 1) = ₂F₁(1/2, 1/2; 3/2; 1 - u²)` reduces it to the cubic Taylor
remainder of that series. Two real-variable estimates are also recorded: the expansion of
`R_C(x, y)` itself near the diagonal, and its logarithmic behaviour for small second argument.

## Main results

* `Carlson.TwoVariable.exists_carlsonRC_sq_expansion`: Exercise 6.9-18.
* `Carlson.TwoVariable.isBigO_carlsonRC_sub_diagonal`: `R_C(x, y) = A^{-1/2}(1 + (x - y)²/(30A²)) +
  O(|x - y|³)` near a real diagonal point, `A = (x + 2y)/3`.
* `Carlson.TwoVariable.tendsto_carlsonRC_sub_log`: `R_C(x, y) - log(4x/y)/(2√x) → 0` as `y → 0⁺`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Filter Asymptotics Set
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **`R_C` near the diagonal**: as `(x, y) → (a, a)` with `a > 0`,
`R_C(x, y) - A^{-1/2} (1 + (x - y)²/(30 A²)) = O(|x - y|³)`, `A = (x + 2y)/3`. -/
theorem isBigO_carlsonRC_sub_diagonal {a : ℝ} (ha : 0 < a) :
    (fun p : ℝ × ℝ => (carlsonRC p.1 p.2).re - (Real.sqrt ((p.1 + 2 * p.2) / 3))⁻¹ *
        (1 + (p.1 - p.2) ^ 2 / (30 * ((p.1 + 2 * p.2) / 3) ^ 2)))
      =O[𝓝 (a, a)] fun p => |p.1 - p.2| ^ 3 := by
  set r := Real.sqrt (a / 2)
  set R := Real.sqrt (2 * a)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = a / 2 := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hrR : r ≤ R := Real.sqrt_le_sqrt (by linarith)
  have hmem : ∀ᶠ p : ℝ × ℝ in 𝓝 (a, a), p ∈ Icc (a / 2) (2 * a) ×ˢ Icc (a / 2) (2 * a) := by
    have h : Icc (a / 2) (2 * a) ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
    exact prod_mem_nhds h h
  refine IsBigO.of_bound (20 * R ^ 2 / (64 * r ^ 9)) ?_
  filter_upwards [hmem] with p hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have h := abs_carlsonRC_sub_le (X := p.1) (Y := p.2) hr hrR (by linarith) (by linarith)
    (by linarith) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_abs]
  linarith [h]

/-- **`R_C` for small second argument**: for fixed `x > 0`,
`R_C(x, y) - log(4x/y)/(2√x) → 0` as `y → 0⁺`. -/
theorem tendsto_carlsonRC_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (carlsonRC x y).re - Real.log (4 * x / y) / (2 * Real.sqrt x))
      (𝓝[>] 0) (𝓝 0) := by
  set s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  set u : ℝ → ℝ := fun y => Real.sqrt (x - y)
  set F : ℝ → ℝ := fun y => Real.log (s + u y) / u y - Real.log (4 * x) / (2 * s)
  set h : ℝ → ℝ := fun y => 1 / (s * u y * (s + u y))
  have hu0 : u 0 = s := by simp [u, s]
  have huc : ContinuousAt u 0 := by simp only [u]; fun_prop
  have hFc : ContinuousAt F 0 := by
    simp only [F]
    refine ContinuousAt.sub (ContinuousAt.div ?_ huc (by rw [hu0]; exact hs.ne')) continuousAt_const
    exact (continuousAt_const.add huc).log (show s + u 0 ≠ 0 by rw [hu0]; positivity)
  have hhc : ContinuousAt h 0 := by
    simp only [h]
    exact continuousAt_const.div ((continuousAt_const.mul huc).mul (continuousAt_const.add huc))
      (by rw [hu0]; positivity)
  have hF0 : F 0 = 0 := by
    simp only [F, hu0]
    rw [show 4 * x = (s + s) ^ 2 by rw [← hs2]; ring, Real.log_pow]
    field_simp; ring
  have hlim : Tendsto (fun y => F y - y * Real.log y * h y / 2) (𝓝[>] 0) (𝓝 0) := by
    have hml : Tendsto (fun y : ℝ => y * Real.log y) (𝓝 0) (𝓝 0) := by
      simpa using Real.continuous_mul_log.tendsto 0
    have := (hFc.tendsto.sub ((hml.mul hhc.tendsto).div_const 2)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hF0] using this
  refine hlim.congr' ?_
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo 0 x := Ioo_mem_nhdsGT hx
  filter_upwards [hev] with y ⟨hy, hyx⟩
  rw [carlsonRC_of_gt hy hyx, ofReal_re]
  have hu : 0 < u y := Real.sqrt_pos.mpr (by linarith)
  have hu2 : u y ^ 2 = x - y := Real.sq_sqrt (by linarith)
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  simp only [F, h]
  rw [Real.log_div (by positivity) hsy.ne', Real.log_sqrt hy.le,
    Real.log_div (by positivity) hy.ne']
  change _ = (Real.log (s + u y) - Real.log y / 2) / u y - (Real.log (4 * x) - Real.log y) / (2 * s)
  generalize Real.log y = ly
  generalize Real.log (s + u y) = L
  generalize Real.log (4 * x) = L4
  generalize u y = v at hu hu2 ⊢
  rw [show y = s ^ 2 - v ^ 2 by rw [hs2, hu2]; ring]
  field_simp
  ring

/-- `R_C(w, 1) = ₂F₁(1/2, 1/2; 3/2; 1 - w)` for `‖1 - w‖ < 1`. -/
theorem carlsonRC_one_eq_ordinaryHypergeometric {w : ℂ} (hw : ‖1 - w‖ < 1) :
    carlsonRC w 1 = ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) (3 / 2) (1 - w) := by
  have hwre : 0 < w.re := by
    have := (abs_re_le_norm (1 - w)).trans_lt hw
    simp only [sub_re, one_re] at this
    linarith [le_abs_self (1 - w.re)]
  have hw' : w ∈ slitPlane := Or.inl hwre
  have h := regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun (1 / 2) (1 / 2) (3 / 2) hw
  rw [sub_sub_cancel, show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num] at h
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := fun k hk => by
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  unfold carlsonRC carlsonR
  rw [← regCarlsonR_pair_swap _ _ _ hw' one_mem_slitPlane, show (-1 / 2 : ℂ) = -(1 / 2) by ring,
    h, ← ordinaryHypergeometric_div_Gamma_eq hc]
  have hsum : ∑ i, pair (1 / 2 : ℂ) 1 i = 3 / 2 := by
    simp only [Fin.sum_univ_two, pair_zero, pair_one]; norm_num
  rw [hsum, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos (by norm_num))]

/-- The cubic Taylor remainder of `₂F₁(1/2, 1/2; 3/2; s)` at `s = 0`. -/
theorem isBigO_ordinaryHypergeometric_half_half_sub :
    (fun s : ℂ => ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) (3 / 2) s -
        (1 + s / 6 + 3 * s ^ 2 / 40)) =O[𝓝 0] fun s => ‖s‖ ^ 3 := by
  set p := ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) (1 / 2) (3 / 2)
  have hr : p.radius = 1 := by
    refine ordinaryHypergeometricSeries_radius_eq_one (𝔸 := ℂ) (1 / 2 : ℂ) (1 / 2) (3 / 2)
      fun k => ⟨?_, ?_, ?_⟩ <;> intro hk <;> have := congrArg re hk <;> simp at this <;>
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hp := (p.hasFPowerSeriesOnBall (by rw [hr]; exact one_pos)).hasFPowerSeriesAt
  have h := hp.isBigO_sub_partialSum_pow 3
  refine h.congr_left fun s => ?_
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.sum_range_zero, p, ordinaryHypergeometricSeries_apply_eq]
  rw [ordinaryHypergeometric]
  simp [ascPochhammer_succ_right, Polynomial.eval_mul]
  norm_num
  ring

/-- `arg (y²) = 2 arg y` for `re y > 0`. -/
theorem arg_sq_of_re_pos {y : ℂ} (hy : 0 < y.re) : arg (y ^ 2) = 2 * arg y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  rw [sq, arg_mul hy0 hy0 ⟨by linarith, by linarith⟩]; ring

/-- Complex homogeneity of `R_C` in the form used near the diagonal:
`R_C((u y)², y²) = y⁻¹ R_C(u², 1)` if `u`, `y` and `u y` lie in the right half-plane. -/
theorem carlsonRC_mul_sq {u y : ℂ} (hu : 0 < u.re) (hy : 0 < y.re) (huy : 0 < (u * y).re) :
    carlsonRC ((u * y) ^ 2) (y ^ 2) = y⁻¹ * carlsonRC (u ^ 2) 1 := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hau := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hay := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have hauy := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl huy))
  rw [arg_mul hu0 hy0 ⟨by linarith, by linarith⟩] at hauy
  have hz : pair (u ^ 2) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simpa [pair, sq] using mul_mem_slitPlane_of_re_pos hu hu
    · simp [pair]
  have hμ : y ^ 2 ∈ slitPlane := by simpa [sq] using mul_mem_slitPlane_of_re_pos hy hy
  have h := regCarlsonR_mul_of_arg_add (-1 / 2) (pair (1 / 2 : ℂ) 1) hz hμ (fun i => by
    fin_cases i
    · simp only [pair, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [arg_sq_of_re_pos hy, arg_sq_of_re_pos hu]
      exact ⟨by linarith, by linarith⟩
    · simp only [pair, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        arg_one, add_zero]
      rw [arg_sq_of_re_pos hy]
      exact ⟨by linarith, by linarith⟩)
  have hp : (fun i => y ^ 2 * pair (u ^ 2) 1 i) = pair ((u * y) ^ 2) (y ^ 2) := by
    funext i; fin_cases i <;> simp [pair]; ring
  rw [hp] at h
  have hsq : (y ^ 2) ^ (-1 / 2 : ℂ) = y⁻¹ := by
    rw [cpow_def_of_ne_zero (pow_ne_zero 2 hy0), sq, log_mul_of_re_pos hy hy,
      show (log y + log y) * (-1 / 2) = -log y by ring, exp_neg, exp_log hy0]
  unfold carlsonRC carlsonR
  rw [h, hsq]; ring

/-- The remainder in Exercise 6.9-18 as a function of `u = x/y`:
`((u + 2)/3) R_C(u², 1) - 1 - (1/5)((u - 1)/(u + 2))² = O(|u - 1|³)` as `u → 1`. -/
theorem isBigO_carlsonRC_sq_one_sub :
    (fun u : ℂ => (u + 2) / 3 * carlsonRC (u ^ 2) 1 - 1 - 1 / 5 * ((u - 1) / (u + 2)) ^ 2)
      =O[𝓝 1] fun u => ‖u - 1‖ ^ 3 := by
  set F : ℂ → ℂ := ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) (3 / 2)
  set P : ℂ → ℂ := fun s => 1 + s / 6 + 3 * s ^ 2 / 40
  set r : ℂ → ℂ := fun u => (9 * (u - 1) ^ 4 + 117 * (u - 1) ^ 3 + 583 * (u - 1) ^ 2 +
    1319 * (u - 1) + 1164) / (360 * (u + 2) ^ 2)
  have hs : Tendsto (fun u : ℂ => 1 - u ^ 2) (𝓝 1) (𝓝 0) := by
    have : Continuous fun u : ℂ => 1 - u ^ 2 := by fun_prop
    simpa using this.tendsto 1
  -- the near-diagonal identity
  have hev : ∀ᶠ u in 𝓝 (1 : ℂ), ‖1 - u ^ 2‖ < 1 ∧ u + 2 ≠ 0 := by
    have h1 := hs.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))
    have hc : Continuous fun u : ℂ => u + 2 := by fun_prop
    have h2 : ∀ᶠ u in 𝓝 (1 : ℂ), u + 2 ≠ 0 := hc.continuousAt.eventually_ne (by norm_num)
    exact h1.and h2
  have hid : (fun u : ℂ => (u + 2) / 3 * carlsonRC (u ^ 2) 1 - 1 -
      1 / 5 * ((u - 1) / (u + 2)) ^ 2) =ᶠ[𝓝 1]
      fun u => (u + 2) / 3 * (F (1 - u ^ 2) - P (1 - u ^ 2)) + (u - 1) ^ 3 * r u := by
    filter_upwards [hev] with u ⟨h1, h2⟩
    rw [carlsonRC_one_eq_ordinaryHypergeometric h1]
    simp only [P, r]
    field_simp
    ring
  refine IsBigO.congr' ?_ hid.symm EventuallyEq.rfl
  have hsq : (fun u : ℂ => ‖1 - u ^ 2‖ ^ 3) =O[𝓝 1] fun u => ‖u - 1‖ ^ 3 := by
    have hb : (fun u : ℂ => -(u + 1)) =O[𝓝 1] fun _ => (1 : ℂ) :=
      ((continuous_id.add continuous_const).neg.tendsto 1).isBigO_one ℂ
    have := (hb.mul (isBigO_refl (fun u : ℂ => u - 1) (𝓝 1))).norm_left.norm_right.pow 3
    refine this.congr (fun u => ?_) (fun u => ?_)
    · congr 2; ring
    · simp
  have h1 : (fun u : ℂ => F (1 - u ^ 2) - P (1 - u ^ 2)) =O[𝓝 1] fun u => ‖u - 1‖ ^ 3 :=
    (isBigO_ordinaryHypergeometric_half_half_sub.comp_tendsto hs).trans hsq
  have hc3 : (fun u : ℂ => (u + 2) / 3) =O[𝓝 1] fun _ => (1 : ℝ) := by
    have hc : Continuous fun u : ℂ => (u + 2) / 3 := by fun_prop
    exact (hc.tendsto 1).isBigO_one ℝ
  have hr : r =O[𝓝 1] fun _ => (1 : ℝ) := by
    refine (ContinuousAt.tendsto ?_).isBigO_one ℝ
    simp only [r]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hA : (fun u : ℂ => (u + 2) / 3 * (F (1 - u ^ 2) - P (1 - u ^ 2))) =O[𝓝 1]
      fun u => ‖u - 1‖ ^ 3 := (hc3.mul h1).congr_right (fun u => by simp)
  have hB : (fun u : ℂ => (u - 1) ^ 3 * r u) =O[𝓝 1] fun u => ‖u - 1‖ ^ 3 := by
    have := ((isBigO_refl (fun u : ℂ => (u - 1) ^ 3) (𝓝 1)).norm_right.mul hr)
    refine this.congr_right fun u => ?_
    simp
  exact hA.add hB

/-- **Exercise 6.9-18**: for `x, y` in the right half-plane and `ε = |1 - x/y|`,
`((x + 2y)/3) R_C(x², y²) = 1 + (1/5)((x - y)/(x + 2y))² + O(ε³)` as `ε → 0`, uniformly: there
are `C` and `δ > 0` with the remainder bounded by `C ε³` whenever `ε < δ`. -/
theorem exists_carlsonRC_sq_expansion :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ x y : ℂ, 0 < x.re → 0 < y.re → ‖1 - x / y‖ < δ →
      ‖(x + 2 * y) / 3 * carlsonRC (x ^ 2) (y ^ 2) - 1 - 1 / 5 * ((x - y) / (x + 2 * y)) ^ 2‖
        ≤ C * ‖1 - x / y‖ ^ 3 := by
  obtain ⟨C, hC⟩ := isBigO_carlsonRC_sq_one_sub.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, min ε 1, lt_min hε one_pos, fun x y hx hy hxy => ?_⟩
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  set u := x / y
  have hux : x = u * y := by simp [u, hy0]
  have hd : dist u 1 < ε := by
    rw [dist_eq_norm, ← norm_neg, neg_sub]; exact hxy.trans_le (min_le_left _ _)
  have hu : 0 < u.re := by
    have := (abs_re_le_norm (1 - u)).trans_lt (hxy.trans_le (min_le_right _ _))
    simp only [sub_re, one_re] at this
    linarith [le_abs_self (1 - u.re)]
  have h := hball hd
  rw [Real.norm_eq_abs, abs_pow, abs_norm, ← norm_neg (u - 1), neg_sub] at h
  rw [hux, carlsonRC_mul_sq hu hy (hux ▸ hx)]
  have hq : (u * y - y) / (u * y + 2 * y) = (u - 1) / (u + 2) := by
    rw [show u * y - y = (u - 1) * y by ring, show u * y + 2 * y = (u + 2) * y by ring,
      mul_div_mul_right _ _ hy0]
  rw [hq, show (u * y + 2 * y) / 3 * (y⁻¹ * carlsonRC (u ^ 2) 1) =
    (u + 2) / 3 * carlsonRC (u ^ 2) 1 by field_simp]
  exact h

end Carlson.TwoVariable
