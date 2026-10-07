/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SingleIntegral.PositiveRay
public import Carlson.R.Explicit

/-!
# `R_{-1}(1/2, 1/2, 1; x, y, z)` as a logarithm (Carlson's Exercise 8.5-1)

By the positive-ray representation, `R_{-1}(1/2, 1/2, 1; x, y, z)` is
`∫₀^∞ (t + x)^{-1/2} (t + y)^{-1/2} (t + z)^{-1} dt`, and with `A = (z - x)^{1/2}`,
`B = (z - y)^{1/2}` an antiderivative of the integrand is
`2/(AB) log [(A (t + y)^{1/2} + B (t + x)^{1/2}) / ((A + B)(t + z)^{1/2})]`. For positive real
nodes the principal square roots `A`, `B` lie in the closed first quadrant, which keeps the
argument of the logarithm in the slit plane.

## Main results

* `Carlson.carlsonR_neg_one_half_half_one`: Exercise 8.5-1 for positive real `x, y, z` with
  `z ≠ x, y`. Carlson states it for all `x, y, z` in the slit plane.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.5.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

/-- A nonzero complex number in the closed right half-plane lies in the slit plane. -/
private theorem mem_slitPlane_of_re_nonneg {u : ℂ} (hre : 0 ≤ u.re) (h0 : u ≠ 0) :
    u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases hre.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr fun him => h0 (Complex.ext ?_ ?_) <;> simp [← h, him]

/-- The closed first quadrant without the origin. -/
private def Quadrant (u : ℂ) : Prop := 0 ≤ u.re ∧ 0 ≤ u.im ∧ u ≠ 0

/-- The principal square root of a nonzero real number lies in the closed first quadrant. -/
private theorem quadrant_sqrt {r : ℝ} (hr : r ≠ 0) : Quadrant ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  rw [one_div]
  refine ⟨by rw [cpow_inv_two_re]; exact Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [cpow_inv_two_im_eq_sqrt (by simp)]; exact Real.sqrt_nonneg _
  · exact cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hr))

/-- Positive combinations stay in the closed first quadrant. -/
private theorem quadrant_add {u v : ℂ} {p q : ℝ} (hu : Quadrant u) (hv : Quadrant v)
    (hp : 0 < p) (hq : 0 < q) : Quadrant (u * p + v * q) := by
  obtain ⟨hu1, hu2, hu0⟩ := hu
  obtain ⟨hv1, hv2, hv0⟩ := hv
  refine ⟨by simp; positivity, by simp; positivity, fun h => hu0 ?_⟩
  have hre := congrArg re h
  have him := congrArg im h
  simp at hre him
  apply Complex.ext <;> simp <;> nlinarith [mul_nonneg hv1 hq.le, mul_nonneg hv2 hq.le]

/-- The quotient of two points of the closed first quadrant lies in the slit plane. -/
private theorem div_mem_slitPlane_of_quadrant {u v : ℂ} (hu : Quadrant u) (hv : Quadrant v) :
    u / v ∈ slitPlane := by
  obtain ⟨hu1, hu2, hu0⟩ := hu
  obtain ⟨hv1, hv2, hv0⟩ := hv
  refine mem_slitPlane_of_re_nonneg ?_ (div_ne_zero hu0 hv0)
  rw [div_re]
  have := normSq_nonneg v
  positivity

/-- The key algebraic identity behind the antiderivative of Exercise 8.5-1. -/
private theorem logarithm_deriv_identity {A B P Q S : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hS : S ≠ 0) (hAB : A + B ≠ 0) (hG : A * Q + B * P ≠ 0)
    (h1 : S ^ 2 = P ^ 2 + A ^ 2) (h2 : S ^ 2 = Q ^ 2 + B ^ 2) :
    2 / (A * B) * (((A * (1 / (2 * Q)) + B * (1 / (2 * P))) * ((A + B) * S) -
        (A * Q + B * P) * ((A + B) * (1 / (2 * S)))) / ((A + B) * S) ^ 2 /
        ((A * Q + B * P) / ((A + B) * S))) = 1 / (P * Q * S ^ 2) := by
  field_simp
  linear_combination (A * P) * h2 + (B * Q) * h1

/-- **Exercise 8.5-1**, for positive real `x, y, z` with `z ≠ x`, `z ≠ y`:
`R_{-1}(1/2, 1/2, 1; x, y, z) = 2 ((z - x)^{1/2} (z - y)^{1/2})⁻¹ log (z^{1/2} [(z - x)^{1/2} +
(z - y)^{1/2}] / [y^{1/2} (z - x)^{1/2} + x^{1/2} (z - y)^{1/2}])`, with principal powers.
When `z < x` or `z < y` the corresponding square root is imaginary. -/
theorem carlsonR_neg_one_half_half_one {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    carlsonR (-1) ![1 / 2, 1 / 2, 1] ![(x : ℂ), y, z] =
      2 / (((z : ℂ) - x) ^ (1 / 2 : ℂ) * ((z : ℂ) - y) ^ (1 / 2 : ℂ)) *
        log ((z : ℂ) ^ (1 / 2 : ℂ) * (((z : ℂ) - x) ^ (1 / 2 : ℂ) + ((z : ℂ) - y) ^ (1 / 2 : ℂ)) /
          ((y : ℂ) ^ (1 / 2 : ℂ) * ((z : ℂ) - x) ^ (1 / 2 : ℂ) +
            (x : ℂ) ^ (1 / 2 : ℂ) * ((z : ℂ) - y) ^ (1 / 2 : ℂ))) := by
  set A : ℂ := ((z : ℂ) - x) ^ (1 / 2 : ℂ)
  set B : ℂ := ((z : ℂ) - y) ^ (1 / 2 : ℂ)
  have hqA : Quadrant A := by
    simpa [A] using quadrant_sqrt (sub_ne_zero.mpr hzx)
  have hqB : Quadrant B := by
    simpa [B] using quadrant_sqrt (sub_ne_zero.mpr hzy)
  have hA0 : A ≠ 0 := hqA.2.2
  have hB0 : B ≠ 0 := hqB.2.2
  have hsq : ∀ u : ℂ, (u ^ (1 / 2 : ℂ)) ^ 2 = u := fun u => by
    rw [one_div, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num]; exact cpow_nat_inv_pow u two_ne_zero
  have hA2 : A ^ 2 = (z : ℂ) - x := hsq _
  have hB2 : B ^ 2 = (z : ℂ) - y := hsq _
  have hqAB : Quadrant (A + B) := by
    simpa using quadrant_add hqA hqB one_pos one_pos
  have hAB0 : A + B ≠ 0 := hqAB.2.2
  -- the square roots along the ray
  set P : ℝ → ℂ := fun t => (Real.sqrt (t + x) : ℂ)
  set Q : ℝ → ℂ := fun t => (Real.sqrt (t + y) : ℂ)
  set S : ℝ → ℂ := fun t => (Real.sqrt (t + z) : ℂ)
  set W : ℝ → ℂ := fun t => (A * Q t + B * P t) / ((A + B) * S t)
  set F : ℝ → ℂ := fun t => 2 / (A * B) * log (W t)
  have hsqrt : ∀ {c t : ℝ}, 0 < c → 0 ≤ t → HasDerivAt (fun t => (Real.sqrt (t + c) : ℂ))
      ((1 / (2 * Real.sqrt (t + c)) : ℝ) : ℂ) t := fun {c t} hc ht =>
    ((Real.hasDerivAt_sqrt (by simp only [id]; linarith)).comp t
      ((hasDerivAt_id t).add_const c)).ofReal_comp
      |>.congr_deriv (by simp)
  have hpos : ∀ {c t : ℝ}, 0 < c → 0 ≤ t → 0 < Real.sqrt (t + c) := fun {c t} hc ht =>
    Real.sqrt_pos.mpr (by linarith)
  have hG : ∀ {t : ℝ}, 0 ≤ t → Quadrant (A * Q t + B * P t) := fun ht =>
    quadrant_add hqA hqB (hpos hy ht) (hpos hx ht)
  have hW : ∀ {t : ℝ}, 0 ≤ t → W t ∈ slitPlane := fun {t} ht => by
    have h := div_mem_slitPlane_of_quadrant (hG ht) hqAB
    have hS := hpos hz ht
    have hWe : W t = (A * Q t + B * P t) / (A + B) / ((Real.sqrt (t + z) : ℝ) : ℂ) := by
      simp only [W, S]; rw [div_div]
    rw [hWe]
    rw [mem_slitPlane_iff] at h ⊢
    simp only [div_ofReal_re, div_ofReal_im]
    rcases h with h | h
    · exact Or.inl (div_pos h hS)
    · exact Or.inr (div_ne_zero h hS.ne')
  -- the integrand
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 : ℂ) - 1) *
    ∏ i, (![(x : ℂ), y, z] i + (t : ℂ)) ^ (-![(1 / 2 : ℂ), 1 / 2, 1] i)
  have hf : ∀ {t : ℝ}, 0 ≤ t → f t = 1 / (P t * Q t * S t ^ 2) := fun {t} ht => by
    have key : ∀ {c : ℝ}, 0 < c → ((c : ℂ) + t) ^ (-(1 / 2 : ℂ)) = 1 / (Real.sqrt (t + c) : ℂ) :=
      fun {c} hc => by
        rw [show (c : ℂ) + t = ((t + c : ℝ) : ℂ) by push_cast; ring,
          show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
          ← ofReal_cpow (by linarith), Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
        push_cast; ring
    have hz2 : S t ^ 2 = (z : ℂ) + t := by
      simp only [S]; rw [← ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
    simp only [f, sub_self, cpow_zero, one_mul, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [key hx, key hy, hz2, cpow_neg_one]
    simp only [P, Q]
    field_simp
  -- the antiderivative
  have hFd : ∀ {t : ℝ}, 0 ≤ t → HasDerivAt F (f t) t := fun {t} ht => by
    have hP := hsqrt hx ht
    have hQ := hsqrt hy ht
    have hS := hsqrt hz ht
    have hp := hpos hx ht
    have hq := hpos hy ht
    have hs := hpos hz ht
    have hD : (A + B) * S t ≠ 0 := mul_ne_zero hAB0 (ofReal_ne_zero.mpr hs.ne')
    have h := ((((hQ.const_mul A).add (hP.const_mul B)).div (hS.const_mul (A + B)) hD).clog_real
      (hW ht)).const_mul (2 / (A * B))
    convert h using 1
    rw [hf ht]
    have h1 : S t ^ 2 = P t ^ 2 + A ^ 2 := by
      simp only [S, P]
      rw [← ofReal_pow, ← ofReal_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith), hA2]
      push_cast; ring
    have h2 : S t ^ 2 = Q t ^ 2 + B ^ 2 := by
      simp only [S, Q]
      rw [← ofReal_pow, ← ofReal_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith), hB2]
      push_cast; ring
    rw [← logarithm_deriv_identity hA0 hB0 (ofReal_ne_zero.mpr hp.ne')
      (ofReal_ne_zero.mpr hq.ne') (ofReal_ne_zero.mpr hs.ne') hAB0 (hG ht).2.2 h1 h2]
    push_cast; rfl
  -- the limit at infinity
  have hratio : ∀ c : ℝ, Tendsto (fun t : ℝ => ((Real.sqrt (t + c) / Real.sqrt (t + z) : ℝ) : ℂ))
      atTop (𝓝 1) := fun c => by
    have h0 : Tendsto (fun t : ℝ => 1 + (c - z) / (t + z)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ z tendsto_id))
    have h1 : Tendsto (fun t : ℝ => (t + c) / (t + z)) atTop (𝓝 1) := by
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (-z)] with t ht
      field_simp [show t + z ≠ 0 by linarith]
      ring
    have h2 := ((Real.continuous_sqrt.tendsto 1).comp h1)
    rw [Real.sqrt_one] at h2
    have h3 := (continuous_ofReal.tendsto 1).comp h2
    rw [ofReal_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp_apply]
    rw [Real.sqrt_div' _ (show 0 ≤ t + z by linarith), ofReal_div]
  have hWlim : Tendsto W atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := A)).mul (hratio y)).add
      ((tendsto_const_nhds (x := B)).mul (hratio x))
    have h' := h.div_const (A + B)
    rw [mul_one, mul_one, div_self hAB0] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hs := hpos hz ht
    simp only [W, P, Q, S]
    push_cast
    field_simp
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have h := ((continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hWlim).const_mul
      (2 / (A * B))
    simpa using h
  -- integrability
  set r : ℝ → ℝ := fun t => 1 / (Real.sqrt (t + x) * Real.sqrt (t + y) * Real.sqrt (t + z) ^ 2)
  have hfr : ∀ {t : ℝ}, 0 ≤ t → f t = r t := fun ht => by
    rw [hf ht]; simp only [r, P, Q, S]; push_cast; ring
  have hint : IntegrableOn f (Ioi 0) := by
    have hre : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => (F t).re) (r t) t := fun t ht => by
      have := (hFd (le_of_lt ht)).hasFDerivAt.restrictScalars ℝ
      have h2 := (reCLM.hasFDerivAt.comp t this).hasDerivAt
      convert h2 using 1
      · rfl
      · simp [hfr (le_of_lt ht)]
    have hr : IntegrableOn r (Ioi 0) := integrableOn_Ioi_deriv_of_nonneg
      ((continuous_re.continuousAt.comp (hFd le_rfl).continuousAt).continuousWithinAt)
      hre (fun t ht => by simp only [r]; positivity)
      ((continuous_re.tendsto 0).comp hFlim)
    exact (hr.ofReal).congr_fun (fun t ht => (hfr (le_of_lt ht)).symm) measurableSet_Ioi
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t ht => hFd ht) hint hFlim
  have hslit : ![(x : ℂ), y, z] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hy
    · exact ofReal_mem_slitPlane.mpr hz
  have hray := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := 1)
    (b := ![(1 / 2 : ℂ), 1 / 2, 1]) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; norm_num) hslit
  unfold carlsonRPositiveRayIntegral at hray
  rw [hFTC, Gamma_one, one_mul, one_mul] at hray
  have hroot : ∀ {c : ℝ}, 0 < c → (c : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt c : ℂ) := fun {c} hc => by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hc.le,
      Real.sqrt_eq_rpow]
  have hW0 := hW (le_refl 0)
  have harg : (W 0).arg ≠ π := (mem_slitPlane_iff_arg.mp hW0).1
  have hinv : (z : ℂ) ^ (1 / 2 : ℂ) * (A + B) /
      ((y : ℂ) ^ (1 / 2 : ℂ) * A + (x : ℂ) ^ (1 / 2 : ℂ) * B) = (W 0)⁻¹ := by
    simp only [W, P, Q, S, zero_add]
    rw [hroot hx, hroot hy, hroot hz, inv_div]
    ring
  rw [carlsonR, show (∑ i, ![(1 / 2 : ℂ), 1 / 2, 1] i) = 1 + 1 by
      simp [Fin.sum_univ_three]; norm_num, Gamma_add_one _ one_ne_zero, Gamma_one, mul_one,
    ← hray, zero_sub]
  simp only [A, B] at hinv ⊢
  rw [hinv, log_inv _ harg]
  simp only [F]
  ring

end Carlson
