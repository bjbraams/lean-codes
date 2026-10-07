/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.RF
public import Carlson.R.SingleIntegral.PositiveRay

/-!
# `R_{-1}(1/2, 1/2, 1/2, 1/2; w, x, y, z)` as a difference of `R_F` (Carlson's Exercise 8.5-2)

On the positive ray, `R_{-1}(1/2, 1/2, 1/2, 1/2; w, x, y, z) = ∫₀^∞ ∏ (t + ·)^{-1/2} dt`. The
substitution `t + w = 1/σ` turns it into `∫₀^{1/w} ∏ (1 + (xᵢ - w) σ)^{-1/2} dσ`, the
difference of the integral over `(0, ∞)`, which is `2 [∏ (xᵢ - w)]^{-1/2} R_F(1/(x - w), …)`, and
the integral over `(1/w, ∞)`, which after `σ = (s + 1)/w` is
`2 w^{1/2} [∏ (xᵢ - w)]^{-1/2} R_F(x/(x - w), …)`.

## Main results

* `Carlson.carlsonR_quartic_eq_carlsonRF_sub`: Exercise 8.5-2 for real `0 < w < x, y, z`.
  Carlson states it for complex nodes off the closed convex hull of `w` and the negative real
  axis.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.5.
-/

open Complex MeasureTheory Set
open scoped Real

@[expose] public noncomputable section

namespace Carlson

/-- `(c + t)^{-1/2} = 1/√(c + t)` for `c + t > 0`. -/
private theorem cpow_neg_half_eq {c t : ℝ} (h : 0 < c + t) :
    ((c : ℂ) + t) ^ (-1 / 2 : ℂ) = ((1 / Real.sqrt (c + t) : ℝ) : ℂ) := by
  rw [show (c : ℂ) + t = ((c + t : ℝ) : ℂ) by push_cast; ring,
    show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h.le,
    Real.rpow_neg h.le, ← Real.sqrt_eq_rpow, one_div]

/-- The positive-ray integrand of `R_F` in real form. -/
private theorem carlsonRF_eq_real_integral {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    carlsonRF p q r = ((1 / 2 * ∫ s in Ioi (0 : ℝ),
      1 / (Real.sqrt (p + s) * Real.sqrt (q + s) * Real.sqrt (r + s)) : ℝ) : ℂ) := by
  rw [carlsonRF_eq_integral (ofReal_mem_slitPlane.mpr hp) (ofReal_mem_slitPlane.mpr hq)
    (ofReal_mem_slitPlane.mpr hr), ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · push_cast; ring
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs : 0 < s := hs
  rw [cpow_neg_half_eq (by linarith), cpow_neg_half_eq (by linarith),
    cpow_neg_half_eq (by linarith)]
  push_cast
  field_simp

/-- `R_{-1}(1/2, 1/2, 1/2, 1/2; w, x, y, z)` as a real ray integral, for positive nodes. -/
private theorem carlsonR_quartic_eq_real_integral {w x y z : ℝ} (hw : 0 < w) (hx : 0 < x)
    (hy : 0 < y) (hz : 0 < z) :
    carlsonR (-1) (fun _ : Fin 4 => 1 / 2) ![(w : ℂ), x, y, z] = ((∫ t in Ioi (0 : ℝ),
      1 / (Real.sqrt (w + t) * Real.sqrt (x + t) * Real.sqrt (y + t) * Real.sqrt (z + t)) : ℝ) :
        ℂ) := by
  have hslit : ![(w : ℂ), x, y, z] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hw
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hy
    · exact ofReal_mem_slitPlane.mpr hz
  have hray := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := 1)
    (b := fun _ : Fin 4 => (1 / 2 : ℂ)) (by norm_num) (by norm_num) (by simp; norm_num) hslit
  unfold carlsonRPositiveRayIntegral at hray
  rw [Gamma_one, one_mul] at hray
  rw [carlsonR, show (∑ _i : Fin 4, (1 / 2 : ℂ)) = 1 + 1 by simp; norm_num,
    Gamma_add_one _ one_ne_zero, Gamma_one, one_mul, ← hray, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := ht
  simp only [sub_self, cpow_zero, one_mul, Fin.prod_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, show -(1 / 2 : ℂ) = -1 / 2 by ring]
  rw [cpow_neg_half_eq (by linarith), cpow_neg_half_eq (by linarith),
    cpow_neg_half_eq (by linarith), cpow_neg_half_eq (by linarith)]
  push_cast
  field_simp

/-- The substitution `t + w = 1/σ` maps the ray integral onto `(0, 1/w)`. -/
private theorem integral_Ioi_quartic_eq {w x y z : ℝ} (hw : 0 < w) (hx : w < x) (hy : w < y)
    (hz : w < z) :
    ∫ t in Ioi (0 : ℝ),
        1 / (Real.sqrt (w + t) * Real.sqrt (x + t) * Real.sqrt (y + t) * Real.sqrt (z + t)) =
      ∫ σ in Ioo 0 w⁻¹, 1 / (Real.sqrt (1 + (x - w) * σ) * Real.sqrt (1 + (y - w) * σ) *
        Real.sqrt (1 + (z - w) * σ)) := by
  set F : ℝ → ℝ := fun t =>
    1 / (Real.sqrt (w + t) * Real.sqrt (x + t) * Real.sqrt (y + t) * Real.sqrt (z + t))
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 w⁻¹) measurableSet_Ioo
    (f := fun σ => σ⁻¹ - w) (f' := fun σ => -(σ ^ 2)⁻¹)
    (fun σ hσ => ((hasDerivAt_inv hσ.1.ne').sub_const w).hasDerivWithinAt)
    (fun a ha b hb hab => by
      have : a⁻¹ = b⁻¹ := by linarith [show a⁻¹ - w = b⁻¹ - w from hab]
      exact inv_injective this) F
  rw [show (fun σ : ℝ => σ⁻¹ - w) '' Ioo 0 w⁻¹ = Ioi 0 by
    ext t; simp only [mem_image, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨σ, ⟨h1, h2⟩, rfl⟩
      have : w < σ⁻¹ := by rw [lt_inv_comm₀ hw h1]; exact h2
      linarith
    · intro ht
      refine ⟨(t + w)⁻¹, ⟨by positivity, ?_⟩, by rw [inv_inv]; ring⟩
      exact inv_strictAnti₀ hw (by linarith)] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hσ0 : 0 < σ := hσ.1
  have e : ∀ c : ℝ, w ≤ c →
      Real.sqrt (c + (σ⁻¹ - w)) = Real.sqrt (1 + (c - w) * σ) / Real.sqrt σ := fun c hc => by
    rw [show c + (σ⁻¹ - w) = (1 + (c - w) * σ) / σ by field_simp; ring,
      Real.sqrt_div' _ hσ0.le]
  have hr := Real.sq_sqrt hσ0.le
  have hr0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ0
  simp only [F, smul_eq_mul]
  rw [e w le_rfl, e x hx.le, e y hy.le, e z hz.le, sub_self, zero_mul, add_zero, Real.sqrt_one,
    abs_neg, abs_of_pos (by positivity)]
  have h1 : 0 < Real.sqrt (1 + (x - w) * σ) := Real.sqrt_pos.mpr (by nlinarith)
  have h2 : 0 < Real.sqrt (1 + (y - w) * σ) := Real.sqrt_pos.mpr (by nlinarith)
  have h3 : 0 < Real.sqrt (1 + (z - w) * σ) := Real.sqrt_pos.mpr (by nlinarith)
  field_simp
  rw [show Real.sqrt σ ^ 4 = (Real.sqrt σ ^ 2) ^ 2 by ring, hr]

/-- The affine substitution `σ = (s + 1)/w` maps the tail `σ > 1/w` onto the positive ray. -/
private theorem integral_Ioi_inv_quartic_eq {w x y z : ℝ} (hw : 0 < w) (hx : w < x)
    (hy : w < y) (hz : w < z) :
    ∫ σ in Ioi w⁻¹, 1 / (Real.sqrt (1 + (x - w) * σ) * Real.sqrt (1 + (y - w) * σ) *
        Real.sqrt (1 + (z - w) * σ)) =
      Real.sqrt w * ∫ s in Ioi (0 : ℝ), 1 / (Real.sqrt (x + (x - w) * s) *
        Real.sqrt (y + (y - w) * s) * Real.sqrt (z + (z - w) * s)) := by
  set g : ℝ → ℝ := fun σ => 1 / (Real.sqrt (1 + (x - w) * σ) * Real.sqrt (1 + (y - w) * σ) *
    Real.sqrt (1 + (z - w) * σ))
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi 0) measurableSet_Ioi
    (f := fun s => (s + 1) * w⁻¹) (f' := fun _ => w⁻¹)
    (fun s _ => (((hasDerivAt_id s).add_const 1).mul_const w⁻¹).hasDerivWithinAt.congr_deriv
      (by simp))
    (fun a _ b _ hab => by
      have := mul_right_cancel₀ (inv_ne_zero hw.ne') hab
      linarith) g
  rw [show (fun s : ℝ => (s + 1) * w⁻¹) '' Ioi 0 = Ioi w⁻¹ by
    ext σ; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩
      nlinarith [inv_pos.mpr hw]
    · intro hσ
      refine ⟨σ * w - 1, ?_, by field_simp; ring⟩
      have := (inv_lt_iff_one_lt_mul₀ hw).mp hσ
      linarith] at hsub
  rw [hsub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have e : ∀ c : ℝ, w ≤ c → Real.sqrt (1 + (c - w) * ((s + 1) * w⁻¹)) =
      Real.sqrt (c + (c - w) * s) / Real.sqrt w := fun c hc => by
    rw [show 1 + (c - w) * ((s + 1) * w⁻¹) = (c + (c - w) * s) / w by field_simp; ring,
      Real.sqrt_div' _ hw.le]
  have hr := Real.sq_sqrt hw.le
  have hr0 : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  simp only [g, smul_eq_mul]
  rw [e x hx.le, e y hy.le, e z hz.le, abs_of_pos (inv_pos.mpr hw)]
  have h1 : 0 < Real.sqrt (x + (x - w) * s) := Real.sqrt_pos.mpr (by nlinarith)
  have h2 : 0 < Real.sqrt (y + (y - w) * s) := Real.sqrt_pos.mpr (by nlinarith)
  have h3 : 0 < Real.sqrt (z + (z - w) * s) := Real.sqrt_pos.mpr (by nlinarith)
  field_simp
  rw [hr]

/-- The reduced integrand `∏ (1 + (xᵢ - w) σ)^{-1/2}` is integrable on the positive ray. -/
private theorem integrableOn_quartic_reduced {A B C : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) :
    IntegrableOn (fun σ => 1 / (Real.sqrt (1 + A * σ) * Real.sqrt (1 + B * σ) *
      Real.sqrt (1 + C * σ))) (Ioi 0) := by
  set g : ℝ → ℝ := fun σ => 1 / (Real.sqrt (1 + A * σ) * Real.sqrt (1 + B * σ) *
    Real.sqrt (1 + C * σ))
  have hcont : ContinuousOn g (Ici 0) := by
    intro σ hσ
    have hσ : 0 ≤ σ := hσ
    apply ContinuousAt.continuousWithinAt
    have h1 : 0 < Real.sqrt (1 + A * σ) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < Real.sqrt (1 + B * σ) := Real.sqrt_pos.mpr (by positivity)
    have h3 : 0 < Real.sqrt (1 + C * σ) := Real.sqrt_pos.mpr (by positivity)
    exact continuousAt_const.div (by fun_prop) (by positivity)
  set m := min A (min B C)
  have hm : 0 < m := lt_min hA (lt_min hB hC)
  have hbound : ∀ σ ∈ Ioi (1 : ℝ), ‖g σ‖ ≤ m ^ (-(3 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ) := by
    intro σ hσ
    have hσ : 1 < σ := hσ
    have hσ0 : 0 < σ := by linarith
    have hmA : m ≤ A := min_le_left _ _
    have hmB : m ≤ B := (min_le_right _ _).trans (min_le_left _ _)
    have hmC : m ≤ C := (min_le_right _ _).trans (min_le_right _ _)
    have hs0 : 0 < Real.sqrt (m * σ) := Real.sqrt_pos.mpr (by positivity)
    have hprod : Real.sqrt (m * σ) ^ 3 ≤
        Real.sqrt (1 + A * σ) * Real.sqrt (1 + B * σ) * Real.sqrt (1 + C * σ) := by
      calc Real.sqrt (m * σ) ^ 3 = Real.sqrt (m * σ) * Real.sqrt (m * σ) * Real.sqrt (m * σ) := by
            ring
        _ ≤ _ := by
          gcongr
          · nlinarith
          · nlinarith
          · nlinarith
    have hpow : Real.sqrt (m * σ) ^ 3 = m ^ ((3 / 2) : ℝ) * σ ^ ((3 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        Real.mul_rpow hm.le hσ0.le]
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [g]; positivity),
      Real.rpow_neg hm.le, Real.rpow_neg hσ0.le, ← mul_inv, ← hpow]
    simp only [g]
    rw [one_div]
    exact inv_anti₀ (by positivity) hprod
  have htail : IntegrableOn g (Ioi 1) := by
    refine Integrable.mono' (((integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
      one_pos).const_mul (m ^ (-(3 / 2) : ℝ)))) ?_ ?_
    · exact (hcont.mono fun σ (hσ : 1 < σ) => (show (0 : ℝ) ≤ σ by linarith)).aestronglyMeasurable
        measurableSet_Ioi
    · exact (ae_restrict_mem measurableSet_Ioi).mono hbound
  have hhead : IntegrableOn g (Ioc 0 1) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hhead.union htail

/-- `R_F(p/A, q/B, r/C)` with the factors `A, B, C` taken out. -/
private theorem carlsonRF_div_eq {A B C p q r : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    carlsonRF (p / A : ℝ) (q / B : ℝ) (r / C : ℝ) = ((1 / 2 * (Real.sqrt A * Real.sqrt B *
      Real.sqrt C) * ∫ s in Ioi (0 : ℝ), 1 / (Real.sqrt (p + A * s) * Real.sqrt (q + B * s) *
        Real.sqrt (r + C * s)) : ℝ) : ℂ) := by
  rw [carlsonRF_eq_real_integral (by positivity) (by positivity) (by positivity)]
  congr 1
  rw [mul_assoc, ← integral_const_mul (Real.sqrt A * Real.sqrt B * Real.sqrt C)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs : 0 < s := hs
  have e : ∀ {D c : ℝ}, 0 < D → 0 < c →
      Real.sqrt (c / D + s) = Real.sqrt (c + D * s) / Real.sqrt D := fun {D c} hD hc => by
    rw [show c / D + s = (c + D * s) / D by field_simp, Real.sqrt_div' _ hD.le]
  rw [e hA hp, e hB hq, e hC hr]
  have h1 : 0 < Real.sqrt (p + A * s) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (q + B * s) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (r + C * s) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have h5 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have h6 : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  field_simp

/-- **Exercise 8.5-2** for real `0 < w < x, y, z` (then `x, y, z` are not in the closed convex
hull of `w` and the negative real axis):
`R_{-1}(1/2, 1/2, 1/2, 1/2; w, x, y, z) = 2 [(x - w)(y - w)(z - w)]^{-1/2} [R_F(1/(x - w),
1/(y - w), 1/(z - w)) - w^{1/2} R_F(x/(x - w), y/(y - w), z/(z - w))]`. -/
theorem carlsonR_quartic_eq_carlsonRF_sub {w x y z : ℝ} (hw : 0 < w) (hx : w < x) (hy : w < y)
    (hz : w < z) :
    carlsonR (-1) (fun _ : Fin 4 => 1 / 2) ![(w : ℂ), x, y, z] =
      2 * (((x : ℂ) - w) * ((y : ℂ) - w) * ((z : ℂ) - w)) ^ (-1 / 2 : ℂ) *
        (carlsonRF (1 / ((x : ℂ) - w)) (1 / ((y : ℂ) - w)) (1 / ((z : ℂ) - w)) -
          (w : ℂ) ^ (1 / 2 : ℂ) *
            carlsonRF ((x : ℂ) / (x - w)) ((y : ℂ) / (y - w)) ((z : ℂ) / (z - w))) := by
  have hA : 0 < x - w := by linarith
  have hB : 0 < y - w := by linarith
  have hC : 0 < z - w := by linarith
  set g : ℝ → ℝ := fun σ => 1 / (Real.sqrt (1 + (x - w) * σ) * Real.sqrt (1 + (y - w) * σ) *
    Real.sqrt (1 + (z - w) * σ))
  set h : ℝ → ℝ := fun s => 1 / (Real.sqrt (x + (x - w) * s) * Real.sqrt (y + (y - w) * s) *
    Real.sqrt (z + (z - w) * s))
  have hint := integrableOn_quartic_reduced hA hB hC
  have hsplit : ∫ σ in Ioi (0 : ℝ), g σ = (∫ σ in Ioo 0 w⁻¹, g σ) + ∫ σ in Ioi w⁻¹, g σ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set (Ioc_subset_Ioi_self))
      (hint.mono_set (Ioi_subset_Ioi (inv_pos.mpr hw).le)),
      Ioc_union_Ioi_eq_Ioi (inv_pos.mpr hw).le]
  have htail := integral_Ioi_inv_quartic_eq hw hx hy hz
  have hRF1 := carlsonRF_div_eq (p := 1) (q := 1) (r := 1) hA hB hC one_pos one_pos one_pos
  have hRF2 := carlsonRF_div_eq (p := x) (q := y) (r := z) hA hB hC (by linarith) (by linarith)
    (by linarith)
  push_cast at hRF1 hRF2
  rw [hRF1, hRF2, carlsonR_quartic_eq_real_integral hw (by linarith) (by linarith)
    (by linarith), integral_Ioi_quartic_eq hw hx hy hz]
  have hroot : ((w : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt w : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hw.le,
      Real.sqrt_eq_rpow]
  have hprod : (((x : ℂ) - w) * ((y : ℂ) - w) * ((z : ℂ) - w)) ^ (-1 / 2 : ℂ) =
      ((1 / (Real.sqrt (x - w) * Real.sqrt (y - w) * Real.sqrt (z - w)) : ℝ) : ℂ) := by
    have := cpow_neg_half_eq (c := (x - w) * (y - w) * (z - w)) (t := 0) (by simp; positivity)
    push_cast at this
    simp only [add_zero] at this
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul hA.le]
    push_cast; ring
  rw [hroot, hprod]
  have h4 : 0 < Real.sqrt (x - w) := Real.sqrt_pos.mpr hA
  have h5 : 0 < Real.sqrt (y - w) := Real.sqrt_pos.mpr hB
  have h6 : 0 < Real.sqrt (z - w) := Real.sqrt_pos.mpr hC
  have hmain : ∫ σ in Ioo 0 w⁻¹, g σ = (∫ σ in Ioi (0 : ℝ), g σ) - Real.sqrt w * ∫ s in Ioi 0, h s
    := by rw [hsplit, htail]; ring
  simp only [g, h] at hmain
  rw [hmain]
  set I0 := ∫ σ in Ioi (0 : ℝ), 1 / (Real.sqrt (1 + (x - w) * σ) *
    Real.sqrt (1 + (y - w) * σ) * Real.sqrt (1 + (z - w) * σ))
  set J := ∫ s in Ioi (0 : ℝ), 1 / (Real.sqrt (x + (x - w) * s) *
    Real.sqrt (y + (y - w) * s) * Real.sqrt (z + (z - w) * s))
  have h4' : (Real.sqrt (x - w) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h4.ne'
  have h5' : (Real.sqrt (y - w) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h5.ne'
  have h6' : (Real.sqrt (z - w) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h6.ne'
  push_cast
  field_simp

end Carlson
