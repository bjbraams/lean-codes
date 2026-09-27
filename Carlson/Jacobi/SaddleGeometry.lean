/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipseCoordinates

/-!
# The Euler saddle contour for second-kind Jacobi functions

For endpoint square roots `a, b` with positive real part of `a * conj b`,
the fractional linear curve `u = b t / (a(1-t)+bt)` passes through the Euler
saddle at `t = 1/2`. Its combined weight-resolvent factor is bounded by
`1/‖a+b‖²`, the rate required by Carlson's elliptic convergence theory.

This module proves the algebraic substitution and the complex norm inequality.
The interior of the curve lies in the principal branch domains of both
endpoint weights. This module does not deform an integral to the curve or
assert asymptotics: integral invariance and justification at the endpoints
remain necessary before the bound applies to the Euler integral.

## Main results

* `norm_jacobiSaddleDenominator_ge`: the complex denominator estimate.
* `jacobiEulerKernel_mobius`: the exact rational substitution identity.
* `norm_jacobiEulerKernel_mobius_le`: the saddle-contour exponential bound.
* `exists_jacobiSaddleRoots`: compatible roots at every point off the focal segment.
* `exists_jacobiEulerSaddle_bound`: the bound expressed in Carlson’s mean radius.
* `jacobiMobius_mem_slitPlane`: both endpoint weights remain on their principal branches.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.4, the saddle-point argument for Representation 7.4-3.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Set
open scoped ComplexConjugate

/-- The product of the two affine square-root factors controls the squared
square-root sum on the unit interval. This inequality retains the complex phases. -/
theorem norm_jacobiSaddleDenominator_ge {a b : ℂ}
    (hab : 0 ≤ (a * conj b).re) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t * (1 - t) * ‖a + b‖ ^ 2 ≤
      ‖(a * (1 - (t : ℂ)) + b * t) * (b * (1 - (t : ℂ)) + a * t)‖ := by
  let v := t * (1 - t)
  let c := (1 - 2 * t) ^ 2
  have hv : 0 ≤ v := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hc : 0 ≤ c := sq_nonneg _
  have hcross : 0 ≤ ((a + b) ^ 2 * conj (a * b)).re := by
    have he : ((a + b) ^ 2 * conj (a * b)).re =
        (normSq a + normSq b) * (a * conj b).re + 2 * normSq a * normSq b := by
      simp only [pow_two, mul_re, mul_im, add_re, add_im, conj_re, conj_im, normSq_apply]
      ring
    rw [he]
    have := normSq_nonneg a
    have := normSq_nonneg b
    positivity
  have hscaled : 0 ≤ (((v : ℂ) * (a + b) ^ 2) * conj ((c : ℂ) * (a * b))).re := by
    have he : (((v : ℂ) * (a + b) ^ 2) * conj ((c : ℂ) * (a * b))).re =
        v * c * ((a + b) ^ 2 * conj (a * b)).re := by
      simp only [map_mul, conj_ofReal, mul_re, mul_im, ofReal_re, ofReal_im]
      ring
    rw [he]
    positivity
  have hn : ‖(v : ℂ) * (a + b) ^ 2‖ ≤
      ‖(v : ℂ) * (a + b) ^ 2 + (c : ℂ) * (a * b)‖ := by
    have h := normSq_add ((v : ℂ) * (a + b) ^ 2) ((c : ℂ) * (a * b))
    simp only [normSq_eq_norm_sq] at h
    nlinarith [sq_nonneg ‖(c : ℂ) * (a * b)‖,
      norm_nonneg ((v : ℂ) * (a + b) ^ 2),
      norm_nonneg ((v : ℂ) * (a + b) ^ 2 + (c : ℂ) * (a * b))]
  have he : (v : ℂ) * (a + b) ^ 2 + (c : ℂ) * (a * b) =
      (a * (1 - (t : ℂ)) + b * t) * (b * (1 - (t : ℂ)) + a * t) := by
    dsimp [v, c]
    push_cast
    ring
  rw [he, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hv] at hn
  exact hn

/-- The fractional linear change of variable exposes the two affine factors
in the combined Euler weight and resolvent. All denominators are explicit. -/
theorem jacobiEulerKernel_mobius (a b t : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hL : a * (1 - t) + b * t ≠ 0) :
    let u := b * t / (a * (1 - t) + b * t)
    u * (1 - u) / (u * a ^ 2 + (1 - u) * b ^ 2) =
      t * (1 - t) / ((a * (1 - t) + b * t) * (b * (1 - t) + a * t)) := by
  dsimp only
  have hden : b * t / (a * (1 - t) + b * t) * a ^ 2 +
      (1 - b * t / (a * (1 - t) + b * t)) * b ^ 2 =
        a * b * (b * (1 - t) + a * t) / (a * (1 - t) + b * t) := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

/-- Along the fractional linear saddle curve the Euler factor has the sharp
square-root-sum upper rate. Positivity of the root pairing keeps both affine
factors nonzero throughout the open unit interval. -/
theorem norm_jacobiEulerKernel_mobius_le {a b : ℂ} (hab : 0 < (a * conj b).re)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let u := b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t)
    ‖u * (1 - u) / (u * a ^ 2 + (1 - u) * b ^ 2)‖ ≤ 1 / ‖a + b‖ ^ 2 := by
  have ha : a ≠ 0 := by intro h; simp [h] at hab
  have hb : b ≠ 0 := by intro h; simp [h] at hab
  have hsum : a + b ≠ 0 := by
    intro h
    have hh := normSq_add a b
    rw [h, normSq_zero] at hh
    linarith [normSq_nonneg a, normSq_nonneg b]
  have hsq : 0 < ‖a + b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsum)
  have htpos : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hbound := norm_jacobiSaddleDenominator_ge hab.le ⟨ht.1.le, ht.2.le⟩
  have hden := (mul_pos htpos hsq).trans_le hbound
  have hne := norm_pos_iff.mp hden
  dsimp only
  rw [jacobiEulerKernel_mobius a b t ha hb (mul_ne_zero_iff.mp hne).1]
  have hnum : ‖(t : ℂ) * (1 - t)‖ = t * (1 - t) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos htpos]
  rw [norm_div, hnum]
  exact (div_le_div_iff₀ hden hsq).mpr (by simpa only [one_mul] using hbound)


/-- An aligned choice of endpoint square roots selects the larger of the two
characteristic moduli in the confocal mean-radius formula. -/
theorem jacobiEllipseRadius_eq_sq_of_re_mul_conj_nonneg (r s z a b : ℂ)
    (ha : a ^ 2 = z - r) (hb : b ^ 2 = z - s) (hab : 0 ≤ (a * conj b).re) :
    jacobiEllipseRadius r s z = ‖a + b‖ ^ 2 / 4 := by
  have hadd := normSq_add a b
  have hsub := normSq_sub a b
  simp only [normSq_eq_norm_sq] at hadd hsub
  rw [jacobiEllipseRadius_eq_max_sq r s z a b ha hb, max_eq_left (by linarith)]

/-- Off the focal segment the signs of the endpoint square roots can always be
chosen with strictly positive real pairing. No principal square-root branch is
needed, and coincident endpoints are included. -/
theorem exists_jacobiSaddleRoots (r s z : ℂ) (hz : z ∉ segment ℝ r s) :
    ∃ a b : ℂ, a ^ 2 = z - r ∧ b ^ 2 = z - s ∧ 0 < (a * conj b).re := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (z - r) (by norm_num : 0 < (2 : ℕ))
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (z - s) (by norm_num : 0 < (2 : ℕ))
  have hab : (a * conj b).re ≠ 0 := by
    intro hzero
    have hadd := normSq_add a b
    have hsub := normSq_sub a b
    simp only [normSq_eq_norm_sq, hzero, mul_zero, add_zero, sub_zero] at hadd hsub
    have heq : ‖a + b‖ = ‖a - b‖ := by
      nlinarith [norm_nonneg (a + b), norm_nonneg (a - b)]
    have he : (a + b) * (a - b) = s - r := by linear_combination ha - hb
    have hn : ‖a + b‖ ^ 2 = ‖r - s‖ := by
      calc
        _ = ‖a + b‖ * ‖a - b‖ := by rw [← heq, pow_two]
        _ = _ := by rw [← norm_mul, he, norm_sub_rev]
    apply hz
    apply (jacobiEllipseRadius_eq_min_iff r s z).mp
    rw [jacobiEllipseRadius_eq_sq_of_re_mul_conj_nonneg r s z a b ha hb (by rw [hzero]), hn]
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, -b, ha, by simpa using hb, ?_⟩
    simpa only [map_neg, mul_neg, neg_re] using neg_pos.mpr h
  · exact ⟨a, b, ha, hb, h⟩

/-- Every exterior point admits a fractional linear saddle curve whose Euler
factor is bounded by the reciprocal of four times its confocal mean radius.
This is the geometric estimate needed for the complex integral deformation. -/
theorem exists_jacobiEulerSaddle_bound (r s z : ℂ) (hz : z ∉ segment ℝ r s) :
    ∃ a b : ℂ, a ^ 2 = z - r ∧ b ^ 2 = z - s ∧ 0 < (a * conj b).re ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        let u := b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t)
        ‖u * (1 - u) / (u * (z - r) + (1 - u) * (z - s))‖ ≤
          1 / (4 * jacobiEllipseRadius r s z) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_jacobiSaddleRoots r s z hz
  refine ⟨a, b, ha, hb, hab, fun t ht => ?_⟩
  rw [jacobiEllipseRadius_eq_sq_of_re_mul_conj_nonneg r s z a b ha hb hab.le,
    show 4 * (‖a + b‖ ^ 2 / 4) = ‖a + b‖ ^ 2 by ring, ← ha, ← hb]
  exact norm_jacobiEulerKernel_mobius_le hab ht


/-- An interior point of the saddle curve has positive real part. -/
private theorem re_jacobiMobius_pos {a b : ℂ} (hab : 0 < (a * conj b).re)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t)).re := by
  have hb : b ≠ 0 := by intro h; simp [h] at hab
  have hdiv : 0 < (a / b).re := by
    rw [div_re, ← add_div]
    apply div_pos _ (normSq_pos.mpr hb)
    simpa only [mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add] using hab
  let D : ℂ := a / b * (1 - (t : ℂ)) + t
  have hD : 0 < D.re := by
    dsimp [D]
    simp only [mul_re, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im,
      sub_self, mul_zero, sub_zero]
    exact add_pos (mul_pos hdiv (sub_pos.mpr ht.2)) ht.1
  have he : b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t) = (t : ℂ) / D := by
    have hD' : D = (a * (1 - (t : ℂ)) + b * t) / b := by
      dsimp [D]
      field_simp
    rw [hD', div_div_eq_mul_div]
    ring
  rw [he, div_re]
  simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos ht.1 hD) (normSq_pos.mpr (ne_zero_of_re_pos hD))

/-- Both endpoint weights use their principal branches along the interior of
the saddle curve: the curve lies in the vertical strip `0 < re u < 1`. -/
theorem jacobiMobius_mem_slitPlane {a b : ℂ} (hab : 0 < (a * conj b).re)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let u := b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t)
    u ∈ slitPlane ∧ 1 - u ∈ slitPlane := by
  have hba : 0 < (b * conj a).re := by
    convert hab using 1
    simp only [mul_re, conj_re, conj_im]
    ring
  have hleft := re_jacobiMobius_pos hab ht
  have hright := re_jacobiMobius_pos hba
    (t := 1 - t) ⟨sub_pos.mpr ht.2, by linarith [ht.1]⟩
  have hL : a * (1 - (t : ℂ)) + b * t ≠ 0 := by
    intro h
    simp [h] at hleft
  have he : 1 - b * (t : ℂ) / (a * (1 - (t : ℂ)) + b * t) =
      a * ((1 - t : ℝ) : ℂ) / (b * (1 - ((1 - t : ℝ) : ℂ)) + a * ((1 - t : ℝ) : ℂ)) := by
    push_cast
    rw [show b * (1 - (1 - (t : ℂ))) + a * (1 - t) = a * (1 - t) + b * t by ring]
    field_simp
    ring
  exact ⟨Or.inl hleft, Or.inl (by rw [he]; exact hright)⟩

end Carlson.TwoVariable
