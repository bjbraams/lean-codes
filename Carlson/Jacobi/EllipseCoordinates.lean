/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Ellipse
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import ToMathlib.Analysis.Connected

/-!
# Square-root coordinates for confocal ellipses

Carlson's branch-independent mean radius equals the larger of the two squared
square-root sums divided by four. Thus it selects the larger characteristic
modulus in the degree asymptotics. Either square root of each endpoint difference
may be used, so no branch assumptions or distinct-endpoint restrictions occur.
The normalized Joukowski map sends circular exteriors onto elliptic exteriors,
which are therefore preconnected. Off the focal segment, one characteristic root
strictly dominates the other in modulus. These are geometric results; the analytic
large-degree estimates for Jacobi functions are not proved here.

## Main results

* `jacobiEllipseRadius_eq_max_sq`: the square-root formula for the elliptic mean radius.
* `exists_jacobiCharacteristicRoots`: the two characteristic roots and their moduli.
* `jacobiEllipseRadius_jacobiJoukowski`: the exterior coordinate modulus is the mean radius.
* `image_jacobiJoukowski_exterior`: circular exteriors map onto elliptic exteriors.
* `isPreconnected_jacobiEllipse_exterior`: connectedness for analytic continuation.
* `exists_dominant_jacobiCharacteristicRoot`: strict dominance off the segment.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.5, equation (3).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Set

/-- The mean radius is the larger squared modulus of the two square-root sums,
divided by four. This identity is independent of both square-root signs. -/
theorem jacobiEllipseRadius_eq_max_sq (r s z a b : ℂ)
    (ha : a ^ 2 = z - r) (hb : b ^ 2 = z - s) :
    jacobiEllipseRadius r s z = max (‖a + b‖ ^ 2) (‖a - b‖ ^ 2) / 4 := by
  have ha' : ‖a‖ ^ 2 = ‖z - r‖ := by rw [← norm_pow, ha]
  have hb' : ‖b‖ ^ 2 = ‖z - s‖ := by rw [← norm_pow, hb]
  have hsum : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖z - r‖ + ‖z - s‖) := by
    rw [← ha', ← hb']
    simp only [← normSq_eq_norm_sq, normSq_add, normSq_sub]
    ring
  have he : (a + b) * (a - b) = s - r := by linear_combination ha - hb
  have hprod : ‖a + b‖ ^ 2 * ‖a - b‖ ^ 2 = ‖r - s‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, he, norm_sub_rev]
  have hrad : (‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2 =
      ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / 2) ^ 2 := by
    nlinarith [sq_nonneg (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 - 2 * (‖z - r‖ + ‖z - s‖))]
  rw [jacobiEllipseRadius, hrad, Real.sqrt_sq_eq_abs]
  rcases le_total (‖a + b‖ ^ 2) (‖a - b‖ ^ 2) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    linarith

/-- The two characteristic roots have sum equal to the centered coordinate,
product equal to the squared quarter-focal difference, and maximum modulus equal
to Carlson's mean radius. -/
theorem exists_jacobiCharacteristicRoots (r s z : ℂ) :
    ∃ u v : ℂ, u + v = z - (r + s) / 2 ∧ u * v = (r - s) ^ 2 / 16 ∧
      jacobiEllipseRadius r s z = max ‖u‖ ‖v‖ := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (z - r) (by norm_num : 0 < (2 : ℕ))
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (z - s) (by norm_num : 0 < (2 : ℕ))
  refine ⟨(a + b) ^ 2 / 4, (a - b) ^ 2 / 4, ?_, ?_, ?_⟩
  · linear_combination (ha + hb) / 2
  · have he : (a + b) * (a - b) = s - r := by linear_combination ha - hb
    calc
      _ = ((a + b) * (a - b)) ^ 2 / 16 := by ring
      _ = _ := by rw [he]; ring
  · simpa only [norm_div, norm_pow, norm_ofNat, max_div_div_right (by norm_num : (0 : ℝ) ≤ 4)]
      using jacobiEllipseRadius_eq_max_sq r s z a b ha hb

/-- The Joukowski map with foci `r, s`, normalized so that the modulus of its
exterior coordinate is Carlson's elliptic mean radius. -/
@[expose] def jacobiJoukowski (r s w : ℂ) : ℂ :=
  (r + s) / 2 + w + (r - s) ^ 2 / (16 * w)

/-- At a nonzero Joukowski coordinate, the mean radius is the maximum of the
moduli of the two reciprocal characteristic coordinates. -/
theorem jacobiEllipseRadius_jacobiJoukowski_eq_max (r s w : ℂ) (hw : w ≠ 0) :
    jacobiEllipseRadius r s (jacobiJoukowski r s w) =
      max ‖w‖ (‖r - s‖ ^ 2 / (16 * ‖w‖)) := by
  obtain ⟨u, v, hsum, hprod, hmu⟩ := exists_jacobiCharacteristicRoots r s (jacobiJoukowski r s w)
  let e := (r - s) ^ 2 / (16 * w)
  have hs : u + v = w + e := by dsimp [jacobiJoukowski] at hsum; dsimp [e]; linear_combination hsum
  have hp : u * v = w * e := by rw [hprod]; dsimp [e]; field_simp
  have hz : (u - w) * (v - w) = 0 := by linear_combination hp - w * hs
  have he : ‖e‖ = ‖r - s‖ ^ 2 / (16 * ‖w‖) := by simp [e, norm_pow]
  rcases mul_eq_zero.mp hz with hu | hv
  · have hu := sub_eq_zero.mp hu
    have hv : v = e := by linear_combination hs - hu
    simpa only [hu, hv, he] using hmu
  · have hv := sub_eq_zero.mp hv
    have hu : u = e := by linear_combination hs - hv
    simpa only [hu, hv, he, max_comm] using hmu

/-- On the exterior branch of the Joukowski map, coordinate modulus is exactly
the elliptic mean radius, including the degenerate case of coincident foci. -/
theorem jacobiEllipseRadius_jacobiJoukowski (r s w : ℂ) (hw : w ≠ 0)
    (hlarge : ‖r - s‖ / 4 ≤ ‖w‖) :
    jacobiEllipseRadius r s (jacobiJoukowski r s w) = ‖w‖ := by
  rw [jacobiEllipseRadius_jacobiJoukowski_eq_max r s w hw, max_eq_left]
  apply (div_le_iff₀ (mul_pos (by norm_num) (norm_pos_iff.mpr hw))).mpr
  nlinarith [norm_nonneg (r - s)]

/-- Every point of positive elliptic mean radius has an exterior Joukowski
coordinate of precisely that modulus. -/
theorem exists_jacobiJoukowski_preimage (r s z : ℂ) (hz : 0 < jacobiEllipseRadius r s z) :
    ∃ w : ℂ, ‖w‖ = jacobiEllipseRadius r s z ∧ jacobiJoukowski r s w = z := by
  obtain ⟨u, v, hsum, hprod, hmu⟩ := exists_jacobiCharacteristicRoots r s z
  have H (u v : ℂ) (hs : u + v = z - (r + s) / 2) (hp : u * v = (r - s) ^ 2 / 16)
      (hm : ‖u‖ = jacobiEllipseRadius r s z) :
      ∃ w : ℂ, ‖w‖ = jacobiEllipseRadius r s z ∧ jacobiJoukowski r s w = z := by
    have hu : u ≠ 0 := norm_pos_iff.mp (hm.symm ▸ hz)
    refine ⟨u, hm, ?_⟩
    have hv : (r - s) ^ 2 / (16 * u) = v := by
      apply (div_eq_iff (mul_ne_zero (by norm_num) hu)).mpr
      linear_combination -16 * hp
    rw [jacobiJoukowski, hv]
    linear_combination hs
  rcases le_total ‖v‖ ‖u‖ with h | h
  · exact H u v hsum hprod (by simpa only [max_eq_left h] using hmu.symm)
  · exact H v u (by simpa only [add_comm] using hsum)
      (by simpa only [mul_comm] using hprod) (by simpa only [max_eq_right h] using hmu.symm)

/-- The exterior of a confocal elliptic disk is the Joukowski image of the
exterior of the circle with the same mean radius. -/
theorem image_jacobiJoukowski_exterior (r s : ℂ) {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    jacobiJoukowski r s '' {w : ℂ | ρ < ‖w‖} = {z | ρ < jacobiEllipseRadius r s z} := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hρ0.trans hw)
    simpa only [mem_ofPred_eq, jacobiEllipseRadius_jacobiJoukowski r s w hw0 (hρ.trans hw).le]
        using hw
  · intro hz
    obtain ⟨w, hw, he⟩ := exists_jacobiJoukowski_preimage r s z (hρ0.trans hz)
    exact ⟨w, by simpa only [mem_ofPred_eq, hw] using hz, he⟩

/-- The exterior of every nondegenerate confocal elliptic disk is preconnected.
This includes circular disks when the foci coincide. -/
theorem isPreconnected_jacobiEllipse_exterior (r s : ℂ) {ρ : ℝ}
    (hρ : ‖r - s‖ / 4 < ρ) :
    IsPreconnected {z | ρ < jacobiEllipseRadius r s z} := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  rw [← image_jacobiJoukowski_exterior r s hρ]
  have hpre : IsPreconnected {w : ℂ | ρ < ‖w‖} := by
    convert (isPreconnected_compl_closedBall (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) 0 ρ) using 1
    ext w
    simp only [mem_ofPred_eq, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  apply hpre.image
  intro w hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hρ0.trans hw)
  exact (((continuousAt_const.add continuousAt_id).add
    (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero (by norm_num) hw0))).continuousWithinAt)

/-- Off the focal segment, one characteristic root strictly dominates the
other in modulus. Its modulus is the mean radius. This is the geometric reason
only one exponential term contributes to the exterior root-growth limit. -/
theorem exists_dominant_jacobiCharacteristicRoot (r s z : ℂ)
    (hz : z ∉ segment ℝ r s) :
    ∃ u v : ℂ, u + v = z - (r + s) / 2 ∧ u * v = (r - s) ^ 2 / 16 ∧
      ‖u‖ = jacobiEllipseRadius r s z ∧ ‖v‖ < ‖u‖ := by
  have hmin : ‖r - s‖ / 4 < jacobiEllipseRadius r s z :=
    lt_of_le_of_ne (le_jacobiEllipseRadius r s z)
      (fun he => hz ((jacobiEllipseRadius_eq_min_iff r s z).mp he.symm))
  obtain ⟨u, v, hs, hp, hm⟩ := exists_jacobiCharacteristicRoots r s z
  have H (u v : ℂ) (hp : u * v = (r - s) ^ 2 / 16)
      (hm : ‖u‖ = jacobiEllipseRadius r s z) (hle : ‖v‖ ≤ ‖u‖) : ‖v‖ < ‖u‖ := by
    have hn : ‖u‖ * ‖v‖ = ‖r - s‖ ^ 2 / 16 := by
      simpa only [norm_mul, norm_div, norm_pow, norm_ofNat] using congrArg norm hp
    by_contra h
    have he : ‖v‖ = ‖u‖ := le_antisymm hle (le_of_not_gt h)
    rw [he] at hn
    rw [← hm] at hmin
    nlinarith [norm_nonneg (r - s)]
  rcases le_total ‖v‖ ‖u‖ with h | h
  · have hu : ‖u‖ = jacobiEllipseRadius r s z := by simpa only [max_eq_left h] using hm.symm
    exact ⟨u, v, hs, hp, hu, H u v hp hu h⟩
  · have hv : ‖v‖ = jacobiEllipseRadius r s z := by simpa only [max_eq_right h] using hm.symm
    have hp' : v * u = (r - s) ^ 2 / 16 := by simpa only [mul_comm] using hp
    exact ⟨v, u, by simpa only [add_comm] using hs, hp', hv, H v u hp' hv h⟩

end Carlson.TwoVariable
