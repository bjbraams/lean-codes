/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindBounds
public import Carlson.Jacobi.SecondKindInfinity
public import Carlson.Jacobi.EllipseCoordinates

/-!
# Elliptic-rate bounds for second-kind Jacobi functions on exterior rays

On the real ray to the right of both endpoints, the combined Euler factor
`t(1-t)/(z-tr-(1-t)s)` is bounded by `1/(4μ(z))`, where `μ` is Carlson's
confocal mean radius. Keeping this factor intact gives the sharp exponential
upper rate for the second-kind functions, for arbitrary complex Jacobi
parameters. A finite degree shift suffices to enter the Euler convergence range.

These estimates prove absolute convergence of second-kind series on the ray
when the coefficient growth rate is less than `μ(z)`. They do not assert the
root-growth lower bound, divergence, or convergence on the whole elliptic
exterior; the latter requires a complex contour argument. Affine covariance
transports the estimates to either exterior ray of an arbitrary complex focal
segment. Coincident endpoints are included.

## Main results

* `jacobiEllipseRadius_ofReal_of_lt`: the positive square-root formula on the ray.
* `norm_jacobiEulerKernel_ofReal_le`: the elliptic bound for the Euler factor.
* `summable_norm_mul_jacobiSecondKind_of_kernel_bound`: convergence from a bound
  on the combined Euler factor, without restrictions on the complex parameters.
* `summable_norm_mul_jacobiSecondKind_ofReal`: convergence at the elliptic rate
  on the exterior real ray.
* `summable_norm_mul_jacobiSecondKind_on_ray`: the corresponding result after
  any invertible complex affine change of variables.
* `exists_bound_pow_mul_norm_jacobiSecondKind_on_ray`: every exponential upper
  rate greater than the reciprocal mean radius is valid on these rays.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.4–7.5, particularly Theorems 7.5-1 and 7.5-3.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter
open scoped Topology

/-- To the right of both real foci the positive square-root sum gives the
confocal mean radius. Coincident foci are allowed. -/
theorem jacobiEllipseRadius_ofReal_of_lt {r s z : ℝ} (hr : r < z) (hs : s < z) :
    jacobiEllipseRadius (r : ℂ) s z =
      (Real.sqrt (z - r) + Real.sqrt (z - s)) ^ 2 / 4 := by
  have ha := Real.sqrt_nonneg (z - r)
  have hb := Real.sqrt_nonneg (z - s)
  have h := jacobiEllipseRadius_eq_max_sq (r : ℂ) s z
    (Real.sqrt (z - r)) (Real.sqrt (z - s))
    (by rw [← ofReal_pow, Real.sq_sqrt (sub_pos.mpr hr).le, ofReal_sub])
    (by rw [← ofReal_pow, Real.sq_sqrt (sub_pos.mpr hs).le, ofReal_sub])
  rw [← ofReal_add, ← ofReal_sub, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    max_eq_left (by nlinarith [mul_nonneg ha hb])] at h
  exact h

/-- The rightmost real endpoint gives a lower bound for distance from a real
point to the complex focal segment. This bound is positive on the exterior ray. -/
theorem sub_max_le_norm_sub_of_mem_segment {r s : ℝ} (z : ℝ)
    {w : ℂ} (hw : w ∈ segment ℝ (r : ℂ) s) :
    z - max r s ≤ ‖(z : ℂ) - w‖ := by
  rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
  have he : (z : ℂ) - (a • (r : ℂ) + b • (s : ℂ)) = (z - (a * r + b * s) : ℝ) := by
    simp [real_smul, ofReal_sub, ofReal_add, ofReal_mul]
  rw [he, norm_real, Real.norm_eq_abs]
  have hle : a * r + b * s ≤ max r s := by
    calc
      _ ≤ a * max r s + b * max r s := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  exact (by linarith : z - max r s ≤ z - (a * r + b * s)).trans (le_abs_self _)

/-- The combined weight-resolvent factor is bounded by the reciprocal of four
times the elliptic mean radius on the exterior real ray. -/
theorem norm_jacobiEulerKernel_ofReal_le {r s z t : ℝ} (hr : r < z) (hs : s < z)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖((t : ℂ) * (1 - t)) / ((z : ℂ) - (t * r + (1 - t) * s))‖ ≤
      1 / (4 * jacobiEllipseRadius (r : ℂ) s z) := by
  let a := Real.sqrt (z - r)
  let b := Real.sqrt (z - s)
  have ha : 0 < a := Real.sqrt_pos.mpr (sub_pos.mpr hr)
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have ha2 : a ^ 2 = z - r := Real.sq_sqrt (sub_pos.mpr hr).le
  have hb2 : b ^ 2 = z - s := Real.sq_sqrt (sub_pos.mpr hs).le
  have hden : 0 < z - (t * r + (1 - t) * s) := by
    have h2 : 0 < t * (z - r) + (1 - t) * (z - s) := by
      by_cases h : t = 0
      · simp [h, sub_pos.mpr hs]
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h))
          (sub_pos.mpr hr)) (mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hs).le)
    nlinarith
  have he : ((t : ℂ) * (1 - t)) / ((z : ℂ) - (t * r + (1 - t) * s)) =
      ((t * (1 - t) / (z - (t * r + (1 - t) * s)) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) hden.le),
    jacobiEllipseRadius_ofReal_of_lt hr hs]
  change t * (1 - t) / (z - (t * r + (1 - t) * s)) ≤ 1 / (4 * ((a + b) ^ 2 / 4))
  rw [show 4 * ((a + b) ^ 2 / 4) = (a + b) ^ 2 by ring]
  apply (div_le_div_iff₀ hden (sq_pos_of_pos (add_pos ha hb))).mpr
  rw [show z - (t * r + (1 - t) * s) = t * a ^ 2 + (1 - t) * b ^ 2 by
    rw [ha2, hb2]; ring]
  nlinarith only [sq_nonneg (a * t - b * (1 - t))]

/-- A bound for the combined Euler kernel gives absolute convergence after
geometric coefficient growth, for every pair of complex Jacobi parameters. -/
theorem summable_norm_mul_jacobiSecondKind_of_kernel_bound (α β r s : ℂ)
    {a : ℕ → ℂ} {C R d q : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hq : 0 ≤ q)
    (hRq : 4 * (R * q) < 1) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {z : ℂ}
    (hdist : ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖)
    (hkernel : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖((t : ℂ) * (1 - t)) / (z - (t * r + (1 - t) * s))‖ ≤ q) :
    Summable (fun n => ‖a n * jacobiSecondKind α β r s n z‖) := by
  have hz : z ∉ segment ℝ r s := by
    intro h
    have := hdist z h
    simp only [sub_self, norm_zero] at this
    linarith
  obtain ⟨N, hα, hβ, B, hB, hbound⟩ := exists_jacobiWeight_shift_bound α β
  apply (summable_nat_add_iff N).mp
  have hsum := (summable_norm_betaShiftNormalization_mul_pow
    (α + N + 1) (β + N + 1) (mul_nonneg hR hq) hRq).mul_left
      (C * R ^ N * (B * (d⁻¹) ^ (N + 1)))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro k
  have hbound' := norm_jacobiSecondKind_add_le_of_kernel_bound α β r s N k
    hα hβ hB hd hq hbound hz hdist hkernel
  rw [show k + N = N + k by omega, norm_mul]
  apply (mul_le_mul (ha _) hbound' (norm_nonneg _) (by positivity)).trans
  apply le_of_eq
  simp only [pow_add, mul_pow]
  ring

/-- Second-kind series with geometric coefficient bound `R` converge absolutely
to the right of the real focal segment whenever `R` is less than the confocal
mean radius. No restrictions are imposed on the complex Jacobi parameters. -/
theorem summable_norm_mul_jacobiSecondKind_ofReal (α β : ℂ) {r s z : ℝ}
    (hr : r < z) (hs : s < z) {a : ℕ → ℂ} {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) (hRμ : R < jacobiEllipseRadius (r : ℂ) s z) :
    Summable (fun n => ‖a n * jacobiSecondKind α β (r : ℂ) s n z‖) := by
  have hμ : 0 < jacobiEllipseRadius (r : ℂ) s z := hR.trans_lt hRμ
  apply summable_norm_mul_jacobiSecondKind_of_kernel_bound α β (r : ℂ) s
    hC hR (sub_pos.mpr (max_lt hr hs)) (by positivity : 0 ≤ 1 / (4 * jacobiEllipseRadius (r : ℂ) s z))
    ?_ ha (fun w hw => sub_max_le_norm_sub_of_mem_segment z hw) ?_
  · rw [show 4 * (R * (1 / (4 * jacobiEllipseRadius (r : ℂ) s z))) =
        R / jacobiEllipseRadius (r : ℂ) s z by ring, div_lt_one hμ]
    exact hRμ
  · intro t ht
    exact norm_jacobiEulerKernel_ofReal_le hr hs ⟨ht.1.le, ht.2.le⟩


/-- Real points to the right of both real endpoints avoid their complex segment. -/
theorem not_mem_segment_ofReal_of_lt {r s z : ℝ} (hr : r < z) (hs : s < z) :
    (z : ℂ) ∉ segment ℝ (r : ℂ) s := by
  intro hz
  have h := sub_max_le_norm_sub_of_mem_segment z hz
  simp only [sub_self, norm_zero] at h
  have := max_lt hr hs
  linarith

/-- The elliptic-rate convergence theorem is covariant under every invertible
complex affine map. Thus it applies to either exterior ray of any complex focal
segment, including coincident endpoints. -/
theorem summable_norm_mul_jacobiSecondKind_on_ray (α β c d : ℂ) (hc : c ≠ 0)
    {r s z : ℝ} (hr : r < z) (hs : s < z) {a : ℕ → ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    (hRμ : R < jacobiEllipseRadius (c * r + d) (c * s + d) (c * z + d)) :
    Summable (fun n => ‖a n *
      jacobiSecondKind α β (c * r + d) (c * s + d) n (c * z + d)‖) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsum := summable_norm_mul_jacobiSecondKind_ofReal α β hr hs hC
    (div_nonneg hR hcpos.le) (a := fun n => a n / c ^ n) (R := R / ‖c‖)
    (fun n => by
      rw [norm_div, norm_pow]
      calc
        _ ≤ (C * R ^ n) / ‖c‖ ^ n := div_le_div_of_nonneg_right (ha n) (by positivity)
        _ = C * (R / ‖c‖) ^ n := by rw [div_pow]; ring)
    (by rw [div_lt_iff₀ hcpos]; simpa only [jacobiEllipseRadius_affine, mul_comm] using hRμ)
  apply (hsum.mul_left ‖c‖⁻¹).congr
  intro n
  rw [jacobiSecondKind_affine α β (r : ℂ) s c d n hc (not_mem_segment_ofReal_of_lt hr hs)]
  simp only [norm_mul, norm_pow, zpow_neg,
    show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast,
    norm_inv, pow_succ, mul_inv_rev, div_eq_mul_inv]
  ring

/-- On an exterior ray the second-kind functions admit every exponential upper
rate strictly greater than the reciprocal ellipse radius. The formulation with
`R^n` also allows `R = 0`. No root-limit lower estimate is asserted. -/
theorem exists_bound_pow_mul_norm_jacobiSecondKind_on_ray (α β c d : ℂ) (hc : c ≠ 0)
    {r s z : ℝ} (hr : r < z) (hs : s < z) {R : ℝ} (hR : 0 ≤ R)
    (hRμ : R < jacobiEllipseRadius (c * r + d) (c * s + d) (c * z + d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      R ^ n * ‖jacobiSecondKind α β (c * r + d) (c * s + d) n (c * z + d)‖ ≤ C := by
  have hsum := summable_norm_mul_jacobiSecondKind_on_ray α β c d hc hr hs
    (C := 1) (by norm_num) hR (a := fun n => (R : ℂ) ^ n)
    (fun n => by simp [norm_pow, abs_of_nonneg hR]) hRμ
  simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hR] at hsum
  refine ⟨∑' n, R ^ n * ‖jacobiSecondKind α β (c * r + d) (c * s + d) n (c * z + d)‖,
    tsum_nonneg (fun n => by positivity), fun n => ?_⟩
  exact hsum.le_tsum n (fun n _ => by positivity)

end Carlson.TwoVariable
