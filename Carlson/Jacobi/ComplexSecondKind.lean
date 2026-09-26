/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindIntegral
public import Carlson.Jacobi.SecondKindInfinity
public import Carlson.Jacobi.ComplexOrthogonality
public import Carlson.Jacobi.BoundaryKernel

/-!
# Complex-parameter Cauchy representations and Jacobi boundary jumps

For `re α, re β > -1`, the second-kind Jacobi function is the Cauchy transform
of a complex Jacobi density. The weight uses principal powers on the real unit
interval. Its symmetric boundary jump is `-2πi` times that density. Affine
covariance transports the jump to every nondegenerate complex segment.
These are limits of differences; no separate boundary limits are asserted.

## Main results

* `jacobiSecondKind_eq_complexEulerIntegral`: the native weighted resolvent.
* `jacobiSecondKind_eq_complexCauchyIntegral`: the Jacobi Cauchy representation.
* `tendsto_jacobiSecondKind_sub_complex`: the jump on the unit segment.
* `tendsto_jacobiSecondKind_sub_complex_affine`: the jump at arbitrary endpoints.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8, in particular equation (5) and Exercise 7.8-8.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Dirichlet Polynomial MeasureTheory Set Filter
open scoped Topology

/-- The scalar normalizing the Jacobi density in its second-kind Cauchy integral. -/
def jacobiCauchyCoefficient (α β : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * Gamma (α + n + 1 + (β + n + 1)) /
    (Gamma (α + n + 1) * Gamma (β + n + 1))

/-- The Euler representation of the second-kind function, with complex exponents
in the full convergence range and evaluation point off the unit segment. -/
theorem jacobiSecondKind_eq_complexEulerIntegral {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z =
      (Gamma (α + n + 1 + (β + n + 1)) /
        (Gamma (α + n + 1) * Gamma (β + n + 1))) *
      ∫ t in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) t *
        (z - t) ^ (-(n + 1 : ℤ)) := by
  have hb : pair (α + n + 1) (β + n + 1) ∈ mvBetaConvergent := by
    intro i
    fin_cases i <;> simp [pair]
    all_goals have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [jacobiSecondKind_eq_native _ _ _ _ _ n hb hz,
    carlsonDirichletAverage, sum_pair, regCarlsonDirichletAverage]
  have he (u : Fin 2 → ℝ) : carlsonAffineForm (pair 1 0) u = (u 0 : ℂ) := by
    simp [carlsonAffineForm, Fin.sum_univ_two]
  simp_rw [he]
  change Gamma _ * regDirichletIntegral ![α + n + 1, β + n + 1]
    (fun u => (z - (u 0 : ℂ)) ^ (-(n + 1 : ℤ))) = _
  rw [regDirichletIntegral_fin_two _ _ (fun t : ℝ => (z - t) ^ (-(n + 1 : ℤ))),
    regEulerIntegral, ← mul_assoc, ← div_eq_mul_inv,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioo]
  simp only [add_sub_cancel_right, complexJacobiWeight]

/-- Integration by parts converts the higher complex resolvent into a simple
Cauchy kernel with the complex Jacobi polynomial density. -/
theorem integral_complexJacobiWeight_mul_resolvent {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    (∫ t in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) t *
        (z - t) ^ (-(n + 1 : ℤ))) =
      (-1 : ℂ) ^ n * ∫ t in (0 : ℝ)..1,
        complexJacobiWeight α β t * (shiftedJacobi α β n).eval (t : ℂ) * (z - t)⁻¹ := by
  let f : ℕ → ℝ → ℂ := fun k t => (k.factorial : ℂ) * (z - t) ^ (-(k + 1 : ℤ))
  have hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z ≠ (t : ℂ) := by
    intro he
    apply hz
    rw [he]
    exact ⟨t, 1 - t, ht.1, sub_nonneg.mpr ht.2, by ring, by simp [real_smul]⟩
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (f k) (f (k + 1) t) t := hasDerivAt_factorial_resolvent k t (hn t ht)
  have h := factorial_mul_integral_complexJacobiWeight hα hβ n f
    (fun k _ t ht => (hd k t ht).continuousAt.continuousWithinAt)
    (fun k _ t ht => hd k t ⟨ht.1.le, ht.2.le⟩)
  simp only [f, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero,
    zero_add, zpow_neg_one] at h
  have he : (fun t : ℝ => complexJacobiWeight (α + n) (β + n) t *
      ((n.factorial : ℂ) * (z - t) ^ (-(n + 1 : ℤ)))) =
      (fun t : ℝ => (n.factorial : ℂ) * (complexJacobiWeight (α + n) (β + n) t *
        (z - t) ^ (-(n + 1 : ℤ)))) := by funext t; ring
  rw [he, intervalIntegral.integral_const_mul] at h
  have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
  have hh := congrArg (fun v : ℂ => (-1) ^ n * v) h
  simp only [← mul_assoc, hs, one_mul] at hh
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ hn
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh.symm

/-- Carlson's complex-parameter Cauchy representation on the unit segment. -/
theorem jacobiSecondKind_eq_complexCauchyIntegral {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z = jacobiCauchyCoefficient α β n *
      ∫ t in (0 : ℝ)..1, complexJacobiWeight α β t *
        (shiftedJacobi α β n).eval (t : ℂ) * (z - t)⁻¹ := by
  rw [jacobiSecondKind_eq_complexEulerIntegral hα hβ n hz,
    integral_complexJacobiWeight_mul_resolvent hα hβ n hz, jacobiCauchyCoefficient]
  ring

/-- The symmetric Jacobi jump for complex parameters in the native convergence range. -/
theorem tendsto_jacobiSecondKind_sub_complex {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β 1 0 n ((x : ℂ) + (c⁻¹ : ℝ) * I) -
      jacobiSecondKind α β 1 0 n ((x : ℂ) - (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (-2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n *
        (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ)))) := by
  let ρ : ℝ → ℂ := fun t => complexJacobiWeight α β t * (shiftedJacobi α β n).eval (t : ℂ)
  have hi : IntervalIntegrable ρ volume 0 1 :=
    (intervalIntegrable_complexJacobiWeight hα hβ).mul_continuousOn
      ((shiftedJacobi α β n).continuous.comp continuous_ofReal).continuousOn
  have hw : ContinuousAt (fun t : ℝ => complexJacobiWeight α β t) x := by
    simpa only [sub_add_cancel] using
      (hasDerivAt_complexJacobiWeight_succ (α - 1) (β - 1)
        (ofReal_mem_slitPlane.mpr hx.1)
        (by apply Or.inl; simp only [sub_re, one_re, ofReal_re]; linarith [hx.2])).comp_ofReal.continuousAt
  have hc : ContinuousAt ρ x := hw.fun_mul
    ((shiftedJacobi α β n).continuous.comp continuous_ofReal).continuousAt
  have h := (tendsto_intervalIntegral_cauchy_sub hi hx hc).const_mul (jacobiCauchyCoefficient α β n)
  have he : jacobiCauchyCoefficient α β n * (-2 * (Real.pi : ℂ) * I * ρ x) =
      -2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * ρ x := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hp : ((x : ℂ) + (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have hm : ((x : ℂ) - (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  rw [jacobiSecondKind_eq_complexCauchyIntegral hα hβ n (not_mem_unitSegment_of_im_ne_zero hp),
    jacobiSecondKind_eq_complexCauchyIntegral hα hβ n (not_mem_unitSegment_of_im_ne_zero hm), mul_sub]

/-- The complex-parameter jump transported to distinct complex endpoints by an
invertible affine map, with a perpendicular approach to the segment. -/
theorem tendsto_jacobiSecondKind_sub_complex_affine {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {r s : ℂ} (hrs : r ≠ s) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) + (c⁻¹ : ℝ) * I) + s) -
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) - (c⁻¹ : ℝ) * I) + s)) atTop
      (𝓝 ((r - s) ^ (-(n + 1 : ℤ)) *
        (-2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n *
          (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ))))) := by
  have h := (tendsto_jacobiSecondKind_sub_complex hα hβ n hx).const_mul
    ((r - s) ^ (-(n + 1 : ℤ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hp : ((x : ℂ) + (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have hm : ((x : ℂ) - (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have he {z : ℂ} (hz : z.im ≠ 0) :
      jacobiSecondKind α β r s n ((r - s) * z + s) =
        (r - s) ^ (-(n + 1 : ℤ)) * jacobiSecondKind α β 1 0 n z := by
    simpa using jacobiSecondKind_affine α β 1 0 (r - s) s n (sub_ne_zero.mpr hrs)
      (not_mem_unitSegment_of_im_ne_zero hz)
  rw [he hp, he hm, mul_sub]

end Carlson.TwoVariable
