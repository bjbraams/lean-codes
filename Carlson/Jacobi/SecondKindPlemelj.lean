/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexSecondKind

/-!
# Separate Jacobi boundary values and principal values

For complex parameters with real parts greater than `-1`, the Jacobi Cauchy
density is integrable on the unit interval and differentiable at each interior
point. Segment Plemelj theory therefore gives separate upper and lower boundary
values of the second-kind function. Their mean is the normalized Cauchy principal
value, also characterized as a symmetric real-axis truncation limit.

Affine covariance transports the separate limits to any pair of distinct complex
endpoints. The limits use perpendicular approaches in affine unit coordinates.
Continuation outside the integrable-weight range and endpoint finite parts are
not covered by these statements.

## Main results

* `tendsto_jacobiSecondKind_upper` and `tendsto_jacobiSecondKind_lower`.
* `tendsto_jacobiSecondKind_principalValue`.
* `tendsto_jacobiSecondKind_upper_affine` and `tendsto_jacobiSecondKind_lower_affine`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8 (associated Jacobi functions).
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial MeasureTheory Set Filter
open scoped Topology

/-- The complex Jacobi weight times the shifted Jacobi polynomial, restricted
to the real line. Its normalization is `jacobiCauchyCoefficient`. -/
def jacobiCauchyDensity (α β : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  complexJacobiWeight α β t * (shiftedJacobi α β n).eval (t : ℂ)

/-- The Jacobi Cauchy density is integrable in the native weight range. -/
theorem intervalIntegrable_jacobiCauchyDensity {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) :
    IntervalIntegrable (jacobiCauchyDensity α β n) volume 0 1 :=
  (intervalIntegrable_complexJacobiWeight hα hβ).mul_continuousOn
    ((shiftedJacobi α β n).continuous.comp continuous_ofReal).continuousOn

/-- The Jacobi Cauchy density is differentiable at interior points, for every
complex parameter pair and every degree, including exceptional degree drops. -/
theorem differentiableAt_jacobiCauchyDensity (α β : ℂ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : DifferentiableAt ℝ (jacobiCauchyDensity α β n) x := by
  have hw : DifferentiableAt ℝ (fun t : ℝ => complexJacobiWeight α β t) x := by
    simpa only [sub_add_cancel] using
      (hasDerivAt_complexJacobiWeight_succ (α - 1) (β - 1)
        (ofReal_mem_slitPlane.mpr hx.1)
        (by
          apply Or.inl; simp only [sub_re, one_re, ofReal_re]; linarith [hx.2])).comp_ofReal
      |>.differentiableAt
  exact hw.mul ((shiftedJacobi α β n).hasDerivAt (x : ℂ)).comp_ofReal.differentiableAt

/-- The regularized Jacobi density is integrable at every interior pole. -/
theorem intervalIntegrable_jacobiCauchyDifferenceQuotient {α β : ℂ}
    (hα : -1 < α.re) (hβ : -1 < β.re) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ =>
      ((x : ℂ) - t)⁻¹ • (jacobiCauchyDensity α β n t - jacobiCauchyDensity α β n x)) volume 0 1 :=
  intervalIntegrable_cauchyDifferenceQuotient (intervalIntegrable_jacobiCauchyDensity hα hβ n)
    (differentiableAt_jacobiCauchyDensity α β n hx)

/-- The normalized principal value of the Jacobi Cauchy representation. -/
def jacobiSecondKindPrincipalValue (α β : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  jacobiCauchyCoefficient α β n * cauchyPrincipalValue (jacobiCauchyDensity α β n) 0 1 x

/-- The upper boundary value equals the normalized principal value minus the
half-jump `πi` times the normalized density. -/
theorem tendsto_jacobiSecondKind_upper {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ => jacobiSecondKind α β 1 0 n ((x : ℂ) + (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (jacobiSecondKindPrincipalValue α β n x -
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x)) := by
  have h := (tendsto_intervalIntegral_cauchy_upper
    (intervalIntegrable_jacobiCauchyDensity hα hβ n) hx
    (intervalIntegrable_jacobiCauchyDifferenceQuotient hα hβ n hx)).const_mul
      (jacobiCauchyCoefficient α β n)
  have he : jacobiCauchyCoefficient α β n *
      (cauchyPrincipalValue (jacobiCauchyDensity α β n) 0 1 x -
        ((Real.pi : ℂ) * I) • jacobiCauchyDensity α β n x) =
      jacobiSecondKindPrincipalValue α β n x -
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x := by
    dsimp [jacobiSecondKindPrincipalValue]; ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  rw [jacobiSecondKind_eq_complexCauchyIntegral hα hβ n
    (not_mem_unitSegment_of_im_ne_zero (by simp [hc.ne']))]
  congr 1
  exact intervalIntegral.integral_congr fun t _ ↦ by
    simp only [jacobiCauchyDensity, smul_eq_mul]; ring

/-- The lower boundary value equals the normalized principal value plus the
half-jump `πi` times the normalized density. -/
theorem tendsto_jacobiSecondKind_lower {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ => jacobiSecondKind α β 1 0 n ((x : ℂ) - (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (jacobiSecondKindPrincipalValue α β n x +
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x)) := by
  have h := (tendsto_intervalIntegral_cauchy_lower
    (intervalIntegrable_jacobiCauchyDensity hα hβ n) hx
    (intervalIntegrable_jacobiCauchyDifferenceQuotient hα hβ n hx)).const_mul
      (jacobiCauchyCoefficient α β n)
  have he : jacobiCauchyCoefficient α β n *
      (cauchyPrincipalValue (jacobiCauchyDensity α β n) 0 1 x +
        ((Real.pi : ℂ) * I) • jacobiCauchyDensity α β n x) =
      jacobiSecondKindPrincipalValue α β n x +
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x := by
    dsimp [jacobiSecondKindPrincipalValue]; ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  rw [jacobiSecondKind_eq_complexCauchyIntegral hα hβ n
    (not_mem_unitSegment_of_im_ne_zero (by simp [hc.ne']))]
  congr 1
  exact intervalIntegral.integral_congr fun t _ ↦ by
    simp only [jacobiCauchyDensity, smul_eq_mul]; ring

/-- The normalized symmetric real-axis truncations converge to the same
principal value that occurs in both separate Jacobi boundary formulas. -/
theorem tendsto_jacobiSecondKind_principalValue {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ => jacobiCauchyCoefficient α β n *
      ((∫ t in (0 : ℝ)..x - c⁻¹, jacobiCauchyDensity α β n t * ((x : ℂ) - t)⁻¹) +
       (∫ t in x + c⁻¹..1, jacobiCauchyDensity α β n t * ((x : ℂ) - t)⁻¹))) atTop
      (𝓝 (jacobiSecondKindPrincipalValue α β n x)) := by
  refine ((tendsto_intervalIntegral_cauchy_principalValue hx
    (intervalIntegrable_jacobiCauchyDifferenceQuotient hα hβ n hx)).const_mul
      (jacobiCauchyCoefficient α β n)).congr fun c ↦ ?_
  congr 2 <;> exact intervalIntegral.integral_congr fun t _ ↦ by rw [smul_eq_mul, mul_comm]

/-- The upper Jacobi boundary value transported to distinct complex endpoints.
The approach is perpendicular to the segment in affine unit coordinates. -/
theorem tendsto_jacobiSecondKind_upper_affine {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {r s : ℂ} (hrs : r ≠ s)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) + (c⁻¹ : ℝ) * I) + s)) atTop
      (𝓝 ((r - s) ^ (-(n + 1 : ℤ)) * (jacobiSecondKindPrincipalValue α β n x -
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x))) := by
  have h := (tendsto_jacobiSecondKind_upper hα hβ n hx).const_mul ((r - s) ^ (-(n + 1 : ℤ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  symm
  simpa using jacobiSecondKind_affine α β 1 0 (r - s) s n (sub_ne_zero.mpr hrs)
    (not_mem_unitSegment_of_im_ne_zero (by simp [hc.ne']))

/-- The lower Jacobi boundary value transported to distinct complex endpoints. -/
theorem tendsto_jacobiSecondKind_lower_affine {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) {r s : ℂ} (hrs : r ≠ s)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) - (c⁻¹ : ℝ) * I) + s)) atTop
      (𝓝 ((r - s) ^ (-(n + 1 : ℤ)) * (jacobiSecondKindPrincipalValue α β n x +
        (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n * jacobiCauchyDensity α β n x))) := by
  have h := (tendsto_jacobiSecondKind_lower hα hβ n hx).const_mul ((r - s) ^ (-(n + 1 : ℤ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  symm
  simpa using jacobiSecondKind_affine α β 1 0 (r - s) s n (sub_ne_zero.mpr hrs)
    (not_mem_unitSegment_of_im_ne_zero (by simp [hc.ne']))

end Carlson.TwoVariable
