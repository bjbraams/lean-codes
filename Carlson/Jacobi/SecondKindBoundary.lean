/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindInfinity
public import Carlson.Jacobi.SecondKindIntegral
public import Carlson.Jacobi.BoundaryKernel

/-!
# Boundary jumps of the second-kind Jacobi function

For real parameters `α, β > -1`, the difference of the second-kind function
at heights `±1/c` over an interior point of the unit segment has a limit as
`c → +∞`. The limit is `-2πi` times the normalized Jacobi density. This follows
from the Cauchy-integral representation and the real Poisson approximate identity.
Affine covariance transports the result to every nondegenerate complex segment.
The theorem asserts a symmetric jump; separate boundary values and their
principal-value representations are not asserted here.

## Main results

* `tendsto_jacobiSecondKind_sub`: the symmetric jump across the unit segment.
* `tendsto_jacobiSecondKind_sub_affine`: transport to any distinct complex endpoints.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7 (Jacobi polynomials and associated functions).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial MeasureTheory Set Filter
open scoped Topology

/-- The upper-minus-lower boundary jump of Carlson's second-kind Jacobi function
at an interior point of the unit segment, for real parameters greater than `-1`. -/
theorem tendsto_jacobiSecondKind_sub {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β 1 0 n ((x : ℂ) + (c⁻¹ : ℝ) * I) -
      jacobiSecondKind α β 1 0 n ((x : ℂ) - (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (-2 * (Real.pi : ℂ) * I *
        ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) *
        (shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x : ℝ))) := by
  let ρ : ℝ → ℂ := fun t =>
    (shiftedJacobiWeight α β t * (shiftedJacobi α β n).eval t : ℝ)
  have hi : IntervalIntegrable ρ volume 0 1 := by
    have h := (intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn
      (shiftedJacobi α β n).continuous.continuousOn
    exact ⟨h.1.ofReal, h.2.ofReal⟩
  have hw : ContinuousAt (shiftedJacobiWeight α β) x := by
    simpa only [sub_add_cancel] using
      (hasDerivAt_shiftedJacobiWeight_succ (α - 1) (β - 1) hx).continuousAt
  have hc : ContinuousAt ρ x := continuous_ofReal.continuousAt.comp
    (hw.mul (shiftedJacobi α β n).continuous.continuousAt)
  have h := (tendsto_intervalIntegral_cauchy_sub hi hx hc).const_mul
    ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ))
  have he : ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) *
      (-2 * (Real.pi : ℂ) * I * ρ x) =
      -2 * (Real.pi : ℂ) * I *
        ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) * ρ x := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hp : ((x : ℂ) + (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have hm : ((x : ℂ) - (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  rw [jacobiSecondKind_eq_cauchyIntegral hα hβ n (not_mem_unitSegment_of_im_ne_zero hp),
    jacobiSecondKind_eq_cauchyIntegral hα hβ n (not_mem_unitSegment_of_im_ne_zero hm), mul_sub]

/-- The symmetric jump transported to any nondegenerate complex segment. The
approach is perpendicular to the segment, in its affine unit coordinates. -/
theorem tendsto_jacobiSecondKind_sub_affine {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {r s : ℂ} (hrs : r ≠ s) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) + (c⁻¹ : ℝ) * I) + s) -
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) - (c⁻¹ : ℝ) * I) + s)) atTop
      (𝓝 ((r - s) ^ (-(n + 1 : ℤ)) *
        (-2 * (Real.pi : ℂ) * I *
          ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) *
          (shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x : ℝ)))) := by
  have h := (tendsto_jacobiSecondKind_sub hα hβ n hx).const_mul
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
