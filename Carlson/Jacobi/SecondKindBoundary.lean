/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindIntegral

/-!
# Boundary jumps of the second-kind Jacobi function

For real parameters `α, β > -1`, the difference of the second-kind function
at heights `±1/c` over an interior point of the unit segment has a limit as
`c → +∞`. The limit is `-2πi` times the normalized Jacobi density. These are the real
specializations of the complex-parameter jumps in `Carlson.Jacobi.ComplexSecondKind`.
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
  have h := tendsto_jacobiSecondKind_sub_complex (α := α) (β := β)
    (by simpa using hα) (by simpa using hβ) n hx
  rwa [jacobiCauchyCoefficient_ofReal, complexJacobiWeight_ofReal α β (Ioo_subset_Icc_self hx),
    shiftedJacobi_eval_ofReal, ← ofReal_mul] at h

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
  have h := tendsto_jacobiSecondKind_sub_complex_affine (α := α) (β := β)
    (by simpa using hα) (by simpa using hβ) n hrs hx
  rwa [jacobiCauchyCoefficient_ofReal, complexJacobiWeight_ofReal α β (Ioo_subset_Icc_self hx),
    shiftedJacobi_eval_ofReal, ← ofReal_mul] at h

end Carlson.TwoVariable
