/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexSecondKind

/-!
# Integral representations of the second-kind Jacobi function at real parameters

For real Jacobi parameters greater than `-1`, the continued second-kind function
with endpoints `1, 0` agrees with its normalized Euler integral. Repeated weighted
integration by parts expresses it as the Cauchy transform of the Jacobi weight
times the shifted Jacobi polynomial. Evaluation points lie outside the closed unit segment.
These are the real specializations of the complex-parameter representations in
`Carlson.Jacobi.ComplexSecondKind`, with Gamma ratios written as beta functions.

## Main results

* `jacobiCauchyCoefficient_ofReal`: the Cauchy coefficient at real parameters.
* `jacobiSecondKind_eq_eulerIntegral`: the normalized integer-kernel integral.
* `integral_shiftedJacobiWeight_mul_resolvent`: the weighted kernel identity.
* `jacobiSecondKind_eq_cauchyIntegral`: the normalized Cauchy representation.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Dirichlet Polynomial MeasureTheory Set

/-- At real parameters the Euler normalization is the reciprocal of a beta function. -/
theorem Gamma_div_Gamma_mul_Gamma_ofReal (α β : ℝ) (n : ℕ) :
    Gamma ((α : ℂ) + n + 1 + ((β : ℂ) + n + 1)) /
        (Gamma ((α : ℂ) + n + 1) * Gamma ((β : ℂ) + n + 1)) =
      (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)⁻¹ := by
  have h (a : ℝ) : (a : ℂ) + n + 1 = ((a + n + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h α, h β, ← ofReal_add, Gamma_ofReal, Gamma_ofReal, Gamma_ofReal]
  simp [ProbabilityTheory.beta, div_eq_mul_inv]

/-- At real parameters the Cauchy coefficient is a signed reciprocal beta function. -/
theorem jacobiCauchyCoefficient_ofReal (α β : ℝ) (n : ℕ) :
    jacobiCauchyCoefficient α β n =
      (-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ) := by
  rw [jacobiCauchyCoefficient, mul_div_assoc, Gamma_div_Gamma_mul_Gamma_ofReal, div_eq_mul_inv]

/-- Real weights agree with complex weights under the integral over the unit interval. -/
private theorem integral_complexJacobiWeight_ofReal (α β : ℝ) (g : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, complexJacobiWeight α β t * g t) =
      ∫ t in (0 : ℝ)..1, (shiftedJacobiWeight α β t : ℂ) * g t := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [complexJacobiWeight_ofReal α β ht]

/-- For real parameters in the orthogonality range, the second-kind function is
the normalized Euler integral of its integer resolvent kernel. -/
theorem jacobiSecondKind_eq_eulerIntegral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z =
      (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..1, (shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
          (z - t) ^ (-(n + 1 : ℤ)) := by
  rw [jacobiSecondKind_eq_complexEulerIntegral (by simpa using hα) (by simpa using hβ) n hz,
    Gamma_div_Gamma_mul_Gamma_ofReal, show ((α : ℂ) + n) = ((α + n : ℝ) : ℂ) by push_cast; rfl,
    show ((β : ℂ) + n) = ((β + n : ℝ) : ℂ) by push_cast; rfl,
    integral_complexJacobiWeight_ofReal]

/-- Weighted integration by parts converts the higher resolvent into a Cauchy
kernel multiplied by the shifted Jacobi polynomial. -/
theorem integral_shiftedJacobiWeight_mul_resolvent {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    (∫ t in (0 : ℝ)..1, (shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
        (z - t) ^ (-(n + 1 : ℤ))) =
      (-1 : ℂ) ^ n * ∫ t in (0 : ℝ)..1,
        (shiftedJacobiWeight α β t * (shiftedJacobi α β n).eval t : ℝ) * (z - t)⁻¹ := by
  have h := integral_complexJacobiWeight_mul_resolvent (α := α) (β := β)
    (by simpa using hα) (by simpa using hβ) n hz
  rw [show ((α : ℂ) + n) = ((α + n : ℝ) : ℂ) by push_cast; rfl,
    show ((β : ℂ) + n) = ((β + n : ℝ) : ℂ) by push_cast; rfl,
    integral_complexJacobiWeight_ofReal] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [complexJacobiWeight_ofReal α β ht, shiftedJacobi_eval_ofReal, ofReal_mul]

/-- The second-kind Jacobi function is the Cauchy transform of the weighted
shifted Jacobi polynomial, with Carlson's normalization. -/
theorem jacobiSecondKind_eq_cauchyIntegral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z =
      ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) *
        ∫ t in (0 : ℝ)..1,
          (shiftedJacobiWeight α β t * (shiftedJacobi α β n).eval t : ℝ) * (z - t)⁻¹ := by
  rw [jacobiSecondKind_eq_eulerIntegral hα hβ n hz,
    integral_shiftedJacobiWeight_mul_resolvent hα hβ n hz]
  ring

end Carlson.TwoVariable
