/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.DifferentialEquation
public import Carlson.Jacobi.Weight
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Jacobi orthogonality in the full real parameter range

For real `α, β > -1`, the Jacobi differential operator is symmetric with respect
to the weight `x^α (1-x)^β` on `[0,1]`. A weighted Wronskian is continuous at both
endpoints and vanishes there. The fundamental theorem of calculus therefore gives
orthogonality of polynomial eigenfunctions with distinct eigenvalues, including
the shifted Jacobi polynomials. No endpoint differentiability is assumed for
nonintegral weights.

## Main results

* `integral_mul_eq_zero_of_jacobi_differential_equation`: orthogonality of distinct
  polynomial eigenfunctions.
* `integral_shiftedJacobi_mul_shiftedJacobi_eq_zero`: Jacobi orthogonality for the
  full real range `α, β > -1`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.8.
-/

public noncomputable section
namespace Polynomial
open MeasureTheory Set

/-- The derivative of the weighted Wronskian of two polynomial Jacobi eigenfunctions. -/
theorem hasDerivAt_weight_mul_wronskian (α β ρ σ : ℝ) (p q : ℝ[X])
    (hp : X * (1 - X) * derivative (derivative p) +
      (C (α + 1) - C (α + β + 2) * X) * derivative p + C ρ * p = 0)
    (hq : X * (1 - X) * derivative (derivative q) +
      (C (α + 1) - C (α + β + 2) * X) * derivative q + C σ * q = 0)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => shiftedJacobiWeight (α + 1) (β + 1) t * (wronskian p q).eval t)
      ((ρ - σ) * (shiftedJacobiWeight α β x * p.eval x * q.eval x)) x := by
  have h := (hasDerivAt_shiftedJacobiWeight_succ α β hx).mul ((wronskian p q).hasDerivAt x)
  have hep := congrArg (eval x) hp
  have heq := congrArg (eval x) hq
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_C, eval_zero] at hep heq
  convert h using 1
  rw [shiftedJacobiWeight_succ α β hx]
  simp only [wronskian, derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul]
  linear_combination shiftedJacobiWeight α β x * q.eval x * hep -
      shiftedJacobiWeight α β x * p.eval x * heq

/-- Distinct polynomial eigenfunctions of the Jacobi differential operator are orthogonal
in its integrable real parameter range. -/
theorem integral_mul_eq_zero_of_jacobi_differential_equation {α β ρ σ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hρσ : ρ ≠ σ) (p q : ℝ[X])
    (hp : X * (1 - X) * derivative (derivative p) +
      (C (α + 1) - C (α + β + 2) * X) * derivative p + C ρ * p = 0)
    (hq : X * (1 - X) * derivative (derivative q) +
      (C (α + 1) - C (α + β + 2) * X) * derivative q + C σ * q = 0) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x * q.eval x) = 0 := by
  have hi := ((intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn
    p.continuous.continuousOn).mul_continuousOn q.continuous.continuousOn
  have hc := ((continuous_shiftedJacobiWeight_succ hα hβ).mul
    (wronskian p q).continuous)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
    (fun x hx => hasDerivAt_weight_mul_wronskian α β ρ σ p q hp hq hx) (hi.const_mul (ρ - σ))
  dsimp only [Pi.mul_apply] at he
  rw [shiftedJacobiWeight_succ_one hβ, shiftedJacobiWeight_succ_zero hα,
    zero_mul, zero_mul, sub_self, intervalIntegral.integral_const_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hρσ)

/-- Shifted Jacobi polynomials of distinct indices are orthogonal for all real parameters
`α, β > -1`. -/
theorem integral_shiftedJacobi_mul_shiftedJacobi_eq_zero {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) (hmn : m ≠ n) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x *
      (shiftedJacobi α β m).eval x * (shiftedJacobi α β n).eval x) = 0 := by
  apply integral_mul_eq_zero_of_jacobi_differential_equation hα hβ _ _ _
    (shiftedJacobi_differential_equation α β m) (shiftedJacobi_differential_equation α β n)
  intro he
  have hfactor : ((m : ℝ) - n) * ((m : ℝ) + n + α + β + 1) = 0 := by
    linear_combination he
  have hsum : 0 < (m : ℝ) + n + α + β + 1 := by
    have hnat : 1 ≤ m + n := by omega
    have hreal : (1 : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hnat
    linarith
  have heq := (mul_eq_zero.mp hfactor).resolve_right hsum.ne'
  exact hmn (by exact_mod_cast sub_eq_zero.mp heq)

end Polynomial
