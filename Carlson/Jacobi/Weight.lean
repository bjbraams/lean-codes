/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic

/-!
# Real Jacobi weights on the unit interval

The shifted Jacobi weight is `x^α (1-x)^β`. Its integrability range is
`α, β > -1`; after increasing both exponents by one the weight is continuous
and vanishes at the endpoints. These facts allow integration by parts without
assuming differentiability of a nonintegral weight at an endpoint.

## Main results

* `intervalIntegrable_shiftedJacobiWeight`: integrability in the full real range.
* `continuous_shiftedJacobiWeight_succ`: continuity of the boundary weight.
* `hasDerivAt_shiftedJacobiWeight_succ`: the Pearson identity in the open interval.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.8.
-/

@[expose] public noncomputable section
namespace Polynomial
open MeasureTheory Set

/-- The Jacobi weight in the coordinate on `[0,1]`. -/
def shiftedJacobiWeight (α β x : ℝ) : ℝ := x ^ α * (1 - x) ^ β

/-- The Jacobi weight is integrable in the usual real parameter range. -/
theorem intervalIntegrable_shiftedJacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (shiftedJacobiWeight α β) volume 0 1 := by
  have h := Complex.betaIntegral_convergent (u := (α + 1 : ℝ)) (v := (β + 1 : ℝ))
    (by simpa using (show 0 < α + 1 by linarith))
    (by simpa using (show 0 < β + 1 by linarith))
  have hr : IntervalIntegrable (fun x : ℝ =>
      ((x : ℂ) ^ ((α + 1 : ℝ) - 1 : ℂ) *
        (1 - (x : ℂ)) ^ ((β + 1 : ℝ) - 1 : ℂ)).re) volume 0 1 := ⟨h.1.re, h.2.re⟩
  apply (intervalIntegrable_congr_uIoo (f := _) (g := shiftedJacobiWeight α β) ?_).mp hr
  intro x hx
  simp only [uIoo_of_lt (by norm_num : (0 : ℝ) < 1), mem_Ioo] at hx
  simp only [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_right]
  rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hx.1.le,
    ← Complex.ofReal_cpow (by linarith : 0 ≤ 1 - x), ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- Increasing both Jacobi exponents by one gives a continuous function, including
at both endpoints of the interval. -/
theorem continuous_shiftedJacobiWeight_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Continuous (shiftedJacobiWeight (α + 1) (β + 1)) :=
  (Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ β + 1)).comp
      (continuous_const.sub continuous_id))

/-- The boundary weight vanishes at the left endpoint. -/
@[simp] theorem shiftedJacobiWeight_succ_zero {α β : ℝ} (hα : -1 < α) :
    shiftedJacobiWeight (α + 1) (β + 1) 0 = 0 := by
  simp [shiftedJacobiWeight, Real.zero_rpow (by linarith : α + 1 ≠ 0)]

/-- The boundary weight vanishes at the right endpoint. -/
@[simp] theorem shiftedJacobiWeight_succ_one {α β : ℝ} (hβ : -1 < β) :
    shiftedJacobiWeight (α + 1) (β + 1) 1 = 0 := by
  simp [shiftedJacobiWeight, Real.zero_rpow (by linarith : β + 1 ≠ 0)]

/-- Multiplication by `x(1-x)` raises both exponents of the Jacobi weight. -/
theorem shiftedJacobiWeight_succ (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    shiftedJacobiWeight (α + 1) (β + 1) x = x * (1 - x) * shiftedJacobiWeight α β x := by
  have hx1 := hx.2
  simp only [shiftedJacobiWeight, Real.rpow_add hx.1,
    Real.rpow_add (by linarith : 0 < 1 - x), Real.rpow_one]
  ring

/-- Pearson's differential identity for the shifted Jacobi weight, on the open interval. -/
theorem hasDerivAt_shiftedJacobiWeight_succ (α β : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (shiftedJacobiWeight (α + 1) (β + 1))
      ((α + 1 - (α + β + 2) * x) * shiftedJacobiWeight α β x) x := by
  have hx1 := hx.2
  have h1 := Real.hasDerivAt_rpow_const (p := α + 1) (Or.inl hx.1.ne')
  have h2 := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).rpow_const
    (p := β + 1) (Or.inl (by linarith : (1 : ℝ) - x ≠ 0))
  dsimp only [Pi.sub_apply, id_eq] at h2
  convert h1.mul h2 using 1
  · rfl
  · simp only [add_sub_cancel_right, zero_sub,
      shiftedJacobiWeight, Real.rpow_add hx.1,
      Real.rpow_add (by linarith : 0 < 1 - x), Real.rpow_one]
    ring

/-- The total mass of an integrable Jacobi weight is strictly positive. -/
theorem integral_shiftedJacobiWeight_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    0 < ∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_shiftedJacobiWeight hα hβ) _ (by norm_num)
  intro x hx
  exact mul_pos (Real.rpow_pos_of_pos hx.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _)

end Polynomial
