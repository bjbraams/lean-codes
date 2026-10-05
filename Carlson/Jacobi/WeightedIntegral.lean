/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AnalyticRodrigues
public import Carlson.Jacobi.ComplexOrthogonality
public import Carlson.Jacobi.Expansion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Weighted Jacobi coefficient integrals

Integration by parts transfers derivatives from the raised Jacobi weight to the
function being expanded. For `α, β > -1` the boundary terms vanish even when the
original weight is singular at an endpoint. A continuous derivative tower on the
closed interval, with derivatives required only in its interior, suffices. The real
identities are specializations of the complex-parameter ones in
`Carlson.Jacobi.ComplexOrthogonality`, through `complexJacobiWeight_ofReal` and
`shiftedJacobi_eval_ofReal`.

## Main results

* `factorial_mul_integral_mul_shiftedJacobi`: repeated integration by parts for
  a continuous derivative tower, including order zero.
* `factorial_mul_integral_mul_shiftedJacobi_of_contDiffOn`: the `Cⁿ` formulation
  using derivatives within the closed interval.
* `integral_mul_shiftedJacobi_eq_integral_derivative`: the polynomial specialization.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8.
-/

public noncomputable section
namespace Polynomial
open Complex MeasureTheory Set

/-- Repeated weighted integration by parts for a derivative tower continuous on
`[0,1]`. Derivative relations are needed only on `(0,1)`, and only through order `n`. -/
theorem factorial_mul_integral_mul_shiftedJacobi {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) (f : ℕ → ℝ → ℝ)
    (hc : ∀ k ≤ n, ContinuousOn (f k) (Icc 0 1))
    (hd : ∀ k < n, ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (f k) (f (k + 1) x) x) :
    (n.factorial : ℝ) * (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * f 0 x *
      (shiftedJacobi α β n).eval x) =
      (-1 : ℝ) ^ n * (∫ x in (0 : ℝ)..1,
        shiftedJacobiWeight (α + n) (β + n) x * f n x) := by
  have h := factorial_mul_integral_complexJacobiWeight (α := α) (β := β)
    (by simpa using hα) (by simpa using hβ) n (fun k x => (f k x : ℂ))
    (fun k hk => continuous_ofReal.comp_continuousOn (hc k hk))
    (fun k hk x hx => (hd k hk x hx).ofReal_comp)
  beta_reduce at h
  have hl : (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * (f 0 x : ℂ) *
      (shiftedJacobi (α : ℂ) β n).eval (x : ℂ)) =
      ((∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * f 0 x *
        (shiftedJacobi α β n).eval x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp only [complexJacobiWeight_ofReal α β hx, shiftedJacobi_eval_ofReal, ofReal_mul]
  have hr : (∫ x in (0 : ℝ)..1, complexJacobiWeight ((α : ℂ) + n) ((β : ℂ) + n) x *
      (f n x : ℂ)) = ((∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + n) (β + n) x * f n x : ℝ) :
        ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have hw := complexJacobiWeight_ofReal (α + n) (β + n) hx
    push_cast at hw
    simp only [hw, ofReal_mul]
  rw [hl, hr] at h
  exact_mod_cast h

/-- A `Cⁿ` function on the closed unit interval satisfies the repeated weighted
integration identity. Derivatives within the interval allow one-sided endpoint data. -/
theorem factorial_mul_integral_mul_shiftedJacobi_of_contDiffOn {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Icc 0 1)) :
    (n.factorial : ℝ) * (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * f x *
      (shiftedJacobi α β n).eval x) =
      (-1 : ℝ) ^ n * (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + n) (β + n) x *
        iteratedDerivWithin n f (Icc 0 1) x) := by
  apply factorial_mul_integral_mul_shiftedJacobi hα hβ n
    (fun k => iteratedDerivWithin k f (Icc 0 1))
  · intro k hk
    exact hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) uniqueDiffOn_Icc_zero_one
  · intro k hk x hx
    rw [iteratedDerivWithin_succ]
    exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk)
      uniqueDiffOn_Icc_zero_one) x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)

/-- The weighted Jacobi integral of a polynomial is the weighted integral of its
`n`th derivative with both weight parameters raised by `n`. -/
theorem integral_mul_shiftedJacobi_eq_integral_derivative {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (p : ℝ[X]) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x *
      (shiftedJacobi α β n).eval x) =
      (-1 : ℝ) ^ n / n.factorial * (∫ x in (0 : ℝ)..1,
        shiftedJacobiWeight (α + n) (β + n) x * (derivative^[n] p).eval x) := by
  have h := factorial_mul_integral_mul_shiftedJacobi hα hβ n
    (fun k x => (derivative^[k] p).eval x)
    (fun k _ => (derivative^[k] p).continuous.continuousOn)
    (fun k _ x _ => by simpa only [Function.iterate_succ_apply'] using
      (derivative^[k] p).hasDerivAt x)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  dsimp only [Function.iterate_zero_apply] at h
  apply (mul_left_cancel₀ hn)
  rw [h]
  field_simp

end Polynomial
