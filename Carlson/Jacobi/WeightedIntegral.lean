/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AnalyticRodrigues
public import Carlson.Jacobi.Expansion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Weighted Jacobi coefficient integrals

Integration by parts transfers derivatives from the raised Jacobi weight to the
function being expanded. For `α, β > -1` the boundary terms vanish even when the
original weight is singular at an endpoint. A continuous derivative tower on the
closed interval, with derivatives required only in its interior, suffices.

## Main results

* `integral_mul_shiftedJacobi_succ`: one step of weighted integration by parts.
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
open MeasureTheory Set

/-- One step of weighted integration by parts for a function continuous up to the
endpoints whose derivative is continuous there and valid in the open interval. -/
theorem integral_mul_shiftedJacobi_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) (f g : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1))
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x) :
    (n + 1 : ℝ) * (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * f x *
      (shiftedJacobi α β (n + 1)).eval x) =
      -(∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + 1) (β + 1) x * g x *
        (shiftedJacobi (α + 1) (β + 1) n).eval x) := by
  have hf' : ContinuousOn f (uIcc (0 : ℝ) 1) := by simpa using hf
  have hg' : ContinuousOn g (uIcc (0 : ℝ) 1) := by simpa using hg
  have hv := (continuous_shiftedJacobiWeight_succ hα hβ).mul
    (shiftedJacobi (α + 1) (β + 1) n).continuous
  have hi := ((intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn
    (shiftedJacobi α β (n + 1)).continuous.continuousOn).const_mul (n + 1 : ℝ)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf' hv.continuousOn (by simpa using hfg)
    (fun x hx => hasDerivAt_weight_mul_shiftedJacobi α β n (by simpa using hx))
    hg'.intervalIntegrable hi
  have hl : (∫ x in (0 : ℝ)..1, f x * ((n + 1 : ℝ) *
      (shiftedJacobiWeight α β x * (shiftedJacobi α β (n + 1)).eval x))) =
      (n + 1 : ℝ) * (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * f x *
        (shiftedJacobi α β (n + 1)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  simp only [Pi.mul_apply] at h
  rw [hl, shiftedJacobiWeight_succ_one hβ, shiftedJacobiWeight_succ_zero hα] at h
  simp only [zero_mul, mul_zero, sub_self, zero_sub] at h
  convert h using 1
  congr 2
  funext x
  ring

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
  induction n generalizing α β f with
  | zero => simp
  | succ n ih =>
    have hs := integral_mul_shiftedJacobi_succ hα hβ n (f 0) (f 1)
      (hc 0 (by omega)) (hc 1 (by omega)) (hd 0 (by omega))
    have hi := ih (α := α + 1) (β := β + 1) (by linarith) (by linarith)
      (fun k => f (k + 1)) (fun k hk => hc (k + 1) (by omega))
      (fun k hk => hd (k + 1) (by omega))
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [Nat.zero_add, add_assoc, add_comm (1 : ℝ) (n : ℝ)] at hi
    linear_combination (n.factorial : ℝ) * hs - hi

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
