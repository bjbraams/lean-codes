/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.WeightedIntegral
public import Carlson.Jacobi.Legendre
public import Pochhammer.BetaIntegral

/-!
# Squared Jacobi norms and coefficient integrals

For real `α, β > -1`, repeated weighted integration by parts evaluates the squared
norm of the shifted Jacobi polynomial. The result is a Pochhammer factor times a
beta integral, valid also at degree zero when `α+β=-1`. This avoids a removable
singularity present in some Gamma quotient forms of the same answer.

## Main results

* `integral_shiftedJacobiWeight_eq_beta`: the mass of the Jacobi weight.
* `integral_shiftedJacobi_sq`: the squared norm as a raised weight integral.
* `integral_shiftedJacobi_sq_eq_beta`: its explicit beta function value.
* `integral_shiftedJacobi_sq_pos`: strict positivity of every squared norm.
* `shiftedJacobiCoefficient_eq_integral_div_norm`: agreement of derivative-average
  coefficients with the usual weighted orthogonal projection coefficients.
* `integral_shiftedLegendre_sq`: the norm `1/(2n+1)` for Mathlib's shifted Legendre
  polynomial, obtained by setting both Jacobi parameters to zero.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8.
-/

public noncomputable section
namespace Polynomial
open MeasureTheory

/-- The total mass of the shifted Jacobi weight is the Euler beta function. -/
theorem integral_shiftedJacobiWeight_eq_beta {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x) =
      ProbabilityTheory.beta (α + 1) (β + 1) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  simpa only [add_sub_cancel_right, shiftedJacobiWeight] using
    Real.integral_Icc_rpow_mul_one_sub_rpow (by linarith : 0 < α + 1)
      (by linarith : 0 < β + 1)

/-- The squared norm of a shifted Jacobi polynomial is its leading Pochhammer
factor divided by `n!`, times the mass of the weight with both exponents raised by `n`. -/
theorem integral_shiftedJacobi_sq {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x ^ 2) =
      (ascPochhammer ℝ n).eval (α + β + n + 1) / n.factorial *
        (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + n) (β + n) x) := by
  have hd := iterate_derivative_shiftedJacobi α β 0 n
  simp only [Nat.zero_add, shiftedJacobi_zero, mul_one] at hd
  have h := integral_mul_shiftedJacobi_eq_integral_derivative hα hβ n
    (shiftedJacobi α β n)
  rw [hd] at h
  simp only [eval_C] at h
  rw [intervalIntegral.integral_mul_const] at h
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; simp
  calc
    _ = (-1 : ℝ) ^ n / n.factorial * ((∫ x in (0 : ℝ)..1,
        shiftedJacobiWeight (α + n) (β + n) x) *
          ((-1 : ℝ) ^ n * (ascPochhammer ℝ n).eval (α + β + n + 1))) := by
      simpa only [pow_two, ← mul_assoc] using h
    _ = _ := by
      calc
        _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            ((ascPochhammer ℝ n).eval (α + β + n + 1) / n.factorial *
              (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + n) (β + n) x)) := by ring
        _ = _ := by rw [hs, one_mul]

/-- The squared Jacobi norm in beta function form, valid throughout the full real
orthogonality range, including degree zero and `α+β=-1`. -/
theorem integral_shiftedJacobi_sq_eq_beta {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x ^ 2) =
      (ascPochhammer ℝ n).eval (α + β + n + 1) / n.factorial *
        ProbabilityTheory.beta (α + n + 1) (β + n + 1) := by
  rw [integral_shiftedJacobi_sq hα hβ,
    integral_shiftedJacobiWeight_eq_beta (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)]

/-- Every shifted Jacobi polynomial has strictly positive squared norm in the
orthogonality range. -/
theorem integral_shiftedJacobi_sq_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < ∫ x in (0 : ℝ)..1,
      shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x ^ 2 := by
  rw [integral_shiftedJacobi_sq hα hβ]
  have hp : 0 < (ascPochhammer ℝ n).eval (α + β + n + 1) := by
    cases n with
    | zero => simp
    | succ n =>
      apply ascPochhammer_pos
      push_cast
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
  exact mul_pos (div_pos hp (by positivity))
    (integral_shiftedJacobiWeight_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

/-- The derivative-average Jacobi coefficient is also the weighted inner product
with the Jacobi polynomial divided by that polynomial's squared norm. -/
theorem shiftedJacobiCoefficient_eq_integral_div_norm {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (p : ℝ[X]) :
    shiftedJacobiCoefficient α β hα hβ n p =
      (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x *
        (shiftedJacobi α β n).eval x) /
      (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x *
        (shiftedJacobi α β n).eval x ^ 2) := by
  rw [shiftedJacobiCoefficient_apply, integral_shiftedJacobi_sq hα hβ,
    integral_mul_shiftedJacobi_eq_integral_derivative hα hβ]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hp := jacobi_pochhammer_ne_zero hα hβ n
  have hm := (integral_shiftedJacobiWeight_pos
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 < α + n)
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 < β + n)).ne'
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; simp
  field_simp
  linear_combination -(∫ x in (0 : ℝ)..1,
    shiftedJacobiWeight (α + n) (β + n) x * (derivative^[n] p).eval x) * hs

/-- Mathlib's shifted Legendre polynomial has squared norm `1/(2n+1)` on `[0,1]`.
This is the zero-parameter specialization of the Jacobi norm formula. -/
theorem integral_shiftedLegendre_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ((shiftedLegendre n).map (Int.castRingHom ℝ)).eval x ^ 2) =
      1 / (2 * n + 1 : ℝ) := by
  have h := integral_shiftedJacobi_sq (α := 0) (β := 0) (by norm_num) (by norm_num) n
  simp only [shiftedJacobi_zero_zero, shiftedJacobiWeight, Real.rpow_zero,
    one_mul, zero_add, Real.rpow_natCast] at h
  have hm : (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n) =
      (n.factorial * n.factorial : ℝ) / (n + n + 1).factorial := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_pow_mul_one_sub_pow]
  rw [hm] at h
  rw [h, ← Nat.cast_one, ← Nat.cast_add, ascPochhammer_nat_eq_natCast_ascFactorial]
  have hp : (n.factorial : ℝ) * ((n + 1).ascFactorial n : ℕ) =
      ((n + n).factorial : ℝ) := by exact_mod_cast Nat.factorial_mul_ascFactorial n n
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hnn : ((n + n).factorial : ℝ) ≠ 0 := by exact_mod_cast (n + n).factorial_ne_zero
  have hd : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hp]

end Polynomial
