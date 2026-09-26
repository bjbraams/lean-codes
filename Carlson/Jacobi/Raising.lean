/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.DifferentialEquation

/-!
# The Jacobi raising identity

Applying the Pearson differential operator to a shifted Jacobi polynomial with
both parameters increased by one raises its degree. The identity is polynomial
in the parameters and holds even at exceptional values. It is the algebraic
step in the analytic Rodrigues formula and in repeated weighted integration by parts.

## Main results

* `shiftedJacobi_raising`: the degree-raising Pearson identity over a
  characteristic-zero field, without parameter restrictions.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8.
-/

public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The Pearson raising operator produces the next shifted Jacobi polynomial.
This identity includes parameter values at which the degree drops. -/
theorem shiftedJacobi_raising (α β : K) (n : ℕ) :
    (C (α + 1) - C (α + β + 2) * X) * shiftedJacobi (α + 1) (β + 1) n +
      X * (1 - X) * derivative (shiftedJacobi (α + 1) (β + 1) n) =
        C (n + 1 : K) * shiftedJacobi α β (n + 1) := by
  let p := (C (α + 1) - C (α + β + 2) * X) * shiftedJacobi (α + 1) (β + 1) n +
    X * (1 - X) * derivative (shiftedJacobi (α + 1) (β + 1) n) -
      C (n + 1 : K) * shiftedJacobi α β (n + 1)
  have hd : derivative p = 0 := by
    have h := shiftedJacobi_differential_equation (α + 1) (β + 1) n
    dsimp only [p]
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_C,
      derivative_X, derivative_one, zero_mul, zero_add,
      mul_one, zero_sub, derivative_shiftedJacobi_succ]
    simp only [C_add, C_mul, C_neg, C_1, C_ofNat] at h ⊢
    linear_combination h
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp only [p]
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, mul_zero, sub_zero,
      zero_mul, add_zero, ← coeff_zero_eq_eval_zero, coeff_shiftedJacobi_zero]
    norm_num only [map_div₀, map_one, map_natCast]
    rw [ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
    rw [Nat.factorial_succ]
    push_cast
    have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  have he := eq_C_of_derivative_eq_zero hd
  rw [h0, C_0] at he
  exact sub_eq_zero.mp he

end Polynomial
