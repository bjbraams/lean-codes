/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Endpoint

/-!
# The Jacobi differential equation

The standard Jacobi differential equation is a polynomial identity. Its proof
uses the endpoint derivative recurrence and polynomial uniqueness, so no
nonvanishing assumption on a Jacobi parameter is required.

## Main results

* `jacobi_differential_equation`: the standard Jacobi equation.
* `shiftedJacobi_differential_equation`: the equation in the coordinate on `[0,1]`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
-/

public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The Jacobi differential equation, as an identity of polynomials at all parameters. -/
theorem jacobi_differential_equation (α β : K) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (jacobi α β n)) +
      (C (β - α) - C (α + β + 2) * X) * derivative (jacobi α β n) +
        C ((n : K) * (n + α + β + 1)) * jacobi α β n = 0 := by
  let p := jacobi α β n
  have he : (1 - X ^ 2) * derivative (derivative p) +
      (C (β - α) - C (α + β + 2) * X) * derivative p +
        C ((n : K) * (n + α + β + 1)) * p =
      derivative^[2] p - derivative^[2] p * X ^ 2 + C (β - α) * derivative p -
        C (α + β + 2) * (derivative p * X) + C ((n : K) * (n + α + β + 1)) * p := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    ring
  change _ = (0 : K[X])
  rw [show jacobi α β n = p from rfl, he]
  apply eq_of_eval_iterate_derivative_eq _ _ 1
  intro k
  simp only [iterate_map_add, iterate_derivative_sub, iterate_derivative_C_mul,
    iterate_derivative_derivative_mul_X_sq, iterate_derivative_derivative_mul_X,
    ← Function.iterate_add_apply, ← Function.iterate_succ_apply, iterate_derivative_zero,
    eval_zero, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
    nsmul_eq_mul, eval_natCast]
  have h := iterate_derivative_jacobi_eval_one_recurrence α β n k
  dsimp only [p]
  change _ = 0
  cases k with
  | zero => simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero] at h ⊢; linear_combination -h
  | succ k =>
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
    linear_combination (norm := (push_cast; ring_nf)) -h

/-- The Jacobi differential equation after shifting the interval to `[0,1]`. -/
theorem shiftedJacobi_differential_equation (α β : K) (n : ℕ) :
    X * (1 - X) * derivative (derivative (shiftedJacobi α β n)) +
      (C (α + 1) - C (α + β + 2) * X) * derivative (shiftedJacobi α β n) +
        C ((n : K) * (n + α + β + 1)) * shiftedJacobi α β n = 0 := by
  have h := congrArg (fun p : K[X] => p.comp (1 - C 2 * X))
    (jacobi_differential_equation α β n)
  rw [← jacobi_comp_one_sub_two_mul_X α β n]
  simp only [derivative_comp, derivative_sub, derivative_one,
    derivative_X, mul_one, zero_sub, derivative_neg, derivative_mul, derivative_C,
    zero_mul, zero_add]
  simp only [add_comp, mul_comp, sub_comp, pow_comp, one_comp, X_comp, C_comp, zero_comp] at h
  simp only [C_add, C_sub, C_1, C_ofNat] at h ⊢
  linear_combination h

end Polynomial
