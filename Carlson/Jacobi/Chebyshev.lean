/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Endpoint
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev polynomials as Jacobi specializations

The symmetric Jacobi parameters `(-1/2,-1/2)` and `(1/2,1/2)` give Mathlib's
Chebyshev polynomials `T` and `U` after explicit scalar normalization. The proofs
use the general Jacobi endpoint derivative recurrence and Mathlib's corresponding
Chebyshev recurrence.

## Main results

* `jacobi_neg_half_eq_chebyshev_T`: the first-kind specialization.
* `jacobi_half_eq_chebyshev_U`: the second-kind specialization.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
* `Mathlib.RingTheory.Polynomial.Chebyshev`.
-/

public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Chebyshev polynomials of the first kind are the symmetric Jacobi specialization
with parameters `-1/2`, with the classical normalization factor. -/
theorem jacobi_neg_half_eq_chebyshev_T (n : ℕ) :
    jacobi (-1 / 2 : K) (-1 / 2) n =
      C ((ascPochhammer K n).eval (1 / 2) / n.factorial) * Chebyshev.T K n := by
  apply eq_of_eval_iterate_derivative_eq _ _ 1
  intro k
  simp only [iterate_derivative_C_mul, eval_mul, eval_C]
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, eval_jacobi_one, Chebyshev.T_eval_one, mul_one]
    norm_num
    ring
  | succ k ih =>
    have hj := iterate_derivative_jacobi_eval_one_recurrence (-1 / 2 : K) (-1 / 2) n k
    have ht := Chebyshev.iterate_derivative_T_eval_one_recurrence (R := K) (n : ℤ) k
    apply mul_left_cancel₀ (show (2 * k + 1 : K) ≠ 0 by
      exact_mod_cast (show 2 * k + 1 ≠ 0 by omega))
    linear_combination (norm := (push_cast; ring_nf))
      hj - ((ascPochhammer K n).eval (1 / 2) / n.factorial) * ht +
        ((n : K) ^ 2 - (k : K) ^ 2) * ih

/-- Chebyshev polynomials of the second kind are the symmetric Jacobi specialization
with parameters `1/2`, including the normalization at index zero. -/
theorem jacobi_half_eq_chebyshev_U (n : ℕ) :
    jacobi (1 / 2 : K) (1 / 2) n =
      C ((ascPochhammer K n).eval (3 / 2) / (n + 1).factorial) * Chebyshev.U K n := by
  apply eq_of_eval_iterate_derivative_eq _ _ 1
  intro k
  simp only [iterate_derivative_C_mul, eval_mul, eval_C]
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, eval_jacobi_one, Chebyshev.U_eval_one]
    norm_num only [map_div₀, map_one, map_natCast, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Int.cast_natCast]
    field_simp
  | succ k ih =>
    have hj := iterate_derivative_jacobi_eval_one_recurrence (1 / 2 : K) (1 / 2) n k
    have ht := Chebyshev.iterate_derivative_U_eval_one_recurrence (R := K) (n : ℤ) k
    apply mul_left_cancel₀ (show (2 * k + 3 : K) ≠ 0 by
      exact_mod_cast (show 2 * k + 3 ≠ 0 by omega))
    linear_combination (norm := (push_cast; ring_nf))
      hj - ((ascPochhammer K n).eval (3 / 2) / (n + 1).factorial) * ht +
        (((n : K) + 1) ^ 2 - ((k : K) + 1) ^ 2) * ih

end Polynomial
