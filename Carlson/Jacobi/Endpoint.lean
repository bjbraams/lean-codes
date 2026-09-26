/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Derivative
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Endpoint derivatives of Jacobi polynomials

Values of all derivatives at one characterize a polynomial over a field of
characteristic zero. The Jacobi endpoint derivatives satisfy a recurrence that
can be used to identify classical specializations without developing a second
independent polynomial theory.

## Main results

* `eq_of_eval_iterate_derivative_eq`: uniqueness from all derivatives at one point.
* `iterate_derivative_jacobi_eval_one_recurrence`: the Jacobi endpoint recurrence.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
-/

public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Polynomials over a characteristic-zero field are determined by all derivatives
at any fixed point. -/
theorem eq_of_eval_iterate_derivative_eq (p q : K[X]) (x : K)
    (h : ∀ k, (derivative^[k] p).eval x = (derivative^[k] q).eval x) : p = q := by
  apply taylor_injective x
  ext k
  apply mul_left_cancel₀ (show (k.factorial : K) ≠ 0 by exact_mod_cast k.factorial_ne_zero)
  rw [taylor_coeff, taylor_coeff]
  have he (r : K[X]) : (k.factorial : K) * (hasseDeriv k r).eval x =
      (derivative^[k] r).eval x := by
    have hi := congrFun (factorial_smul_hasseDeriv (R := K) (k := k)) r
    change k.factorial • hasseDeriv k r = derivative^[k] r at hi
    have hv := congrArg (eval x) hi
    simpa only [LinearMap.smul_apply, nsmul_eq_mul, eval_mul, eval_natCast] using hv
  rw [he, he, h k]

/-- The recurrence between consecutive endpoint derivatives, below the polynomial index. -/
private theorem iterate_derivative_jacobi_eval_one_recurrence_add
    (α β : K) (m k : ℕ) :
    2 * (α + k + 1) * (derivative^[k + 1] (jacobi α β (m + (k + 1)))).eval 1 =
      (m + 1 : K) * (α + β + (m + (k + 1) : ℕ) + k + 1) *
        (derivative^[k] (jacobi α β (m + (k + 1)))).eval 1 := by
  rw [iterate_derivative_jacobi,
    show m + (k + 1) = (m + 1) + k by omega, iterate_derivative_jacobi]
  simp only [eval_mul, eval_C, eval_jacobi_one]
  rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
  rw [ascPochhammer_succ_left (S := K) m]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  norm_num only [map_div₀, map_one, map_ofNat, map_natCast, map_mul, map_add, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hm : (m.factorial : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hm1 : (m : K) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  field_simp
  ring_nf

/-- Jacobi endpoint derivatives satisfy a division-free recurrence, including derivatives
above the degree and exceptional parameter values. -/
theorem iterate_derivative_jacobi_eval_one_recurrence (α β : K) (n k : ℕ) :
    2 * (α + k + 1) * (derivative^[k + 1] (jacobi α β n)).eval 1 =
      ((n : K) - k) * (α + β + n + k + 1) * (derivative^[k] (jacobi α β n)).eval 1 := by
  by_cases hk : k < n
  · have hn : n = (n - (k + 1)) + (k + 1) := by omega
    rw [hn]
    convert iterate_derivative_jacobi_eval_one_recurrence_add α β (n - (k + 1)) k using 1
    push_cast
    ring
  · have hn : (jacobi α β n).natDegree < k + 1 :=
      (natDegree_jacobi_le α β n).trans_lt (by omega)
    rw [iterate_derivative_eq_zero hn, eval_zero, mul_zero]
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hk) with rfl | hlt
    · simp
    · rw [iterate_derivative_eq_zero ((natDegree_jacobi_le α β n).trans_lt hlt),
        eval_zero, mul_zero]

end Polynomial
