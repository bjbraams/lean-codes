/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basic

/-!
# Derivatives of Jacobi polynomials

Formal differentiation shifts both Jacobi parameters by one and lowers the index.
These identities hold over any commutative rational algebra, without restrictions
on the parameters or on the degree of the resulting polynomial.

## Main results

* `derivative_shiftedJacobi_succ`: derivative in the shifted coordinate.
* `derivative_jacobi_succ`: the classical Jacobi derivative identity.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
-/

public noncomputable section
namespace Polynomial
open Finset
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient identity underlying the Jacobi derivative formula. -/
theorem jacobiCoeff_succ_right (α β : R) (i j : ℕ) :
    jacobiCoeff α β i (j + 1) * (j + 1 : R) =
      -(α + β + (i + j : ℕ) + 2) * jacobiCoeff (α + 1) (β + 1) i j := by
  have hq : ((-1 : ℚ) ^ (j + 1) / (i.factorial * (j + 1).factorial)) * (j + 1) =
      -((-1 : ℚ) ^ j / (i.factorial * j.factorial)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_add, map_natCast, map_one, map_neg] at hr
  have hs (p : R) : (ascPochhammer R (j + 1)).eval p =
      p * (ascPochhammer R j).eval (p + 1) := by
    simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one]
  simp only [jacobiCoeff, hs, Nat.cast_add, Nat.cast_one]
  rw [show α + (j + 1) + 1 = α + 1 + j + 1 by ring,
    show α + β + (i + (j + 1)) + 1 = α + β + (i + j) + 2 by ring,
    show α + β + (i + j) + 2 + 1 = α + 1 + (β + 1) + (i + j) + 1 by ring]
  linear_combination
    (ascPochhammer R i).eval (α + 1 + j + 1) *
      (α + β + (i + j) + 2) *
      (ascPochhammer R j).eval (α + 1 + (β + 1) + (i + j) + 1) * hr

/-- Differentiation in the shifted coordinate lowers the index and shifts both parameters. -/
theorem derivative_shiftedJacobi_succ (α β : R) (n : ℕ) :
    derivative (shiftedJacobi α β (n + 1)) =
      C (-(α + β + n + 2)) * shiftedJacobi (α + 1) (β + 1) n := by
  rw [shiftedJacobi, Finset.Nat.sum_antidiagonal_succ']
  simp only [pow_zero, mul_one, derivative_add, derivative_C, zero_add,
    derivative_sum, derivative_C_mul, derivative_X_pow_succ]
  rw [shiftedJacobi, mul_sum]
  apply sum_congr rfl
  intro ij hij
  rw [← mul_assoc, ← C_mul, jacobiCoeff_succ_right, mem_antidiagonal.mp hij, C_mul]
  ring

/-- The classical derivative identity, valid even when a parameter causes degree loss. -/
theorem derivative_jacobi_succ (α β : R) (n : ℕ) :
    derivative (jacobi α β (n + 1)) =
      C (algebraMap ℚ R (1 / 2) * (α + β + n + 2)) *
        jacobi (α + 1) (β + 1) n := by
  simp only [jacobi, derivative_comp, derivative_shiftedJacobi_succ, mul_comp, C_comp,
    derivative_C_mul, derivative_sub, derivative_one, derivative_X, zero_sub]
  simp only [C_neg, C_mul]
  ring

/-- Repeated differentiation of a shifted Jacobi polynomial. The index `n + k`
ensures that the remaining polynomial has nonnegative index. -/
theorem iterate_derivative_shiftedJacobi (α β : R) (n k : ℕ) :
    derivative^[k] (shiftedJacobi α β (n + k)) =
      C ((-1 : R) ^ k * (ascPochhammer R k).eval (α + β + (n + k : ℕ) + 1)) *
        shiftedJacobi (α + k) (β + k) n := by
  induction k generalizing α β with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← Nat.add_assoc, derivative_shiftedJacobi_succ,
      iterate_derivative_C_mul, ih]
    simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one,
      Nat.cast_add, Nat.cast_one, pow_succ, C_mul, C_neg, C_1]
    rw [show α + 1 + k = α + (k + 1) by ring,
      show β + 1 + k = β + (k + 1) by ring,
      show α + 1 + (β + 1) + (n + k) + 1 = α + β + (n + (k + 1)) + 1 + 1 by ring]
    simp only [C_add, C_ofNat, C_1]
    ring_nf

/-- Repeated differentiation in the standard coordinate. -/
theorem iterate_derivative_jacobi (α β : R) (n k : ℕ) :
    derivative^[k] (jacobi α β (n + k)) =
      C (algebraMap ℚ R (1 / 2) ^ k *
        (ascPochhammer R k).eval (α + β + (n + k : ℕ) + 1)) *
        jacobi (α + k) (β + k) n := by
  induction k generalizing α β with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← Nat.add_assoc, derivative_jacobi_succ,
      iterate_derivative_C_mul, ih]
    simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one,
      Nat.cast_add, Nat.cast_one, pow_succ, C_mul]
    rw [show α + 1 + k = α + (k + 1) by ring,
      show β + 1 + k = β + (k + 1) by ring,
      show α + 1 + (β + 1) + (n + k) + 1 = α + β + (n + (k + 1)) + 1 + 1 by ring]
    simp only [C_add, C_ofNat, C_1]
    ring_nf

end Polynomial
