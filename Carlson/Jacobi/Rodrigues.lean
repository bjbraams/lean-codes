/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Carlson

/-!
# Polynomial Rodrigues formula for Jacobi polynomials

For nonnegative integer parameters the Jacobi weight is a polynomial. The Rodrigues
identity is then an identity of polynomials, including at both endpoints, with no
choices of powers or branches. This module proves that algebraic version; Rodrigues
formulas for nonintegral parameters require a separate analytic argument.

## Main results

* `iterate_derivative_one_sub_X_pow`: derivatives of the polynomial endpoint weight.
* `shiftedJacobi_rodrigues_nat`: the polynomial Rodrigues identity.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.8, equation (7.8-1).
-/

public noncomputable section
namespace Polynomial
open Finset

/-- Repeated derivatives of a power of `1 - X`, in any commutative ring. -/
theorem iterate_derivative_one_sub_X_pow {R : Type*} [CommRing R] (m k : ℕ) :
    derivative^[k] ((1 - X : R[X]) ^ m) =
      C ((-1 : R) ^ k * (m.descFactorial k : R)) * (1 - X) ^ (m - k) := by
  have h := iterate_derivative_comp_one_sub_X (X ^ m : R[X]) k
  simpa only [pow_comp, X_comp, iterate_derivative_X_pow_eq_C_mul, mul_comp, C_comp,
    C_mul, C_pow, C_neg, C_1, mul_assoc] using h

/-- Rodrigues' formula for nonnegative integer Jacobi parameters, as a polynomial identity.
The factor `n!` is cleared, so the statement also includes `n = 0` directly. -/
private theorem shiftedJacobi_rodrigues_nat_complex (a b n : ℕ) :
    derivative^[n] ((X : ℂ[X]) ^ (a + n) * (1 - X) ^ (b + n)) =
      C (n.factorial : ℂ) * X ^ a * (1 - X) ^ b * shiftedJacobi (a : ℂ) b n := by
  apply Polynomial.funext
  intro x
  have h := Carlson.TwoVariable.factorial_mul_eval_shiftedJacobi (a : ℂ) b x n
  rw [iterate_derivative_mul]
  simp only [eval_finsetSum, nsmul_eq_mul, eval_natCast,
    iterate_derivative_X_pow_eq_C_mul, iterate_derivative_one_sub_X_pow,
    eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  have hn : (n.factorial : ℂ) * x ^ a * (1 - x) ^ b * (shiftedJacobi (a : ℂ) b n).eval x =
      x ^ a * (1 - x) ^ b * ((-1 : ℂ) ^ n *
        Carlson.TwoVariable.carlsonRPolynomialNumerator₂ n (-a - n) (-b - n) (1 - x) (-x)) := by
    linear_combination x ^ a * (1 - x) ^ b * h
  rw [hn, Carlson.TwoVariable.carlsonRPolynomialNumerator₂]
  simp only [mul_sum]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j i =>
    (n.choose j : ℂ) *
      (((a + n).descFactorial i : ℂ) * x ^ (a + n - i) *
        (((-1 : ℂ) ^ j * (b + n).descFactorial j) * (1 - x) ^ (b + n - j)))) n]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply sum_congr rfl
  intro ij hij
  dsimp only [Prod.swap]
  have hij' := mem_antidiagonal.mp hij
  have hpow : (-1 : ℂ) ^ n * (-1 : ℂ) ^ ij.1 * (-1 : ℂ) ^ ij.2 = 1 := by
    rw [mul_assoc, ← pow_add, hij', ← mul_pow]
    simp
  have ha : (ascPochhammer ℂ ij.1).eval (-(a : ℂ) - n) =
      (-1 : ℂ) ^ ij.1 * ((a + n).descFactorial ij.1 : ℂ) := by
    rw [show -(a : ℂ) - n = -((a + n : ℕ) : ℂ) by push_cast; ring,
      ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have hb : (ascPochhammer ℂ ij.2).eval (-(b : ℂ) - n) =
      (-1 : ℂ) ^ ij.2 * ((b + n).descFactorial ij.2 : ℂ) := by
    rw [show -(b : ℂ) - n = -((b + n : ℕ) : ℂ) by push_cast; ring,
      ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  rw [ha, hb, neg_pow, show a + n - ij.1 = a + ij.2 by omega,
    show b + n - ij.2 = b + ij.1 by omega, pow_add, pow_add]
  have hc : n.choose ij.1 = n.choose ij.2 := by rw [← hij']; exact Nat.choose_symm_add
  rw [hc]
  linear_combination
    -((n.choose ij.2 : ℂ) * (a + n).descFactorial ij.1 * (b + n).descFactorial ij.2 *
      x ^ a * x ^ ij.2 * (1 - x) ^ b * (1 - x) ^ ij.1 * (-1 : ℂ) ^ ij.2) * hpow

/-- Rodrigues' formula for nonnegative integer parameters over any commutative
rational algebra. This is an identity of polynomials, including at the endpoints. -/
theorem shiftedJacobi_rodrigues_nat {R : Type*} [CommRing R] [Algebra ℚ R] (a b n : ℕ) :
    derivative^[n] ((X : R[X]) ^ (a + n) * (1 - X) ^ (b + n)) =
      C (n.factorial : R) * X ^ a * (1 - X) ^ b * shiftedJacobi (a : R) b n := by
  have hc : (shiftedJacobi (a : ℚ) b n).map (algebraMap ℚ ℂ) =
      shiftedJacobi (a : ℂ) b n := by
    simpa using map_shiftedJacobi (Algebra.ofId ℚ ℂ) (a : ℚ) b n
  have hr : (shiftedJacobi (a : ℚ) b n).map (algebraMap ℚ R) =
      shiftedJacobi (a : R) b n := by
    simpa using map_shiftedJacobi (Algebra.ofId ℚ R) (a : ℚ) b n
  have hq : derivative^[n] ((X : ℚ[X]) ^ (a + n) * (1 - X) ^ (b + n)) =
      C (n.factorial : ℚ) * X ^ a * (1 - X) ^ b * shiftedJacobi (a : ℚ) b n := by
    apply Polynomial.map_injective (algebraMap ℚ ℂ) (RingHom.injective _)
    simpa only [← iterate_derivative_map, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, map_X, map_C, map_natCast, Polynomial.map_natCast, hc] using shiftedJacobi_rodrigues_nat_complex a b n
  have h := congrArg (Polynomial.map (algebraMap ℚ R)) hq
  simpa only [← iterate_derivative_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_one, map_X, map_C, map_natCast, Polynomial.map_natCast, hr] using h

end Polynomial
