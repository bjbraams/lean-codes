/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Rodrigues
public import Carlson.Jacobi.Expansion
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Orthogonality of Jacobi polynomials with polynomial weights

Repeated integration by parts is available for polynomial boundary weights.
Orthogonality on `[0,1]` with weight `x^a (1-x)^b` is obtained by specializing the
full real Jacobi theory, rather than by introducing an independent orthogonal family.

## Main results

* `integral_mul_iterate_derivative_eq`: repeated integration by parts with vanishing
  boundary derivatives.
* `integral_mul_shiftedJacobi_eq_zero_nat`: orthogonality to every polynomial of
  lower degree.
* `integral_shiftedJacobi_mul_shiftedJacobi_eq_zero_nat`: pairwise orthogonality.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.8, especially (7.8-1)–(7.8-3).
-/

public noncomputable section
namespace Polynomial
open MeasureTheory

/-- Repeated integration by parts for polynomials whose required boundary derivatives vanish. -/
theorem integral_mul_iterate_derivative_eq (p q : ℝ[X]) (a b : ℝ) (n : ℕ)
    (ha : ∀ k < n, (derivative^[k] q).eval a = 0)
    (hb : ∀ k < n, (derivative^[k] q).eval b = 0) :
    (∫ x in a..b, p.eval x * (derivative^[n] q).eval x) =
      (-1 : ℝ) ^ n * ∫ x in a..b, (derivative^[n] p).eval x * q.eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      p.continuous.continuousOn (derivative^[n] q).continuous.continuousOn
      (fun x _ => p.hasDerivAt x) (fun x _ => (derivative^[n] q).hasDerivAt x)
      (p.derivative.continuous.intervalIntegrable a b)
      ((derivative (derivative^[n] q)).continuous.intervalIntegrable a b)]
    rw [ha n (Nat.lt_succ_self n), hb n (Nat.lt_succ_self n), mul_zero, mul_zero,
      sub_self, zero_sub, ih p.derivative (fun k hk => ha k (by omega))
        (fun k hk => hb k (by omega)), Function.iterate_succ_apply, pow_succ]
    ring

/-- Differentiation fewer times than a vanishing power preserves a zero at that point. -/
theorem eval_iterate_derivative_eq_zero_of_pow_dvd {R : Type*} [CommRing R]
    (p q : R[X]) (x : R) {n k : ℕ} (h : q ^ n ∣ p) (hk : k < n) (hx : q.eval x = 0) :
    (derivative^[k] p).eval x = 0 := by
  obtain ⟨r, hr⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k h
  rw [hr, eval_mul, eval_pow, hx, zero_pow (by omega), zero_mul]

/-- For nonnegative integer parameters, a shifted Jacobi polynomial is orthogonal to
all polynomials of smaller degree with respect to its Jacobi weight. -/
theorem integral_mul_shiftedJacobi_eq_zero_nat (a b n : ℕ) (p : ℝ[X])
    (hp : p.degree < n) :
    (∫ x in (0 : ℝ)..1,
      p.eval x * (shiftedJacobi (a : ℝ) b n).eval x * x ^ a * (1 - x) ^ b) = 0 := by
  simpa only [shiftedJacobiWeight, Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using
    integral_mul_shiftedJacobi_eq_zero (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg a))
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg b)) n p hp

/-- Pairwise weighted orthogonality of shifted Jacobi polynomials at nonnegative
integer parameters. -/
theorem integral_shiftedJacobi_mul_shiftedJacobi_eq_zero_nat (a b m n : ℕ) (hmn : m < n) :
    (∫ x in (0 : ℝ)..1,
      (shiftedJacobi (a : ℝ) b m).eval x * (shiftedJacobi (a : ℝ) b n).eval x *
        x ^ a * (1 - x) ^ b) = 0 := by
  apply integral_mul_shiftedJacobi_eq_zero_nat
  exact (degree_le_of_natDegree_le (natDegree_shiftedJacobi_le (a : ℝ) b m)).trans_lt
    (by exact_mod_cast hmn)

end Polynomial
