/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basic
public import Carlson.Jacobi.Chebyshev
public import Carlson.Jacobi.Legendre
public import Carlson.Jacobi.RealOrthogonality

/-!
# Gegenbauer polynomials and symmetric Jacobi polynomials

The Gegenbauer polynomial is defined by a finite sum with rational factorial
denominators. Its coefficients are polynomial in the parameter, so the definition
also covers zero and the exceptional negative half-integer parameters. The
identification with Jacobi polynomials is stated with its parameter denominator
cleared.

## Main results

* `gegenbauer`: the standard Gegenbauer polynomial over a commutative rational algebra.
* `pochhammer_mul_gegenbauer`: the denominator-free identification with symmetric Jacobi
  polynomials over a field of characteristic zero.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
-/

@[expose] public noncomputable section
namespace Polynomial
open Finset

/-- Gegenbauer polynomials in the shifted coordinate, defined at every parameter. -/
def shiftedGegenbauer {R : Type*} [CommRing R] [Algebra ℚ R] (ρ : R) (n : ℕ) : R[X] :=
  ∑ ij ∈ antidiagonal n,
    C (algebraMap ℚ R ((-4 : ℚ) ^ ij.2 / (ij.1.factorial * ij.2.factorial)) *
      (ascPochhammer R ij.2).eval ρ * (ascPochhammer R ij.1).eval (2 * ρ + 2 * ij.2)) * X ^ ij.2

/-- Gegenbauer polynomials in classical normalization. This finite formula involves
no division by parameter-dependent factors. -/
def gegenbauer {R : Type*} [CommRing R] [Algebra ℚ R] (ρ : R) (n : ℕ) : R[X] :=
  (shiftedGegenbauer ρ n).comp (C (algebraMap ℚ R (1 / 2)) * (1 - X))

/-- The degree-zero Gegenbauer polynomial is one. -/
@[simp] theorem gegenbauer_zero {R : Type*} [CommRing R] [Algebra ℚ R] (ρ : R) :
    gegenbauer ρ 0 = 1 := by
  simp [gegenbauer, shiftedGegenbauer, -RingHom.map_rat_algebraMap]

/-- At parameter zero the positive-index Gegenbauer polynomials vanish. In particular,
Chebyshev polynomials of the first kind are not obtained by substituting zero without rescaling. -/
@[simp] theorem gegenbauer_zero_param_succ {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ) :
    gegenbauer (0 : R) (n + 1) = 0 := by
  have hs : shiftedGegenbauer (0 : R) (n + 1) = 0 := by
    apply sum_eq_zero
    intro ij hij
    have hn := mem_antidiagonal.mp hij
    by_cases hj : ij.2 = 0
    · have hi : ij.1 ≠ 0 := by omega
      simp [hj, hi]
    · simp [hj]
  rw [gegenbauer, hs, zero_comp]

variable {K : Type*} [Field K] [CharZero K]

/-- The shifted Gegenbauer/Jacobi identification with its parameter denominator cleared. -/
theorem pochhammer_mul_shiftedGegenbauer (ρ : K) (n : ℕ) :
    C ((ascPochhammer K n).eval (ρ + 1 / 2)) * shiftedGegenbauer ρ n =
      C ((ascPochhammer K n).eval (2 * ρ)) * shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) n := by
  simp only [shiftedGegenbauer, shiftedJacobi, mul_sum]
  apply sum_congr rfl
  intro ij hij
  simp only [← mul_assoc, ← C_mul]
  congr 2
  rw [jacobiCoeff]
  have hn := mem_antidiagonal.mp hij
  have hs := ascPochhammer_add_eval (2 * ρ) n ij.2
  rw [← hn, show ij.1 + ij.2 + ij.2 = 2 * ij.2 + ij.1 by omega,
    ascPochhammer_add_eval, ascPochhammer_eval_double] at hs
  rw [hn] at hs
  push_cast at hs
  have ht := ascPochhammer_add_eval (ρ + 1 / 2) ij.2 ij.1
  rw [show ij.2 + ij.1 = n by omega] at ht
  norm_num only [map_div₀, map_pow, map_neg, map_ofNat, map_one, map_mul, map_natCast]
  rw [show ρ - 1 / 2 + ij.2 + 1 = ρ + 1 / 2 + ij.2 by ring,
    show ρ - 1 / 2 + (ρ - 1 / 2) + (ij.1 + ij.2 : ℕ) + 1 = 2 * ρ + n by rw [hn]; ring]
  have hpow : (-4 : K) ^ ij.2 = (-1 : K) ^ ij.2 * 4 ^ ij.2 := by rw [← mul_pow]; norm_num
  rw [hpow, ht]
  have hi : (ij.1.factorial : K) ≠ 0 := by exact_mod_cast ij.1.factorial_ne_zero
  have hj : (ij.2.factorial : K) ≠ 0 := by exact_mod_cast ij.2.factorial_ne_zero
  field_simp
  linear_combination (norm := (push_cast; ring_nf))
    (ascPochhammer K ij.1).eval (ρ + 1 / 2 + ij.2) * hs

/-- Gegenbauer polynomials are rescaled symmetric Jacobi polynomials. The cleared
identity also holds at zeros of the usual parameter denominator. -/
theorem pochhammer_mul_gegenbauer (ρ : K) (n : ℕ) :
    C ((ascPochhammer K n).eval (ρ + 1 / 2)) * gegenbauer ρ n =
      C ((ascPochhammer K n).eval (2 * ρ)) * jacobi (ρ - 1 / 2) (ρ - 1 / 2) n := by
  simpa only [mul_comp, C_comp, gegenbauer, jacobi] using
    congrArg (fun p : K[X] => p.comp (C (algebraMap ℚ K (1 / 2)) * (1 - X)))
      (pochhammer_mul_shiftedGegenbauer ρ n)

/-- The quotient form of the shifted Gegenbauer/Jacobi relation on the nonsingular set. -/
theorem shiftedGegenbauer_eq_shiftedJacobi (ρ : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (ρ + 1 / 2) ≠ 0) :
    shiftedGegenbauer ρ n = C ((ascPochhammer K n).eval (2 * ρ) /
      (ascPochhammer K n).eval (ρ + 1 / 2)) * shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) n := by
  apply mul_left_cancel₀ (show C ((ascPochhammer K n).eval (ρ + 1 / 2)) ≠ 0 by simpa using h)
  rw [pochhammer_mul_shiftedGegenbauer, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ h]

/-- The quotient form of the Gegenbauer/Jacobi relation where its denominator is nonzero. -/
theorem gegenbauer_eq_jacobi (ρ : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (ρ + 1 / 2) ≠ 0) :
    gegenbauer ρ n = C ((ascPochhammer K n).eval (2 * ρ) /
      (ascPochhammer K n).eval (ρ + 1 / 2)) * jacobi (ρ - 1 / 2) (ρ - 1 / 2) n := by
  apply mul_left_cancel₀ (show C ((ascPochhammer K n).eval (ρ + 1 / 2)) ≠ 0 by simpa using h)
  rw [pochhammer_mul_gegenbauer, ← mul_assoc, ← C_mul]
  rw [mul_div_cancel₀ _ h]

/-- Gegenbauer parameter `1/2` gives the Legendre specialization of Jacobi. -/
theorem gegenbauer_half_param (n : ℕ) :
    gegenbauer (1 / 2 : K) n = jacobi (0 : K) 0 n := by
  have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [gegenbauer_eq_jacobi (1 / 2 : K) n (by norm_num only [show (1 / 2 : K) + 1 / 2 = 1 by ring, ascPochhammer_eval_one]; exact hf)]
  norm_num [hf]

/-- The Legendre specialization uses Mathlib's existing shifted Legendre polynomial. -/
theorem gegenbauer_half_param_eq_shiftedLegendre (n : ℕ) :
    gegenbauer (1 / 2 : K) n = ((shiftedLegendre n).map (Int.castRingHom K)).comp
      (C (algebraMap ℚ K (1 / 2)) * (1 - X)) := by
  rw [gegenbauer_half_param, jacobi_zero_zero]

/-- Gegenbauer parameter one gives Mathlib's Chebyshev polynomial of the second kind. -/
theorem gegenbauer_one_param_eq_chebyshev_U (n : ℕ) :
    gegenbauer (1 : K) n = Chebyshev.U K n := by
  have ht : (ascPochhammer K n).eval (2 : K) = ((n + 1).factorial : K) := by
    simpa only [Nat.factorial_one, Nat.cast_one, one_mul, one_add_one_eq_two, Nat.add_comm] using
      factorial_mul_ascPochhammer K 1 n
  have hq : (ascPochhammer ℚ n).eval (3 / 2 : ℚ) ≠ 0 :=
    (ascPochhammer_pos n _ (by norm_num)).ne'
  have hk : (ascPochhammer K n).eval (3 / 2 : K) ≠ 0 := by
    have he : algebraMap ℚ K ((ascPochhammer ℚ n).eval (3 / 2)) =
        (ascPochhammer K n).eval (3 / 2) := by
      rw [← eval₂_at_apply, ascPochhammer_eval₂ (algebraMap ℚ K)]
      norm_num
    rw [← he]
    simpa only [map_zero] using (algebraMap ℚ K).injective.ne hq
  rw [gegenbauer_eq_jacobi (1 : K) n (by rw [show (1 : K) + 1 / 2 = 3 / 2 by ring]; exact hk)]
  norm_num only [one_mul, show (1 : K) + 1 / 2 = 3 / 2 by ring,
    show (1 : K) - 1 / 2 = 1 / 2 by ring]
  rw [jacobi_half_eq_chebyshev_U, ← mul_assoc, ← C_mul, ht]
  have hf : ((n + 1).factorial : K) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
  rw [show ((n + 1).factorial : K) / (ascPochhammer K n).eval (3 / 2) *
      ((ascPochhammer K n).eval (3 / 2) / (n + 1).factorial) = 1 by field_simp,
    C_1, one_mul]

/-- Gegenbauer orthogonality on the shifted interval follows from Jacobi orthogonality.
The parameter zero is allowed: its positive-index polynomials vanish. -/
theorem integral_shiftedGegenbauer_mul_shiftedGegenbauer_eq_zero {ρ : ℝ} (hρ : -1 / 2 < ρ)
    (m n : ℕ) (hmn : m ≠ n) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (ρ - 1 / 2) (ρ - 1 / 2) x *
      (shiftedGegenbauer ρ m).eval x * (shiftedGegenbauer ρ n).eval x) = 0 := by
  have hd (k : ℕ) : (ascPochhammer ℝ k).eval (ρ + 1 / 2) ≠ 0 :=
    (ascPochhammer_pos k _ (by linarith)).ne'
  rw [shiftedGegenbauer_eq_shiftedJacobi ρ m (hd m),
    shiftedGegenbauer_eq_shiftedJacobi ρ n (hd n)]
  simp only [eval_mul, eval_C]
  let cm := (ascPochhammer ℝ m).eval (2 * ρ) / (ascPochhammer ℝ m).eval (ρ + 1 / 2)
  let cn := (ascPochhammer ℝ n).eval (2 * ρ) / (ascPochhammer ℝ n).eval (ρ + 1 / 2)
  have he (x : ℝ) : shiftedJacobiWeight (ρ - 1 / 2) (ρ - 1 / 2) x *
      (cm * (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) m).eval x) *
      (cn * (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) n).eval x) =
      (cm * cn) * (shiftedJacobiWeight (ρ - 1 / 2) (ρ - 1 / 2) x *
        (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) m).eval x *
        (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) n).eval x) := by ring
  change (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (ρ - 1 / 2) (ρ - 1 / 2) x *
    (cm * (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) m).eval x) *
    (cn * (shiftedJacobi (ρ - 1 / 2) (ρ - 1 / 2) n).eval x)) = 0
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    integral_shiftedJacobi_mul_shiftedJacobi_eq_zero (by linarith) (by linarith) m n hmn,
    mul_zero]

end Polynomial
