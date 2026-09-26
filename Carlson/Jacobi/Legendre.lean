/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# Legendre polynomials as Jacobi polynomials

The zero-parameter Jacobi polynomial is identified with Mathlib's existing
`shiftedLegendre`, whose coordinate convention is `Pₙ(1 - 2X)`.
No second definition of Legendre polynomials is introduced.

## Main results

* `shiftedJacobi_zero_zero`: the identification over a commutative rational algebra.
* `jacobi_zero_zero`: the corresponding identification in the standard coordinate.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7.
* `Mathlib.RingTheory.Polynomial.ShiftedLegendre`.
-/

public noncomputable section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- At zero parameters the Jacobi coefficient reduces to two binomial coefficients. -/
theorem jacobiCoeff_zero_zero (i j : ℕ) :
    jacobiCoeff (0 : R) 0 i j =
      (-1 : R) ^ j * ((i + j).choose j : R) * ((i + j + j).choose (i + j) : R) := by
  have ha (a b : ℕ) : (ascPochhammer R b).eval ((a : R) + 1) =
      (b.factorial : R) * ((a + b).choose b : R) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp only [jacobiCoeff, zero_add, ha]
  rw [Nat.add_comm j i, Nat.choose_symm_add, Nat.choose_symm_add]
  have hq : ((-1 : ℚ) ^ j / (i.factorial * j.factorial)) * i.factorial * j.factorial =
      (-1 : ℚ) ^ j := by field_simp
  have hr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one] at hr
  linear_combination ((i + j).choose j : R) * ((i + j + j).choose j : R) * hr

/-- Mathlib's shifted Legendre polynomial is exactly the zero-parameter Jacobi polynomial. -/
theorem shiftedJacobi_zero_zero (n : ℕ) :
    shiftedJacobi (0 : R) 0 n = (shiftedLegendre n).map (Int.castRingHom R) := by
  ext k
  rw [coeff_shiftedJacobi, coeff_map, coeff_shiftedLegendre]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  split_ifs with hk
  · rw [jacobiCoeff_zero_zero, Nat.sub_add_cancel hk]
  · simp [Nat.choose_eq_zero_of_lt (not_le.mp hk)]

/-- The standard Legendre polynomial obtained from Mathlib's shifted polynomial is Jacobi
with both parameters zero. -/
theorem jacobi_zero_zero (n : ℕ) :
    jacobi (0 : R) 0 n = ((shiftedLegendre n).map (Int.castRingHom R)).comp
      (C (algebraMap ℚ R (1 / 2)) * (1 - X)) := by
  rw [jacobi, shiftedJacobi_zero_zero]

end Polynomial
