/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.Identities
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Tactic

/-!
# Jacobi polynomials over a rational algebra

The standard Jacobi polynomial is `jacobi α β n`. Its shifted version is
`shiftedJacobi α β n`, with the convention `Pₙ⁽α,β⁾(1 - 2X)`.
The finite Pochhammer formula uses only rational denominators, and therefore defines
polynomials at every parameter, including values where the degree drops. Coefficients
may lie in any commutative rational algebra.

## Main results

* `coeff_shiftedJacobi`: the coefficients of the shifted polynomial.
* `natDegree_shiftedJacobi_le`: the degree bound, without parameter restrictions.
* `shiftedJacobi_zero`, `jacobi_zero`: the degree-zero normalization.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 7, especially §§7.1 and 7.8. Carlson's polynomials have monic normalization;
  `jacobi` uses the classical normalization.
-/

@[expose] public noncomputable section
namespace Polynomial
open Finset
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient of `X^j` in the shifted Jacobi polynomial of degree `i + j`.
Only factorials occur in the denominator, so no parameter values are excluded. -/
def jacobiCoeff (α β : R) (i j : ℕ) : R :=
  algebraMap ℚ R ((-1 : ℚ) ^ j / (i.factorial * j.factorial)) *
    (ascPochhammer R i).eval (α + j + 1) *
    (ascPochhammer R j).eval (α + β + (i + j : ℕ) + 1)

/-- The standard Jacobi polynomial evaluated at `1 - 2X`, defined over any
commutative rational algebra. -/
def shiftedJacobi (α β : R) (n : ℕ) : R[X] :=
  ∑ ij ∈ antidiagonal n, C (jacobiCoeff α β ij.1 ij.2) * X ^ ij.2

/-- The Jacobi polynomial in classical normalization, with
`Pₙ⁽α,β⁾(1) = (α + 1)ₙ / n!`. -/
def jacobi (α β : R) (n : ℕ) : R[X] :=
  (shiftedJacobi α β n).comp (C (algebraMap ℚ R (1 / 2)) * (1 - X))

/-- Coefficients of a shifted Jacobi polynomial, including those above its degree. -/
theorem coeff_shiftedJacobi (α β : R) (n k : ℕ) :
    (shiftedJacobi α β n).coeff k =
      if k ≤ n then jacobiCoeff α β (n - k) k else 0 := by
  simp only [shiftedJacobi, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_ite_eq]

/-- The shifted Jacobi polynomial has degree at most its index, also at exceptional parameters. -/
theorem natDegree_shiftedJacobi_le (α β : R) (n : ℕ) :
    (shiftedJacobi α β n).natDegree ≤ n := by
  exact natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
    simp [coeff_shiftedJacobi, not_le.mpr hk]

/-- The highest possible coefficient is a rising factorial in the parameter sum. -/
theorem coeff_shiftedJacobi_self (α β : R) (n : ℕ) :
    (shiftedJacobi α β n).coeff n =
      algebraMap ℚ R ((-1 : ℚ) ^ n / n.factorial) *
        (ascPochhammer R n).eval (α + β + n + 1) := by
  simp [coeff_shiftedJacobi, jacobiCoeff]

/-- The constant term is the usual endpoint normalization. -/
theorem coeff_shiftedJacobi_zero (α β : R) (n : ℕ) :
    (shiftedJacobi α β n).coeff 0 =
      algebraMap ℚ R (1 / n.factorial) * (ascPochhammer R n).eval (α + 1) := by
  simp [coeff_shiftedJacobi, jacobiCoeff]

/-- The degree-zero shifted Jacobi polynomial is one. -/
@[simp] theorem shiftedJacobi_zero (α β : R) : shiftedJacobi α β 0 = 1 := by
  simp [shiftedJacobi, jacobiCoeff, -RingHom.map_rat_algebraMap]

/-- The degree-zero Jacobi polynomial is one. -/
@[simp] theorem jacobi_zero (α β : R) : jacobi α β 0 = 1 := by
  simp [jacobi, -RingHom.map_rat_algebraMap]

/-- Evaluating the standard Jacobi polynomial amounts to an affine change of variable. -/
theorem eval_jacobi (α β x : R) (n : ℕ) :
    (jacobi α β n).eval x =
      (shiftedJacobi α β n).eval (algebraMap ℚ R (1 / 2) * (1 - x)) := by
  simp [jacobi, -RingHom.map_rat_algebraMap]

/-- The standard Jacobi polynomial has its classical normalization at one. -/
theorem eval_jacobi_one (α β : R) (n : ℕ) :
    (jacobi α β n).eval 1 =
      algebraMap ℚ R (1 / n.factorial) * (ascPochhammer R n).eval (α + 1) := by
  rw [eval_jacobi]
  simpa only [sub_self, mul_zero, ← coeff_zero_eq_eval_zero] using coeff_shiftedJacobi_zero α β n

/-- An affine substitution recovers the shifted polynomial from the standard one. -/
theorem jacobi_comp_one_sub_two_mul_X (α β : R) (n : ℕ) :
    (jacobi α β n).comp (1 - C 2 * X) = shiftedJacobi α β n := by
  have hh : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (algebraMap ℚ R) (by norm_num : (2 : ℚ) * (1 / 2) = 1)
  rw [jacobi, comp_assoc]
  have harg : (C (algebraMap ℚ R (1 / 2)) * (1 - X)).comp (1 - C 2 * X) = X := by
    simp only [mul_comp, C_comp, sub_comp, one_comp, X_comp]
    have hp := congrArg C hh
    simp only [C_mul, C_1] at hp
    linear_combination X * hp
  rw [harg, comp_X]

/-- The standard Jacobi polynomial has degree at most its index. -/
theorem natDegree_jacobi_le (α β : R) (n : ℕ) :
    (jacobi α β n).natDegree ≤ n := by
  refine natDegree_comp_le.trans ?_
  have ha : (C (algebraMap ℚ R (1 / 2)) * (1 - X)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_sub_le_of_le
      (show (1 : R[X]).natDegree ≤ 1 by simp) natDegree_X_le)
  simpa only [mul_one] using Nat.mul_le_mul (natDegree_shiftedJacobi_le α β n) ha

/-- Clearing the factorial denominators in a Jacobi coefficient gives a binomial coefficient. -/
theorem factorial_mul_jacobiCoeff (α β : R) (i j : ℕ) :
    ((i + j).factorial : R) * jacobiCoeff α β i j =
      (-1 : R) ^ j * ((i + j).choose j : R) *
        (ascPochhammer R i).eval (α + j + 1) *
        (ascPochhammer R j).eval (α + β + (i + j : ℕ) + 1) := by
  have hf : ((i + j).choose j : ℚ) * i.factorial * j.factorial =
      (i + j).factorial := by exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial i j
  have hq : ((i + j).factorial : ℚ) * ((-1 : ℚ) ^ j / (i.factorial * j.factorial)) =
      (-1 : ℚ) ^ j * (i + j).choose j := by
    rw [← hf]
    field_simp
  have hr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one] at hr
  unfold jacobiCoeff
  linear_combination
    (ascPochhammer R i).eval (α + j + 1) *
      (ascPochhammer R j).eval (α + β + (i + j : ℕ) + 1) * hr

/-- Jacobi coefficients commute with homomorphisms of rational algebras. -/
theorem map_jacobiCoeff {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (α β : R) (i j : ℕ) :
    f (jacobiCoeff α β i j) = jacobiCoeff (f α) (f β) i j := by
  have he (p : R) (k : ℕ) : f ((ascPochhammer R k).eval p) =
      (ascPochhammer S k).eval (f p) := by
    change (f : R →+* S) ((ascPochhammer R k).eval p) =
      (ascPochhammer S k).eval ((f : R →+* S) p)
    rw [← eval₂_at_apply, ← eval_map, ascPochhammer_map]
  simp only [jacobiCoeff, map_mul, f.commutes, he, map_add, map_natCast, map_one]

/-- Shifted Jacobi polynomials commute with homomorphisms of rational algebras. -/
theorem map_shiftedJacobi {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (α β : R) (n : ℕ) :
    (shiftedJacobi α β n).map (f : R →+* S) = shiftedJacobi (f α) (f β) n := by
  simp only [shiftedJacobi, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
    map_X, AlgHom.coe_toRingHom, map_jacobiCoeff]

/-- Standard Jacobi polynomials commute with homomorphisms of rational algebras. -/
theorem map_jacobi {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (α β : R) (n : ℕ) :
    (jacobi α β n).map (f : R →+* S) = jacobi (f α) (f β) n := by
  simp only [jacobi, map_comp, map_shiftedJacobi, Polynomial.map_mul, map_C,
    Polynomial.map_sub, Polynomial.map_one, map_X, AlgHom.coe_toRingHom, f.commutes]

end Polynomial
