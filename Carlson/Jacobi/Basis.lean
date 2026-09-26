/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Derivative

/-!
# Degree and basis properties of Jacobi polynomials

The top coefficient detects exactly when a Jacobi polynomial retains its expected
degree. Over a field, a family without degree loss is a polynomial basis, using
Mathlib's `Polynomial.Sequence` construction. This provides the algebraic existence
and uniqueness of finite Jacobi expansions; it does not yet identify the expansion
coefficients with Carlson's Dirichlet averages.

## Main results

* `factorial_mul_coeff_jacobi_self`: the leading coefficient with its factorial cleared.
* `degree_jacobi`: exact degree under the nonvanishing Pochhammer condition.
* `jacobiBasis`: the Jacobi polynomial basis over a field.
* `sum_jacobiBasis_repr`: the finite expansion supplied by this basis.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §§7.1–7.2.
* `Mathlib.Algebra.Polynomial.Sequence`.
-/

@[expose] public noncomputable section
namespace Polynomial

/-- The coefficient of the highest possible power, with its factorial denominator cleared. -/
theorem factorial_mul_coeff_jacobi_self {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    (n.factorial : R) * (jacobi α β n).coeff n =
      algebraMap ℚ R (1 / 2) ^ n * (ascPochhammer R n).eval (α + β + n + 1) := by
  have h := congrArg (fun p : R[X] => p.coeff 0) (iterate_derivative_jacobi α β 0 n)
  simpa only [Nat.zero_add, jacobi_zero, mul_one, coeff_C, ↓reduceIte,
    coeff_iterate_derivative, Nat.descFactorial_self, nsmul_eq_mul] using h

variable {K : Type*} [Field K] [CharZero K]

/-- A Jacobi polynomial has its expected degree precisely when its top Pochhammer
factor is nonzero; this direction records the sufficient condition. -/
theorem degree_jacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobi α β n).degree = n := by
  apply degree_eq_of_le_of_coeff_ne_zero
    (degree_le_of_natDegree_le (natDegree_jacobi_le α β n))
  intro hc
  have he := factorial_mul_coeff_jacobi_self α β n
  rw [hc, mul_zero] at he
  have hhalf : algebraMap ℚ K (1 / 2) ≠ 0 := by norm_num
  exact (mul_ne_zero (pow_ne_zero n hhalf) h) he.symm

/-- The natural degree under the nonvanishing leading-coefficient condition. -/
theorem natDegree_jacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobi α β n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_jacobi α β n h)

/-- Jacobi polynomials form a polynomial sequence whenever none loses degree. -/
def jacobiSequence (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) : Sequence K where
  elems' := jacobi α β
  degree_eq' n := degree_jacobi α β n (h n)

/-- The polynomial basis given by the Jacobi sequence. The explicit hypothesis
excludes precisely the parameter values that cause degree loss in some member. -/
def jacobiBasis (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    Module.Basis ℕ K K[X] :=
  (jacobiSequence α β h).basis (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr ((jacobiSequence α β h).ne_zero n)))

/-- The vectors of the Jacobi basis are the standard Jacobi polynomials. -/
@[simp] theorem jacobiBasis_apply (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) (n : ℕ) :
    jacobiBasis α β h n = jacobi α β n := by
  exact Sequence.basis_eq_self _ _ n

/-- Every polynomial has a finite expansion in the Jacobi basis. -/
theorem sum_jacobiBasis_repr (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) (p : K[X]) :
    ((jacobiBasis α β h).repr p).sum (fun n c => c • jacobi α β n) = p := by
  simpa only [Finsupp.linearCombination_apply, jacobiBasis_apply] using
    (jacobiBasis α β h).linearCombination_repr p

/-- In the usual real orthogonality range no Jacobi polynomial loses degree. -/
theorem jacobi_pochhammer_ne_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (ascPochhammer ℝ n).eval (α + β + n + 1) ≠ 0 := by
  cases n with
  | zero => simp
  | succ n =>
    apply ne_of_gt (ascPochhammer_pos _ _ _)
    push_cast
    have := Nat.cast_nonneg (α := ℝ) n
    linarith

/-- The shifted Jacobi polynomial retains degree `n` under the same Pochhammer condition. -/
theorem degree_shiftedJacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (shiftedJacobi α β n).degree = n := by
  apply degree_eq_of_le_of_coeff_ne_zero
    (degree_le_of_natDegree_le (natDegree_shiftedJacobi_le α β n))
  rw [coeff_shiftedJacobi_self]
  apply mul_ne_zero _ h
  norm_num only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (by exact_mod_cast n.factorial_ne_zero)

/-- The shifted Jacobi polynomial sequence at parameters without degree loss. -/
def shiftedJacobiSequence (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) : Sequence K where
  elems' := shiftedJacobi α β
  degree_eq' n := degree_shiftedJacobi α β n (h n)

/-- The shifted Jacobi basis, constructed from Mathlib's polynomial sequence API. -/
def shiftedJacobiBasis (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    Module.Basis ℕ K K[X] :=
  (shiftedJacobiSequence α β h).basis (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr ((shiftedJacobiSequence α β h).ne_zero n)))

/-- The vectors of the shifted Jacobi basis are the shifted Jacobi polynomials. -/
@[simp] theorem shiftedJacobiBasis_apply (α β : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) (n : ℕ) :
    shiftedJacobiBasis α β h n = shiftedJacobi α β n :=
  Sequence.basis_eq_self _ _ n

end Polynomial
