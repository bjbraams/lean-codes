/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Carlson.TwoVariable.ParameterSymmetry

/-!
# The terminating cases of Gauss's theorem

The terminating part of Carlson's Theorem 8.3-4 is the Chu--Vandermonde identity.
It requires only that the denominator Pochhammer symbol through the terminating degree
be nonzero, and no real-part inequality. The Pochhammer quotient remains meaningful
when the Gamma quotient in the nonterminating formula has removable singularities.

The proof specializes the existing polynomial identity at the nodes `(0,1)`.
-/

open Complex Polynomial

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **Carlson's Theorem 8.3-4, terminating case**, with the denominator cleared.
Only the first `n` denominator factors need be nonzero. -/
theorem ascPochhammer_mul_ordinaryHypergeometric_one (n : ℕ) (β γ : ℂ)
    (hγ : (ascPochhammer ℂ n).eval γ ≠ 0) :
    (ascPochhammer ℂ n).eval γ * ordinaryHypergeometric (-(n : ℂ)) β γ 1 =
      (ascPochhammer ℂ n).eval (γ - β) := by
  have h := carlsonRPolynomialNumerator₂_eq_hypergeometric n β (γ - β) 0
    (y := 1) one_ne_zero (by simpa only [add_sub_cancel] using hγ)
  simpa only [add_sub_cancel, zero_div, sub_zero, one_pow, mul_one,
    carlsonRPolynomialNumerator₂_zero_left] using h.symm

/-- **Chu--Vandermonde summation**, the terminating Gauss theorem at unit argument.
There is no restriction on `re (γ + n - β)`. -/
theorem ordinaryHypergeometric_neg_natCast_one (n : ℕ) (β γ : ℂ)
    (hγ : (ascPochhammer ℂ n).eval γ ≠ 0) :
    ordinaryHypergeometric (-(n : ℂ)) β γ 1 =
      (ascPochhammer ℂ n).eval (γ - β) / (ascPochhammer ℂ n).eval γ := by
  apply (eq_div_iff hγ).mpr
  simpa only [mul_comm] using ascPochhammer_mul_ordinaryHypergeometric_one n β γ hγ

/-- The terminating Gauss theorem when the second numerator parameter is a nonpositive
integer, by symmetry of the two numerator parameters. -/
theorem ordinaryHypergeometric_neg_natCast_one_right (n : ℕ) (α γ : ℂ)
    (hγ : (ascPochhammer ℂ n).eval γ ≠ 0) :
    ordinaryHypergeometric α (-(n : ℂ)) γ 1 =
      (ascPochhammer ℂ n).eval (γ - α) / (ascPochhammer ℂ n).eval γ := by
  have hsym : ordinaryHypergeometric α (-(n : ℂ)) γ (1 : ℂ) =
      ordinaryHypergeometric (-(n : ℂ)) α γ 1 := by
    unfold ordinaryHypergeometric
    rw [ordinaryHypergeometricSeries_symm]
  rw [hsym, ordinaryHypergeometric_neg_natCast_one n α γ hγ]

end Carlson.TwoVariable
