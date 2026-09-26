/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basis
public import Carlson.Jacobi.Carlson

/-!
# Standard and monic Jacobi normalization

Carlson's Chapter 7 uses monic polynomials. The standard Jacobi polynomial is
converted to this normalization by its explicit leading coefficient. Monicity
requires a nonzero Pochhammer factor; the standard polynomial itself remains
well-defined at every parameter.

## Main results

* `Polynomial.coeff_jacobi_self`: the explicit top coefficient.
* `Polynomial.monic_monicJacobi`: monicity on the nonsingular parameter set.
* `Carlson.TwoVariable.eval_monicJacobi_eq_numerator`: identification with Carlson's
  ordinary polynomial quotient, without using a Gamma quotient at its poles.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.1, equation (7.1-11).
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The leading coefficient in the standard Jacobi normalization. It may vanish. -/
theorem coeff_jacobi_self (α β : K) (n : ℕ) :
    (jacobi α β n).coeff n =
      (ascPochhammer K n).eval (α + β + n + 1) / (2 ^ n * n.factorial) := by
  have h := factorial_mul_coeff_jacobi_self α β n
  norm_num only [map_div₀, map_one, map_ofNat, div_pow, one_pow] at h
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have htwo : (2 : K) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (eq_div_iff (mul_ne_zero htwo hn)).mpr
  field_simp at h
  linear_combination h

/-- Carlson's monic Jacobi polynomial on `[-1,1]`. At a zero of the normalizing
Pochhammer symbol this totalized expression is zero and is not monic. -/
def monicJacobi (α β : K) (n : ℕ) : K[X] :=
  C ((2 ^ n * n.factorial : K) / (ascPochhammer K n).eval (α + β + n + 1)) *
    jacobi α β n

/-- The normalized Jacobi polynomial is monic when its normalizing factor is nonzero. -/
theorem monic_monicJacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (monicJacobi α β n).Monic := by
  rw [Monic, monicJacobi, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff, natDegree_jacobi α β n h, coeff_jacobi_self]
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

end Polynomial
namespace Carlson.TwoVariable
open Polynomial

/-- Carlson's monic Jacobi polynomial is the numerator divided by the total-parameter
Pochhammer symbol. The parameter dependence is rational. At a zero of the
denominator both sides use field division by zero, not an analytic limiting value. -/
theorem eval_monicJacobi_eq_numerator (α β x : ℂ) (n : ℕ) :
    (monicJacobi α β n).eval x =
      carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (x + 1) (x - 1) /
        (ascPochhammer ℂ n).eval (-α - β - 2 * n) := by
  have hr : (ascPochhammer ℂ n).eval (-α - β - 2 * n) =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval (α + β + n + 1) := by
    rw [show -α - β - 2 * n = 1 - (α + β + n + 1) - n by ring]
    exact ascPochhammer_eval_reflect _ _
  rw [monicJacobi, eval_mul, eval_C, div_mul_eq_mul_div,
    factorial_mul_eval_jacobi, hr]
  by_cases h : (ascPochhammer ℂ n).eval (α + β + n + 1) = 0
  · simp [h]
  · have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
    field_simp
    linear_combination
      carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (x + 1) (x - 1) * hs

end Carlson.TwoVariable
