/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Endpoints
public import Carlson.Jacobi.Carlson

/-!
# Identification of Carlson's endpoint Jacobi polynomials

The monic polynomial constructed by scaling and translating the shifted Jacobi
polynomial agrees with Carlson's two-node numerator divided by its total-parameter
Pochhammer factor. This identifies the arbitrary-endpoint finite expansion with
Carlson's normalization. Coincident endpoints are included explicitly.

## Main results

* `eval_jacobiOn_eq_numerator`: Carlson's rational normalization of the endpoint
  polynomial at every nonsingular parameter pair.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Definition 7.1-1, equation (7.1-11).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Polynomial Complex

/-- The shifted numerator identity with nodes in Carlson's endpoint orientation. -/
theorem factorial_mul_eval_shiftedJacobi_eq_numerator (α β x : ℂ) (n : ℕ) :
    (n.factorial : ℂ) * (shiftedJacobi α β n).eval x =
      carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (x - 1) x := by
  have hs := carlsonRPolynomialNumerator₂_smul n (-α - n) (-β - n) (-1) (1 - x) (-x)
  rw [show (-1 : ℂ) * (1 - x) = x - 1 by ring,
    show (-1 : ℂ) * -x = x by ring] at hs
  rw [hs]
  exact factorial_mul_eval_shiftedJacobi α β x n

/-- The endpoint polynomial equals Carlson's numerator quotient. This is a
rational dependence on the parameters; the hypothesis excludes its poles. -/
theorem eval_jacobiOn_eq_numerator (α β r s x : ℂ) (n : ℕ)
    (h : (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β r s n).eval x =
      carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (x - r) (x - s) /
        (ascPochhammer ℂ n).eval (-α - β - 2 * n) := by
  have hr : (ascPochhammer ℂ n).eval (-α - β - 2 * n) =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval (α + β + n + 1) := by
    rw [show -α - β - 2 * n = 1 - (α + β + n + 1) - n by ring]
    exact ascPochhammer_eval_reflect _ _
  have hd : (ascPochhammer ℂ n).eval (-α - β - 2 * n) ≠ 0 := by
    rw [hr]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
  by_cases hrs : r = s
  · subst r
    rw [jacobiOn_self α β s n h, eval_pow, eval_sub, eval_X, eval_C]
    have hz : pair (x - s) (x - s) = fun _ => x - s := by
      ext i; fin_cases i <;> rfl
    rw [← carlsonRPolynomialNumerator_pair, hz, carlsonRPolynomialNumerator_const, sum_pair]
    rw [show -α - n + (-β - n) = -α - β - 2 * n by ring]
    field_simp
  · let u := (x - s) / (r - s)
    have hx : (r - s) * u + s = x := by dsimp [u]; field_simp; ring
    have hj := eval_jacobiOn_affine α β r s u n h
    rw [hx] at hj
    rw [hj, hr]
    have hs := carlsonRPolynomialNumerator₂_smul n (-α - n) (-β - n) (r - s) (u - 1) u
    rw [show (r - s) * (u - 1) = x - r by linear_combination hx,
      show (r - s) * u = x - s by linear_combination hx,
      ← factorial_mul_eval_shiftedJacobi_eq_numerator] at hs
    rw [hs]
    ring

end Carlson.TwoVariable
