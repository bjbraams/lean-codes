/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Basic
public import Carlson.TwoVariable.PolynomialDifferential

/-!
# Jacobi polynomials and the Carlson numerator

The Jacobi polynomial is identified with the two-node Carlson Pochhammer numerator.
The identities clear all parameter-dependent denominators and hence apply also
where Carlson's monic normalization is singular.

## Main results

* `factorial_mul_eval_shiftedJacobi`: identification in the shifted coordinate.
* `factorial_mul_eval_jacobi`: identification in the standard coordinate.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.1, equation (7.1-11), and §7.8.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Polynomial Finset

/-- The shifted Jacobi polynomial is a specialization of the Carlson numerator.
This identity remains valid at all complex parameters. -/
theorem factorial_mul_eval_shiftedJacobi (α β x : ℂ) (n : ℕ) :
    (n.factorial : ℂ) * (shiftedJacobi α β n).eval x =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (1 - x) (-x) := by
  have ht : carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (1 - x) (-x) =
      carlsonRPolynomialNumerator₂ n (α + β + n + 1) (-α - n) x 1 := by
    rw [carlsonRPolynomialNumerator₂_swap,
      carlsonRPolynomialNumerator₂_transform]
    rw [show 1 - (-β - n) - (-α - n) - n = α + β + n + 1 by ring,
      show -x - (1 - x) = -1 by ring]
    have hs := carlsonRPolynomialNumerator₂_smul n (α + β + n + 1) (-α - n) (-1) x 1
    simp only [neg_mul, one_mul, mul_one] at hs
    rw [hs]
    simp [← mul_assoc, ← mul_pow]
  rw [ht]
  simp only [shiftedJacobi, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum]
  rw [carlsonRPolynomialNumerator₂, mul_sum]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply sum_congr rfl
  intro ij hij
  obtain hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  dsimp only [Prod.swap]
  rw [← mul_assoc, ← hn, factorial_mul_jacobiCoeff]
  have hr : (ascPochhammer ℂ ij.1).eval (-α - (ij.1 + ij.2 : ℕ)) =
      (-1 : ℂ) ^ ij.1 * (ascPochhammer ℂ ij.1).eval (α + ij.2 + 1) := by
    rw [show -α - (ij.1 + ij.2 : ℕ) = 1 - (α + ij.2 + 1) - ij.1 by push_cast; ring]
    exact ascPochhammer_eval_reflect (α + ij.2 + 1) ij.1
  rw [hr, one_pow, mul_one]
  have hsign : (-1 : ℂ) ^ (ij.1 + ij.2) * (-1 : ℂ) ^ ij.1 = (-1 : ℂ) ^ ij.2 := by
    rw [pow_add]
    calc
      _ = ((-1 : ℂ) * (-1)) ^ ij.1 * (-1 : ℂ) ^ ij.2 := by rw [mul_pow]; ring
      _ = _ := by simp
  linear_combination
    -((ij.1 + ij.2).choose ij.2 : ℂ) *
      (ascPochhammer ℂ ij.1).eval (α + ij.2 + 1) *
      (ascPochhammer ℂ ij.2).eval (α + β + (ij.1 + ij.2 : ℕ) + 1) * x ^ ij.2 * hsign

/-- The classical Jacobi normalization of Carlson's two-node polynomial numerator. -/
theorem factorial_mul_eval_jacobi (α β x : ℂ) (n : ℕ) :
    (2 ^ n * n.factorial : ℂ) * (jacobi α β n).eval x =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) (x + 1) (x - 1) := by
  have h := factorial_mul_eval_shiftedJacobi α β ((1 - x) / 2) n
  have hnodes := carlsonRPolynomialNumerator₂_smul n (-α - n) (-β - n) 2
    (1 - (1 - x) / 2) (-((1 - x) / 2))
  rw [show (2 : ℂ) * (1 - (1 - x) / 2) = x + 1 by ring,
    show (2 : ℂ) * -((1 - x) / 2) = x - 1 by ring] at hnodes
  rw [hnodes, eval_jacobi]
  norm_num only [map_div₀, map_one, map_ofNat] at ⊢
  rw [show (1 / 2 : ℂ) * (1 - x) = (1 - x) / 2 by ring]
  linear_combination (2 : ℂ) ^ n * h

end Carlson.TwoVariable
