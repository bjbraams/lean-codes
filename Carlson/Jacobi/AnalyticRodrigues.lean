/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Raising
public import Carlson.Jacobi.Weight
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Rodrigues' formula for arbitrary real Jacobi parameters

On the open unit interval the Jacobi weight is smooth for every pair of real
exponents. The Pearson raising identity gives the derivative of a weighted Jacobi
polynomial; iteration gives Rodrigues' formula without integrality or positivity
assumptions on the parameters. Endpoint integrability is a separate question.

## Main results

* `hasDerivAt_weight_mul_shiftedJacobi`: differentiation raises the Jacobi index
  and lowers both weight parameters.
* `iteratedDeriv_shiftedJacobiWeight`: analytic Rodrigues formula on `(0,1)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8.
-/

public noncomputable section
namespace Polynomial
open Set

/-- Differentiating a weighted shifted Jacobi polynomial raises its index by one. -/
theorem hasDerivAt_weight_mul_shiftedJacobi (α β : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => shiftedJacobiWeight (α + 1) (β + 1) t *
      (shiftedJacobi (α + 1) (β + 1) n).eval t)
      ((n + 1 : ℝ) * (shiftedJacobiWeight α β x *
        (shiftedJacobi α β (n + 1)).eval x)) x := by
  have he := congrArg (eval x) (shiftedJacobi_raising α β n)
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one] at he
  convert (hasDerivAt_shiftedJacobiWeight_succ α β hx).mul
    ((shiftedJacobi (α + 1) (β + 1) n).hasDerivAt x) using 1
  rw [shiftedJacobiWeight_succ α β hx]
  linear_combination -shiftedJacobiWeight α β x * he

/-- Rodrigues' formula for arbitrary real exponents, at interior points of the
unit interval. The normalization is `Qₙ(x) = Pₙ(1-2x)`. -/
theorem iteratedDeriv_shiftedJacobiWeight (α β : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv n (shiftedJacobiWeight (α + n) (β + n)) x =
      n.factorial * (shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x) := by
  induction n generalizing α β x with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (shiftedJacobiWeight (α + (n + 1)) (β + (n + 1)))
        =ᶠ[nhds x] (fun t => n.factorial * (shiftedJacobiWeight (α + 1) (β + 1) t *
          (shiftedJacobi (α + 1) (β + 1) n).eval t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      simpa only [add_assoc, add_comm (1 : ℝ) (n : ℝ)] using ih (α + 1) (β + 1) ht
    rw [iteratedDeriv_succ, Nat.cast_add, Nat.cast_one, he.deriv_eq]
    rw [((hasDerivAt_weight_mul_shiftedJacobi α β n hx).const_mul
      (n.factorial : ℝ)).deriv]
    rw [Nat.factorial_succ]
    push_cast
    ring

end Polynomial
