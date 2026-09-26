/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexAverage
public import Carlson.Jacobi.Endpoints

/-!
# Carlson's finite Jacobi expansion at complex endpoints

The monic polynomial `jacobiOn α β r s n` has coefficient equal to the continued
Dirichlet average of the `n`th derivative divided by `n!`. The theorem holds for
all complex endpoints, including the Taylor case `r=s`, and for all complex
parameters such that `α+β+2` is not a nonpositive integer.

## Main results

* `sum_carlsonJacobiCoefficient`: Carlson's finite polynomial expansion with
  coefficients expressed in the continued polynomial-average API.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Theorem 7.2-2.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Polynomial Dirichlet Complex

/-- Raising both Jacobi parameters preserves admissibility of their total beta parameter. -/
theorem jacobiTotalParameter_shift {α β : ℂ}
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m : ℕ) :
    IsCarlsonGammaRegular (α + m + 1 + (β + m + 1)) := by
  convert hc.add_nat (m + m) using 1; push_cast; ring

/-- The Jacobi coefficient is the continued Dirichlet average of a derivative,
divided by its factorial. -/
def carlsonJacobiCoefficient (α β r s : ℂ) (m : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ((m.factorial : ℂ)⁻¹) •
    (carlsonPolynomialAverage (pair (α + m + 1) (β + m + 1)) (pair r s)).comp (derivative ^ m)

/-- The coefficient functional as a quotient of a continued derivative average. -/
theorem carlsonJacobiCoefficient_apply (α β r s : ℂ) (m : ℕ) (p : ℂ[X]) :
    carlsonJacobiCoefficient α β r s m p =
      carlsonPolynomialAverage (pair (α + m + 1) (β + m + 1)) (pair r s)
        (derivative^[m] p) / (m.factorial : ℂ) := by
  simp only [carlsonJacobiCoefficient, LinearMap.smul_apply, LinearMap.comp_apply,
    Module.End.pow_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- At coincident endpoints the Jacobi coefficients are the ordinary Taylor coefficients. -/
theorem carlsonJacobiCoefficient_self (α β s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m : ℕ) (p : ℂ[X]) :
    carlsonJacobiCoefficient α β s s m p = (derivative^[m] p).eval s / (m.factorial : ℂ) := by
  rw [carlsonJacobiCoefficient_apply]
  have hz : pair s s = fun _ => s := by ext i; fin_cases i <;> rfl
  rw [hz, carlsonPolynomialAverage_const_nodes]
  simpa only [sum_pair] using jacobiTotalParameter_shift hc m

/-- The affine change of variable transports the algebraic derivative coefficient
to Carlson's monic derivative-average coefficient. -/
theorem algebraicJacobiCoefficient_comp_affine (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m : ℕ) (p : ℂ[X]) :
    algebraicJacobiCoefficient α β m (p.comp (C (r - s) * X + C s)) =
      carlsonJacobiCoefficient α β r s m p * (r - s) ^ m *
        ((m.factorial : ℂ) / ((-1 : ℂ) ^ m *
          (ascPochhammer ℂ m).eval (α + β + m + 1))) := by
  rw [algebraicJacobiCoefficient_apply, iterate_derivative_comp_affine,
    ← smul_eq_C_mul, map_smul, carlsonJacobiCoefficient_apply,
    carlsonPolynomialAverage_pair _ _ r s (jacobiTotalParameter_shift hc m)]
  simp only [smul_eq_mul]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

/-- Every complex polynomial has Carlson's finite Jacobi expansion. Admissibility
concerns only the total parameter; coincident endpoints recover Taylor's formula. -/
theorem sum_carlsonJacobiCoefficient (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (p : ℂ[X]) :
    ∑ m ∈ Finset.range (p.natDegree + 1),
      carlsonJacobiCoefficient α β r s m p • jacobiOn α β r s m = p := by
  have hadm : ∀ k : ℕ, α + β + 2 + k ≠ 0 := by
    intro k hk
    exact hc k (by linear_combination hk)
  have hpoch := jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hadm
  apply Polynomial.funext
  intro x
  simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  by_cases hrs : r = s
  · subst r
    simp_rw [jacobiOn_self α β s _ (hpoch _), carlsonJacobiCoefficient_self α β s hc,
      eval_pow, eval_sub, eval_X, eval_C]
    exact sum_eval_iterate_derivative_div_factorial p s x
  · let q := p.comp (C (r - s) * X + C s)
    have hq : q.natDegree = p.natDegree := by
      simp only [q, natDegree_comp, natDegree_add_C,
        natDegree_C_mul (sub_ne_zero.mpr hrs), natDegree_X, mul_one]
    have hx : (r - s) * ((x - s) / (r - s)) + s = x := by
      field_simp
      ring
    have he := congrArg (eval ((x - s) / (r - s)))
      (sum_algebraicJacobiCoefficient α β hadm q)
    rw [hq] at he
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, q, eval_comp,
      eval_add, eval_mul, eval_C, eval_X, hx] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro m _
    rw [algebraicJacobiCoefficient_comp_affine α β r s hc]
    have hj := eval_jacobiOn_affine α β r s ((x - s) / (r - s)) m (hpoch m)
    rw [hx] at hj
    rw [hj]
    ring

/-- Continued derivative-average coefficients are dual to the monic endpoint
Jacobi polynomials, with no distinct-endpoint assumption. -/
theorem carlsonJacobiCoefficient_apply_jacobiOn (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (n m : ℕ) :
    carlsonJacobiCoefficient α β r s n (jacobiOn α β r s m) = if m = n then 1 else 0 := by
  have hadm : ∀ k : ℕ, α + β + 2 + k ≠ 0 := by
    intro k hk
    exact hc k (by linear_combination hk)
  let hp := jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hadm
  let b := jacobiOnBasis α β r s hp
  have hb (k : ℕ) : b.repr (jacobiOn α β r s k) = Finsupp.single k 1 := by
    simpa only [b, jacobiOnBasis_apply] using b.repr_self k
  by_cases hnm : n ≤ m
  · have he := congrArg (fun q => b.repr q n)
      (sum_carlsonJacobiCoefficient α β r s hc (jacobiOn α β r s m))
    rw [natDegree_jacobiOn α β r s m (hp m)] at he
    simpa [map_sum, map_smul, hb, Finsupp.smul_apply, Finsupp.single_apply, Finset.mem_range,
      Nat.lt_succ_of_le hnm] using he
  · rw [carlsonJacobiCoefficient_apply, iterate_derivative_eq_zero
      (by rw [natDegree_jacobiOn α β r s m (hp m)]; omega), map_zero, zero_div]
    simp only [show m ≠ n by omega, ↓reduceIte]

end Carlson.TwoVariable
