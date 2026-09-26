/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.BetaAverage

/-!
# Finite Jacobi expansions at algebraic parameters

Normalized beta averages of derivatives give the coefficients in the shifted
Jacobi basis. The result holds over every characteristic-zero field, provided
`α + β + 2` avoids the nonpositive integers. In particular it applies to complex
parameters outside the exceptional total-parameter hyperplanes. No positivity
or integration hypothesis is used.

## Main results

* `algebraicJacobiCoefficient_apply_shiftedJacobi`: duality of the derivative
  averages and the shifted Jacobi polynomials.
* `sum_algebraicJacobiCoefficient`: the explicit finite expansion.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Theorem 7.2-2.
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Admissibility of the total parameter implies the nonvanishing conditions for
the Jacobi polynomial basis. -/
theorem jacobi_pochhammer_ne_zero_of_add_nat_ne_zero (α β : K)
    (hc : ∀ k : ℕ, α + β + 2 + k ≠ 0) (n : ℕ) :
    (ascPochhammer K n).eval (α + β + n + 1) ≠ 0 := by
  cases n with
  | zero => simp
  | succ n =>
    apply ascPochhammer_ne_zero_of_add_nat_ne_zero
    intro k
    convert hc (n + k) using 1; push_cast; ring

/-- The coefficient of a shifted Jacobi polynomial, obtained by taking the beta
average of the corresponding derivative and dividing by its leading derivative. -/
def algebraicJacobiCoefficient (α β : K) (m : ℕ) : K[X] →ₗ[K] K :=
  (((-1 : K) ^ m * (ascPochhammer K m).eval (α + β + m + 1))⁻¹) •
    (betaAverage (α + m + 1) (β + m + 1)).comp (derivative ^ m)

omit [CharZero K] in
/-- Explicit derivative-average formula for a coefficient. -/
theorem algebraicJacobiCoefficient_apply (α β : K) (m : ℕ) (p : K[X]) :
    algebraicJacobiCoefficient α β m p =
      betaAverage (α + m + 1) (β + m + 1) (derivative^[m] p) /
        ((-1 : K) ^ m * (ascPochhammer K m).eval (α + β + m + 1)) := by
  simp only [algebraicJacobiCoefficient, LinearMap.smul_apply, LinearMap.comp_apply,
    Module.End.pow_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The algebraic derivative-average functionals are dual to the shifted Jacobi basis. -/
theorem algebraicJacobiCoefficient_apply_shiftedJacobi (α β : K)
    (hc : ∀ k : ℕ, α + β + 2 + k ≠ 0) (m n : ℕ) :
    algebraicJacobiCoefficient α β m (shiftedJacobi α β n) = if n = m then 1 else 0 := by
  rw [algebraicJacobiCoefficient_apply]
  by_cases hmn : m ≤ n
  · have hn : n = (n - m) + m := by omega
    rw [hn, iterate_derivative_shiftedJacobi, ← smul_eq_C_mul, map_smul]
    rw [betaAverage_shiftedJacobi (α + m) (β + m)
      (by intro k; convert hc (m + m + k) using 1; push_cast; ring)]
    by_cases he : n = m
    · subst n
      simp only [Nat.sub_self, Nat.zero_add, ↓reduceIte, smul_eq_mul, mul_one]
      exact div_self (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hc m))
    · simp only [show n - m ≠ 0 by omega, show n - m + m ≠ m by omega,
        ↓reduceIte, smul_zero, zero_div]
  · rw [iterate_derivative_eq_zero ((natDegree_shiftedJacobi_le α β n).trans_lt
      (Nat.lt_of_not_ge hmn)), map_zero, zero_div]
    simp only [show n ≠ m by omega, ↓reduceIte]

/-- Derivative averages recover the coordinates in the algebraic Jacobi basis. -/
theorem algebraicJacobiCoefficient_eq_repr (α β : K)
    (hc : ∀ k : ℕ, α + β + 2 + k ≠ 0) (m : ℕ) (p : K[X]) :
    algebraicJacobiCoefficient α β m p =
      (shiftedJacobiBasis α β (jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hc)).repr p m := by
  let b := shiftedJacobiBasis α β (jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hc)
  have he : algebraicJacobiCoefficient α β m = (Finsupp.lapply m).comp b.repr.toLinearMap := by
    apply b.ext
    intro n
    change algebraicJacobiCoefficient α β m (b n) = b.repr (b n) m
    rw [Module.Basis.repr_self]
    simp only [b, shiftedJacobiBasis_apply,
      algebraicJacobiCoefficient_apply_shiftedJacobi α β hc, Finsupp.single_apply]
  exact congrArg (fun L : K[X] →ₗ[K] K => L p) he

/-- Every polynomial has a finite shifted Jacobi expansion with algebraic
derivative-average coefficients, including at nonreal admissible parameters. -/
theorem sum_algebraicJacobiCoefficient (α β : K)
    (hc : ∀ k : ℕ, α + β + 2 + k ≠ 0) (p : K[X]) :
    ∑ m ∈ Finset.range (p.natDegree + 1),
      algebraicJacobiCoefficient α β m p • shiftedJacobi α β m = p := by
  let b := shiftedJacobiBasis α β (jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β hc)
  have hs : (b.repr p).support ⊆ Finset.range (p.natDegree + 1) := by
    intro m hm
    rw [Finset.mem_range]
    by_contra h
    have hz : algebraicJacobiCoefficient α β m p = 0 := by
      rw [algebraicJacobiCoefficient_apply, iterate_derivative_eq_zero (by omega),
        map_zero, zero_div]
    rw [algebraicJacobiCoefficient_eq_repr α β hc] at hz
    exact Finsupp.mem_support_iff.mp hm hz
  simp_rw [algebraicJacobiCoefficient_eq_repr α β hc]
  rw [← Finset.sum_subset hs (fun m _ hm => by
    rw [Finsupp.notMem_support_iff.mp hm, zero_smul])]
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, b, shiftedJacobiBasis_apply] using
    b.linearCombination_repr p

end Polynomial
