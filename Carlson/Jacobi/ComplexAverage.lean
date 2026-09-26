/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AlgebraicExpansion
public import Carlson.PolynomialAverage
public import Carlson.TwoVariable.RPolynomial

/-!
# Complex Carlson averages and Jacobi coefficients

The algebraic beta functional is the ordinary normalization of the entire
regularized Carlson polynomial average at nodes `1, 0`. This identifies the
finite Jacobi coefficients with continued Dirichlet averages of derivatives,
including complex parameters outside the native integral convergence region.

## Main results

* `carlsonPolynomialAverage_pair_one_zero`: identification of the continued
  Carlson transform with the algebraic beta average.
* `carlsonPolynomialAverage_pair`: the same identification at arbitrary endpoints
  by affine substitution, including coincident endpoints.
* `sum_carlsonPolynomialAverage_shiftedJacobi`: the finite complex Jacobi expansion.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Theorem 7.2-2.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Polynomial Dirichlet Complex

/-- The two-node polynomial numerator with second node zero has one surviving term. -/
theorem carlsonRPolynomialNumerator₂_zero_right (n : ℕ) (a b x : ℂ) :
    carlsonRPolynomialNumerator₂ n a b x 0 = (ascPochhammer ℂ n).eval a * x ^ n := by
  unfold carlsonRPolynomialNumerator₂
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro ij hij hne
    have hj : ij.2 ≠ 0 := by
      intro h
      apply hne
      have hs := Finset.mem_antidiagonal.mp hij
      ext <;> simp_all
    simp [zero_pow hj]
  · simp

/-- The beta moments are the ordinary normalization of the continued Carlson moments. -/
theorem carlsonPolynomialAverage_pair_one_zero (a b : ℂ)
    (hc : IsCarlsonGammaRegular (a + b)) :
    carlsonPolynomialAverage (pair a b) (pair 1 0) = betaAverage a b := by
  apply LinearMap.ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [carlsonPolynomialAverage, LinearMap.smul_apply, smul_eq_mul,
      regCarlsonPolynomialAverage_monomial, betaAverage_monomial, sum_pair]
    change Gamma (a + b) * (c * regRPolynomial n a b 1 0) = _
    rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
      carlsonRPolynomialNumerator₂_zero_right, one_pow, mul_one]
    have he : Gamma (a + b) * (Gamma (a + b + n))⁻¹ =
        1 / (ascPochhammer ℂ n).eval (a + b) := by
      apply (eq_div_iff (hc.ascPochhammer_ne_zero n)).mpr
      calc
        _ = Gamma (a + b) * ((ascPochhammer ℂ n).eval (a + b) *
            (Gamma (a + b + n))⁻¹) := by ring
        _ = Gamma (a + b) * (Gamma (a + b))⁻¹ := by
          rw [← one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat]
        _ = 1 := mul_inv_cancel₀ (Gamma_ne_zero hc)
    calc
      _ = c * (ascPochhammer ℂ n).eval a *
          (Gamma (a + b) * (Gamma (a + b + n))⁻¹) := by ring
      _ = _ := by rw [he]; ring

/-- The two-node continued polynomial average is an affine beta average, even when
the nodes coincide. -/
theorem carlsonPolynomialAverage_pair (a b r s : ℂ)
    (hc : IsCarlsonGammaRegular (a + b)) (p : ℂ[X]) :
    carlsonPolynomialAverage (pair a b) (pair r s) p =
      betaAverage a b (p.comp (C (r - s) * X + C s)) := by
  rw [← carlsonPolynomialAverage_pair_one_zero a b hc]
  simp only [carlsonPolynomialAverage, LinearMap.smul_apply, smul_eq_mul]
  rw [regCarlsonPolynomialAverage_comp_affine]
  have hz : (fun i => (r - s) * pair 1 0 i + s) = pair r s := by
    funext i
    fin_cases i <;> simp [pair]
  rw [hz]

/-- The complex finite expansion has coefficients given by continued Carlson
averages of derivatives, with the standard shifted-Jacobi normalization. -/
theorem sum_carlsonPolynomialAverage_shiftedJacobi (α β : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (p : ℂ[X]) :
    ∑ m ∈ Finset.range (p.natDegree + 1),
      (carlsonPolynomialAverage (pair (α + m + 1) (β + m + 1)) (pair 1 0)
          (derivative^[m] p) /
        ((-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (α + β + m + 1))) •
        shiftedJacobi α β m = p := by
  have hadm : ∀ k : ℕ, α + β + 2 + k ≠ 0 := by
    intro k hk
    exact hc k (by linear_combination hk)
  have hm (m : ℕ) : IsCarlsonGammaRegular (α + m + 1 + (β + m + 1)) := by
    convert hc.add_nat (m + m) using 1; push_cast; ring
  simp_rw [carlsonPolynomialAverage_pair_one_zero _ _ (hm _),
    ← algebraicJacobiCoefficient_apply]
  exact sum_algebraicJacobiCoefficient α β hadm p

end Carlson.TwoVariable
