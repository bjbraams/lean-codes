/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AlgebraicExpansion
public import Carlson.Jacobi.RealOrthogonality

/-!
# Finite Jacobi expansions from derivative averages

For real `α, β > -1`, the coefficient of the shifted Jacobi polynomial of index `m`
is obtained by integrating the `m`th derivative against the weight with parameters
`α+m, β+m`. Dividing by the mass of that weight gives its normalized beta average;
the remaining factor converts the standard Jacobi normalization to Carlson's monic
normalization. Agreement with the algebraic coefficient functional makes the
finite expansion a specialization of the characteristic-zero-field theorem.

## Main results

* `shiftedJacobiIntegral`: the weighted polynomial integral as a linear functional.
* `shiftedJacobiCoefficient`: the normalized derivative-average coefficient functional.
* `shiftedJacobiCoefficient_apply_shiftedJacobi`: these functionals are dual to the
  shifted Jacobi polynomials.
* `shiftedJacobiCoefficient_eq_algebraic`: agreement of the integral and algebraic coefficients.
* `betaAverage_eq_integral`: the algebraic beta functional is a normalized weighted integral.
* `sum_shiftedJacobiCoefficient`: the finite expansion of any real polynomial.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §§7.2 and 7.8.
-/

@[expose] public noncomputable section
namespace Polynomial
open MeasureTheory Finset

/-- Integration of polynomials against an integrable shifted Jacobi weight. -/
def shiftedJacobiIntegral (α β : ℝ) (hα : -1 < α) (hβ : -1 < β) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x
  map_add' p q := by
    simp only [eval_add, mul_add]
    exact intervalIntegral.integral_add
      ((intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn p.continuous.continuousOn)
      ((intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn q.continuous.continuousOn)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (shiftedJacobiWeight α β _) c]
    exact intervalIntegral.integral_const_mul _ _

/-- Evaluation of the Jacobi integral functional. -/
theorem shiftedJacobiIntegral_apply (α β : ℝ) (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    shiftedJacobiIntegral α β hα hβ p =
      ∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x := rfl

/-- The coefficient functional obtained by a normalized average of the `m`th derivative.
Its denominator is nonzero in the stated real parameter range. -/
def shiftedJacobiCoefficient (α β : ℝ) (hα : -1 < α) (hβ : -1 < β) (m : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (1 / ((-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (α + β + m + 1) *
    ∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + m) (β + m) x)) •
      (shiftedJacobiIntegral (α + m) (β + m) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
        (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).comp (derivative ^ m)

/-- The coefficient functional written as an explicit quotient of integrals. -/
theorem shiftedJacobiCoefficient_apply (α β : ℝ) (hα : -1 < α) (hβ : -1 < β)
    (m : ℕ) (p : ℝ[X]) :
    shiftedJacobiCoefficient α β hα hβ m p =
      (∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + m) (β + m) x *
        (derivative^[m] p).eval x) /
      ((-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (α + β + m + 1) *
        ∫ x in (0 : ℝ)..1, shiftedJacobiWeight (α + m) (β + m) x) := by
  simp only [shiftedJacobiCoefficient, LinearMap.smul_apply, LinearMap.comp_apply,
    Module.End.pow_apply, shiftedJacobiIntegral_apply, smul_eq_mul, div_eq_mul_inv, one_mul,
    mul_comm]

/-- The normalized derivative-average functionals are dual to the Jacobi polynomials. -/
theorem shiftedJacobiCoefficient_apply_shiftedJacobi (α β : ℝ) (hα : -1 < α) (hβ : -1 < β)
    (m n : ℕ) :
    shiftedJacobiCoefficient α β hα hβ m (shiftedJacobi α β n) = if n = m then 1 else 0 := by
  rw [shiftedJacobiCoefficient_apply]
  have ham : -1 < α + m := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hbm : -1 < β + m := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  by_cases hmn : m ≤ n
  · have hn : n = (n - m) + m := by omega
    rw [hn, iterate_derivative_shiftedJacobi]
    simp only [eval_mul, eval_C]
    simp_rw [mul_left_comm (shiftedJacobiWeight (α + m) (β + m) _)]
    rw [intervalIntegral.integral_const_mul]
    by_cases he : n = m
    · subst n
      simp only [Nat.sub_self, Nat.zero_add, shiftedJacobi_zero, eval_one, mul_one,
        ↓reduceIte]
      exact div_self (mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (jacobi_pochhammer_ne_zero hα hβ m))
        (integral_shiftedJacobiWeight_pos ham hbm).ne')
    · have hz := integral_shiftedJacobi_mul_shiftedJacobi_eq_zero ham hbm 0 (n - m)
        (by omega)
      simp only [shiftedJacobi_zero, eval_one, mul_one] at hz
      rw [hz, mul_zero, zero_div, ite_eq_right (by omega)]
  · rw [iterate_derivative_eq_zero ((natDegree_shiftedJacobi_le α β n).trans_lt
      (Nat.lt_of_not_ge hmn))]
    simp [show n ≠ m by omega]

/-- The derivative-average coefficient is the coordinate in the shifted Jacobi basis. -/
theorem shiftedJacobiCoefficient_eq_repr (α β : ℝ) (hα : -1 < α) (hβ : -1 < β)
    (m : ℕ) (p : ℝ[X]) :
    shiftedJacobiCoefficient α β hα hβ m p =
      (shiftedJacobiBasis α β (jacobi_pochhammer_ne_zero hα hβ)).repr p m := by
  let b := shiftedJacobiBasis α β (jacobi_pochhammer_ne_zero hα hβ)
  have he : shiftedJacobiCoefficient α β hα hβ m =
      (Finsupp.lapply m).comp b.repr.toLinearMap := by
    apply b.ext
    intro n
    change shiftedJacobiCoefficient α β hα hβ m (b n) = b.repr (b n) m
    rw [Module.Basis.repr_self]
    simp only [b, shiftedJacobiBasis_apply, shiftedJacobiCoefficient_apply_shiftedJacobi,
      Finsupp.single_apply]
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ => L p) he

/-- The integral coefficient is the real specialization of the algebraic
coefficient, so the real and complex finite expansion APIs use the same normalization. -/
theorem shiftedJacobiCoefficient_eq_algebraic {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (m : ℕ) (p : ℝ[X]) :
    shiftedJacobiCoefficient α β hα hβ m p = algebraicJacobiCoefficient α β m p := by
  have hc : ∀ k : ℕ, α + β + 2 + k ≠ 0 := by
    intro k
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [shiftedJacobiCoefficient_eq_repr, algebraicJacobiCoefficient_eq_repr α β hc]

/-- The algebraic beta average is the normalized weighted integral for admissible
real exponents. -/
theorem betaAverage_eq_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    betaAverage (α + 1) (β + 1) p =
      (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x) /
        (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x) := by
  have h := shiftedJacobiCoefficient_eq_algebraic hα hβ 0 p
  simpa only [shiftedJacobiCoefficient_apply, algebraicJacobiCoefficient_apply,
    Nat.cast_zero, add_zero, pow_zero, ascPochhammer_zero, eval_one, mul_one,
    one_mul, Function.iterate_zero_apply, div_one] using h.symm

/-- Every real polynomial has a finite Jacobi expansion whose coefficients are normalized
averages of its derivatives. This is the real specialization of the algebraic theorem. -/
theorem sum_shiftedJacobiCoefficient (α β : ℝ) (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    ∑ m ∈ range (p.natDegree + 1),
      shiftedJacobiCoefficient α β hα hβ m p • shiftedJacobi α β m = p := by
  simp_rw [shiftedJacobiCoefficient_eq_algebraic hα hβ]
  apply sum_algebraicJacobiCoefficient
  intro k
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

/-- Orthogonality to every polynomial of lower degree in the full real parameter range. -/
theorem integral_mul_shiftedJacobi_eq_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) (p : ℝ[X]) (hp : p.degree < n) :
    (∫ x in (0 : ℝ)..1, shiftedJacobiWeight α β x * p.eval x *
      (shiftedJacobi α β n).eval x) = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hdeg : p.natDegree < n := (natDegree_lt_iff_degree_lt hp0).mpr hp
  let L : ℝ[X] →ₗ[ℝ] ℝ := (shiftedJacobiIntegral α β hα hβ).comp
    (LinearMap.mulRight ℝ (shiftedJacobi α β n))
  have hL (q : ℝ[X]) : L q = ∫ x in (0 : ℝ)..1,
      shiftedJacobiWeight α β x * q.eval x * (shiftedJacobi α β n).eval x := by
    simp only [L, LinearMap.comp_apply, LinearMap.mulRight_apply,
      shiftedJacobiIntegral_apply, eval_mul, mul_assoc]
  rw [← hL, ← sum_shiftedJacobiCoefficient α β hα hβ p, map_sum]
  apply sum_eq_zero
  intro m hm
  rw [map_smul, hL, integral_shiftedJacobi_mul_shiftedJacobi_eq_zero hα hβ m n
    (by simp only [mem_range] at hm; omega), smul_zero]

end Polynomial
