/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
/-! # Coefficients of Carlson's R-polynomials

Home for Carlson's Section 6.2: multi-index coefficients, zero specializations, and termination.
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The coefficient form of the multinomial theorem for Carlson's homogeneous power
polynomial.  This is the algebraic core of Carlson's representation 6.2-1. -/
theorem coeff_carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) (m : ι →₀ ℕ) :
    (carlsonPowerPolynomial n z).coeff m =
      if m.sum (fun _ e ↦ e) = n then
        (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)
      else 0 := by
  rw [carlsonPowerPolynomial]
  have hlinear : carlsonAffinePolynomial z =
      ∑ i, z i • (MvPolynomial.X i : MvPolynomial ι ℂ) := by
    simp [carlsonAffinePolynomial, Algebra.smul_def]
  rw [hlinear, MvPolynomial.coeff_linearCombination_X_pow_of_fintype]

/-- Only multi-indices of total degree `n` can occur in Carlson's degree-`n` power
polynomial. -/
theorem coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne (n : ℕ) (z : ι → ℂ)
    (m : ι →₀ ℕ) (hm : m.sum (fun _ e ↦ e) ≠ n) :
    (carlsonPowerPolynomial n z).coeff m = 0 := by
  simp [coeff_carlsonPowerPolynomial, hm]

/-- Carlson's regularized polynomial written as the finite sum of its total-degree `n`
multi-index terms. -/
theorem regCarlsonRPolynomial_eq_sum_support (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
        ((m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)) *
          regDirichletMonomialTransform (m : ι → ℕ) b := by
  unfold regCarlsonRPolynomial regDirichletMvPolynomialTransform
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.sum (fun _ e ↦ e) = n := by
    by_contra hne
    have hz := coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne
    exact (MvPolynomial.mem_support_iff.mp hm) hz
  rw [coeff_carlsonPowerPolynomial]
  simp [hmdeg]

/-- Carlson's regularized polynomial written explicitly in Pochhammer--Gamma form. -/
theorem regCarlsonRPolynomial_eq_pochhammer_sum (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
        ((m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)) *
          ((∏ i, (ascPochhammer ℂ (m i)).eval (b i)) *
            (Gamma (∑ i, (b i + m i : ℂ)))⁻¹) := by
  rw [regCarlsonRPolynomial_eq_sum_support]
  apply Finset.sum_congr rfl
  intro m _
  rw [regDirichletMonomialTransform_eq]

/-- The Pochhammer numerator of Carlson's degree-`n` R-polynomial.

Carlson's usual polynomial is obtained by dividing this expression by
`(∑ i, b i)ₙ`.  Keeping the numerator separate makes transformation identities valid
without exclusions at zeros of that Pochhammer symbol. -/
def carlsonRPolynomialNumerator (n : ℕ) (b z : ι → ℂ) : ℂ :=
  ∑ m ∈ (carlsonPowerPolynomial n z).support,
    (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i)

/-- The regularized Carlson polynomial is its Pochhammer numerator times the reciprocal
Gamma factor at the translated total parameter. -/
theorem regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma
    (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      carlsonRPolynomialNumerator n b z * (Gamma ((∑ i, b i) + n))⁻¹ := by
  rw [regCarlsonRPolynomial_eq_pochhammer_sum]
  unfold carlsonRPolynomialNumerator
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.sum (fun _ e ↦ e) = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm)
      (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne)
  have hsum : ∑ i, (b i + m i : ℂ) = (∑ i, b i) + n := by
    rw [Finset.sum_add_distrib]
    congr 1
    have hmfun : ∑ i, m i = n := by
      rw [← m.sum_fintype (fun _ e ↦ e) (fun _ ↦ rfl)]
      exact hmdeg
    exact_mod_cast hmfun
  rw [hsum]
  ring

/-- Carlson's degree-zero power polynomial is the constant polynomial one. -/
@[simp] theorem carlsonPowerPolynomial_zero (z : ι → ℂ) :
    carlsonPowerPolynomial 0 z = 1 := by
  simp [carlsonPowerPolynomial]

/-- Carlson's degree-one power polynomial is its defining affine polynomial. -/
@[simp] theorem carlsonPowerPolynomial_one (z : ι → ℂ) :
    carlsonPowerPolynomial 1 z = carlsonAffinePolynomial z := by
  simp [carlsonPowerPolynomial]

/-- The regularized Carlson polynomial of degree zero is the reciprocal Gamma factor. -/
@[simp] theorem regCarlsonRPolynomial_zero (b z : ι → ℂ) :
    regCarlsonRPolynomial 0 b z = (Gamma (∑ i, b i))⁻¹ := by
  simp [regCarlsonRPolynomial, regDirichletMvPolynomialTransform]
  change regDirichletMonomialTransform (fun _ ↦ 0) b = (Gamma (∑ i, b i))⁻¹
  exact regDirichletMonomialTransform_zero b

/-- If all Carlson variables vanish, every positive-degree Carlson polynomial vanishes. -/
@[simp] theorem regCarlsonRPolynomial_zero_variables (b : ι → ℂ) {n : ℕ} (hn : n ≠ 0) :
    regCarlsonRPolynomial n b (fun _ ↦ 0) = 0 := by
  rw [regCarlsonRPolynomial]
  have hp : carlsonPowerPolynomial n (fun _ : ι ↦ (0 : ℂ)) = 0 := by
    simp [carlsonPowerPolynomial, carlsonAffinePolynomial, hn]
  rw [hp]
  simp [regDirichletMvPolynomialTransform]

end DirichletTransform
end CarlsonRPolynomial
