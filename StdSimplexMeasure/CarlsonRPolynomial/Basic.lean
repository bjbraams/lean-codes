/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonDirichletAverage.Continuation

/-! # Carlson's R-polynomials -/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The entire regularized Carlson polynomial of degree `n`, with argument order adapted to
the general Carlson `R` function. -/
def regCarlsonRPolynomial (n : ℕ) (b z : ι → ℂ) : ℂ :=
  regCarlsonR n z b

/-- Compatibility with the original argument order of `regCarlsonR`. -/
theorem regCarlsonRPolynomial_eq_regCarlsonR (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z = regCarlsonR n z b := rfl

/-- The multivariate polynomial kernel defining the Carlson polynomial is homogeneous in its
Carlson variables. -/
theorem carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z : ι → ℂ) :
    carlsonPowerPolynomial n (fun i ↦ a * z i) =
      MvPolynomial.C (a ^ n) * carlsonPowerPolynomial n z := by
  unfold carlsonPowerPolynomial carlsonAffinePolynomial
  rw [show (∑ i, MvPolynomial.C (a * z i) * MvPolynomial.X i) =
      MvPolynomial.C a * ∑ i, MvPolynomial.C (z i) * MvPolynomial.X i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_assoc]]
  rw [mul_pow, MvPolynomial.C_pow]

/-- Evaluation of a translated and scaled Carlson power kernel gives the corresponding
binomial power. -/
theorem eval_carlsonPowerPolynomial_affine (n : ℕ) (a t : ℂ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i + t)).eval (fun i ↦ (u i : ℂ)) =
      (a * carlsonAffineForm z u + t) ^ n := by
  rw [eval_carlsonPowerPolynomial, carlsonAffineForm_affine hu]

end DirichletTransform
end CarlsonRPolynomial
