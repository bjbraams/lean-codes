/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonDirichletAverage.Basic
import StdSimplexMeasure.DirichletTransform

/-! # Carlson's R-polynomials -/

open Complex ProbabilityTheory
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The entire regularized Carlson polynomial `Rₙ(b,z) / Γ(∑ i, b i)`. -/
def regCarlsonRPolynomial (n : ℕ) (b z : ι → ℂ) : ℂ :=
  regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b

/-- Compatibility spelling using the argument order of the original implementation. -/
abbrev regCarlsonR (n : ℕ) (z b : ι → ℂ) : ℂ :=
  regCarlsonRPolynomial n b z

/-- On the ordinary convergence region, the regularized Carlson polynomial agrees with the
native Dirichlet average of the corresponding power. -/
theorem regCarlsonDirichletAverage_pow (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b z (fun w ↦ w ^ n) = regCarlsonR n z b := by
  unfold regCarlsonDirichletAverage
  change regDirichletIntegral b (fun u ↦ carlsonAffineForm z u ^ n) =
    regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b
  rw [← regDirichletIntegral_mvPolynomial b hb (carlsonPowerPolynomial n z)]
  congr 1
  funext u
  exact (eval_carlsonPowerPolynomial n z u).symm

/-- For fixed degree and Carlson variables, the regularized Carlson polynomial is entire in
the Dirichlet parameters. -/
theorem differentiable_regCarlsonR (n : ℕ) (z : ι → ℂ) :
    Differentiable ℂ (regCarlsonR n z) :=
  differentiable_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

/-- Analytic form of entire dependence on the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonR (n : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonR n z) Set.univ :=
  analyticOnNhd_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

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
