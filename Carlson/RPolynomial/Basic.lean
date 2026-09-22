/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Polynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Carlson's R-polynomials

The polynomial Dirichlet averages `Rₙ(b, z)` of Carlson's Section 5.7, defined for every complex
Dirichlet parameter vector through the entire regularized polynomial transform of
`Dirichlet.Polynomial`. On the native convergence region they are the Dirichlet averages of the
powers `w ↦ w ^ n`.

## Main definitions

* `Carlson.regCarlsonRPolynomial`: the entire regularized polynomial `Rₙ(b, z) / Γ(∑ i, b i)`.

## Main results

* `Carlson.regCarlsonDirichletAverage_pow`: agreement with the native power average.
* `Carlson.analyticOnNhd_regCarlsonRPolynomial`: entire dependence on the parameters.
* `Carlson.regCarlsonRPolynomial_smul_of_mem_mvBetaConvergent`,
  `Carlson.regCarlsonRPolynomial_const`: homogeneity and the diagonal value, Carlson's 5.7(3).

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory
@[expose] public noncomputable section CarlsonRPolynomial
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The entire regularized Carlson polynomial `Rₙ(b,z) / Γ(∑ i, b i)`. -/
def regCarlsonRPolynomial (n : ℕ) (b z : ι → ℂ) : ℂ :=
  regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b

/-- On the ordinary convergence region, the regularized Carlson polynomial agrees with the
native Dirichlet average of the corresponding power. -/
theorem regCarlsonDirichletAverage_pow (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b z (fun w ↦ w ^ n) = regCarlsonRPolynomial n b z := by
  unfold regCarlsonDirichletAverage
  change regDirichletIntegral b (fun u ↦ carlsonAffineForm z u ^ n) =
    regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b
  rw [← regDirichletIntegral_mvPolynomial b hb (carlsonPowerPolynomial n z)]
  congr 1
  funext u
  exact (eval_carlsonPowerPolynomial n z u).symm

/-- For fixed degree and Carlson variables, the regularized Carlson polynomial is entire in
the Dirichlet parameters. -/
theorem differentiable_regCarlsonRPolynomial (n : ℕ) (z : ι → ℂ) :
    Differentiable ℂ (regCarlsonRPolynomial n · z) :=
  differentiable_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

/-- Analytic form of entire dependence on the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonRPolynomial (n : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonRPolynomial n · z) Set.univ :=
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
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i + t)).eval (fun i ↦ (u i : ℂ)) =
      (a * carlsonAffineForm z u + t) ^ n := by
  rw [eval_carlsonPowerPolynomial, carlsonAffineForm_affine hu]

/-- Carlson's degree-`n` regularized R-polynomial is homogeneous in its variables on the
native convergence domain.  This is the homogeneous-polynomial observation following
Definition 5.7-1. -/
theorem regCarlsonRPolynomial_smul_of_mem_mvBetaConvergent (n : ℕ) (a : ℂ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonRPolynomial n b (fun i => a * z i) = a ^ n * regCarlsonRPolynomial n b z := by
  rw [← regCarlsonDirichletAverage_pow n _ hb,
    ← regCarlsonDirichletAverage_pow n z hb]
  unfold regCarlsonDirichletAverage
  calc
    regDirichletIntegral b (fun u => carlsonAffineForm (fun i => a * z i) u ^ n) =
        regDirichletIntegral b (fun u => a ^ n * carlsonAffineForm z u ^ n) := by
      apply regDirichletIntegral_congr
      intro u hu
      rw [show (fun i => a * z i) = fun i => a * z i + 0 by simp]
      dsimp only
      rw [carlsonAffineForm_affine hu]
      simp [mul_pow]
    _ = a ^ n * regDirichletIntegral b (fun u => carlsonAffineForm z u ^ n) :=
      regDirichletIntegral_smul b _ _

/-- The restriction of a regularized R-polynomial to the diagonal, corresponding to
Carlson's equation 5.7(3). -/
theorem regCarlsonRPolynomial_const (n : ℕ) (w : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    regCarlsonRPolynomial n b (fun _ => w) = w ^ n / Gamma (∑ i, b i) := by
  rw [← regCarlsonDirichletAverage_pow n _ hb]
  exact regCarlsonDirichletAverage_const (fun x => x ^ n) w hb

end Carlson
end CarlsonRPolynomial
