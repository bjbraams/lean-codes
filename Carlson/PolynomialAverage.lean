/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Basic
public import Dirichlet.Average.Continuation

/-!
# Continued Carlson averages of univariate polynomials

The regularized Carlson polynomials are the moments of a linear functional on
univariate polynomials. The resulting transform is entire in the Dirichlet
parameters and agrees with the native integral on its convergence domain.
Multiplication by Gamma of the total parameter gives the ordinary normalization;
at Gamma poles that expression is totalized, not an asserted removable value.

## Main results

* `isRegCarlsonContinuation_polynomial`: the moment functional is the unique
  regularized continuation of the polynomial average.
* `regCarlsonPolynomialAverage_comp_affine`: affine changes of variables commute
  with the continued transform.
* `regCarlsonPolynomialAverage_const_nodes`: coincident nodes give evaluation
  times reciprocal Gamma, at every parameter vector.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapters 5–7.
-/

@[expose] public noncomputable section
namespace Carlson
open Polynomial Dirichlet Complex
variable {ι : Type*} [Fintype ι]

/-- The regularized continued Carlson average as a linear functional on polynomials. -/
def regCarlsonPolynomialAverage (b z : ι → ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  lsum (fun n => LinearMap.mulRight ℂ (regCarlsonRPolynomial n b z))

/-- The ordinary continued polynomial average. Analytic assertions about this
normalization exclude poles of Gamma of the total parameter. -/
def carlsonPolynomialAverage (b z : ι → ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  Gamma (∑ i, b i) • regCarlsonPolynomialAverage b z

/-- The regularized polynomial average is the finite sum of its moments. -/
theorem regCarlsonPolynomialAverage_apply (b z : ι → ℂ) (p : ℂ[X]) :
    regCarlsonPolynomialAverage b z p =
      ∑ n ∈ p.support, p.coeff n * regCarlsonRPolynomial n b z := rfl

/-- The regularized average of a monomial. -/
@[simp] theorem regCarlsonPolynomialAverage_monomial (b z : ι → ℂ) (n : ℕ) (c : ℂ) :
    regCarlsonPolynomialAverage b z (monomial n c) = c * regCarlsonRPolynomial n b z := by
  simp [regCarlsonPolynomialAverage, lsum_apply, sum_monomial_index]

/-- The explicit moment functional is entire in all Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonPolynomialAverage (p : ℂ[X]) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (fun b => regCarlsonPolynomialAverage b z p) Set.univ := by
  intro b _
  simp only [regCarlsonPolynomialAverage_apply]
  exact Finset.analyticAt_fun_sum _ fun n _ =>
    analyticAt_const.mul (analyticOnNhd_regCarlsonRPolynomial n z b (Set.mem_univ _))

/-- The moment functional agrees with the convergent native polynomial integral. -/
theorem regCarlsonPolynomialAverage_eq_native (p : ℂ[X]) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonPolynomialAverage b z p = regCarlsonDirichletAverage b z (fun x => p.eval x) := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [regCarlsonDirichletAverage_finsetSum hb _ (by
    intro n _; exact (continuous_const.mul ((continuous_carlsonAffineForm z).pow n)).continuousOn)]
  simp_rw [regCarlsonDirichletAverage_const_mul, regCarlsonDirichletAverage_pow _ _ hb]
  rfl

/-- The polynomial moment functional is a regularized Carlson continuation. -/
theorem isRegCarlsonContinuation_polynomial (p : ℂ[X]) (z : ι → ℂ) :
    IsRegCarlsonContinuation (fun x => p.eval x) z
      (fun b => regCarlsonPolynomialAverage b z p) :=
  ⟨analyticOnNhd_regCarlsonPolynomialAverage p z,
    fun _ hb => regCarlsonPolynomialAverage_eq_native p z hb⟩

/-- Affine substitutions commute with the regularized continued polynomial average. -/
theorem regCarlsonPolynomialAverage_comp_affine (p : ℂ[X]) (a t : ℂ) (b z : ι → ℂ) :
    regCarlsonPolynomialAverage b z (p.comp (C a * X + C t)) =
      regCarlsonPolynomialAverage b (fun i => a * z i + t) p := by
  have he := analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonPolynomialAverage (p.comp (C a * X + C t)) z)
    (analyticOnNhd_regCarlsonPolynomialAverage p (fun i => a * z i + t)) (fun b hb => by
      rw [regCarlsonPolynomialAverage_eq_native _ _ hb,
        regCarlsonPolynomialAverage_eq_native _ _ hb]
      simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
      exact regCarlsonDirichletAverage_comp_affine b z (fun x => p.eval x) a t)
  exact congrFun he b

/-- At coincident nodes the regularized average is evaluation times reciprocal Gamma. -/
theorem regCarlsonPolynomialAverage_const_nodes (p : ℂ[X]) (w : ℂ) (b : ι → ℂ) :
    regCarlsonPolynomialAverage b (fun _ => w) p = p.eval w / Gamma (∑ i, b i) := by
  have hR : AnalyticOnNhd ℂ (fun b : ι → ℂ => p.eval w / Gamma (∑ i, b i)) Set.univ := by
    intro b _
    apply AnalyticAt.mul analyticAt_const
    exact ((analyticOnNhd_univ_iff_differentiable.mpr
      Complex.differentiable_one_div_Gamma) _ (Set.mem_univ _)).comp
      (Finset.analyticAt_fun_sum _ fun i _ =>
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
  exact congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonPolynomialAverage p (fun _ => w)) hR (fun b hb => by
      rw [regCarlsonPolynomialAverage_eq_native _ _ hb]
      exact regCarlsonDirichletAverage_const (fun x => p.eval x) w hb)) b

/-- At coincident nodes the ordinary continued average is evaluation, provided
the total parameter is not a Gamma pole. -/
theorem carlsonPolynomialAverage_const_nodes (p : ℂ[X]) (w : ℂ) (b : ι → ℂ)
    (hb : IsCarlsonGammaRegular (∑ i, b i)) :
    carlsonPolynomialAverage b (fun _ => w) p = p.eval w := by
  simp only [carlsonPolynomialAverage, LinearMap.smul_apply, smul_eq_mul,
    regCarlsonPolynomialAverage_const_nodes]
  exact mul_div_cancel₀ _ (Gamma_ne_zero hb)

end Carlson
