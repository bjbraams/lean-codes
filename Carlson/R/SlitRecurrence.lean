/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.AssociatedRecurrence
public import Carlson.R.Explicit
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Polynomial recurrences on the full slit domain

Finite relations among R-functions with polynomial coefficients in the nodes, once known on the
right-half-plane node domain, extend with the same coefficients to the whole product slit
plane by analytic continuation. Carlson's homogeneity recurrence 8.4-1 is a polynomial identity
after Gamma regularization, so it holds for all complex exponents and Dirichlet parameters on
right-half-plane nodes by continuation in the parameters, and then on the whole slit domain.

## Main results

* `Carlson.polynomial_relation_regCarlsonR_of_right`: transport of polynomial relations.
* `Carlson.sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR`: Relation 8.4-1 on the slit
  domain.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- A finite polynomial-coefficient relation extends with its original coefficients. -/
theorem polynomial_relation_regCarlsonR_of_right {κ : Type*} (s : Finset κ)
    (A : κ → MvPolynomial ι ℂ) (t : κ → ℂ) (b : κ → ι → ℂ)
    (h : ∀ (z : ι → ℂ) (_ : z ∈ carlsonRVariableDomain),
      ∑ j ∈ s, (A j).eval z * regCarlsonR (t j) (b j) z = 0)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ j ∈ s, (A j).eval z * regCarlsonR (t j) (b j) z = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z =>
      ∑ j ∈ s, (A j).eval z * regCarlsonR (t j) (b j) z) carlsonRSlitDomain := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact ((AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (A j)) z trivial).mul
      (analyticOnNhd_regCarlsonR (t j) (b j) z hz)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane ha analyticOnNhd_const ?_ hz
  intro w hw
  change ∑ j ∈ s, (A j).eval w * regCarlsonR (t j) (b j) w = 0
  exact h w hw

/-- Carlson 8.4-1 on right-half-plane nodes, by continuation in the parameters from the native
integral. -/
private theorem sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR_of_mem_variableDomain
    [Nonempty ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
        regCarlsonR (-a - n) b z = 0 := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ?_ analyticOnNhd_const ?_) b
  · intro c _
    apply Finset.analyticAt_fun_sum
    intro n _
    apply AnalyticAt.mul
    · exact analyticAt_carlsonAssociatedRecurrencePolynomial_eval
        (a := fun _ : ι → ℂ => a) (a' := fun c : ι → ℂ => (∑ i, c i) - a)
        (b := fun c : ι → ℂ => c) (x := c) analyticAt_const
        ((Finset.analyticAt_fun_sum _ (fun i _ =>
          (ContinuousLinearMap.proj (R := ℂ) i).analyticAt c)).sub analyticAt_const)
        (fun i => (ContinuousLinearMap.proj (R := ℂ) i).analyticAt c) n z
    · exact analyticOnNhd_regCarlsonR_parameters (-a - n) (carlsonRVariableDomain_subset_slitDomain
        hz) c (mem_univ _)
  · intro c hc
    dsimp only
    simp_rw [regCarlsonR_eq_regCarlsonRIntegral (-a - _) hc hz]
    exact carlsonAssociatedRecurrenceResidual_eq_zero a hc hz

/-- Relation 8.4-1, with its polynomial coefficients, on the full slit domain. -/
theorem sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR [Nonempty ι]
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
        regCarlsonR (-a - n) b z = 0 :=
  polynomial_relation_regCarlsonR_of_right _ _ _ _
    (fun _ hw => sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR_of_mem_variableDomain a
        b hw) hz

end Carlson
