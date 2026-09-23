/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Carlson.R.SlitRecurrence
public import Carlson.R.SlitDeriv

/-!
# Two-variable associated R-relations

Contiguous relations, the mixed node derivative and the three-term recurrence for the two-node
R-function on the full slit domain, with division-free coefficients. These are the two-variable
forms of Carlson's associated-function relations used by the L-function article.

## Main results

* `Carlson.TwoVariable.regCarlsonR_pair_contiguous`,
  `Carlson.TwoVariable.regCarlsonR_pair_contiguous_last`: contiguous relations.
* `Carlson.TwoVariable.regCarlsonR_pair_three_term`: the three-term recurrence.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
* [Carl87] B. C. Carlson, *Dirichlet averages of `x^t log x`*, SIAM J. Math. Anal. 18 (1987).
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The first two-node contiguous R-relation, without parameter denominators. -/
theorem regCarlsonR_pair_contiguous (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    u * (y - x) * regCarlsonR t (pair (u + 1) v) (pair x y) =
      y * regCarlsonR t (pair u v) (pair x y) -
        regCarlsonR (t + 1) (pair u v) (pair x y) := by
  have h₀ := regCarlsonR_eq_sum_addDirichletUnit t (pair u v) hz
  have h₁ := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit t (pair u v) hz
  have hu : addDirichletUnit (pair u v) 0 = pair (u + 1) v := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [Fin.sum_univ_two, pair_zero, pair_one, hu] at h₀ h₁
  linear_combination h₁ - y * h₀

/-- The companion contiguous relation, raising the second parameter. -/
theorem regCarlsonR_pair_contiguous_last (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    v * (x - y) * regCarlsonR t (pair u (v + 1)) (pair x y) =
      x * regCarlsonR t (pair u v) (pair x y) -
        regCarlsonR (t + 1) (pair u v) (pair x y) := by
  have h₀ := regCarlsonR_eq_sum_addDirichletUnit t (pair u v) hz
  have h₁ := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit t (pair u v) hz
  have hv : addDirichletUnit (pair u v) 1 = pair u (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [Fin.sum_univ_two, pair_zero, pair_one, hv] at h₀ h₁
  linear_combination h₁ - x * h₀

/-- The R-correction in (3.10) has a squared node-difference factor. -/
theorem regCarlsonR_pair_correction_factor (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    -regCarlsonR (t + 1) (pair u v) (pair x y) +
        (x + y) * regCarlsonR t (pair u v) (pair x y) -
        x * y * regCarlsonR (t - 1) (pair u v) (pair x y) =
      u * v * (x - y) ^ 2 * regCarlsonR (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  have h₀ := regCarlsonR_pair_contiguous_last t u v hz
  have h₁ := regCarlsonR_pair_contiguous_last (t - 1) u v hz
  have h₂ := regCarlsonR_pair_contiguous (t - 1) u (v + 1) hz
  simp only [sub_add_cancel] at h₁ h₂
  linear_combination -h₀ + y * h₁ + v * (x - y) * h₂

/-- The two-node mixed derivative, valid even at the exceptional integral exponents. -/
theorem carlsonPartialDeriv_regCarlsonR_pair_mixed (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    carlsonPartialDeriv 0 (carlsonPartialDeriv 1 (regCarlsonR (t + 1) (pair u v)))
        (pair x y) =
      t * (t + 1) * u * v * regCarlsonR (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  have hshift : addDirichletUnit (addDirichletUnit (pair u v) 1) 0 =
      pair (u + 1) (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  rw [carlsonPartialDeriv_carlsonPartialDeriv_regCarlsonR (t + 1) (pair u v) hz,
    hshift, show t + 1 - 2 = t - 1 by ring]
  simp [addDirichletUnit, pair]
  ring

/-- The three-term R-recurrence, with division-free coefficients. -/
theorem regCarlsonR_pair_three_term (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    (u + v + t) * regCarlsonR (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonR t (pair u v) (pair x y) +
      t * x * y * regCarlsonR (t - 1) (pair u v) (pair x y) = 0 := by
  have he₂ : (MvPolynomial.esymm (Fin 2) ℂ 2).eval (pair x y) = x * y := by
    simpa [carlsonElementarySymmetric,
        Fin.prod_univ_two] using carlsonElementarySymmetric_card (pair x y)
  have h := sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR (-t - 1) (pair u v) hz
  norm_num [Finset.sum_range_succ, carlsonAssociatedRecurrencePolynomial,
    MvPolynomial.esymm_one, Fin.sum_univ_two, he₂, pair_zero, pair_one] at h
  ring_nf at h ⊢
  linear_combination h

end Carlson.TwoVariable
