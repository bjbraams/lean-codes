/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differentiation of Carlson's Dirichlet averages

This file is reserved for the native differentiation formulas of Carlson's Section 5.3 and
the Euler--Poisson differential equations of Section 5.4.  Keeping this layer separate allows
the measure-theoretic differentiation and integration-by-parts arguments to be developed
without importing the analytic-continuation machinery.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Sections 5.3--5.4,
  Academic Press, 1977.
-/

public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

open Complex
open scoped Classical

variable {ι : Type*} [Fintype ι]

/-! ## Pointwise differentiation of the averaging kernel -/

/-- Updating one parameter of Carlson's affine form changes its value by the corresponding
simplex coordinate times the change in that parameter. -/
theorem carlsonAffineForm_update (z : ι → ℂ) (u : ι → ℝ) (i : ι) (w : ℂ) :
    carlsonAffineForm (Function.update z i w) u =
      carlsonAffineForm z u + (u i : ℂ) * (w - z i) := by
  classical
  unfold carlsonAffineForm
  calc
    ∑ j, (u j : ℂ) * Function.update z i w j =
        ∑ j, ((u j : ℂ) * z j + if j = i then (u i : ℂ) * (w - z i) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp
        ring
      · simp [hji]
    _ = ∑ j, (u j : ℂ) * z j + (u i : ℂ) * (w - z i) := by
      rw [Finset.sum_add_distrib]
      simp

/-- As a function of one variable `z i`, Carlson's affine form has derivative `u i`. -/
theorem hasDerivAt_carlsonAffineForm_update (z : ι → ℂ) (u : ι → ℝ) (i : ι) :
    HasDerivAt (fun w ↦ carlsonAffineForm (Function.update z i w) u) (u i : ℂ) (z i) := by
  have h := (hasDerivAt_const (x := z i) (c := carlsonAffineForm z u)).add
    ((hasDerivAt_id (x := z i)).sub_const (z i) |>.const_mul (u i : ℂ))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
  · simpa only [Pi.add_apply, id_eq] using carlsonAffineForm_update z u i w
  · ring

/-- Differentiating a composed Carlson kernel with respect to `z i` introduces the factor
`u i`.  This is the pointwise identity underlying Carlson's formula (5.3-2). -/
theorem HasDerivAt.comp_carlsonAffineForm_update {f : ℂ → ℂ} {f' : ℂ}
    {z : ι → ℂ} {u : ι → ℝ} (i : ι)
    (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    HasDerivAt (fun w ↦ f (carlsonAffineForm (Function.update z i w) u))
      ((u i : ℂ) * f') (z i) := by
  have hf' : HasDerivAt f f'
      (carlsonAffineForm (Function.update z i (z i)) u) := by simpa using hf
  have h := hf'.comp (z i) (hasDerivAt_carlsonAffineForm_update z u i)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ rfl)).congr_deriv ?_
  ring

/-! ## Differential operators -/

/-- The partial derivative in the Carlson variable `z i`, defined by updating that coordinate
while holding all other coordinates fixed. -/
def carlsonPartialDeriv (i : ι)
    (G : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  deriv (fun w ↦ G (Function.update z i w)) (z i)

/-- The partial derivative of a Carlson kernel is the derivative of the univariate function
times the corresponding simplex coordinate.  This is the pointwise form of Carlson's
formula (5.3-2). -/
theorem carlsonPartialDeriv_comp_carlsonAffineForm {f : ℂ → ℂ} {f' : ℂ}
    {z : ι → ℂ} {u : ι → ℝ} (i : ι)
    (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    carlsonPartialDeriv i (fun z ↦ f (carlsonAffineForm z u)) z = (u i : ℂ) * f' := by
  unfold carlsonPartialDeriv
  exact (HasDerivAt.comp_carlsonAffineForm_update i hf).deriv

/-- Mixed partial differentiation of a Carlson kernel introduces the product of the two
corresponding simplex coordinates. -/
theorem carlsonPartialDeriv_carlsonPartialDeriv_comp_carlsonAffineForm
    {f f' : ℂ → ℂ} {f'' : ℂ} {z : ι → ℂ} {u : ι → ℝ} (i j : ι)
    (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf' : HasDerivAt f' f'' (carlsonAffineForm z u)) :
    carlsonPartialDeriv i
        (carlsonPartialDeriv j (fun z ↦ f (carlsonAffineForm z u))) z =
      (u i : ℂ) * (u j : ℂ) * f'' := by
  have hinner : carlsonPartialDeriv j (fun z ↦ f (carlsonAffineForm z u)) =
      fun z ↦ (u j : ℂ) * f' (carlsonAffineForm z u) := by
    funext z'
    exact carlsonPartialDeriv_comp_carlsonAffineForm j
      (hf (carlsonAffineForm z' u))
  rw [hinner]
  unfold carlsonPartialDeriv
  have hcomp := HasDerivAt.comp_carlsonAffineForm_update i hf'
  simpa [mul_assoc, mul_left_comm] using (hcomp.const_mul (u j : ℂ)).deriv

/-- Carlson's Euler--Poisson differential expression for a twice differentiable function of
the variables `z`.  The equation in Theorem 5.4-1 asserts that this expression vanishes. -/
def carlsonEulerPoissonOperator (i j : ι) (b z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) : ℂ :=
  (z i - z j) * carlsonPartialDeriv i (carlsonPartialDeriv j G) z +
    b i * carlsonPartialDeriv j G z - b j * carlsonPartialDeriv i G z

omit [Fintype ι] in
/-- The diagonal members of the Euler--Poisson system vanish identically. -/
@[simp] theorem carlsonEulerPoissonOperator_self (i : ι) (b z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) :
    carlsonEulerPoissonOperator i i b z G = 0 := by
  simp [carlsonEulerPoissonOperator]

/-- Evaluation of the Euler--Poisson operator on a Carlson kernel.  The integral of this
expression is the quantity killed by Carlson's integration-by-parts argument in the proof of
Theorem 5.4-1. -/
theorem carlsonEulerPoissonOperator_comp_carlsonAffineForm
    (i j : ι) (b z : ι → ℂ) (u : ι → ℝ)
    {f f' : ℂ → ℂ} {f'' : ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf' : HasDerivAt f' f'' (carlsonAffineForm z u)) :
    carlsonEulerPoissonOperator i j b z
        (fun z ↦ f (carlsonAffineForm z u)) =
      (z i - z j) * ((u i : ℂ) * (u j : ℂ) * f'') +
        b i * ((u j : ℂ) * f' (carlsonAffineForm z u)) -
        b j * ((u i : ℂ) * f' (carlsonAffineForm z u)) := by
  rw [carlsonEulerPoissonOperator,
    carlsonPartialDeriv_carlsonPartialDeriv_comp_carlsonAffineForm i j hf hf',
    carlsonPartialDeriv_comp_carlsonAffineForm j (hf (carlsonAffineForm z u)),
    carlsonPartialDeriv_comp_carlsonAffineForm i (hf (carlsonAffineForm z u))]

end DirichletTransform

end CarlsonDirichletAverage
