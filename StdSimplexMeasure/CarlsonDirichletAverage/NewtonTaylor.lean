/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage.Deriv
import StdSimplexMeasure.CarlsonDirichletAverage.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Newton--Taylor formulas from Carlson's Dirichlet averages

This file develops Carlson's Section 5.5.  The unweighted Dirichlet average is isolated first,
and divided differences are defined from averages of iterated derivatives.  Canonical finite
index types are used for lists of interpolation nodes; permutation invariance can subsequently
remove any dependence on their chosen ordering.

The central remaining analytic input is Carlson's Lemma 5.5-1, whose proof is a
fundamental-theorem-of-calculus and Fubini argument on a simplex.  The definitions and
normalization lemmas below isolate that input from the finite Newton interpolation induction.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.5,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonNewtonTaylor

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's unweighted Dirichlet average, obtained by setting every Dirichlet parameter
equal to one. -/
def carlsonUnweightedAverage (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  realCarlsonDirichletAverage (fun _ ↦ 1) z f

omit [Fintype ι] in
/-- The unweighted Dirichlet parameters belong to the positive real parameter domain. -/
theorem one_mem_mvRealBetaDomain : (fun _ : ι ↦ (1 : ℝ)) ∈ mvRealBetaDomain := by
  intro i
  simp

/-- Averaging at a constant vector of nodes is evaluation at that node. -/
theorem carlsonUnweightedAverage_const [Nonempty ι] (f : ℂ → ℂ) (w : ℂ) :
    carlsonUnweightedAverage (fun _ : ι ↦ w) f = f w := by
  let b : ι → ℝ := fun _ ↦ 1
  let _ : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure one_mem_mvRealBetaDomain
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  change (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) = f w
  have hrestrict := dirichletMeasure_restrict b
  have hmem : ∀ᵐ u ∂dirichletMeasure b, u ∈ stdSimplex ℝ ι := by
    rw [← hrestrict]
    exact self_mem_ae_restrict (isClosed_stdSimplex ℝ ι).measurableSet
  calc
    (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) =
        ∫ _, f w ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [hmem] with u hu
      rw [carlsonAffineForm_const hu]
    _ = f w := by simp

/-- Permuting the nodes does not change the unweighted Carlson average. -/
theorem carlsonUnweightedAverage_perm (z : ι → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm ι) :
    carlsonUnweightedAverage (z ∘ σ) f = carlsonUnweightedAverage z f := by
  let b : ι → ℝ := fun _ ↦ 1
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun u := u ∘ σ.symm
    invFun u := u ∘ σ
    left_inv u := by funext i; simp
    right_inv u := by funext i; simp
    measurable_toFun := continuous_pi (fun i ↦ continuous_apply (σ.symm i)) |>.measurable
    measurable_invFun := continuous_pi (fun i ↦ continuous_apply (σ i)) |>.measurable
  }
  have hg : MeasurePreserving g (dirichletMeasure b) (dirichletMeasure b) := by
    convert measurePreserving_dirichletMeasure_perm b σ.symm using 1 <;>
      simp [g, b, Function.comp_def]
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  rw [← hg.integral_comp' (fun u ↦ f (carlsonAffineForm z u))]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  simpa [g, Function.comp_def] using
    (carlsonAffineForm_perm (z ∘ σ) σ.symm u).symm

/-- The node vector obtained by placing `x` before a vector of `n` nodes. -/
def prependNewtonNode (x : ℂ) (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons x z

/-- The node vector obtained by placing `x` and `y` before a vector of `n` nodes. -/
def prependTwoNewtonNodes (x y : ℂ) (z : Fin n → ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons x (Fin.cons y z)

/-- A divided difference of order `n`, expressed as Carlson's unweighted average of the
`n`th derivative divided by `n!`; this is formula (5.5-6). -/
def carlsonDividedDifference (n : ℕ) (f : ℂ → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  carlsonUnweightedAverage z (iteratedDeriv n f) / (n.factorial : ℂ)

/-- Divided differences are invariant under permutations of their nodes. -/
theorem carlsonDividedDifference_perm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    carlsonDividedDifference n f (z ∘ σ) = carlsonDividedDifference n f z := by
  rw [carlsonDividedDifference, carlsonDividedDifference,
    carlsonUnweightedAverage_perm]

/-- A divided difference of order zero is evaluation at its unique node. -/
@[simp] theorem carlsonDividedDifference_zero (f : ℂ → ℂ) (z : Fin 1 → ℂ) :
    carlsonDividedDifference 0 f z = f (z 0) := by
  have hz : z = fun _ ↦ z 0 := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  rw [hz]
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- If all nodes coincide, Carlson's divided difference is the corresponding Taylor
coefficient. -/
theorem carlsonDividedDifference_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    carlsonDividedDifference n f (fun _ ↦ w) =
      iteratedDeriv n f w / (n.factorial : ℂ) := by
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- The Newton basis polynomial associated to a finite vector of preceding nodes. -/
def newtonBasis (z : Fin n → ℂ) (x : ℂ) : ℂ :=
  ∏ i, (x - z i)

/-- The empty Newton basis is one. -/
@[simp] theorem newtonBasis_zero (z : Fin 0 → ℂ) (x : ℂ) :
    newtonBasis z x = 1 := by
  simp [newtonBasis]

/-- Prepending a node adds the corresponding linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_prepend (z : Fin n → ℂ) (a x : ℂ) :
    newtonBasis (prependNewtonNode a z) x = (x - a) * newtonBasis z x := by
  simp [newtonBasis, prependNewtonNode, Fin.prod_univ_succ]

end DirichletTransform

end CarlsonNewtonTaylor
