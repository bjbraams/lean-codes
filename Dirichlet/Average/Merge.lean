/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Bridge
public import Dirichlet.Transform.Merge

/-!
# Merging two nodes of a Dirichlet average

For averages the merging identity of `Dirichlet.Merge` and `Dirichlet.Transform.Merge` is
Carlson's (1969) representation (4.21) in the case of a group of two nodes: the average with
nodes `z` is a two-node average, over the segment joining `z a` and `z a'`, of the average in
which these two nodes are replaced by a single moving node with the merged parameter. In
regularized form the factor `Γ(b a + b a')` appears.

## Main definitions

* `Dirichlet.mergeNodes`: the merged node vector.

## Main results

* `Dirichlet.carlsonAffineForm_mergeMap`: the affine form of merged coordinates.
* `Dirichlet.realCarlsonDirichletAverage_eq_merge`: the identity for probability averages.
* `Dirichlet.regCarlsonDirichletAverage_ofReal_eq_merge`: the regularized identity for positive
  real parameters.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, equation (4.21).
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [DecidableEq ι] {a a' : ι}

/-- The merged node vector, with the node `w` in place of the two merged nodes. -/
def mergeNodes {α : Type*} (a a' : ι) (z : ι → α) (w : α) : {i : ι // i ≠ a'} → α :=
  fun j => if (j : ι) = a then w else z j

variable [Fintype ι]

/-- The affine form of the merged coordinates is the affine form of the merged nodes. -/
theorem carlsonAffineForm_mergeMap (h : a ≠ a') (z : ι → ℂ) (v : Fin 2 → ℝ)
    (y : {i : ι // i ≠ a'} → ℝ) :
    carlsonAffineForm z (mergeMap h v y) =
      carlsonAffineForm (mergeNodes a a' z (carlsonAffineForm (pairParam a a' z) v)) y := by
  unfold carlsonAffineForm
  rw [sum_eq_merge h, sum_merged_eq h, mergeMap_apply_right, mergeMap_apply_left]
  simp_rw [mergeMap_apply_other]
  have hk : ∀ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h},
      mergeNodes a a' z (∑ i, (v i : ℂ) * pairParam a a' z i) k.1 = z k.1.1 := by
    intro k
    have h2 : (k.1 : ι) ≠ a := fun e => k.2 (Subtype.ext e)
    simp [mergeNodes, h2]
  simp_rw [hk]
  simp only [mergeNodes, mergeIndex, ite_true, Fin.sum_univ_two, pairParam, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  ring

/-- **The merging identity for probability averages.** -/
theorem realCarlsonDirichletAverage_eq_merge (h : a ≠ a') {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    realCarlsonDirichletAverage b z f =
      realCarlsonDirichletAverage (pairParam a a' b) (pairParam a a' z)
        (fun w => realCarlsonDirichletAverage (mergeParam a a' b) (mergeNodes a a' z w) f) := by
  unfold realCarlsonDirichletAverage
  rw [integral_dirichletMeasure_eq_merge h hb hf]
  simp_rw [carlsonAffineForm_mergeMap h]

/-- **The regularized merging identity** for positive real parameters: the factor
`Γ(b a + b a')` compensates the regularization of the two-node average. -/
theorem regCarlsonDirichletAverage_ofReal_eq_merge (h : a ≠ a') {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regCarlsonDirichletAverage (fun i => (b i : ℂ)) z f =
      Gamma ((b a : ℂ) + b a') *
        regCarlsonDirichletAverage (pairParam a a' (fun i => (b i : ℂ))) (pairParam a a' z)
          (fun w => regCarlsonDirichletAverage (mergeParam a a' (fun i => (b i : ℂ)))
            (mergeNodes a a' z w) f) := by
  unfold regCarlsonDirichletAverage
  rw [regDirichletIntegral_ofReal_eq_merge h hb hf]
  simp_rw [carlsonAffineForm_mergeMap h]

end Dirichlet

end
