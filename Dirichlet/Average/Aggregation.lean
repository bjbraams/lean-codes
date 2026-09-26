/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Continuation
public import Dirichlet.Moments
public import Dirichlet.Transform.Aggregation

/-!
# Aggregation of continued Dirichlet averages

Carlson's equal-node aggregation theorem holds for all complex parameters after
regularization. The probability aggregation theorem supplies the identity on positive
real parameters; analytic uniqueness extends it to the whole complex parameter space.
The partition is surjective, so no empty blocks are inserted.

## Main results

* `Dirichlet.carlsonAffineForm_aggregate`: The affine form factors through aggregation when
  nodes are constant on blocks.
* `Dirichlet.realCarlsonDirichletAverage_aggregate`: Real Dirichlet averages respect any
  surjective grouping of equal nodes.
* `Dirichlet.IsRegCarlsonContinuation.aggregate`: Entire-parameter form of Carlson's Theorem
  5.2-4. Equal nodes are merged and their parameters added, including zero and negative
  parameters.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The affine form factors through aggregation when nodes are constant on blocks. -/
theorem carlsonAffineForm_aggregate (q : ι → κ) (z : κ → ℂ) (u : ι → ℝ) :
    carlsonAffineForm z (stdSimplexAggregate q u) = carlsonAffineForm (z ∘ q) u := by
  classical
  unfold carlsonAffineForm
  simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  push_cast
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ k, ∑ i ∈ Finset.univ with q i = k, (u i : ℂ) * z (q i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ q _

/-- Real Dirichlet averages respect any surjective grouping of equal nodes. -/
theorem realCarlsonDirichletAverage_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : κ → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ κ)) :
    realCarlsonDirichletAverage b (z ∘ q) f =
      realCarlsonDirichletAverage (stdSimplexAggregate q b) z f := by
  simpa only [realCarlsonDirichletAverage, carlsonAffineForm_aggregate] using
    integral_dirichletMeasure_comp_aggregate hq hb hf

/-- Entire-parameter form of Carlson's Theorem 5.2-4. Equal nodes are merged and
their parameters added, including zero and negative parameters. -/
theorem IsRegCarlsonContinuation.aggregate
    {q : ι → κ} (hq : Function.Surjective q) {f : ℂ → ℂ} {z : κ → ℂ}
    {G : (ι → ℂ) → ℂ} {H : (κ → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (z ∘ q) G) (hH : IsRegCarlsonContinuation f z H)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ κ))
    (b : ι → ℂ) : G b = H (stdSimplexAggregate q b) := by
  apply IsRegDirichletContinuation.aggregate hq (hH := hH) (hg := hf) (b := b)
  simpa only [IsRegDirichletContinuation, carlsonAffineForm_aggregate] using
    (show IsRegDirichletContinuation (fun u => f (carlsonAffineForm (z ∘ q) u)) G from hG)

end Dirichlet
end
