/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import Dirichlet.Bridge
public import Dirichlet.Real.Aggregation

/-!
# Aggregation for general Dirichlet transforms

A kernel on a smaller simplex can be pulled back by summing coordinate blocks. Its
continued transform is the transform on the smaller simplex with the same blocks of
parameters summed. Surjectivity excludes empty blocks; empty index types are handled.
-/

open Complex MeasureTheory ProbabilityTheory Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Fiber summation preserves the total parameter. -/
theorem sum_aggregate_dirichletParameters (q : ι → κ) (b : ι → ℂ) :
    ∑ k, stdSimplexAggregate q b k = ∑ i, b i := by
  classical
  simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_fiberwise Finset.univ q b

/-- Aggregating simplex coordinates transports expectations of arbitrary kernels. -/
theorem integral_dirichletMeasure_comp_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {g : (κ → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ κ)) :
    (∫ u, g (stdSimplexAggregate q u) ∂dirichletMeasure b) =
      ∫ u, g u ∂dirichletMeasure (stdSimplexAggregate q b) := by
  have hmap := (measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb).map_eq
  have hm : AEStronglyMeasurable g (dirichletMeasure (stdSimplexAggregate q b)) := by
    rw [← dirichletMeasure_restrict]
    exact hg.aestronglyMeasurable (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet
  rw [← hmap, integral_map (_root_.continuous_stdSimplexAggregate q).measurable.aemeasurable
    (by rwa [hmap])]

/-- Aggregating coordinates and adding their parameters commutes with entire continuation. -/
theorem IsRegDirichletContinuation.aggregate
    {q : ι → κ} (hq : Function.Surjective q) {g : (κ → ℝ) → ℂ}
    {F : (ι → ℂ) → ℂ} {H : (κ → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation (fun u => g (stdSimplexAggregate q u)) F)
    (hH : IsRegDirichletContinuation g H)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ κ)) (b : ι → ℂ) :
    F b = H (stdSimplexAggregate q b) := by
  have hA : AnalyticOnNhd ℂ (stdSimplexAggregate (R := ℂ) q) univ := by
    intro c _
    exact ((FunOnFinite.linearMap ℂ ℂ q).toContinuousLinearMap).analyticAt c
  apply congrFun (analyticOnNhd_eq_of_eqOn_realDirichletDomain hF.1
    (hH.1.comp hA (fun _ _ => mem_univ _)) ?_) b
  intro c hc
  change F (fun i => (c i : ℂ)) = H (stdSimplexAggregate q (fun i => (c i : ℂ)))
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have : IsEmpty κ := ⟨fun k => (hq k).elim fun i _ => isEmptyElim i⟩
    rw [hF.eq_native (by intro i; exact isEmptyElim i),
      hH.eq_native (by intro k; exact isEmptyElim k)]
    simp [regDirichletIntegral]
  | inr hι =>
    have : Nonempty κ := ⟨q (Classical.arbitrary ι)⟩
    have hc' := mem_mvRealBetaDomain_stdSimplexAggregate hq hc
    have hcast : stdSimplexAggregate q (fun i => (c i : ℂ)) =
        fun k => ((stdSimplexAggregate (R := ℝ) q c k : ℝ) : ℂ) := by
      simpa only [Complex.ofRealHom_eq_coe] using
        stdSimplexAggregate_map Complex.ofRealHom q c
    rw [hcast, hF.eq_native (by simpa [mvBetaConvergent, mvRealBetaDomain] using hc),
      hH.eq_native (by simpa [mvBetaConvergent, mvRealBetaDomain] using hc'),
      regDirichletIntegral_ofReal hc, regDirichletIntegral_ofReal hc',
      integral_dirichletMeasure_comp_aggregate hq hc hg]
    congr 2
    rw [← hcast, sum_aggregate_dirichletParameters]

end Dirichlet
end
