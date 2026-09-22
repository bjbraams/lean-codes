/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Associated.Deriv
public import Dirichlet.Average.KernelAnalytic

/-!
# Node and joint analyticity of native Dirichlet averages

Carlson's Theorem 5.3-3: on a convex open domain of holomorphy of the averaged function, the
regularized Dirichlet average is holomorphic in the nodes, and jointly holomorphic in the
Dirichlet parameters and the nodes. The joint statement follows from separate analyticity by
Hartogs' theorem.

## Main results

* `Dirichlet.analyticOnNhd_regCarlsonDirichletAverage_nodes`: node analyticity.
* `Dirichlet.analyticOnNhd_regCarlsonDirichletAverage_parameters_nodes`: joint analyticity.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- **Carlson 5.3-3, node-variable part.** On a convex domain of holomorphy, a regularized
Carlson average is analytic in all node variables throughout the corresponding product domain. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (fun z => regCarlsonDirichletAverage b z f)
      {z : ι → ℂ | Set.range z ⊆ Ω} := by
  obtain ⟨W, _, hH, hW⟩ := exists_analyticOnNhd_carlsonComplexKernel hΩopen hΩconv hf (ι := ι)
  exact analyticOnNhd_regDirichletIntegral_kernel (isOpen_carlsonNodeDomain hΩopen) hH hW hb

/-- A common integrable Dirichlet majorant bounds the average near each parameter and
node vector. No continuity of the density at the simplex boundary is required. -/
theorem locallyBounded_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {p : (ι → ℂ) × (ι → ℂ)}
    (hb : p.1 ∈ mvBetaConvergent) (hz : Set.range p.2 ⊆ Ω) :
    ∃ M : ℝ, ∀ᶠ q : (ι → ℂ) × (ι → ℂ) in nhds p,
      ‖regCarlsonDirichletAverage q.1 q.2 f‖ ≤ M := by
  apply locallyBounded_regDirichletIntegral_kernel (isOpen_carlsonNodeDomain hΩopen) (F :=
    fun z u => f (carlsonAffineForm z u)) ?_ hb hz
  apply hf.comp _ (fun q hq =>
    convexHull_min hq.1 hΩconv (carlsonAffineForm_mem_convexHull q.1 hq.2))
  exact (by unfold carlsonAffineForm; fun_prop :
    Continuous (fun q : (ι → ℂ) × (ι → ℝ) => carlsonAffineForm q.1 q.2)).continuousOn

/-- **Carlson 5.3-3, joint form.** Separate analyticity gives joint analyticity by
Hartogs' theorem. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonDirichletAverage p.1 p.2 f)
      {p | p.1 ∈ mvBetaConvergent ∧ Set.range p.2 ⊆ Ω} := by
  obtain ⟨W, _, hH, hW⟩ := exists_analyticOnNhd_carlsonComplexKernel hΩopen hΩconv hf (ι := ι)
  exact analyticOnNhd_regDirichletIntegral_kernel_joint (isOpen_carlsonNodeDomain hΩopen) hH hW

end Dirichlet
