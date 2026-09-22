/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Kernel
public import Dirichlet.Complex.Parametric

/-!
# Holomorphic kernels for Carlson averages

The first stage of Carlson's transform sends a scalar function to its composition
with the affine simplex form. Its complexification supplies the holomorphic kernel
needed by the general Dirichlet transform, with the nodes as auxiliary parameters.
-/

open Complex ProbabilityTheory Set
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- The complexified Carlson kernel, with nodes first and simplex variables second. -/
def carlsonComplexKernel (f : ℂ → ℂ) (p : (ι → ℂ) × (ι → ℂ)) : ℂ :=
  f (∑ i, p.2 i * p.1 i)

/-- Restricting the complexified kernel to real weights gives Carlson's affine kernel. -/
theorem carlsonComplexKernel_ofReal (f : ℂ → ℂ) (z : ι → ℂ) (u : ι → ℝ) :
    carlsonComplexKernel f (z, fun i => (u i : ℂ)) = f (carlsonAffineForm z u) := rfl

/-- A finite tuple of points in an open scalar domain varies in an open set. -/
theorem isOpen_carlsonNodeDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen {z : ι → ℂ | Set.range z ⊆ D} := by
  simp only [Set.range_subset_iff, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => hD.preimage (continuous_apply i)

/-- A holomorphic scalar function on a convex open domain supplies an admissible
kernel for the general Dirichlet transform on every node vector in that domain. -/
theorem exists_analyticOnNhd_carlsonComplexKernel
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    ∃ W : Set ((ι → ℂ) × (ι → ℂ)), IsOpen W ∧
      AnalyticOnNhd ℂ (carlsonComplexKernel f) W ∧
      ∀ z : ι → ℂ, Set.range z ⊆ Ω →
        ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
          (z, fun i => (u i : ℂ)) ∈ W := by
  let A := fun p : (ι → ℂ) × (ι → ℂ) => ∑ i, p.2 i * p.1 i
  have hA : AnalyticOnNhd ℂ A univ := by
    intro p _
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
      analyticAt_snd rfl).mul
      (((ContinuousLinearMap.proj i : (ι → ℂ)
          →L[ℂ] ℂ).analyticAt p.1).comp_of_eq analyticAt_fst rfl)
  refine ⟨A ⁻¹' Ω, hΩopen.preimage (continuousOn_univ.mp hA.continuousOn), ?_, ?_⟩
  · exact fun p hp => (hf (A p) hp).comp_of_eq (hA p (mem_univ _)) rfl
  · intro z hz u hu
    exact convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu)

end Dirichlet
end
