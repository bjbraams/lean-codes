/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper local homeomorphisms onto simply connected spaces

A proper local homeomorphism from a Hausdorff space is a covering map: its fibres are compact and
discrete, hence finite, and a proper map is closed. A covering map from a path-connected space
onto a simply connected space is injective: a path between two points of a fibre maps to a loop,
which is null-homotopic, and the lifts of homotopic paths have the same endpoint.

This is the topological core of the classical argument that a Schwarz–Christoffel map is
one-to-one onto its polygon.

## Main results

* `IsLocalHomeomorph.isCoveringMap_of_isProperMap`: proper local homeomorphisms are coverings.
* `IsCoveringMap.injective_of_simplyConnectedSpace`: coverings of simply connected spaces from
  path-connected spaces are injective.
* `IsLocalHomeomorph.injective_of_isProperMap`: the combination.
* `isLocalHomeomorph_of_isOpenMap_of_injOn`: a continuous open map that is injective near every
  point is a local homeomorphism.
-/

@[expose] public section

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- A continuous open map that is injective on a neighbourhood of every point is a local
homeomorphism. -/
theorem isLocalHomeomorph_of_isOpenMap_of_injOn (hc : Continuous f) (ho : IsOpenMap f)
    (hi : ∀ e, ∃ U ∈ 𝓝 e, InjOn f U) : IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro e
  obtain ⟨U, hU, hinj⟩ := hi e
  refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (hc.comp continuous_subtype_val) ?_
    (ho.comp isOpen_interior.isOpenMap_subtype_val)
  intro u v huv
  exact Subtype.ext (hinj (interior_subset u.2) (interior_subset v.2) huv)

/-- A proper local homeomorphism from a Hausdorff space is a covering map. -/
theorem IsLocalHomeomorph.isCoveringMap_of_isProperMap [T2Space E] (hf : IsLocalHomeomorph f)
    (hp : IsProperMap f) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
    ((isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hf).mono (subset_univ _))
  have hc : IsCompact (f ⁻¹' {x}) := hp.isCompact_preimage isCompact_singleton
  exact hc.finite (IsDiscrete.of_openPartialHomeomorph f subset_rfl fun e _ => by
    obtain ⟨φ, hφ, hfφ⟩ := hf e
    exact ⟨φ, hφ, hfφ.symm⟩)

/-- A covering map from a path-connected space onto a simply connected space is injective. -/
theorem IsCoveringMap.injective_of_simplyConnectedSpace [PathConnectedSpace E]
    [SimplyConnectedSpace X] (hf : IsCoveringMap f) : Function.Injective f := by
  intro e₀ e₁ he
  let γ : Path e₀ e₁ := PathConnectedSpace.somePath e₀ e₁
  let δ : Path (f e₀) (f e₀) := (γ.map hf.continuous).cast rfl he
  have hhom : Path.Homotopic δ (Path.refl (f e₀)) := SimplyConnectedSpace.paths_homotopic _ _
  have h0 : δ.toContinuousMap 0 = f e₀ := by simp
  have h0' : (Path.refl (f e₀)).toContinuousMap 0 = f e₀ := by simp
  have hlift := hf.liftPath_apply_one_eq_of_homotopicRel hhom e₀ h0 h0'
  have hγ : γ.toContinuousMap = hf.liftPath δ.toContinuousMap e₀ h0 := by
    rw [hf.eq_liftPath_iff']
    refine ⟨?_, by simp⟩
    funext t
    simp [δ]
  have hc : hf.liftPath (Path.refl (f e₀)).toContinuousMap e₀ h0' = ContinuousMap.const _ e₀ := by
    symm
    rw [hf.eq_liftPath_iff']
    exact ⟨by funext t; simp, by simp⟩
  rw [← hγ, hc] at hlift
  simpa using hlift.symm

/-- A proper local homeomorphism from a path-connected Hausdorff space onto a simply connected
space is injective. -/
theorem IsLocalHomeomorph.injective_of_isProperMap [T2Space E] [PathConnectedSpace E]
    [SimplyConnectedSpace X] (hf : IsLocalHomeomorph f) (hp : IsProperMap f) :
    Function.Injective f :=
  (hf.isCoveringMap_of_isProperMap hp).injective_of_simplyConnectedSpace
