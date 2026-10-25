/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Regrouping convergent series over explicit finite fibers

Mathlib's fiberwise summation theorem can be stated using finite sums when
an explicit finite description of each fiber is available.
-/

public noncomputable section

variable {ι κ E : Type*} [AddCommMonoid E] [TopologicalSpace E]
  [ContinuousAdd E] [RegularSpace E]

/-- Regroup a convergent series over explicitly enumerated finite fibers. -/
theorem HasSum.sum_finite_fibers {f : ι → E} {a : E} (hf : HasSum f a)
    (p : ι → κ) (s : κ → Finset ι) (hs : ∀ i k, i ∈ s k ↔ p i = k) :
    HasSum (fun k => ∑ i ∈ s k, f i) a := by
  classical
  apply ((Equiv.sigmaFiberEquiv p).hasSum_iff.mpr hf).sigma
  intro k
  let e : {i // p i = k} ≃ ↥(s k) :=
    ⟨fun i => ⟨i.val, (hs i.val k).mpr i.property⟩,
      fun i => ⟨i.val, (hs i.val k).mp i.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  have h := e.hasSum_iff.mpr (hasSum_fintype (fun i : ↥(s k) => f i.val))
  simpa only [Finset.sum_coe_sort, Function.comp_def, e,
    Equiv.coe_fn_mk, Equiv.sigmaFiberEquiv] using h
