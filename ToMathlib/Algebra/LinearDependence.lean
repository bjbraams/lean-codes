/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra.Submodule.SaturationLocalization
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.FiniteType

/-!
# Linear dependence in saturated spans

Over a commutative ring, more than `n` vectors in the saturation of a span of `n`
generators are linearly dependent, provided zero is not an allowed denominator.
The denominators may be zero divisors. The ambient module need not be free,
finitely generated, or torsion-free.

The proof reuses Mathlib's preservation of linear independence under localization
and its bound on the size of an independent family in a finite span.

## Proposed Mathlib home

`Mathlib/LinearAlgebra/Dimension/Saturation.lean`, importing the saturation bridge
in `Mathlib/Algebra/Module/LocalizedModule/Submodule.lean`.
The `FiniteType` import supplies the strong rank condition for commutative rings.
-/

public section

variable {R M J K : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype J] [Fintype K]

/-- An independent finite family in a saturated finite span has at most as many
members as there are generators, provided zero is not an allowed denominator. -/
theorem LinearIndependent.fintype_card_le_of_mem_saturation_span
    {w : J → M} (hw : LinearIndependent R w) (S : Submonoid R) (hS : (0 : R) ∉ S)
    (v : K → M) (hmem : ∀ j, w j ∈ (Submodule.span R (Set.range v)).saturation S) :
    Fintype.card J ≤ Fintype.card K := by
  classical
  let : Nontrivial (Localization S) :=
    (IsLocalization.toLocalizationMap S (Localization S)).nontrivial hS
  let f := LocalizedModule.mkLinearMap S M
  have hli := hw.of_isLocalizedModule (Localization S) S f
  have hmem' (j : J) :
      f (w j) ∈ Submodule.span (Localization S) (Set.range (f ∘ v)) := by
    have h : f (w j) ∈ (Submodule.span R (Set.range v)).localized₀ S f := by
      simpa only [Submodule.saturation_eq_comap_localized₀ _ S f, Submodule.mem_comap]
        using hmem j
    change f (w j) ∈ (Submodule.span R (Set.range v)).localized' (Localization S) S f at h
    simpa only [Submodule.localized'_span, Set.range_comp] using h
  calc
    Fintype.card J ≤ Fintype.card (Set.range (f ∘ v)) :=
      linearIndependent_le_span_aux' _ hli _ (by rintro _ ⟨j, rfl⟩; exact hmem' j)
    _ ≤ Fintype.card K := Fintype.card_range_le _

/-- More vectors than generators in a saturated span admit a nontrivial relation,
provided zero is not an allowed denominator. -/
theorem Submodule.exists_relation_of_mem_saturation (S : Submonoid R) (hS : (0 : R) ∉ S)
    (v : K → M) (w : J → M) (hcard : Fintype.card K < Fintype.card J)
    (hw : ∀ j, w j ∈ (Submodule.span R (Set.range v)).saturation S) :
    ∃ a : J → R, (∃ j, a j ≠ 0) ∧ ∑ j, a j • w j = 0 := by
  have hdep : ¬ LinearIndependent R w :=
    fun h => hcard.not_ge (h.fintype_card_le_of_mem_saturation_span S hS v hw)
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  exact ⟨a, ⟨j, hj⟩, ha⟩
