/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.FiniteType

/-!
# Denominator-cleared dependence over an integral domain

For modules over an integral domain, this file defines the closure of a submodule under clearing
nonzero scalar denominators. It proves cancellation and finite linear-relation lemmas, including
a reduction from dependence in a saturated finite span to a relation between coefficient
vectors.

## Main results

* `Submodule.mem_denominatorClosure`: A submodule is contained in its closure under clearing
  nonzero denominators.
* `Submodule.denominatorClosure_cancel`: A nonzero scalar can be cancelled from membership in
  the denominator closure.
* `Submodule.mem_denominatorClosure_of_sum_smul_eq_zero`: Cancellation in a finite linear
  relation: if all but one term of a vanishing linear combination lie in the denominator closure
  and the remaining coefficient is nonzero, then the remaining vector lies in the denominator
  closure as well.
* `Submodule.exists_relation_of_mem_denominatorClosure`: Clearing denominators reduces
  dependence in a saturated finite span to dependence of coefficient vectors over the original
  integral domain.

## References

* `Mathlib.LinearAlgebra.Dimension.Constructions`: formal background used by this module.
* `Mathlib.LinearAlgebra.Dimension.Finite`: formal background used by this module.
* `Mathlib.RingTheory.FiniteType`: formal background used by this module.
-/

@[expose] public noncomputable section
namespace Submodule

/-- Clearing a nonzero scalar denominator in a submodule. -/
def denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) : Submodule A M where
  carrier := {v | ∃ d : A, d ≠ 0 ∧ d • v ∈ P}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v w ⟨d, hd, hv⟩ ⟨e, he, hw⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm d e v]
    exact P.add_mem (P.smul_mem e hv) (P.smul_mem d hw)
  smul_mem' := by
    rintro c v ⟨d, hd, hv⟩
    refine ⟨d, hd, ?_⟩
    rw [smul_comm d c v]
    exact P.smul_mem c hv

/-- A submodule is contained in its closure under clearing nonzero denominators. -/
theorem mem_denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {v : M} (hv : v ∈ P) :
    v ∈ denominatorClosure P :=
  ⟨1, one_ne_zero, by simpa using hv⟩

/-- A nonzero scalar can be cancelled from membership in the denominator closure. -/
theorem denominatorClosure_cancel {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {c : A} {v : M}
    (hc : c ≠ 0) (hv : c • v ∈ denominatorClosure P) :
    v ∈ denominatorClosure P := by
  obtain ⟨d, hd, hv⟩ := hv
  exact ⟨d * c, mul_ne_zero hd hc, by simpa [mul_smul] using hv⟩

/-- Cancellation in a finite linear relation: if all but one term of a vanishing linear
combination lie in the denominator closure and the remaining coefficient is nonzero, then the
remaining vector lies in the denominator closure as well. -/
theorem mem_denominatorClosure_of_sum_smul_eq_zero {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {κ : Type*} {s : Finset κ}
    {C : κ → A} {F : κ → M} (hsum : ∑ j ∈ s, C j • F j = 0) {i : κ} (hi : i ∈ s)
    (hci : C i ≠ 0) (hrest : ∀ j ∈ s, j ≠ i → F j ∈ denominatorClosure P) :
    F i ∈ denominatorClosure P := by
  classical
  have hmem : ∑ j ∈ s.erase i, C j • F j ∈ denominatorClosure P :=
    Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (hrest j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
  have heq := Finset.sum_erase_add s (fun j => C j • F j) hi
  rw [hsum] at heq
  exact denominatorClosure_cancel P hci
    ((eq_neg_of_add_eq_zero_right heq) ▸ Submodule.neg_mem _ hmem)

/-- Clearing denominators reduces dependence in a saturated finite span to dependence
of coefficient vectors over the original integral domain. -/
theorem exists_relation_of_mem_denominatorClosure
    {A M J K : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Fintype J] [Fintype K] (v : K → M) (w : J → M)
    (hcard : Fintype.card K < Fintype.card J)
    (hw : ∀ j, w j ∈ denominatorClosure (Submodule.span A (Set.range v))) :
    ∃ a : J → A, (∃ j, a j ≠ 0) ∧ ∑ j, a j • w j = 0 := by
  choose d hd hmem using hw
  choose p hp using fun j => (Submodule.mem_span_range_iff_exists_fun A).mp (hmem j)
  have hdep : ¬ LinearIndependent A p := by
    intro h
    have hc := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hc
    omega
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨fun j => a j * d j, ⟨j, mul_ne_zero hj (hd j)⟩, ?_⟩
  simp_rw [mul_smul, ← hp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (k : K) : ∑ j, a j * p j k = 0 := by
    simpa using congrFun ha k
  simp_rw [← Finset.sum_smul, hcoeff, zero_smul, Finset.sum_const_zero]

end Submodule
