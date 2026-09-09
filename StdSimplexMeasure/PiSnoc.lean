/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Last-coordinate splitting of finite product spaces

This file records the measurable equivalence
`(Fin n → α) × α ≃ᵐ (Fin (n + 1) → α)` given by `Fin.snoc`, together with the fact that it
preserves product Lebesgue measure. It is a temporary home for results intended for
`Mathlib.MeasureTheory.MeasurableSpace.Embedding` and
`Mathlib.MeasureTheory.Constructions.Pi`.

This is `Fin.snocEquiv` with the product factors swapped, so that the last coordinate is the
`Prod.snd` factor. Equivalently, it is `MeasurableEquiv.prodComm` followed by
`(MeasurableEquiv.piFinSuccAbove _ (Fin.last n)).symm`.
-/

open MeasureTheory MeasureTheory.Measure

public section

namespace MeasurableEquiv

/-- Measurable equivalence `(Fin n → α) × α ≃ᵐ (Fin (n + 1) → α)` given by `Fin.snoc`. -/
def piFinSnoc (n : ℕ) (α : Type*) [MeasurableSpace α] :
    (Fin n → α) × α ≃ᵐ (Fin (n + 1) → α) :=
  (prodComm : (Fin n → α) × α ≃ᵐ α × (Fin n → α)).trans
    (piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)).symm

@[simp]
theorem piFinSnoc_apply (n : ℕ) (α : Type*) [MeasurableSpace α] (p : (Fin n → α) × α) :
    piFinSnoc n α p = @Fin.snoc n (fun _ => α) p.1 p.2 := by
  simp [piFinSnoc, Fin.insertNthEquiv_last, Fin.snocEquiv, MeasurableEquiv.prodComm]

end MeasurableEquiv

namespace MeasureTheory

/-- Last-coordinate splitting preserves product volume. -/
theorem measurePreserving_piFinSnoc (n : ℕ) (α : Type*) [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (MeasurableEquiv.piFinSnoc n α) volume volume := by
  unfold MeasurableEquiv.piFinSnoc
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)).symm).comp
    measurePreserving_swap

end MeasureTheory
