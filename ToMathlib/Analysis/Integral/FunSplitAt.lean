/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Splitting one coordinate off Lebesgue measure

Lebesgue measure on `ι → ℝ` is the product of Lebesgue measure on one coordinate and Lebesgue
measure on the remaining coordinates, through `Homeomorph.funSplitAt`.

## Main results

* `MeasureTheory.volume_preserving_funSplitAt`: the splitting map is measure preserving.
-/

@[expose] public noncomputable section

namespace MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]

open scoped Classical in
/-- Splitting one coordinate from a finite real coordinate space preserves product Lebesgue
measure. -/
theorem volume_preserving_funSplitAt (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) volume (volume.prod volume) := by
  let eidx : Unit ⊕ {j : ι // j ≠ i} ≃ ι :=
    { toFun := fun q => Sum.elim (fun _ => i) Subtype.val q
      invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
      left_inv := by
        rintro (_ | j)
        · simp
        · simp [j.property]
      right_inv := by
        intro j
        dsimp
        split_ifs with h
        · exact h.symm
        · rfl }
  let ec := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) eidx
  let es := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ {j : ι // j ≠ i} => ℝ)
  let eu := MeasurableEquiv.prodCongr
    (MeasurableEquiv.funUnique Unit ℝ)
    (MeasurableEquiv.refl ({j : ι // j ≠ i} → ℝ))
  have hc := (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) eidx).symm
  have hs := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ {j : ι // j ≠ i} => ℝ)
  have hu : MeasurePreserving eu volume (volume.prod volume) := by
    rw [Measure.volume_eq_prod]
    exact (volume_preserving_funUnique Unit ℝ).prod (MeasurePreserving.id volume)
  have h := hu.comp (hs.comp hc)
  convert h using 1
  funext x
  apply Prod.ext
  · change x i = x (eidx (Sum.inl ()))
    rfl
  · funext j
    change x j = x (eidx (Sum.inr j))
    rfl

end MeasureTheory

end
