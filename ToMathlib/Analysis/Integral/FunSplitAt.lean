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
# Splitting one coordinate off a product measure

For a σ-finite measure `μ`, the product measure `Measure.pi (fun _ ↦ μ)` on `ι → Y` is the product
of `μ` on one coordinate and the product measure on the remaining coordinates, through
`Homeomorph.funSplitAt`. In particular this holds for Lebesgue measure on `ι → ℝ`.

## Main results

* `MeasureTheory.measurePreserving_funSplitAt`: the splitting map is measure preserving.
* `MeasureTheory.volume_preserving_funSplitAt`: the case of Lebesgue measure on `ι → ℝ`.
-/

@[expose] public noncomputable section

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Splitting one coordinate from a finite product preserves the product of a σ-finite
measure. -/
theorem measurePreserving_funSplitAt {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt Y i) (Measure.pi fun _ : ι ↦ μ)
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} ↦ μ)) := by
  let eidx : Unit ⊕ {j : ι // j ≠ i} ≃ ι :=
    { toFun := fun q ↦ Sum.elim (fun _ ↦ i) Subtype.val q
      invFun := fun j ↦ if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
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
  let eu := MeasurableEquiv.prodCongr
    (MeasurableEquiv.funUnique Unit Y)
    (MeasurableEquiv.refl ({j : ι // j ≠ i} → Y))
  have hc := (measurePreserving_piCongrLeft (α := fun _ : ι ↦ Y) (fun _ ↦ μ) eidx).symm
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ {j : ι // j ≠ i} ↦ μ)
  have hu : MeasurePreserving eu ((Measure.pi fun _ : Unit ↦ μ).prod
      (Measure.pi fun _ : {j : ι // j ≠ i} ↦ μ)) (μ.prod (Measure.pi fun _ ↦ μ)) :=
    (measurePreserving_funUnique μ Unit).prod (MeasurePreserving.id _)
  have h := hu.comp (hs.comp hc)
  convert h using 1
  funext x
  apply Prod.ext
  · change x i = x (eidx (Sum.inl ()))
    rfl
  · funext j
    change x j = x (eidx (Sum.inr j))
    rfl

/-- Splitting one coordinate from a finite real coordinate space preserves product Lebesgue
measure. -/
theorem volume_preserving_funSplitAt (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) volume (volume.prod volume) :=
  measurePreserving_funSplitAt volume i

end MeasureTheory

end
