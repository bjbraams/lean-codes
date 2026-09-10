/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Null affine hyperplanes in finite real products

This file proves that the solution set of a nontrivial weighted affine equation in a finite
product of real lines has Lebesgue measure zero. Coordinate and coordinate-sum hyperplanes are
recorded as corollaries.
-/

open MeasureTheory MeasurableEquiv

public noncomputable section

namespace MeasureTheory.Measure

/-- A level set of a weighted coordinate sum has volume zero if one of its coefficients is
nonzero. This is the finite-product form of the fact that a proper affine hyperplane is
Lebesgue-null. -/
theorem volume_setOf_fin_weighted_sum_eq {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hi : a i ≠ 0) (c : ℝ) :
    volume {x : Fin n → ℝ | ∑ j, a j * x j = c} = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).trans
        (MeasurableEquiv.prodComm : ℝ × (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ)
      have hmp : MeasurePreserving e volume volume := measurePreserving_swap.comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
      have hmeas : MeasurableSet
          {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c} :=
        (isClosed_eq (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (continuous_apply j)) continuous_const).measurableSet
      have hpremeas : MeasurableSet
          (e.symm ⁻¹' {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}) :=
        hmeas.preimage e.symm.measurable
      rw [← hmp.symm.measure_preimage_equiv
        {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}]
      change (volume.prod volume) (e.symm ⁻¹' _) = 0
      refine (Measure.measure_prod_null hpremeas).2
        (Filter.Eventually.of_forall fun y => ?_)
      have hsection : Prod.mk y ⁻¹' (e.symm ⁻¹'
          {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}) =
          {(c - ∑ j, a (i.succAbove j) * y j) / a i} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        rw [i.sum_univ_succAbove]
        have hei : e.symm (y, t) i = t := by
          simp [e, MeasurableEquiv.trans, MeasurableEquiv.prodComm]
        have hej : ∀ j, e.symm (y, t) (i.succAbove j) = y j := by
          intro j
          simp [e, MeasurableEquiv.trans, MeasurableEquiv.prodComm]
        rw [hei]
        simp_rw [hej]
        constructor <;> intro h
        · apply (eq_div_iff hi).2
          linarith
        · rw [h]
          field_simp
          ring
      change volume (Prod.mk y ⁻¹' (e.symm ⁻¹'
        {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c})) = 0
      rw [hsection]
      simp

/-- A level set of a weighted coordinate sum in an arbitrary nonempty finite real product has
volume zero if one of its coefficients is nonzero. -/
theorem volume_setOf_fintype_weighted_sum_eq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (i : ι) (hi : a i ≠ 0) (c : ℝ) :
    volume {x : ι → ℝ | ∑ j, a j * x j = c} = 0 := by
  classical
  let σ := Fintype.equivFin ι
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) σ.symm
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) σ.symm
  rw [← hmp.measure_preimage_equiv {x : ι → ℝ | ∑ j, a j * x j = c}]
  have hpre : e ⁻¹' {x : ι → ℝ | ∑ j, a j * x j = c} =
      {x : Fin (Fintype.card ι) → ℝ | ∑ j, a (σ.symm j) * x j = c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have he : ∀ j, e x j = x (σ j) := by
      intro j
      simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ι => ℝ) σ.symm x (σ j)
    simp_rw [he]
    change (∑ j, a j * x (σ j)) = c ↔ _
    rw [← σ.symm.sum_comp (fun j => a j * x (σ j))]
    simp
  rw [hpre]
  exact volume_setOf_fin_weighted_sum_eq (fun j => a (σ.symm j)) (σ i) (by simpa [σ]) c

/-- A level set of a coordinate projection in a finite real product has volume zero. -/
theorem volume_setOf_eval_eq {ι : Type*} [Fintype ι] (i : ι) (c : ℝ) :
    volume {x : ι → ℝ | x i = c} = 0 := by
  classical
  let a : ι → ℝ := fun j => if j = i then 1 else 0
  have hi : a i ≠ 0 := by simp [a]
  rw [show {x : ι → ℝ | x i = c} = {x | ∑ j, a j * x j = c} by
    ext x
    simp [a]]
  exact volume_setOf_fintype_weighted_sum_eq a i hi c

/-- A level set of the coordinate sum in a nonempty finite real product has volume zero. -/
theorem volume_setOf_fintype_sum_eq {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    volume {x : ι → ℝ | ∑ i, x i = c} = 0 := by
  classical
  let i : ι := Classical.choice inferInstance
  rw [show {x : ι → ℝ | ∑ j, x j = c} =
      {x | ∑ j, (1 : ℝ) * x j = c} by ext x; simp]
  exact volume_setOf_fintype_weighted_sum_eq (fun _ : ι => 1) i one_ne_zero c

/-- A level set of the coordinate sum in a nonempty finite real product has volume zero.  The
nonempty hypothesis is necessary: in dimension zero the level set at zero is the whole space. -/
theorem volume_setOf_fin_sum_eq {n : ℕ} (hn : 0 < n) (c : ℝ) :
    volume {x : Fin n → ℝ | ∑ i, x i = c} = 0 := by
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact volume_setOf_fintype_sum_eq c

end MeasureTheory.Measure

end
