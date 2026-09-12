/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import StdSimplexMeasure.Measure
public import Pochhammer.BetaIntegral
public import StdSimplexMeasure.PositiveSimplex

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import StdSimplexMeasure.EuclideanCrossSection
import all StdSimplexMeasure.Measure

/-!
# Integrals on the standard simplex

This file develops change-of-coordinates, slicing, permutation, monomial, and aggregation
formulas for integrals with respect to `stdSimplexMeasure`.
-/

open Fintype (card)

public noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]

open scoped Classical

/-- Scaling the free coordinates by `c` divides the Bochner integral by
`c ^ (card ι - 1)`. -/
theorem integral_smul_free_coords
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (c : ℝ) (hc : 0 < c)
    (f : ({j : ι // j ≠ i} → ℝ) → E) :
  ∫ x, f (c • x) ∂volume =
    (c ^ (card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
  let e : ({j : ι // j ≠ i} → ℝ) ≃ₜ ({j : ι // j ≠ i} → ℝ) :=
    Homeomorph.smulOfNeZero c hc.ne'
  have hmap : Measure.map e volume =
      ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume := by
    simpa [e] using volume_map_smul_free_coords i c hc
  calc
    ∫ x, f (c • x) ∂volume = ∫ x, f x ∂Measure.map e volume := by
      simpa [e] using (e.isClosedEmbedding.integral_map f).symm
    _ = ∫ x, f x ∂(ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume) := by rw [hmap]
    _ = (c ^ (card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
      rw [integral_smul_measure]
      simp [(pow_pos hc _).le]

/-- Integration over the standard simplex can be computed in any free-coordinate chart. This is
stated for functions taking values in a normed real vector space. -/
theorem integral_stdSimplex_eq_integral_freeCoords
    [Nonempty ι] (i : ι)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact
    (isClosedEmbedding_stdSimplexCoordMap i).integral_map f

/-- A nonnegative integral over the standard simplex can be computed in any free-coordinate
chart. -/
theorem lintegral_stdSimplex_eq_lintegral_freeCoords
    [Nonempty ι] (i : ι) (f : (ι → ℝ) → ENNReal) :
    ∫⁻ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
      ∫⁻ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.lintegral_map f

/-- Splitting one coordinate from a finite real coordinate space preserves product Lebesgue
measure. -/
private theorem volume_preserving_funSplitAt (i : ι) :
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

/-- In a free-coordinate chart omitting `j`, separating the coordinate corresponding to
`i ≠ j` turns the chart domain into the standard product-coordinate simplex slices. -/
private theorem image_stdSimplexFreeCoords_funSplitAt (i j : ι) (hij : i ≠ j) :
    let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
    Homeomorph.funSplitAt ℝ ii '' stdSimplexFreeCoords j = posSimplexSlices ii 1 := by
  dsimp only
  let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
  change Homeomorph.funSplitAt ℝ ii '' posSimplex {q : ι // q ≠ j} 1 =
    posSimplexSlices ii 1
  exact image_posSimplex_funSplitAt (⟨i, hij⟩ : {q : ι // q ≠ j}) 1

/-- Reindexing the coordinates left after deleting two distinct indices in opposite orders. -/
def stdSimplexDoubleComplementEquiv (i j : ι) (hij : i ≠ j) :
    {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} ≃
      {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} where
  toFun q := ⟨⟨q.val.val, fun h => q.property (Subtype.ext h)⟩,
    fun h => q.val.property (congrArg Subtype.val h)⟩
  invFun q := ⟨⟨q.val.val, fun h => q.property (Subtype.ext h)⟩,
    fun h => q.val.property (congrArg Subtype.val h)⟩
  left_inv q := by ext; rfl
  right_inv q := by ext; rfl

/-- Reindexing by `stdSimplexDoubleComplementEquiv` preserves finite coordinate sums. -/
private theorem sum_stdSimplexDoubleComplementEquiv (i j : ι) (hij : i ≠ j)
    (x : {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} → ℝ) :
    (∑ q : {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}, x q) =
      ∑ q : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩},
        x ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
  rw [Equiv.sum_comp]

/-- The double-complement reindexing sends the unit positive simplex onto itself. -/
private theorem image_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    T '' posSimplex D 1 = posSimplex C 1 := by
  dsimp only
  let e := stdSimplexDoubleComplementEquiv i j hij
  let T := MeasurableEquiv.piCongrLeft (fun _ : _ => ℝ) e
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hxs⟩
    refine ⟨?_, ?_⟩
    · intro q
      change 0 ≤ x (e.symm q)
      exact hx0 (e.symm q)
    · change (∑ q, x (e.symm q)) ≤ 1
      rw [← sum_stdSimplexDoubleComplementEquiv i j hij]
      exact hxs
  · intro hy
    refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
    rcases hy with ⟨hy0, hys⟩
    refine ⟨?_, ?_⟩
    · intro q
      change 0 ≤ y (e q)
      exact hy0 (e q)
    · change (∑ q, y (e q)) ≤ 1
      rw [Equiv.sum_comp]
      exact hys

/-- Integrals over the two double-complement coordinate spaces agree after reindexing. -/
private theorem integral_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ({q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} → ℝ) → E) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    ∫ y in posSimplex C 1, g y = ∫ x in posSimplex D 1, g (T x) := by
  dsimp only
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  have hT := volume_measurePreserving_piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  rw [← image_posSimplex_stdSimplexDoubleComplementEquiv i j hij]
  exact hT.setIntegral_image_emb T.measurableEmbedding g _

/-- Nonnegative integrals over the two double-complement coordinate spaces agree after
reindexing. -/
private theorem lintegral_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j)
    (g : ({q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} → ℝ) → ENNReal) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    ∫⁻ y in posSimplex C 1, g y = ∫⁻ x in posSimplex D 1, g (T x) := by
  dsimp only
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  have hT := volume_measurePreserving_piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  rw [← image_posSimplex_stdSimplexDoubleComplementEquiv i j hij]
  exact ((hT.restrict_image_emb T.measurableEmbedding
    (posSimplex {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} 1)).lintegral_comp_emb
      T.measurableEmbedding g).symm

/-- Fubini disintegration of a positive simplex after separating one coordinate. -/
private theorem integral_posSimplex_split
    {α : Type*} [Fintype α] (i : α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (α → ℝ) → E) (hg : IntegrableOn g (posSimplex α 1)) :
    ∫ x in posSimplex α 1, g x =
      ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ y in posSimplex {j : α // j ≠ i} (1 - t),
          g ((Homeomorph.funSplitAt ℝ i).symm (t, y)) := by
  let e := Homeomorph.funSplitAt ℝ i
  let G : ℝ × ({j : α // j ≠ i} → ℝ) → E := fun p => g (e.symm p)
  have hmp := volume_preserving_funSplitAt i
  have hset : e '' posSimplex α 1 = posSimplexSlices i 1 :=
    image_posSimplex_funSplitAt i 1
  have hGI : IntegrableOn G (posSimplexSlices i 1) (volume.prod volume) := by
    rw [← hset]
    change Integrable G ((volume.prod volume).restrict (e '' posSimplex α 1))
    rw [← (hmp.restrict_image_emb e.measurableEmbedding
      (posSimplex α 1)).integrable_comp_emb e.measurableEmbedding]
    have heq : G ∘ e = g := by
      funext x
      exact congrArg g (e.symm_apply_apply x)
    rw [heq]
    exact hg
  calc
    ∫ x in posSimplex α 1, g x = ∫ p in posSimplexSlices i 1, G p ∂volume.prod volume := by
      rw [← hset]
      convert (hmp.setIntegral_image_emb e.measurableEmbedding G
        (posSimplex α 1)).symm using 1
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg g (e.symm_apply_apply x).symm
    _ = ∫ t, ∫ y, (posSimplexSlices i 1).indicator G (t, y) := by
      rw [← integral_indicator (measurableSet_posSimplexSlices i 1)]
      exact integral_prod _ (hGI.integrable_indicator (measurableSet_posSimplexSlices i 1))
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ y in posSimplex {j : α // j ≠ i} (1 - t),
          g (e.symm (t, y)) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        rw [← integral_indicator (measurableSet_posSimplex _ _)]
        apply integral_congr_ae
        filter_upwards [] with y
        have hy : ((t, y) ∈ posSimplexSlices i 1 ↔
            y ∈ posSimplex {j : α // j ≠ i} (1 - t)) := by
          exact Set.ext_iff.mp (preimage_posSimplexSlices_of_mem i 1 t ht) y
        simp only [Set.indicator_apply]
        simp [hy, G]
      · simp only [Set.indicator_apply, ht, ↓reduceIte]
        rw [integral_eq_zero_of_ae]
        filter_upwards [] with y
        have hy : (t, y) ∉ posSimplexSlices i 1 := by
          intro hmem
          have : y ∈ Prod.mk t ⁻¹' posSimplexSlices i 1 := hmem
          rw [preimage_posSimplexSlices_eq_empty_of_not_mem i 1 t ht] at this
          exact this
        simp [hy]

/-- Tonelli disintegration of a positive simplex after separating one coordinate. Unlike the
Bochner-integral version, this statement requires no prior integrability assumption. -/
private theorem lintegral_posSimplex_split
    {α : Type*} [Fintype α] (i : α) (g : (α → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α 1, g x =
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ y in posSimplex {j : α // j ≠ i} (1 - t),
          g ((Homeomorph.funSplitAt ℝ i).symm (t, y)) := by
  let e := Homeomorph.funSplitAt ℝ i
  let G : ℝ × ({j : α // j ≠ i} → ℝ) → ENNReal := fun p => g (e.symm p)
  have hmp := volume_preserving_funSplitAt i
  have hset : e '' posSimplex α 1 = posSimplexSlices i 1 :=
    image_posSimplex_funSplitAt i 1
  calc
    ∫⁻ x in posSimplex α 1, g x =
        ∫⁻ p in posSimplexSlices i 1, G p ∂volume.prod volume := by
      rw [← hset]
      convert (hmp.restrict_image_emb e.measurableEmbedding
        (posSimplex α 1)).lintegral_comp_emb e.measurableEmbedding G using 1
      apply lintegral_congr
      intro x
      exact congrArg g (e.symm_apply_apply x).symm
    _ = ∫⁻ t, ∫⁻ y, (posSimplexSlices i 1).indicator G (t, y) := by
      rw [← lintegral_indicator (measurableSet_posSimplexSlices i 1)]
      exact lintegral_prod _ ((hg.comp e.symm.measurable).indicator
        (measurableSet_posSimplexSlices i 1)).aemeasurable
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ y in posSimplex {j : α // j ≠ i} (1 - t),
          g (e.symm (t, y)) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
        apply lintegral_congr
        intro y
        have hy : ((t, y) ∈ posSimplexSlices i 1 ↔
            y ∈ posSimplex {j : α // j ≠ i} (1 - t)) := by
          exact Set.ext_iff.mp (preimage_posSimplexSlices_of_mem i 1 t ht) y
        simp only [Set.indicator_apply]
        simp [hy, G]
      · simp only [Set.indicator_apply, ht, ↓reduceIte]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with y
        have hy : (t, y) ∉ posSimplexSlices i 1 := by
          intro hmem
          have : y ∈ Prod.mk t ⁻¹' posSimplexSlices i 1 := hmem
          rw [preimage_posSimplexSlices_eq_empty_of_not_mem i 1 t ht] at this
          exact this
        simp [hy]

/-- Scaling a positive-simplex slice produces the expected power of its radius. -/
private theorem integral_posSimplex_scale
    {α : Type*} [Fintype α] (i : α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : 0 < c) (g : ({j : α // j ≠ i} → ℝ) → E) :
    ∫ y in posSimplex {j : α // j ≠ i} c, g y =
      (c ^ (Fintype.card α - 1)) •
        ∫ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
  let h : ({j : α // j ≠ i} → ℝ) → E :=
    (posSimplex {j : α // j ≠ i} c).indicator g
  have hs : ∀ x : {j : α // j ≠ i} → ℝ,
      x ∈ posSimplex {j : α // j ≠ i} 1 ↔
        c • x ∈ posSimplex {j : α // j ≠ i} c := by
    intro x
    simp only [posSimplex, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => mul_nonneg hc.le (hx q), ?_⟩
      rw [← Finset.mul_sum]
      nlinarith
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx q) hc, ?_⟩
      rw [← Finset.mul_sum] at hsum
      nlinarith
  have hi := integral_smul_free_coords i c hc h
  rw [integral_indicator (measurableSet_posSimplex _ _)] at hi
  have hil : (∫ x, h (c • x)) =
      ∫ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
    rw [← integral_indicator (measurableSet_posSimplex _ _)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [h, Set.indicator_apply]
    rw [if_congr (hs x).symm rfl rfl]
  rw [hil] at hi
  have hc_pow : c ^ (Fintype.card α - 1) ≠ 0 := pow_ne_zero _ hc.ne'
  symm
  rw [hi, smul_inv_smul₀ hc_pow]

/-- Scaling a positive-simplex slice in the nonnegative integral. -/
private theorem lintegral_posSimplex_scale
    {α : Type*} [Fintype α] (i : α) (c : ℝ) (hc : 0 < c)
    (g : ({j : α // j ≠ i} → ℝ) → ENNReal) :
    ∫⁻ y in posSimplex {j : α // j ≠ i} c, g y =
      ENNReal.ofReal (c ^ (Fintype.card α - 1)) *
        ∫⁻ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
  let e : ({j : α // j ≠ i} → ℝ) ≃ᵐ ({j : α // j ≠ i} → ℝ) :=
    (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
  let h : ({j : α // j ≠ i} → ℝ) → ENNReal :=
    (posSimplex {j : α // j ≠ i} c).indicator g
  have hs : ∀ x : {j : α // j ≠ i} → ℝ,
      x ∈ posSimplex {j : α // j ≠ i} 1 ↔
        c • x ∈ posSimplex {j : α // j ≠ i} c := by
    intro x
    simp only [posSimplex, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => mul_nonneg hc.le (hx q), ?_⟩
      rw [← Finset.mul_sum]
      nlinarith
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx q) hc, ?_⟩
      rw [← Finset.mul_sum] at hsum
      nlinarith
  let A : ENNReal := ENNReal.ofReal (c ^ (Fintype.card α - 1))
  have hmap : Measure.map e volume = A⁻¹ • volume := by
    rw [show A⁻¹ = ENNReal.ofReal (c ^ (Fintype.card α - 1))⁻¹ by
      exact (ENNReal.ofReal_inv_of_pos (pow_pos hc _)).symm]
    simpa [e] using volume_map_smul_free_coords i c hc
  have hi : (∫⁻ x, h (c • x)) = A⁻¹ * ∫⁻ x, h x := by
    change (∫⁻ x, h (e x)) = _
    rw [← e.measurableEmbedding.lintegral_map h, hmap, lintegral_smul_measure]
    rfl
  have hA0 : A ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc _)
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
  have hil : (∫⁻ x, h (c • x)) =
      ∫⁻ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
    rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
    apply lintegral_congr
    intro x
    simp only [h, Set.indicator_apply]
    rw [if_congr (hs x).symm rfl rfl]
  rw [← hil, hi, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]

/- Helper theorems towards integral_stdSimplex_split_at -/

/-- Equivalence of the nested-slice coordinate map and the directly scaled coordinate map. -/
theorem stdSimplexCoordMap_split_eq (i j : ι) (hij : i ≠ j)
    (t : ℝ) (v : {q : ι // q ≠ i} → ℝ) (h_sum : ∑ q, v q = 1) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let e := stdSimplexDoubleComplementEquiv i j hij
    stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm
      (t, fun q : C ↦ (1 - t) * v (e.symm q))) =
    stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) := by
  dsimp only
  let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  let e := stdSimplexDoubleComplementEquiv i j hij
  let y : {q : {q : ι // q ≠ j} // q ≠ ii} → ℝ :=
    fun q => (1 - t) * v (e.symm q)
  let z := (Homeomorph.funSplitAt ℝ ii).symm (t, y)
  have hz : (Homeomorph.funSplitAt ℝ ii) z = (t, y) :=
    (Homeomorph.funSplitAt ℝ ii).apply_symm_apply (t, y)
  have hzself : z ii = t := congrArg Prod.fst hz
  have hzrest : (fun q : {q : {q : ι // q ≠ j} // q ≠ ii} => z q) = y :=
    congrArg Prod.snd hz
  have hsum_rest : (∑ q : {q : {q : ι // q ≠ i} // q ≠ jj}, v q) = 1 - v jj := by
    have h := Fintype.sum_eq_add_sum_subtype_ne v jj
    rw [h_sum] at h
    linarith
  ext q
  by_cases hqi : q = i
  · subst q
    rw [stdSimplexCoordMap_apply_of_ne j i hij, stdSimplexCoordMap_apply_self]
    change z ii = 1 - ∑ q, (1 - t) * v q
    rw [hzself, ← Finset.mul_sum, h_sum]
    ring
  by_cases hqj : q = j
  · subst q
    rw [stdSimplexCoordMap_apply_self, stdSimplexCoordMap_apply_of_ne i j hij.symm]
    change 1 - ∑ q, z q = (1 - t) * v jj
    rw [Fintype.sum_eq_add_sum_subtype_ne z ii, hzself, hzrest]
    simp only [y, ← Finset.mul_sum]
    have hreindex : (∑ q, v (e.symm q)) =
        ∑ q : {q : {q : ι // q ≠ i} // q ≠ jj}, v q := by
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [hreindex, hsum_rest]
    ring
  · rw [stdSimplexCoordMap_apply_of_ne j q hqj,
      stdSimplexCoordMap_apply_of_ne i q hqi]
    change z ⟨q, hqj⟩ = (1 - t) * v ⟨q, hqi⟩
    have hne : (⟨q, hqj⟩ : {q : ι // q ≠ j}) ≠ ii := by
      intro h
      exact hqi (congrArg Subtype.val h)
    rw [congrFun hzrest ⟨⟨q, hqj⟩, hne⟩]
    rfl

/-- Evaluates the inner sliced integral by reindexing the double-complement and scaling. -/
theorem integral_posSimplex_inner_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : ι) (hij : i ≠ j) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (f : (ι → ℝ) → E) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    ∫ y in posSimplex C (1 - t),
      f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))) =
    ((1 - t) ^ (Fintype.card ι - 2)) •
      ∫ v in stdSimplex ℝ {q : ι // q ≠ i},
        f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) ∂stdSimplexMeasure := by
  dsimp only
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  have hs := integral_posSimplex_scale
    (⟨i, hij⟩ : {q : ι // q ≠ j}) (1 - t) hc
    (fun y => f (stdSimplexCoordMap j
      ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))))
  convert hs using 1
  · congr <;> funext q <;> apply Subsingleton.elim
  · have hcard : Fintype.card {q : ι // q ≠ j} - 1 = Fintype.card ι - 2 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    rw [hcard]
    congr 1
    symm
    have hr := integral_posSimplex_stdSimplexDoubleComplementEquiv i j hij
      (fun y => f (stdSimplexCoordMap j
        ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, (1 - t) • y))))
    convert hr using 1
    · congr <;> funext q <;> apply Subsingleton.elim
    · let _ : Nonempty {q : ι // q ≠ i} := ⟨jj⟩
      rw [integral_stdSimplex_eq_integral_freeCoords jj]
      convert MeasureTheory.integral_congr_ae (μ := volume.restrict (stdSimplexFreeCoords jj)) ?_ using 1
      · congr <;> funext q <;> apply Subsingleton.elim
      filter_upwards [] with x
      apply congrArg f
      symm
      have hfun :
          (1 - t) • (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
            (stdSimplexDoubleComplementEquiv i j hij)) x =
            fun q => (1 - t) * stdSimplexCoordMap jj x
              ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
        funext q
        rw [stdSimplexCoordMap_apply_of_ne jj _
          ((stdSimplexDoubleComplementEquiv i j hij).symm q).property]
        rfl
      rw [hfun]
      exact stdSimplexCoordMap_split_eq i j hij t (stdSimplexCoordMap jj x)
        (sum_stdSimplexCoordMap jj x)

/-- Evaluates a nonnegative inner sliced integral by reindexing the double complement and
scaling. -/
theorem lintegral_posSimplex_inner_slice
    (i j : ι) (hij : i ≠ j) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (f : (ι → ℝ) → ENNReal) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    ∫⁻ y in posSimplex C (1 - t),
      f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))) =
    ENNReal.ofReal ((1 - t) ^ (Fintype.card ι - 2)) *
      ∫⁻ v in stdSimplex ℝ {q : ι // q ≠ i},
        f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) ∂stdSimplexMeasure := by
  dsimp only
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  have hs := lintegral_posSimplex_scale
    (⟨i, hij⟩ : {q : ι // q ≠ j}) (1 - t) hc
    (fun y => f (stdSimplexCoordMap j
      ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))))
  convert hs using 1
  · congr <;> funext q <;> apply Subsingleton.elim
  · have hcard : Fintype.card {q : ι // q ≠ j} - 1 = Fintype.card ι - 2 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    rw [hcard]
    congr 1
    symm
    have hr := lintegral_posSimplex_stdSimplexDoubleComplementEquiv i j hij
      (fun y => f (stdSimplexCoordMap j
        ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, (1 - t) • y))))
    convert hr using 1
    · congr <;> funext q <;> apply Subsingleton.elim
    · let _ : Nonempty {q : ι // q ≠ i} := ⟨jj⟩
      rw [lintegral_stdSimplex_eq_lintegral_freeCoords jj]
      convert MeasureTheory.lintegral_congr (μ :=
        volume.restrict (stdSimplexFreeCoords jj)) ?_ using 1
      · congr <;> funext q <;> apply Subsingleton.elim
      intro x
      apply congrArg f
      symm
      have hfun :
          (1 - t) • (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
            (stdSimplexDoubleComplementEquiv i j hij)) x =
            fun q => (1 - t) * stdSimplexCoordMap jj x
              ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
        funext q
        rw [stdSimplexCoordMap_apply_of_ne jj _
          ((stdSimplexDoubleComplementEquiv i j hij).symm q).property]
        rfl
      rw [hfun]
      exact stdSimplexCoordMap_split_eq i j hij t (stdSimplexCoordMap jj x)
        (sum_stdSimplexCoordMap jj x)

/-- Tonelli reduction of a nonnegative integral over the standard simplex after separating one
coordinate. Unlike `integral_stdSimplex_split_at`, no integrability hypothesis is required. -/
public theorem lintegral_stdSimplex_split_at
    (i : ι) [Nontrivial ι] (f : (ι → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) ^ (card ι - 2)) *
          ∫⁻ v in stdSimplex ℝ {j // j ≠ i},
            f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j)) ∂stdSimplexMeasure := by
  obtain ⟨j, hji⟩ := exists_ne i
  rw [lintegral_stdSimplex_eq_lintegral_freeCoords j]
  change (∫⁻ x in posSimplex {q : ι // q ≠ j} 1,
    f (stdSimplexCoordMap j x)) = _
  rw [lintegral_posSimplex_split (⟨i, hji.symm⟩ : {q : ι // q ≠ j})]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
    have htIco : t ∈ Set.Ico (0 : ℝ) 1 := by
      exact heq.mpr htIcc
    convert lintegral_posSimplex_inner_slice i j hji.symm t htIco f using 1
    congr
    funext q
    apply Subsingleton.elim
    funext q
    apply Subsingleton.elim
    funext y
    congr
    funext a b
    apply Subsingleton.elim
  · exact hf.comp (continuous_stdSimplexCoordMap j).measurable

/-- Evaluates an integral over the standard simplex by separating out the `i`-th coordinate.
This theorem provides the standard Fubini reduction (integration by slices) for the simplex.
It expresses the integral of a function `f` over the $(k-1)$-simplex (where $k$ is `card ι`)
as an iterated integral:
1. An outer 1D integral over the isolated coordinate $t \in [0, 1]$.
2. An inner integral over the $(k-2)$-simplex of the remaining coordinates $v$.
Because the remaining coordinates are subject to the constraint $\sum v = 1 - t$, they are
scaled by $(1 - t)$ to map them back to a standard unit $(k-1)$-simplex.
This change of variables introduces a Jacobian determinant factor of $(1 - t)^{k - 2}$. -/
public theorem integral_stdSimplex_split_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) [Nontrivial ι]
    (f : (ι → ℝ) → E)
    (hf : IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ t in Set.Icc (0 : ℝ) 1,
      ((1 - t) ^ (card ι - 2)) •
      ∫ v in stdSimplex ℝ {j // j ≠ i}, f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j))
        ∂stdSimplexMeasure := by
  obtain ⟨j, hji⟩ := exists_ne i
  have hg : IntegrableOn (fun x => f (stdSimplexCoordMap j x))
      (stdSimplexFreeCoords j) := by
    have hfm := hf
    change Integrable f (stdSimplexMeasure.restrict (stdSimplex ℝ ι)) at hfm
    rw [stdSimplexMeasure_restrict_stdSimplex j] at hfm
    change Integrable (fun x => f (stdSimplexCoordMap j x))
      (volume.restrict (stdSimplexFreeCoords j))
    exact (isClosedEmbedding_stdSimplexCoordMap j).measurableEmbedding.integrable_map_iff.mp hfm
  rw [integral_stdSimplex_eq_integral_freeCoords j]
  change (∫ x in posSimplex {q : ι // q ≠ j} 1, f (stdSimplexCoordMap j x)) = _
  rw [integral_posSimplex_split (⟨i, hji.symm⟩ : {q : ι // q ≠ j}) _ hg]
  simp_rw [integral_Icc_eq_integral_Ico]
  have h_inner : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      (∫ y in posSimplex {q : {q : ι // q ≠ j} // q ≠ ⟨i, hji.symm⟩} (1 - t),
        f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hji.symm⟩).symm (t, y)))) =
      ((1 - t) ^ (card ι - 2)) •
        ∫ v in stdSimplex ℝ {j // j ≠ i},
          f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j)) ∂stdSimplexMeasure := by
    filter_upwards [self_mem_ae_restrict (μ := volume) measurableSet_Ico] with t ht
    exact integral_posSimplex_inner_slice i j hji.symm t ht f
  -- The displayed nested subtype types differ only in synthesized decidability data.
  convert MeasureTheory.integral_congr_ae h_inner using 1
  congr
  funext t
  congr
  · funext q
    apply Subsingleton.elim
  · funext q
    apply Subsingleton.elim
  · funext y
    congr
    funext a b
    apply Subsingleton.elim

/-- The integral of a function over the standard simplex is invariant under coordinate
permutations. -/
theorem integral_stdSimplex_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Equiv.Perm ι) (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f (u ∘ σ) ∂stdSimplexMeasure =
    ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure := by
  have hp := measurePreserving_stdSimplexMeasure_perm σ
  have he : MeasurableEmbedding (fun u : ι → ℝ => u ∘ σ) := by
    apply (continuous_pi (fun j => continuous_apply (σ j))).measurableEmbedding
    intro u v huv
    funext j
    have := congrFun huv (σ.symm j)
    simpa using this
  have hr := hp.restrict_preimage_emb he (stdSimplex ℝ ι)
  rw [preimage_stdSimplex_perm] at hr
  exact hr.integral_comp he f

/-- Continuous functions are integrable on the standard simplex. -/
theorem ContinuousOn.integrableOn_stdSimplex
    [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure := by
  apply hf.integrableOn_of_subset_isCompact
    (isCompact_stdSimplex ℝ ι)
    (isClosed_stdSimplex ℝ ι).measurableSet
    Set.Subset.rfl
  rw [← Measure.restrict_apply_univ]
  exact measure_ne_top _ _

/-- The integral of `f` over the standard simplex depends only on the values of `f` on
the standard simplex. -/
theorem integral_stdSimplex_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : (ι → ℝ) → E}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
      ∫ u in stdSimplex ℝ ι, g u ∂stdSimplexMeasure := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [self_mem_ae_restrict
      (μ := stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
  exact hfg hu

/-- For a single-point index set, the integral over the simplex reduces to evaluation at the
all-ones vector. (Base case for induction.) -/
theorem integral_stdSimplex_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Unique ι] (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure = f (fun _ ↦ 1) := by
  classical
  rw [stdSimplexMeasure_unique]
  change ∫ u, f u ∂(dirac (fun _ : ι => (1 : ℝ))).restrict (stdSimplex ℝ ι) = _
  rw [MeasureTheory.restrict_dirac' (isClosed_stdSimplex ℝ ι).measurableSet]
  have hmem : (fun _ : ι => (1 : ℝ)) ∈ stdSimplex ℝ ι := by simp [stdSimplex]
  rw [if_pos hmem]
  exact MeasureTheory.integral_dirac f (fun _ : ι => (1 : ℝ))

/-- Reduce a monomial integral on a nontrivial simplex to the monomial integral on the simplex
obtained by deleting coordinate `i`. -/
theorem integral_stdSimplex_explicit_monomial_succ [Nontrivial ι] (i : ι) (m : ι → ℕ) :
  ∫ u in stdSimplex ℝ ι, (∏ j, u j ^ m j) ∂stdSimplexMeasure =
    (Nat.factorial (m i) * Nat.factorial (card ι + (∑ j, m j) - 2 - m i)
      / Nat.factorial (card ι + ∑ j, m j - 1) : ℝ)
      * ∫ u in stdSimplex ℝ {j : ι // j ≠ i}, (∏ j, u j ^ m j.val) ∂stdSimplexMeasure := by
  have hf : IntegrableOn (fun u : ι → ℝ => ∏ j, u j ^ m j)
      (stdSimplex ℝ ι) stdSimplexMeasure := by
    apply ContinuousOn.integrableOn_stdSimplex
    fun_prop
  rw [integral_stdSimplex_split_at i _ hf]
  have hfactor (t : ℝ) (v : {j : ι // j ≠ i} → ℝ)
      (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
      (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j) =
        t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hvsum : ∑ q, v q = 1 := hv.2
    rw [stdSimplexCoordMap_apply_self, ← Finset.mul_sum, hvsum]
    simp only [mul_one, sub_sub_cancel]
    have hprod :
        (∏ q : {j : ι // j ≠ i},
          stdSimplexCoordMap i (fun q => (1 - t) * v q) q.val ^ m q.val) =
        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
      calc
        _ = ∏ q : {j : ι // j ≠ i}, ((1 - t) * v q) ^ m q.val := by
          apply Finset.prod_congr rfl
          intro q _
          rw [stdSimplexCoordMap_apply_of_ne i q.val q.property]
        _ = _ := by
          simp_rw [mul_pow, Finset.prod_mul_distrib,
            ← Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    ring
  have hinner (t : ℝ) :
      ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
          (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j)
          ∂stdSimplexMeasure =
        (t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) *
          ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
            (∏ q, v q ^ m q.val) ∂stdSimplexMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ _).measurableSet] with v hv
    exact hfactor t v hv
  simp_rw [hinner]
  simp only [smul_eq_mul]
  have hcard : 2 ≤ card ι := Nat.succ_le_iff.mpr Fintype.one_lt_card
  have hsum : ∑ j, m j = m i + ∑ q : {j : ι // j ≠ i}, m q.val :=
    Fintype.sum_eq_add_sum_subtype_ne m i
  let b : ℕ := card ι - 2 + ∑ q : {j : ι // j ≠ i}, m q.val
  have hb : card ι + (∑ j, m j) - 2 - m i = b := by
    rw [hsum]
    dsimp [b]
    omega
  have hden : card ι + (∑ j, m j) - 1 = m i + b + 1 := by
    rw [hsum]
    dsimp [b]
    omega
  let A : ℝ := ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
    (∏ q, v q ^ m q.val) ∂stdSimplexMeasure
  calc
    ∫ t in Set.Icc (0 : ℝ) 1,
        (1 - t) ^ (card ι - 2) *
          ((t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) * A) =
        A * ∫ t in Set.Icc (0 : ℝ) 1, t ^ m i * (1 - t) ^ b := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show b = (card ι - 2) + ∑ q : {j : ι // j ≠ i}, m q.val by rfl,
        pow_add]
      ring
    _ = A * ((Nat.factorial (m i) * Nat.factorial b : ℝ) /
        Nat.factorial (m i + b + 1)) := by
      rw [integral_Icc_pow_mul_one_sub_pow]
    _ = _ := by
      rw [hb, hden]
      dsimp [A]
      ring

/-- The integral of a monomial with natural exponents over the standard simplex. -/
theorem integral_stdSimplex_explicit_monomial (m : ι → ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, (∏ i, u i ^ m i) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  classical
  suffices h : ∀ n : ℕ, ∀ (α : Type u) [Fintype α], card α = n →
      ∀ (a : α → ℕ), Nonempty α →
        ∫ u in stdSimplex ℝ α, (∏ j, u j ^ a j) ∂stdSimplexMeasure =
          (∏ j, Nat.factorial (a j)) /
            (Nat.factorial (card α + (∑ j, a j) - 1) : ℝ) by
    exact h (card ι) ι rfl m inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro α _ hα a hne
      let : Nonempty α := hne
      cases subsingleton_or_nontrivial α with
      | inl hs =>
          let : Unique α := ⟨⟨Classical.choice hne⟩, fun x => hs.elim x _⟩
          rw [integral_stdSimplex_unique]
          simp
          field_simp
      | inr hn =>
          let : Nontrivial α := hn
          let i : α := Classical.choice hne
          rw [integral_stdSimplex_explicit_monomial_succ i a]
          have hlt : card {j : α // j ≠ i} < n := by
            rw [← hα, Fintype.card_subtype_compl]
            exact Nat.sub_lt (Fintype.card_pos_iff.mpr hne) Nat.zero_lt_one
          have hsub : Nonempty {j : α // j ≠ i} := by
            obtain ⟨j, hj⟩ := exists_ne i
            exact ⟨⟨j, hj⟩⟩
          rw [ih (card {j : α // j ≠ i}) hlt {j : α // j ≠ i} rfl
            (fun j => a j.val) hsub]
          have hsum : ∑ j, a j = a i + ∑ q : {j : α // j ≠ i}, a q.val :=
            Fintype.sum_eq_add_sum_subtype_ne a i
          have hcardsub : card {j : α // j ≠ i} = card α - 1 := by
            simpa using card_subtype_compl (fun j : α => j = i)
          have hidx : card {j : α // j ≠ i} +
              (∑ q : {j : α // j ≠ i}, a q.val) - 1 =
              card α + (∑ j, a j) - 2 - a i := by
            rw [hcardsub, hsum]
            have hc : 2 ≤ card α := Nat.succ_le_iff.mpr Fintype.one_lt_card
            omega
          rw [hidx, Fintype.prod_eq_mul_prod_subtype_ne _ i]
          field_simp
          norm_cast

/-- The integral of the constant function 1 over the standard simplex. -/
theorem integral_stdSimplex_constant [Nonempty ι] :
    ∫ _ in stdSimplex ℝ ι, (1 : ℝ) ∂stdSimplexMeasure =
      1 / (Nat.factorial (card ι - 1) : ℝ) := by
  rw [MeasureTheory.setIntegral_const, Measure.real, stdSimplexMeasure_stdSimplex_toReal]
  ring

/-- The integral of a `MvPolynomial` monomial over the standard simplex. -/
theorem integral_stdSimplex_MvPolynomial_monomial (m : ι →₀ ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, m.prod (fun i n => u i ^ n) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  simp_rw [m.prod_fintype _ fun _ ↦ pow_zero _]
  exact integral_stdSimplex_explicit_monomial (⇑m)

/-- Transformation of integrals under coordinate aggregation. The measurability hypothesis is
stated for the weighted target measure, which is exactly the push-forward measure occurring in
the change of variables. -/
theorem integral_stdSimplex_comp_aggregate
    {κ : Type*} [Fintype κ]
    (f : ι → κ) (hf : Function.Surjective f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (κ → ℝ) → E)
    (hg : AEStronglyMeasurable g
      (((stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)).withDensity
        (stdSimplexAggregateDensity f))) :
    ∫ u in stdSimplex ℝ ι,
        g (stdSimplexAggregate f u) ∂stdSimplexMeasure
      =
    ∫ v in stdSimplex ℝ κ,
        (∏ k,
          v k ^ (stdSimplexAggregateFiberCard f k - 1) /
            Nat.factorial
              (stdSimplexAggregateFiberCard f k - 1)) •
          g v
        ∂stdSimplexMeasure := by
  classical
  let μ := (stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let ν := (stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)
  let d := stdSimplexAggregateDensity f
  have hagg : Measurable (stdSimplexAggregate (R := ℝ) f) := by
    exact (FunOnFinite.continuous_linearMap ℝ ℝ f).measurable
  have hd : Measurable d := by
    unfold d stdSimplexAggregateDensity
    fun_prop
  have hd_top : ∀ v, d v ≠ ⊤ := by
    intro v
    unfold d stdSimplexAggregateDensity
    apply ENNReal.prod_ne_top
    intro k _
    exact ENNReal.div_ne_top (by simp) (by simp [Nat.factorial_ne_zero])
  have hmeasure : Measure.map (stdSimplexAggregate f) μ = ν.withDensity d := by
    simpa only [μ, ν, d] using
      (map_stdSimplexMeasure_restrict_stdSimplex_aggregate f hf)
  have hgmap : AEStronglyMeasurable g (Measure.map (stdSimplexAggregate f) μ) := by
    rw [hmeasure]
    exact hg
  have hd_lt : ∀ᵐ v ∂ν, d v < ⊤ :=
    Filter.Eventually.of_forall fun v => lt_top_iff_ne_top.mpr (hd_top v)
  calc
    ∫ u, g (stdSimplexAggregate f u) ∂μ =
        ∫ v, g v ∂Measure.map (stdSimplexAggregate f) μ := by
      exact (integral_map hagg.aemeasurable hgmap).symm
    _ = ∫ v, g v ∂ν.withDensity d := by
      rw [hmeasure]
    _ = ∫ v, (d v).toReal • g v ∂ν := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hd_lt]
    _ = ∫ v in stdSimplex ℝ κ,
        (∏ k, v k ^ (stdSimplexAggregateFiberCard f k - 1) /
          Nat.factorial (stdSimplexAggregateFiberCard f k - 1)) • g v
          ∂stdSimplexMeasure := by
      apply integral_congr_ae
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ κ).measurableSet
      filter_upwards [hmem] with v hv
      congr 1
      unfold d stdSimplexAggregateDensity
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro k _
      rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      · simp
      · exact hv.1 k

end MeasureTheory

end StdSimplexIntegral
