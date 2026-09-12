/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import StdSimplexMeasure.CoordinateRealization

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Dirac
import StdSimplexMeasure.PositiveSimplex

/-!
# Coordinate measure on the standard simplex

This file defines the coordinate-normalized measure on the affine hull of the real standard
simplex. It proves independence of the omitted coordinate, permutation invariance, the
simplex-volume formula, boundary-nullity, and the push-forward formula for coordinate
aggregation. This coordinate measure differs by a dimension-dependent constant from the
Euclidean Hausdorff measure on the affine hull.
-/

public noncomputable section StdSimplexCoordinateMeasure

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- Density associated with the cardinalities of the fibers of a coordinate aggregation map. -/
def stdSimplexAggregateDensity
    {κ : Type*} [Fintype κ] (f : ι → κ) (v : κ → ℝ) : ENNReal := by
  classical
  exact ∏ k,
      (ENNReal.ofReal (v k)) ^
          (stdSimplexAggregateFiberCard f k - 1) /
        (Nat.factorial
          (stdSimplexAggregateFiberCard f k - 1) : ENNReal)

/-- For a surjective aggregation, the total degree of the aggregation density is the difference
between the dimensions of the source and target affine coordinate spaces. -/
theorem sum_stdSimplexAggregateFiberCard_sub_one
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f) :
    ∑ k, (stdSimplexAggregateFiberCard f k - 1) =
      Fintype.card ι - Fintype.card κ := by
  have hpos : ∀ k, 1 ≤ stdSimplexAggregateFiberCard f k := fun k =>
    stdSimplexAggregateFiberCard_pos hf k
  have hsum : (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + Fintype.card κ =
      Fintype.card ι := by
    rw [← sum_stdSimplexAggregateFiberCard f]
    calc
      (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + Fintype.card κ =
          (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + ∑ _k : κ, 1 := by simp
      _ = ∑ k, ((stdSimplexAggregateFiberCard f k - 1) + 1) :=
        Finset.sum_add_distrib.symm
      _ = ∑ k, stdSimplexAggregateFiberCard f k := by
        apply Finset.sum_congr rfl
        intro k _
        exact Nat.sub_add_cancel (hpos k)
  omega

/-- The coordinate map is measurable. -/
theorem measurable_stdSimplexCoordMap (i : ι) :
    Measurable (stdSimplexCoordMap (R := ℝ) i) :=
  (continuous_stdSimplexCoordMap i).measurable

/-- Lebesgue measure pushed forward from the free coordinates omitting i. -/
def stdSimplexMeasureAt (i : ι) : Measure (ι → ℝ) := by
  classical
  exact Measure.map (stdSimplexCoordMap (R := ℝ) i) volume

/-- The Lebesgue measure is homogeneous of degree `(Fintype.card ι - 1)` in the free coordinates. -/
theorem volume_map_smul_free_coords (i : ι) (c : ℝ) (hc : 0 < c) :
    Measure.map (c • · : ({j : ι // j ≠ i} → ℝ) → ({j : ι // j ≠ i} → ℝ)) volume =
      ENNReal.ofReal (c ^ (Fintype.card ι - 1))⁻¹ • volume := by
  let f : ({j : ι // j ≠ i} → ℝ) →ₗ[ℝ] ({j : ι // j ≠ i} → ℝ) :=
    c • LinearMap.id
  have hf : LinearMap.det f ≠ 0 := by
    simp [f, hc.ne']
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hf
  change Measure.map f volume = _
  simpa [f, abs_of_pos hc, Fintype.card_subtype_compl,
    ENNReal.ofReal_inv_of_pos (pow_pos hc _)] using hmap

/-- Coordinate explicit form of `stdSimplexMeasureAt`. -/
theorem stdSimplexMeasureAt_eq_map_piSplitAt_symm (i : ι) :
    stdSimplexMeasureAt i =
      Measure.map (Homeomorph.piSplitAt i (fun _ => ℝ)).symm
        (Measure.map (fun x : {j : ι // j ≠ i} → ℝ => (1 - ∑ q, x q, x)) volume) := by
  unfold stdSimplexMeasureAt stdSimplexCoordMap
  rw [Measure.map_map]
  · rfl
  · exact (Homeomorph.piSplitAt i (fun _ => ℝ)).symm.measurable
  · fun_prop

/-- The absolute determinant of uniform scaling on the free-coordinate space. -/
private lemma stdSimplexScaleMap_det (t : ℝ) (i : ι) :
    abs (LinearMap.det ((1 - t) • (LinearMap.id : ({j // j ≠ i} → ℝ) →ₗ[ℝ] _)))
      = abs (1 - t) ^ (Fintype.card ι - 1) := by
  simp [LinearMap.det_smul, Fintype.card_subtype_compl, abs_pow]

/-- Pushing `stdSimplexMeasureAt (σ i)` forward along `σ` gives `stdSimplexMeasureAt i`. -/
theorem stdSimplexMeasureAt_map_perm (i : ι) (σ : Equiv.Perm ι) :
  Measure.map (fun u => u ∘ σ)
    (stdSimplexMeasureAt (σ i)) = stdSimplexMeasureAt i := by
  let e : {j : ι // j ≠ i} ≃ {j : ι // j ≠ σ i} := {
    toFun j := ⟨σ j, fun h => j.property (σ.injective h)⟩
    invFun j := ⟨σ.symm j, fun h => j.property (by simpa using congrArg σ h)⟩
    left_inv j := by ext; simp
    right_inv j := by ext; simp
  }
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {j : ι // j ≠ i} => ℝ) e.symm
  have hT : Measure.map T volume = volume :=
    (volume_measurePreserving_piCongrLeft
      (fun _ : {j : ι // j ≠ i} => ℝ) e.symm).map_eq
  unfold stdSimplexMeasureAt
  calc
    Measure.map (fun u => u ∘ σ) (Measure.map (stdSimplexCoordMap (σ i)) volume) =
        Measure.map ((fun u => u ∘ σ) ∘ stdSimplexCoordMap (σ i)) volume := by
          exact Measure.map_map
            (continuous_pi (fun j => continuous_apply (σ j)) |>.measurable)
            (measurable_stdSimplexCoordMap (σ i))
    _ = Measure.map (stdSimplexCoordMap i ∘ T) volume := by
      congr 1
      funext x
      have hTx : T x = fun ⟨j, hj⟩ => x ⟨σ j, fun h => hj (σ.injective h)⟩ := by
        funext j
        change T x j = x (e j)
        rw [show j = e.symm (e j) by simp]
        rw [MeasurableEquiv.piCongrLeft_apply_apply]
        exact congrArg x (e.apply_symm_apply (e j)).symm
      change stdSimplexCoordMap (σ i) x ∘ σ = stdSimplexCoordMap i (T x)
      rw [hTx]
      exact stdSimplexCoordMap_comp_perm i σ x
    _ = Measure.map (stdSimplexCoordMap i) (Measure.map T volume) := by
      exact (Measure.map_map (measurable_stdSimplexCoordMap i) T.measurable).symm
    _ = Measure.map (stdSimplexCoordMap i) volume := by rw [hT]

/-- Pushing `stdSimplexMeasureAt i` forward along the transposition `swap i j` gives
`stdSimplexMeasureAt j`. -/
theorem stdSimplexMeasureAt_swap (i j : ι) :
    Measure.map (fun x => x ∘ Equiv.swap i j) (stdSimplexMeasureAt i) =
      stdSimplexMeasureAt j := by
  simpa [Equiv.swap_apply_def] using
    (stdSimplexMeasureAt_map_perm j (Equiv.swap i j))

/-- The affine free-coordinate change induced by swapping two ambient coordinates preserves
Lebesgue measure. -/
private theorem map_stdSimplexFreeCoordSwap_volume (i j : ι) (hij : i ≠ j) :
    Measure.map (stdSimplexFreeCoordSwap (R := ℝ) i j hij) volume = volume := by
  let α := {q : ι // q ≠ i}
  let ji : α := ⟨j, Ne.symm hij⟩
  let L := stdSimplexFreeCoordSwapLinear (R := ℝ) i j hij
  have hLinv : L.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext q
    by_cases hq : q = ji
    · subst q
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      change (if ji = ji then -∑ q, L x q else L x ji) = x ji
      rw [if_pos rfl, sum_stdSimplexFreeCoordSwapLinear]
      simp only [neg_neg]
      congr 1
    · simp [L, stdSimplexFreeCoordSwapLinear, ji, hq]
  have hdet_sq : LinearMap.det L * LinearMap.det L = 1 := by
    rw [← LinearMap.det_comp, hLinv, LinearMap.det_id]
  have hdet_abs : |LinearMap.det L| = 1 := by
    have ha : |LinearMap.det L| ^ 2 = 1 := by
      rw [sq_abs]
      nlinarith
    nlinarith [abs_nonneg (LinearMap.det L)]
  have hmapL : Measure.map L volume = volume := by
    have hdet_ne : LinearMap.det L ≠ 0 := by
      intro h
      simp [h] at hdet_abs
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet_ne]
    simp [abs_inv, hdet_abs]
  let c : α → ℝ := fun q => if q = ji then 1 else 0
  rw [show stdSimplexFreeCoordSwap i j hij = (fun y => c + y) ∘ L by rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hmapL]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self c

/-- The coordinate measure is independent of the chosen special coordinate. -/
theorem stdSimplexMeasureAt_eq (i j : ι) :
    stdSimplexMeasureAt i = stdSimplexMeasureAt j := by
  by_cases hij : i = j
  · subst j
    rfl
  have hswap : Measure.map (fun u : ι → ℝ => u ∘ Equiv.swap i j)
      (stdSimplexMeasureAt i) = stdSimplexMeasureAt i := by
    unfold stdSimplexMeasureAt
    calc
      Measure.map (fun u : ι → ℝ => u ∘ Equiv.swap i j)
          (Measure.map (stdSimplexCoordMap i) volume) =
          Measure.map ((fun u : ι → ℝ => u ∘ Equiv.swap i j) ∘
            stdSimplexCoordMap i) volume :=
        Measure.map_map (by fun_prop) (measurable_stdSimplexCoordMap i)
      _ = Measure.map (stdSimplexCoordMap i ∘ stdSimplexFreeCoordSwap i j hij) volume := by
        rw [stdSimplexCoordMap_comp_freeCoordSwap i j hij]
      _ = Measure.map (stdSimplexCoordMap i)
          (Measure.map (stdSimplexFreeCoordSwap i j hij) volume) :=
        (Measure.map_map (measurable_stdSimplexCoordMap i)
          (continuous_stdSimplexFreeCoordSwap i j hij).measurable).symm
      _ = Measure.map (stdSimplexCoordMap i) volume := by
        rw [map_stdSimplexFreeCoordSwap_volume i j hij]
  exact hswap.symm.trans (stdSimplexMeasureAt_swap i j)

/-- The coordinate Lebesgue measure on `stdSimplexAffineSet`. When `ι` is empty the measure
is zero; otherwise it is the push-forward of Lebesgue measure from any set of free
coordinates. -/
def stdSimplexMeasure :
    Measure (ι → ℝ) := by
  by_cases h : Nonempty ι
  · exact stdSimplexMeasureAt (Classical.choice h)
  · exact 0

/-- `stdSimplexMeasure` equals `stdSimplexMeasureAt i`, for any `i`. -/
theorem stdSimplexMeasure_eq_at [Nonempty ι] (i : ι) :
    stdSimplexMeasure (ι := ι) = stdSimplexMeasureAt i := by
  unfold stdSimplexMeasure
  rw [dif_pos (inferInstance : Nonempty ι)]
  exact stdSimplexMeasureAt_eq _ i

/-- The coordinate map pushes the restricted volume on the free coordinates to the restricted
simplex measure. -/
theorem stdSimplexMeasure_restrict_stdSimplex
    [Nonempty ι] (i : ι) :
    (stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι) =
      Measure.map (stdSimplexCoordMap i)
        (volume.restrict (stdSimplexFreeCoords i)) := by
  rw [stdSimplexMeasure_eq_at i]
  unfold stdSimplexMeasureAt
  rw [Measure.restrict_map
    (measurable_stdSimplexCoordMap i)
    (isClosed_stdSimplex ℝ ι).measurableSet]
  rw [preimage_stdSimplexCoordMap]

/-- `stdSimplexMeasure` is zero when `ι` is empty. -/
@[simp] theorem stdSimplexMeasure_empty [IsEmpty ι] :
    stdSimplexMeasure (ι := ι) = 0 := by
  unfold stdSimplexMeasure
  exact dif_neg (not_nonempty_iff.mpr inferInstance)

/-- `stdSimplexMeasure` is a `SigmaFinite` measure. -/
instance sigmaFinite_stdSimplexMeasure :
    SigmaFinite (stdSimplexMeasure (ι := ι)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      rw [stdSimplexMeasure_empty]
      infer_instance
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.sigmaFinite_map

/-- For a type with a unique element, the pushforward measure at that element is a Dirac mass
at the all-ones point. -/
@[simp] theorem stdSimplexMeasureAt_of_unique [Unique ι] (i : ι) :
    stdSimplexMeasureAt i = dirac (fun _ ↦ (1 : ℝ)) := by
  let : IsEmpty {j : ι // j ≠ i} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  unfold stdSimplexMeasureAt
  rw [Measure.volume_pi_eq_dirac]
  rw [Measure.map_dirac' (measurable_stdSimplexCoordMap i)]
  congr 1
  funext j
  have hji : j = i := Subsingleton.elim _ _
  subst j
  simp

/-- Restating `stdSimplexMeasureAt_of_unique` in terms of `stdSimplexMeasure`. -/
theorem stdSimplexMeasure_unique [Unique ι] :
    stdSimplexMeasure (ι := ι) = dirac (fun _ ↦ (1 : ℝ)) := by
  rw [stdSimplexMeasure_eq_at default, stdSimplexMeasureAt_of_unique]

/-- The coordinate Lebesgue measure is supported on `stdSimplexAffineSet`. -/
theorem stdSimplexMeasure_restrict_stdSimplexAffineSet :
  stdSimplexMeasure (ι := ι) =
    stdSimplexMeasure.restrict stdSimplexAffineSet := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      symm
      rw [Measure.restrict_map (measurable_stdSimplexCoordMap i)
        isClosed_stdSimplexAffineSet.measurableSet]
      have hp : stdSimplexCoordMap (R := ℝ) i ⁻¹'
          stdSimplexAffineSet (R := ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        exact mem_fintypeAffineCoords_iff_sum.mpr (sum_stdSimplexCoordMap i x)
      rw [hp, Measure.restrict_univ]

/-- The coordinate Lebesgue measure is finite on the standard simplex. -/
instance : IsFiniteMeasure (stdSimplexMeasure.restrict (stdSimplex ℝ ι)) := by
  refine ⟨?_⟩
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_restrict_stdSimplex i]
      rw [Measure.map_apply (measurable_stdSimplexCoordMap i) MeasurableSet.univ]
      rw [Set.preimage_univ, Measure.restrict_apply_univ]
      have hc : IsCompact (stdSimplexFreeCoords (R := ℝ) i) := by
        rw [← preimage_stdSimplexCoordMap i]
        exact (isClosedEmbedding_stdSimplexCoordMap i).isCompact_preimage
          (isCompact_stdSimplex ℝ ι)
      exact hc.measure_lt_top

/-- Permuting coordinates is a measure-preserving transformation of `stdSimplexMeasure`:
the map `x ↦ x ∘ σ` is measurable, and it pushes `stdSimplexMeasure` forward to itself. -/
theorem measurePreserving_stdSimplexMeasure_perm (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    stdSimplexMeasure stdSimplexMeasure := by
  refine ⟨continuous_pi (fun j => continuous_apply (σ j)) |>.measurable, ?_⟩
  cases isEmpty_or_nonempty ι with
  | inl h =>
      rw [stdSimplexMeasure_empty, Measure.map_zero]
  | inr h =>
      rw [stdSimplexMeasure_eq_at (σ (Classical.choice h)),
        stdSimplexMeasureAt_map_perm]
      exact stdSimplexMeasureAt_eq _ _

/-- The pushforward of `stdSimplexMeasure` under a coordinate permutation is
`stdSimplexMeasure` itself — the `Measure.map` equation extracted from
`measurePreserving_stdSimplexMeasure_perm`. -/
theorem stdSimplexMeasure_map_perm (σ : Equiv.Perm ι) :
  Measure.map (fun x ↦ x ∘ σ) stdSimplexMeasure = stdSimplexMeasure :=
  (measurePreserving_stdSimplexMeasure_perm σ).map_eq

/-- Extended real evaluation of the measure of the standard simplex. The value is
$1/(k-1)!$ where `k = Fintype.card ι`. -/
@[simp] theorem stdSimplexMeasure_stdSimplex [Nonempty ι] :
  stdSimplexMeasure (stdSimplex ℝ ι) =
    1 / (Nat.factorial (Fintype.card ι - 1) : ENNReal) := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  rw [← Measure.restrict_apply_univ]
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  rw [Measure.map_apply (measurable_stdSimplexCoordMap i) MeasurableSet.univ]
  rw [Set.preimage_univ, Measure.restrict_apply_univ]
  change volume (posSimplex {j : ι // j ≠ i} 1) = _
  rw [volume_posSimplex _ 1 (by positivity)]
  simp

/-- Real-valued form of the coordinate-volume formula for the standard simplex. -/
theorem stdSimplexMeasure_stdSimplex_toReal [Nonempty ι] :
  (stdSimplexMeasure (stdSimplex ℝ ι)).toReal =
    1 / (Nat.factorial (Fintype.card ι - 1) : ℝ) := by
  rw [stdSimplexMeasure_stdSimplex]
  simp

/-- The measure of the standard simplex is finite. -/
theorem stdSimplexMeasure_stdSimplex_ne_top [Nonempty ι] :
    stdSimplexMeasure (stdSimplex ℝ ι) ≠ ⊤ := by
  rw [stdSimplexMeasure_stdSimplex]
  exact ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)

/-- The projected measure of a measurable set: `stdSimplexMeasureAt i s` equals the volume
of the preimage of `s` under `stdSimplexCoordMap i`. -/
theorem stdSimplexMeasureAt_apply
    (i : ι) {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    stdSimplexMeasureAt i s =
      volume (stdSimplexCoordMap i ⁻¹' s) := by
  unfold stdSimplexMeasureAt
  exact Measure.map_apply (continuous_stdSimplexCoordMap i).measurable hs

/-- The coordinate faces have measure 0. -/
theorem stdSimplexMeasure_coord_eq_zero [Nonempty ι] (i : ι) :
  stdSimplexMeasure {u : ι → ℝ | u i = 0} = 0 := by
  cases subsingleton_or_nontrivial ι with
  | inl hι =>
      let : Unique ι :=
        ⟨⟨Classical.choice (inferInstance : Nonempty ι)⟩, fun a => hι.elim _ _⟩
      rw [stdSimplexMeasure_unique]
      simp
  | inr hι =>
      obtain ⟨j, hji⟩ := exists_ne i
      rw [stdSimplexMeasure_eq_at j,
        stdSimplexMeasureAt_apply j
          (isClosed_eq (continuous_apply i) continuous_const).measurableSet]
      rw [volume_pi]
      have hs : stdSimplexCoordMap j ⁻¹' {u : ι → ℝ | u i = 0} =
          {x : {q : ι // q ≠ j} → ℝ | x ⟨i, hji.symm⟩ = 0} := by
        ext x
        change stdSimplexCoordMap j x i = 0 ↔ x ⟨i, hji.symm⟩ = 0
        rw [stdSimplexCoordMap_apply_of_ne j i hji.symm]
      rw [hs]
      exact Measure.pi_hyperplane (fun _ : {q : ι // q ≠ j} => volume) ⟨i, hji.symm⟩ 0

/-- Almost every point of the simplex has every coordinate strictly positive, with respect to
`stdSimplexMeasure` restricted to the simplex. -/
theorem ae_zero_lt_of_mem_stdSimplex [Nonempty ι] :
  ∀ᵐ u ∂stdSimplexMeasure.restrict (stdSimplex ℝ ι),
    ∀ i, 0 < u i := by
  rw [ae_all_iff]
  intro i
  have hne_full : ∀ᵐ u ∂stdSimplexMeasure, u i ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using stdSimplexMeasure_coord_eq_zero i
  have hne : ∀ᵐ u ∂stdSimplexMeasure.restrict (stdSimplex ℝ ι), u i ≠ 0 :=
    (ae_mono Measure.restrict_le_self) hne_full
  filter_upwards
    [self_mem_ae_restrict
      (μ := stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet, hne] with u hu hne
  exact lt_of_le_of_ne (hu.1 i) (Ne.symm hne)

/-- The aggregation formula when the target has one coordinate. This is the base case for
fiberwise induction on a general surjective aggregation map. -/
theorem map_stdSimplexMeasure_restrict_stdSimplex_aggregate_of_unique
    {κ : Type*} [Fintype κ] [Unique κ] [Nonempty ι]
    (f : ι → κ) :
    Measure.map (stdSimplexAggregate f)
      ((stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)) =
    ((stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)).withDensity
      (stdSimplexAggregateDensity f) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  rw [withDensity_apply _ hs]
  rw [stdSimplexMeasure_unique (ι := κ)]
  have hconst_mem : (fun _ : κ => (1 : ℝ)) ∈ stdSimplex ℝ κ := by
    simp [stdSimplex]
  rw [MeasureTheory.restrict_dirac' (isClosed_stdSimplex ℝ κ).measurableSet,
    if_pos hconst_mem]
  have hd : Measurable (stdSimplexAggregateDensity f) := by
    unfold stdSimplexAggregateDensity
    fun_prop
  rw [MeasureTheory.setLIntegral_dirac' hd hs]
  by_cases hmem : (fun _ : κ => (1 : ℝ)) ∈ s
  · rw [if_pos hmem]
    have hpre : stdSimplexAggregate f ⁻¹' s ∩ stdSimplex ℝ ι = stdSimplex ℝ ι := by
      ext u
      simp only [Set.mem_inter_iff]
      constructor
      · exact fun h => h.2
      · intro hu
        refine ⟨?_, hu⟩
        have ha := stdSimplexAggregate_mem_stdSimplex (f := f) hu
        have heq : stdSimplexAggregate f u = fun _ : κ => (1 : ℝ) := by
          funext k
          simpa [stdSimplex, Subsingleton.elim k default] using ha.2
        simpa [heq] using hmem
    rw [Measure.restrict_apply (hs.preimage (by fun_prop)), hpre,
      stdSimplexMeasure_stdSimplex]
    simp [stdSimplexAggregateDensity, stdSimplexAggregateFiberCard,
      Subsingleton.elim (f _) default]
  · rw [if_neg hmem]
    have hpre : stdSimplexAggregate f ⁻¹' s ∩ stdSimplex ℝ ι = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨huS, hu⟩
        have ha := stdSimplexAggregate_mem_stdSimplex (f := f) hu
        have heq : stdSimplexAggregate f u = fun _ : κ => (1 : ℝ) := by
          funext k
          simpa [stdSimplex, Subsingleton.elim k default] using ha.2
        exact (hmem (heq ▸ huS)).elim
      · exact False.elim
    rw [Measure.restrict_apply (hs.preimage (by fun_prop)), hpre, measure_empty]

/-- In omitted-coordinate charts, aggregation discards the coordinates in the remainder of
the omitted target fibre and aggregates all complementary coordinates. -/
private theorem stdSimplexAggregate_coordMap_split
    {κ : Type*} [Fintype κ] (f : ι → κ) (k : κ) (i : ι) (hi : f i = k)
    (x : {j : ι // j ≠ i} → ℝ) :
    let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
    let e := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
    let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
      fun a ↦ ⟨f a, a.property⟩
    stdSimplexAggregate f (stdSimplexCoordMap i x) =
      stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1) := by
  classical
  dsimp only
  let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
  let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
    fun a ↦ ⟨f a, a.property⟩
  have hfree (j : κ) (hj : j ≠ k) :
      stdSimplexAggregate f (stdSimplexCoordMap i x) j =
        FunOnFinite.linearMap ℝ ℝ f' (e x).1 ⟨j, hj⟩ := by
    change FunOnFinite.linearMap ℝ ℝ f (stdSimplexCoordMap i x) j = _
    rw [FunOnFinite.linearMap_apply_apply, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_subtype (p := fun a : ι ↦ f a = j)
      (Finset.univ.filter fun a : ι ↦ f a = j) (by simp)]
    rw [Finset.sum_subtype
      (p := fun a : {a : {q : ι // q ≠ i} // p a} ↦ f' a = ⟨j, hj⟩)
      (Finset.univ.filter fun a : {a : {q : ι // q ≠ i} // p a} ↦
        f' a = ⟨j, hj⟩) (by simp)]
    let E : {a : ι // f a = j} ≃
        {a : {a : {q : ι // q ≠ i} // p a} // f' a = ⟨j, hj⟩} :=
      { toFun := fun a =>
          ⟨⟨⟨a, fun hai => hj (a.property.symm.trans ((congrArg f hai).trans hi))⟩,
              fun hak => hj (a.property.symm.trans hak)⟩,
            Subtype.ext a.property⟩
        invFun := fun a => ⟨a.1.1.1, congrArg Subtype.val a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    apply Fintype.sum_equiv E
    intro a
    rw [stdSimplexCoordMap_apply_of_ne i a
      (fun hai => hj (a.property.symm.trans ((congrArg f hai).trans hi)))]
    simp [e, p, E]
  funext j
  by_cases hj : j = k
  · subst j
    have hsum_left :
        ∑ j, stdSimplexAggregate f (stdSimplexCoordMap i x) j = 1 := by
      rw [show (∑ j, stdSimplexAggregate f (stdSimplexCoordMap i x) j) =
          ∑ j, ∑ a ∈ Finset.univ.filter (fun a : ι ↦ f a = j),
            stdSimplexCoordMap i x a by
        apply Finset.sum_congr rfl
        intro j _
        change FunOnFinite.linearMap ℝ ℝ f (stdSimplexCoordMap i x) j = _
        rw [FunOnFinite.linearMap_apply_apply]]
      rw [Finset.sum_fiberwise Finset.univ f (stdSimplexCoordMap i x)]
      exact sum_stdSimplexCoordMap i x
    calc
      stdSimplexAggregate f (stdSimplexCoordMap i x) k =
          1 - ∑ q : {j : κ // j ≠ k},
            stdSimplexAggregate f (stdSimplexCoordMap i x) q := by
              rw [← hsum_left, Fintype.sum_eq_add_sum_subtype_ne _ k]
              ring
      _ = 1 - ∑ q : {j : κ // j ≠ k},
          FunOnFinite.linearMap ℝ ℝ f' (e x).1 q := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            exact hfree q q.property
      _ = stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1) k := by
        rw [stdSimplexCoordMap_apply_self]
  · rw [stdSimplexCoordMap_apply_of_ne k j hj]
    exact hfree j hj

/-- In the same omitted-coordinate charts, the standard-simplex aggregation density is the
solid-simplex aggregation density on the complementary fibres times the volume of the
remainder of the omitted fibre. -/
private theorem stdSimplexAggregateDensity_coordMap_split
    {κ : Type*} [Fintype κ] (f : ι → κ) (k : κ) (i : ι) (hi : f i = k)
    (z : {j : κ // j ≠ k} → ℝ) :
    let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
    let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
      fun a ↦ ⟨f a, a.property⟩
    let A := {a : {j : ι // j ≠ i} // ¬p a}
    stdSimplexAggregateDensity f (stdSimplexCoordMap k z) =
      (ENNReal.ofReal (1 - ∑ q, z q) ^ Fintype.card A /
        (Nat.factorial (Fintype.card A) : ENNReal)) *
        posSimplexAggregateDensity f' z := by
  classical
  dsimp only
  let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
  let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
    fun a ↦ ⟨f a, a.property⟩
  let A := {a : {j : ι // j ≠ i} // ¬p a}
  have hkcard : stdSimplexAggregateFiberCard f k - 1 = Fintype.card A := by
    let E : A ≃ {a : {a : ι // f a = k} // a ≠ ⟨i, hi⟩} :=
      { toFun := fun a =>
          ⟨⟨a.1.1, Classical.not_not.mp a.property⟩,
            fun hai => a.1.property (congrArg Subtype.val hai)⟩
        invFun := fun a =>
          ⟨⟨a.1.1, fun hai => a.property (Subtype.ext hai)⟩,
            fun hne => hne a.1.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    unfold stdSimplexAggregateFiberCard
    rw [Fintype.card_congr E]
    rw [Fintype.card_subtype_compl (fun a : {a : ι // f a = k} => a = ⟨i, hi⟩),
      Fintype.card_subtype_eq]
  unfold stdSimplexAggregateDensity posSimplexAggregateDensity
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  rw [stdSimplexCoordMap_apply_self, hkcard]
  congr 1
  apply Fintype.prod_congr
  intro j
  letI (a : {a : {q : ι // q ≠ i} // p a}) : Decidable (f' a = j) :=
    Classical.propDecidable _
  rw [stdSimplexCoordMap_apply_of_ne k j j.property]
  have hjcard : stdSimplexAggregateFiberCard f j =
      Fintype.card {a : {a : {q : ι // q ≠ i} // p a} // f' a = j} := by
    let E : {a : ι // f a = j} ≃
        {a : {a : {q : ι // q ≠ i} // p a} // f' a = j} :=
      { toFun := fun a =>
          ⟨⟨⟨a, fun hai => j.property
              (a.property.symm.trans ((congrArg f hai).trans hi))⟩,
            fun hak => j.property (a.property.symm.trans hak)⟩,
            Subtype.ext a.property⟩
        invFun := fun a => ⟨a.1.1.1, congrArg Subtype.val a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    unfold stdSimplexAggregateFiberCard
    exact Fintype.card_congr E
  rw [hjcard]

/-- Pushing the restricted simplex measure forward under coordinate aggregation gives the
restricted target simplex measure weighted by the product of the fiber-volume densities.

This is the standard-simplex form of `lintegral_posSimplex_comp_aggregate`. -/
theorem map_stdSimplexMeasure_restrict_stdSimplex_aggregate
    {κ : Type*} [Fintype κ]
    (f : ι → κ) (hf : Function.Surjective f) :
    Measure.map (stdSimplexAggregate f)
      ((stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι))
      =
    ((stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)).withDensity
      (stdSimplexAggregateDensity f) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      have : IsEmpty κ := ⟨fun k ↦ (hf k).elim fun a _ ↦ isEmptyElim a⟩
      rw [stdSimplexMeasure_empty, stdSimplexMeasure_empty]
      simp
  | inr hι =>
      cases subsingleton_or_nontrivial κ with
      | inl _ =>
          let : Unique κ :=
            { default := f (Classical.choice hι)
              uniq := fun _ ↦ Subsingleton.elim _ _ }
          exact map_stdSimplexMeasure_restrict_stdSimplex_aggregate_of_unique f
      | inr _ =>
          let k : κ := Classical.choice (inferInstance : Nonempty κ)
          obtain ⟨i, hi⟩ := hf k
          let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
          let e := MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
          let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
            fun a ↦ ⟨f a, a.property⟩
          have hf' : Function.Surjective f' := by
            intro j
            obtain ⟨a, ha⟩ := hf j
            have hai : a ≠ i := fun hai => j.property
              (ha.symm.trans ((congrArg f hai).trans hi))
            exact ⟨⟨⟨a, hai⟩, fun hak => j.property (ha.symm.trans hak)⟩,
              Subtype.ext ha⟩
          let A := {a : {j : ι // j ≠ i} // ¬p a}
          let D : ({j : κ // j ≠ k} → ℝ) → ENNReal := fun z ↦
            ENNReal.ofReal (1 - ∑ q, z q) ^ Fintype.card A /
              (Nat.factorial (Fintype.card A) : ENNReal)
          have hsum (u : {a : {j : ι // j ≠ i} // p a} → ℝ) :
              ∑ q, FunOnFinite.linearMap ℝ ℝ f' u q = ∑ a, u a := by
            rw [show (∑ q, FunOnFinite.linearMap ℝ ℝ f' u q) =
                ∑ q, ∑ a ∈ Finset.univ.filter (fun a => f' a = q), u a by
              apply Finset.sum_congr rfl
              intro q _
              rw [FunOnFinite.linearMap_apply_apply]]
            exact Finset.sum_fiberwise Finset.univ f' u
          apply Measure.ext_of_lintegral
          intro g hg
          have hdensity : Measurable (stdSimplexAggregateDensity f) := by
            unfold stdSimplexAggregateDensity
            fun_prop
          have haggregate : Measurable (stdSimplexAggregate (R := ℝ) f) := by
            fun_prop
          have hleft :
              ∫⁻ u, g u ∂Measure.map (stdSimplexAggregate f)
                ((stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)) =
              ∫⁻ x in posSimplex {j : ι // j ≠ i} 1,
                g (stdSimplexAggregate f (stdSimplexCoordMap i x)) := by
            rw [lintegral_map hg (by fun_prop),
              stdSimplexMeasure_restrict_stdSimplex i]
            change ∫⁻ a, (g ∘ stdSimplexAggregate f) a
                ∂Measure.map (stdSimplexCoordMap i)
                  (volume.restrict (stdSimplexFreeCoords i)) = _
            rw [lintegral_map (hg.comp haggregate)
              (measurable_stdSimplexCoordMap i)]
            rw [stdSimplexFreeCoords]
            rfl
          have hright :
              ∫⁻ u, g u ∂((stdSimplexMeasure (ι := κ)).restrict
                  (stdSimplex ℝ κ)).withDensity (stdSimplexAggregateDensity f) =
              ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z) := by
            rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hg,
              stdSimplexMeasure_restrict_stdSimplex k]
            let Q : (κ → ℝ) → ENNReal := fun u ↦ stdSimplexAggregateDensity f u * g u
            have hQ : Measurable Q := hdensity.mul hg
            change ∫⁻ a, Q a ∂Measure.map (stdSimplexCoordMap k)
                (volume.restrict (stdSimplexFreeCoords k)) = _
            rw [lintegral_map hQ (measurable_stdSimplexCoordMap k)]
            rw [stdSimplexFreeCoords]
            rfl
          rw [hleft, hright]
          let G :
              ({a : {j : ι // j ≠ i} // p a} → ℝ) ×
                (A → ℝ) → ENNReal := fun q ↦
            g (stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' q.1))
          have hG : Measurable G := by
            apply hg.comp
            apply (measurable_stdSimplexCoordMap k).comp
            fun_prop
          let H : ({j : κ // j ≠ k} → ℝ) → ENNReal := fun z ↦
            g (stdSimplexCoordMap k z) * D z
          have hH : Measurable H := by
            apply (hg.comp (measurable_stdSimplexCoordMap k)).mul
            unfold D
            fun_prop
          calc
            ∫⁻ x in posSimplex {j : ι // j ≠ i} 1,
                g (stdSimplexAggregate f (stdSimplexCoordMap i x)) =
                ∫⁻ x in posSimplex {j : ι // j ≠ i} 1, G (e x) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro x _
              change g (stdSimplexAggregate f (stdSimplexCoordMap i x)) =
                g (stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1))
              rw [stdSimplexAggregate_coordMap_split f k i hi x]
            _ = ∫⁻ u in posSimplex {a : {j : ι // j ≠ i} // p a} 1,
                ∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v) := by
              simpa only [A] using
                (lintegral_posSimplex_split_pred p 1 G hG)
            _ = ∫⁻ u in posSimplex {a : {j : ι // j ≠ i} // p a} 1,
                H (FunOnFinite.linearMap ℝ ℝ f' u) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro u hu
              have hr : 0 ≤ 1 - ∑ a, u a := sub_nonneg.mpr hu.2
              change (∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v)) =
                H (FunOnFinite.linearMap ℝ ℝ f' u)
              rw [show (∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v)) =
                  G (u, Classical.arbitrary (A → ℝ)) *
                    volume (posSimplex A (1 - ∑ a, u a)) by
                rw [← setLIntegral_const]]
              rw [volume_posSimplex A _ hr]
              unfold G H D
              rw [hsum]
            _ = ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                H z * posSimplexAggregateDensity f' z :=
              lintegral_posSimplex_comp_aggregate f' hf' 1 zero_le_one H hH
            _ = ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro z _
              change H z * posSimplexAggregateDensity f' z =
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z)
              rw [stdSimplexAggregateDensity_coordMap_split f k i hi z]
              unfold H D
              ac_rfl

/-- Coordinates belong to every `Lᵖ` space for a finite measure supported on the simplex. -/
theorem memLp_coordinate_of_restrict_stdSimplex
    {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (stdSimplex ℝ ι) = μ) (i : ι) (p : ENNReal) :
    MemLp (fun u : ι → ℝ => u i) p μ := by
  apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 1
  have hmem : ∀ᵐ u ∂μ, u ∈ stdSimplex ℝ ι := by
    rw [← hμ]
    exact ae_restrict_mem (isClosed_stdSimplex ℝ ι).measurableSet
  filter_upwards [hmem] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  exact (mem_Icc_of_mem_stdSimplex hu i).2

end MeasureTheory.Measure

end StdSimplexCoordinateMeasure
