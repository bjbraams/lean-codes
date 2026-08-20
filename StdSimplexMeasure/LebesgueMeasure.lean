/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Coordinate Lebesgue measure on the standard simplex and its affine hull

This file defines the natural coordinate Lebesgue measure on the affine hull of the real
standard simplex `stdSimplex ℝ ι`.

For a finite index type `ι` and a chosen coordinate `i : ι`, the affine hyperplane
`∑ j, u j = 1` is parametrized by the remaining `card ι - 1` coordinates, with the omitted
coordinate reconstructed as `1 - ∑ j, u j`. Pushing forward product Lebesgue measure along
this parametrization gives `stdSimplexMeasureAt i`. The resulting measure is independent of
the omitted coordinate and therefore defines a canonical measure `stdSimplexMeasure`.

The file develops basic properties of this measure, including coordinate and permutation
invariance, change-of-coordinates formulas for integration, the measure of the standard
simplex, nullity of its coordinate faces, and integration formulas for monomials. Integral
results are stated for functions taking values in a normed real vector space when appropriate.

This construction complements `Mathlib.Analysis.Convex.StdSimplex`, which defines the standard
simplex over an ordered semiring but does not equip it with a measure.

## Main definitions and results

* `stdSimplexAffineSet`: the affine hyperplane `∑ j, u j = 1`.
* `stdSimplexCoordHomeomorph`: its parametrization by `card ι - 1` free coordinates.
* `stdSimplexMeasure`: coordinate Lebesgue measure on this affine hyperplane.
* `stdSimplexMeasure_restrict_stdSimplex`: the corresponding measure on the standard simplex.
* `integral_stdSimplex_eq_integral_freeCoords`: integration in free coordinates.
* `stdSimplexMeasure_stdSimplex`: the simplex has measure `1 / (card ι - 1)!`.
-/

open Fintype Set

noncomputable section StdSimplexLebesgueMeasure

namespace MeasureTheory.Measure

/- DESIGN QUESTION: What is the appropriate namespace and the appropriate location?
I suggest primary namespace MeasureTheory.Measure, but maybe just MeasureTheory for the
elements that are concerned with integration.
I suggest location Mathlib.MeasureTheory.Measure.StdSimplex.
Raised on Zulip: <link once posted>.
-/

/- DESIGN QUESTION: Should any of the `theorem`s be renamed to `lemma` or `private lemma`?
With very few exceptions the facts here are presented as `theorem`.
Raised on Zulip: <link once posted>.
-/

/- Defining the standard index set as a `Type*`. -/
variable {ι : Type*} [Fintype ι]

/-- Allow `ι` to have noncomputable equality. -/
local instance stdSimplexDecidableEq : DecidableEq ι := Classical.decEq ι

/- DESIGN QUESTION: should we use `[DecidableEq ι]` as a `variable` hypothesis instead
of introducing the classical `local instance`?
Risk of the `local instance` style: instance diamond against the standard computable
`DecidableEq` for concrete types like `Fin k`.
In favour of the `local instance` style: may allow theorems to be applied, for example, to a
quotient space lacking computable equality.
Raised on Zulip: <link once posted>.
-/

/- The standard simplex is invariant under permuting coordinates. -/
@[simp] theorem preimage_stdSimplex_perm (σ : Equiv.Perm ι) :
  (fun u : ι → ℝ => u ∘ σ) ⁻¹' stdSimplex ℝ ι = stdSimplex ℝ ι := by
  ext u
  simp only [Set.mem_preimage, stdSimplex, Set.mem_ofPred_eq, Function.comp_apply,
    Equiv.sum_comp σ u]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i => by simpa using h1 (σ.symm i), h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun i => h1 (σ i), h2⟩⟩

/-- The affine hyperplane `{x | ∑ j, x j = 1}` (affine hull of the standard simplex)
defined as a plain set. -/
def stdSimplexAffineSet : Set (ι → ℝ) := {x | ∑ j, x j = 1}

/-- The linear functional summing all coordinates. -/
def stdSimplexSumLinearMap : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j, LinearMap.proj j

/-- `stdSimplexSumLinearMap`, viewed as an affine map. -/
def stdSimplexSumAffineMap : (ι → ℝ) →ᵃ[ℝ] ℝ :=
  stdSimplexSumLinearMap.toAffineMap

/-- Two ways of summing over all coordinates give the same result. -/
private theorem sum_eq_apply_add_sum_ne (u : ι → ℝ) (i : ι) :
    ∑ j, u j = u i + ∑ j : {j : ι // j ≠ i}, u j := by
  classical
  simpa using (Fintype.sum_eq_add_sum_subtype_ne u i)

/-- `stdSimplexAffineSet` is closed. -/
theorem isClosed_stdSimplexAffineSet :
    IsClosed (stdSimplexAffineSet (ι := ι)) := by
  have heq : stdSimplexAffineSet (ι := ι) = stdSimplexSumLinearMap ⁻¹' {1} := by
    ext x; simp [stdSimplexAffineSet, stdSimplexSumLinearMap]
  rw [heq]
  exact isClosed_singleton.preimage stdSimplexSumLinearMap.continuous_of_finiteDimensional

/-- The affine hyperplane `{x | ∑ j, x j = 1}` as an `AffineSubspace`: the preimage of the
point `1` under `stdSimplexSumAffineMap`. -/
def stdSimplexAffineSubspace : AffineSubspace ℝ (ι → ℝ) :=
  AffineSubspace.comap stdSimplexSumAffineMap (AffineSubspace.mk' (1 : ℝ) ⊥)

/-- The elements of the affine subspace are exactly the elements of the affine set. -/
@[simp] theorem mem_stdSimplexAffineSubspace_iff (x : ι → ℝ) :
    x ∈ stdSimplexAffineSubspace ↔ x ∈ stdSimplexAffineSet := by
  simp [stdSimplexAffineSubspace, stdSimplexAffineSet,
    stdSimplexSumAffineMap, stdSimplexSumLinearMap, sub_eq_zero]

/-- The coordinate projection that eliminates coordinate `i`. -/
def stdSimplexCoordProj (i : ι) (u : ι → ℝ) :
    {j : ι // j ≠ i} → ℝ :=
  fun j => u j

/-- Map from the free-coordinate space that omits coordinate `i` to `stdSimplexAffineSet`,
constructed as the inverse function of `funSplitAt ℝ i`. -/
def stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → ℝ) : ι → ℝ := by
  exact (Homeomorph.funSplitAt ℝ i).symm (1 - ∑ j, x j, x)

/-- The value of the dependent coordinate `i` is `1 - ∑ j, x j`. -/
@[simp] theorem stdSimplexCoordMap_apply_self (i : ι) (x : {j : ι // j ≠ i} → ℝ) :
    stdSimplexCoordMap i x i = 1 - ∑ j, x j := by
  simp [stdSimplexCoordMap]

/-- The value of a free coordinate `j ≠ i` remains unchanged under the coordinate map. -/
@[simp] theorem stdSimplexCoordMap_apply_of_ne (i j : ι) (h : j ≠ i)
    (x : {j : ι // j ≠ i} → ℝ) :
    stdSimplexCoordMap i x j = x ⟨j, h⟩ := by
  simp [stdSimplexCoordMap, h]

/-- The coordinate map maps to `stdSimplexAffineSet`. -/
@[simp] theorem sum_stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → ℝ) :
    stdSimplexCoordMap i x ∈ stdSimplexAffineSet := by
  sorry

/-- Projecting after applying the coordinate map recovers the free coordinates. -/
@[simp] theorem stdSimplexCoordProj_coordMap
    (i : ι) (x : {j : ι // j ≠ i} → ℝ) :
    stdSimplexCoordProj i (stdSimplexCoordMap i x) = x := by
  ext ⟨j, hj⟩
  simp [stdSimplexCoordProj, stdSimplexCoordMap, hj]

/-- Applying the coordinate map after projecting recovers the vector on
`stdSimplexAffineSet`. -/
theorem stdSimplexCoordMap_coordProj
    (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplexAffineSet) :
    stdSimplexCoordMap i (stdSimplexCoordProj i u) = u := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [stdSimplexCoordMap_apply_self]
    change 1 - ∑ j : {j : ι // j ≠ i}, u j = u i
    have hsum := sum_eq_apply_add_sum_ne u i
    change ∑ j, u j = 1 at hu
    rw [hu] at hsum
    linarith
  · simp [stdSimplexCoordMap_apply_of_ne,
      stdSimplexCoordProj, hji]

-- The range of `stdSimplexCoordMap` is `stdSimplexAffineSet`. -/
theorem range_stdSimplexCoordMap (i : ι) :
    Set.range (stdSimplexCoordMap i) = stdSimplexAffineSet := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact sum_stdSimplexCoordMap i x
  · intro hu
    refine ⟨stdSimplexCoordProj i u, ?_⟩
    exact stdSimplexCoordMap_coordProj i hu

/-- The coordinate map relates stdSimplexCoordMap (σ i) composed with σ to
stdSimplexCoordMap i applied to the permuted free coordinates. -/
theorem stdSimplexCoordMap_comp_perm (i : ι) (σ : Equiv.Perm ι)
    (x : {j : ι // j ≠ σ i} → ℝ) :
  stdSimplexCoordMap (σ i) x ∘ σ =
    stdSimplexCoordMap i (fun ⟨j, hj⟩ ↦ x ⟨σ j, fun h ↦ hj (σ.injective h)⟩) := by
  sorry

/-- The coordinate map is continuous. -/
theorem continuous_stdSimplexCoordMap (i : ι) :
  Continuous (stdSimplexCoordMap i) := by
  unfold stdSimplexCoordMap
  exact (Homeomorph.funSplitAt ℝ i).symm.continuous.comp
    (continuous_const.sub (continuous_finsetSum _ (fun j _ => continuous_apply j))
      |>.prodMk continuous_id)

omit [Fintype ι] in
/-- The projection map is continuous. -/
theorem continuous_stdSimplexCoordProj (i : ι) :
  Continuous (stdSimplexCoordProj i) := by
  exact continuous_pi (fun j => continuous_apply j.val)

/-- The free coordinates obtained by omitting `i` are equivalent to
`stdSimplexAffineSet`. -/
def stdSimplexCoordEquiv (i : ι) :
    ({j : ι // j ≠ i} → ℝ) ≃ stdSimplexAffineSet (ι := ι) where
  toFun x :=
    ⟨stdSimplexCoordMap i x, sum_stdSimplexCoordMap i x⟩
  invFun u :=
    stdSimplexCoordProj i u.1
  left_inv x := by
    simp
  right_inv u := by
    apply Subtype.ext
    exact stdSimplexCoordMap_coordProj i u.property

/-- The free-coordinate equivalence with `stdSimplexAffineSet` is a homeomorphism. -/
def stdSimplexCoordHomeomorph (i : ι) :
    ({j : ι // j ≠ i} → ℝ) ≃ₜ stdSimplexAffineSet (ι := ι) where
  toEquiv := stdSimplexCoordEquiv i
  continuous_toFun :=
    (continuous_stdSimplexCoordMap i).subtype_mk _
  continuous_invFun :=
    (continuous_stdSimplexCoordProj i).comp continuous_subtype_val

/-- The coordinate map is injective. -/
theorem injective_stdSimplexCoordMap (i : ι) :
    Function.Injective (stdSimplexCoordMap i) := by
  intro x y hxy
  have h := congrArg (stdSimplexCoordProj i) hxy
  simpa using h

/-- The filled `(card ι - 1)`-dimensional simplex of free coordinates corresponding to
points of `stdSimplex ℝ ι`. (Not to be confused with `stdSimplex ℝ {j // j ≠ i}`.) -/
def stdSimplexFreeCoords (i : ι) :
    Set ({j : ι // j ≠ i} → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1}

/-- The preimage of `stdSimplex ℝ ι` under `stdSimplexCoordMap i` is
`stdSimplexFreeCoords i`. -/
@[simp] theorem preimage_stdSimplexCoordMap (i : ι) :
    stdSimplexCoordMap i ⁻¹' stdSimplex ℝ ι =
      stdSimplexFreeCoords i := by
  ext x
  simp only [Set.mem_preimage, stdSimplex,
    stdSimplexFreeCoords, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hpos j.1
      rw [stdSimplexCoordMap_apply_of_ne i j.1 j.2 x] at hj
      exact hj
    · have hi := hpos i
      rw [stdSimplexCoordMap_apply_self] at hi
      exact sub_nonneg.mp hi
  · rintro ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        rw [stdSimplexCoordMap_apply_self]
        exact sub_nonneg.mpr hsum
      · simpa [stdSimplexCoordMap_apply_of_ne, hji]
          using hpos ⟨j, hji⟩
    · simpa [stdSimplexAffineSet] using
        (sum_stdSimplexCoordMap i x)

/-- The pointwise preimage of the coordinate map: `stdSimplexCoordMap i x ∈ stdSimplex ℝ ι`
iff `x ∈ stdSimplexFreeCoords i`. -/
@[simp] theorem stdSimplexCoordMap_mem_stdSimplex_iff
    (i : ι) (x : {j : ι // j ≠ i} → ℝ) :
  stdSimplexCoordMap i x ∈ stdSimplex ℝ ι ↔
    x ∈ stdSimplexFreeCoords i := by
  change x ∈ stdSimplexCoordMap i ⁻¹' stdSimplex ℝ ι ↔ _
  rw [preimage_stdSimplexCoordMap]

/-- The coordinate map gives a closed embedding. -/
theorem isClosedEmbedding_stdSimplexCoordMap (i : ι) :
    Topology.IsClosedEmbedding (stdSimplexCoordMap i) := by
  have h₁ :=
    (stdSimplexCoordHomeomorph i).isClosedEmbedding
  have h₂ :=
    (isClosed_stdSimplexAffineSet (ι := ι)).isClosedEmbedding_subtypeVal
  change Topology.IsClosedEmbedding
    (fun x => ((stdSimplexCoordHomeomorph i) x : ι → ℝ))
  exact h₂.comp h₁

/-- The coordinate aggregation map sending `u : ι → ℝ` to its block sums under a partition
`f : ι → κ`: block `k` collects the coordinates `i` with `π i = k`. -/
def stdSimplexAggregate {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (u : ι → ℝ) : κ → ℝ :=
  fun k => ∑ i ∈ Finset.univ.filter (fun i => f i = k), u i

/-- Aggregating positive parameters along a surjective partition gives positive
parameters. -/
theorem stdSimplexAggregate_pos {κ : Type*} [DecidableEq κ]
    {f : ι → κ} (hf : Function.Surjective f)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    ∀ k, 0 < stdSimplexAggregate f u k := by
  intro k
  unfold stdSimplexAggregate
  apply Finset.sum_pos
  · intro i _
    exact hu i
  · rcases hf k with ⟨i, hi⟩
    use i
    simp [hi]

/-- The aggregation map sends the standard simplex on `ι` into the standard simplex on
`κ`. -/
theorem stdSimplexAggregate_mem_stdSimplex {κ : Type*} [Fintype κ] [DecidableEq κ]
    {f : ι → κ} {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
    stdSimplexAggregate f u ∈ stdSimplex ℝ κ := by
  simp only [stdSimplex, Set.mem_ofPred_eq]
  refine ⟨fun k => ?_, ?_⟩
  · unfold stdSimplexAggregate
    apply Finset.sum_nonneg
    intro i _
    exact hu.1 i
  · unfold stdSimplexAggregate
    have h_sum : (∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), u i) = ∑ i, u i :=
      Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (f i)) u
    rw [h_sum]
    exact hu.2

/-- Fiber cardinality of an aggregation map. -/
def stdSimplexAggregateFiberCard {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (k : κ) : ℕ :=
  Fintype.card {i : ι // f i = k}

/-- Density associated with the fiber cardinality. -/
def stdSimplexAggregateDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (v : κ → ℝ) : ENNReal :=
  ∏ k,
    (ENNReal.ofReal (v k)) ^
        (stdSimplexAggregateFiberCard f k - 1) /
      (Nat.factorial
        (stdSimplexAggregateFiberCard f k - 1) : ENNReal)

/- Now we turn to measure properties -/

/-- The coordinate map is measurable. -/
theorem measurable_stdSimplexCoordMap (i : ι) :
    Measurable (stdSimplexCoordMap i) :=
  (continuous_stdSimplexCoordMap i).measurable

/-- Lebesgue measure pushed forward from the free coordinates omitting i. -/
def stdSimplexMeasureAt (i : ι) : Measure (ι → ℝ) := by
  classical
  exact Measure.map (stdSimplexCoordMap i) volume

/-- The Lebesgue measure is homogeneous of degree `(card ι - 1)` in the free coordinates. -/
theorem volume_map_smul_free_coords (i : ι) (c : ℝ) (hc : 0 < c) :
    Measure.map (c • · : ({j : ι // j ≠ i} → ℝ) → ({j : ι // j ≠ i} → ℝ)) volume =
      ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume := by
  sorry

/-- Coordinate explicit form of `stdSimplexMeasureAt`. -/
theorem stdSimplexMeasureAt_eq_map_piSplitAt_symm (i : ι) :
    stdSimplexMeasureAt i =
      Measure.map (Homeomorph.piSplitAt i (fun _ => ℝ)).symm
        (Measure.map (fun x : {j : ι // j ≠ i} → ℝ => (1 - ∑ q, x q, x)) volume) := by
  sorry

/-- Pushing `stdSimplexMeasureAt i` forward along the transposition `swap i j` gives
`stdSimplexMeasureAt j`. -/
theorem stdSimplexMeasureAt_swap (i j : ι) (hij : i ≠ j) :
    Measure.map (fun x => x ∘ Equiv.swap i j) (stdSimplexMeasureAt i) =
      stdSimplexMeasureAt j := by
  sorry

/-- Pushing `stdSimplexMeasureAt (σ i)` forward along `σ` gives `stdSimplexMeasureAt i`. -/
theorem stdSimplexMeasureAt_map_perm (i : ι) (σ : Equiv.Perm ι) :
  Measure.map (fun u => u ∘ σ)
    (stdSimplexMeasureAt (σ i)) = stdSimplexMeasureAt i := by
  sorry

/-- The coordinate measure is independent of the chosen special coordinate. -/
theorem stdSimplexMeasureAt_eq (i j : ι) :
    stdSimplexMeasureAt i = stdSimplexMeasureAt j := by
  sorry

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
  rw [dite_eq_left (inferInstance : Nonempty ι)]
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
  exact dite_eq_right (not_nonempty_iff.mpr inferInstance)

/-- For a type with a unique element, the pushforward measure at that element is a Dirac mass
at the all-ones point. -/
@[simp] theorem stdSimplexMeasureAt_of_unique [Unique ι] (i : ι) :
    stdSimplexMeasureAt i = dirac (fun _ ↦ (1 : ℝ)) := by
  sorry

/-- Restating `stdSimplexMeasureAt_of_unique` in terms of `stdSimplexMeasure`. -/
theorem stdSimplexMeasure_unique [Unique ι] :
    stdSimplexMeasure (ι := ι) = dirac (fun _ ↦ (1 : ℝ)) := by
  sorry

/-- The coordinate Lebesgue measure is supported on `stdSimplexAffineSet`. -/
theorem stdSimplexMeasure_restrict_stdSimplexAffineSet :
  stdSimplexMeasure (ι := ι) =
    stdSimplexMeasure.restrict stdSimplexAffineSet := by
  sorry

/-- The coordinate Lebesgue measure is finite on the standard simplex. -/
instance : IsFiniteMeasure (stdSimplexMeasure.restrict (stdSimplex ℝ ι)) := by
  sorry

/-- Permuting coordinates is a measure-preserving transformation of `stdSimplexMeasure`:
the map `x ↦ x ∘ σ` is measurable, and it pushes `stdSimplexMeasure` forward to itself. -/
theorem measurePreserving_stdSimplexMeasure_perm (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    stdSimplexMeasure stdSimplexMeasure := by
  sorry

/-- The pushforward of `stdSimplexMeasure` under a coordinate permutation is
`stdSimplexMeasure` itself — the `Measure.map` equation extracted from
`measurePreserving_stdSimplexMeasure_perm`. -/
theorem stdSimplexMeasure_map_perm (σ : Equiv.Perm ι) :
  Measure.map (fun x ↦ x ∘ σ) stdSimplexMeasure = stdSimplexMeasure :=
  (measurePreserving_stdSimplexMeasure_perm σ).map_eq

/-- Extended real evaluation of the measure of the standard simplex. The value is
$1/(k-1)!$ where `k = card ι`. -/
@[simp] theorem stdSimplexMeasure_stdSimplex [Nonempty ι] :
  stdSimplexMeasure (stdSimplex ℝ ι) =
    1 / (Nat.factorial (card ι - 1) : ENNReal) := by
  sorry

/-- The standard real measure of the standard simplex. -/
theorem stdSimplexMeasure_stdSimplex_toReal [Nonempty ι] :
  (stdSimplexMeasure (stdSimplex ℝ ι)).toReal =
    1 / (Nat.factorial (card ι - 1) : ℝ) := by
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
  sorry

/-- Coordinates are almost never 0. -/
theorem ae_zero_lt_of_mem_stdSimplex [Nonempty ι] :
  ∀ᵐ u ∂stdSimplexMeasure.restrict (stdSimplex ℝ ι),
    ∀ i, 0 < u i := by
  sorry

/-- The push-forward of measure under coordinate aggregation. -/
theorem map_stdSimplexMeasure_restrict_stdSimplex_aggregate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Surjective f) :
    Measure.map (stdSimplexAggregate f)
      ((stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι))
      =
    ((stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)).withDensity
      (stdSimplexAggregateDensity f) := by
  sorry

/- Some properties of the integral -/

/-- Scaling the free coordinates by `c` divides the Bochner integral by
`c ^ (card ι - 1)`. -/
theorem integral_smul_free_coords
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (c : ℝ) (hc : 0 < c)
    (f : ({j : ι // j ≠ i} → ℝ) → E) :
  ∫ x, f (c • x) ∂volume =
    (c ^ (Fintype.card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
  sorry

/-- The coordinate map preserves an integral. This is stated for functions taking values in
a normed real vector space.. -/
theorem integral_stdSimplex_eq_integral_freeCoords
    [Nonempty ι] (i : ι)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact
    (isClosedEmbedding_stdSimplexCoordMap i).integral_map f

/-- Evaluates an integral over the standard simplex by separating out the `i`-th coordinate.
This theorem provides the standard Fubini reduction (integration by slices) for the simplex.
It expresses the integral of a function `f` over the $(k-1)$-simplex (where $k$ is `card ι`)
as an iterated integral:
1. An outer 1D integral over the isolated coordinate $t \in [0, 1]$.
2. An inner integral over the $(k-2)$-simplex of the remaining coordinates $v$.
Because the remaining coordinates are subject to the constraint $\sum v = 1 - t$, they are
scaled by $(1 - t)$ to map them back to a standard unit $(k-1)$-simplex.
This change of variables introduces a Jacobian determinant factor of $(1 - t)^{k - 2}$. -/
theorem integral_stdSimplex_split_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) [Nontrivial ι]
    (f : (ι → ℝ) → E)
    (hf : IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ t in Set.Icc (0 : ℝ) 1,
      ((1 - t) ^ (Fintype.card ι - 2)) •
      ∫ v in stdSimplex ℝ {j // j ≠ i}, f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j))
        ∂stdSimplexMeasure := by
  sorry

/-- The integral of a function over the standard simplex is invariant under coordinate
permutations. -/
theorem integral_stdSimplex_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Equiv.Perm ι) (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f (u ∘ σ) ∂stdSimplexMeasure =
    ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure := by
  sorry

/-- Continuous functions are integrable on the standard simplex. -/
theorem ContinuousOn.integrableOn_stdSimplex
    [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure := by
  sorry

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
  sorry

/-- Basic recursion for evaluation of a monomial integral. -/
theorem integral_stdSimplex_explicit_monomial_succ (i : ι) (m : ι → ℕ) :
  ∫ u in stdSimplex ℝ ι, (∏ j, u j ^ m j) ∂stdSimplexMeasure =
    (Nat.factorial (m i) * Nat.factorial (card ι + (∑ j, m j) - 2 - m i)
      / Nat.factorial (card ι + ∑ j, m j - 1) : ℝ)
      * ∫ u in stdSimplex ℝ {j : ι // j ≠ i}, (∏ j, u j ^ m j.val) ∂stdSimplexMeasure := by
  sorry

/-- The integral of an explicit monomial over the standard simplex. -/
theorem integral_stdSimplex_explicit_monomial (m : ι → ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, (∏ i, u i ^ m i) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  sorry

/-- The integral of the constant function 1 over the standard simplex. -/
theorem integral_stdSimplex_constant [Nonempty ι] :
    ∫ _ in stdSimplex ℝ ι, (1 : ℝ) ∂stdSimplexMeasure =
      1 / (Nat.factorial (card ι - 1) : ℝ) := by
  rw [MeasureTheory.setIntegral_const, Measure.real, stdSimplexMeasure_stdSimplex_toReal]
  ring

/-- Equality between a Finsupp.prod and a full finite product for the same exponent
vector. -/
theorem MvPolynomial_monomial_eq (m : ι →₀ ℕ) (u : ι → ℝ) :
    m.prod (fun i n => u i ^ n) = ∏ i, u i ^ (m i) := by
  rw [Finsupp.prod]
  refine Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => ?_)
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]

/-- The integral of a `MvPolynomial` monomial over the standard simplex. -/
theorem integral_stdSimplex_MvPolynomial_monomial (m : ι →₀ ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, m.prod (fun i n => u i ^ n) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  simp_rw [MvPolynomial_monomial_eq]
  exact integral_stdSimplex_explicit_monomial (⇑m)

/-- Transformation of integrals under coordinate aggregation. -/
theorem integral_stdSimplex_comp_aggregate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Surjective f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (κ → ℝ) → E) :
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
  sorry

end MeasureTheory.Measure

end StdSimplexLebesgueMeasure
-- #lint
