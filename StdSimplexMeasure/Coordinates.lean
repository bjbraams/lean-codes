/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinates on the standard simplex and its affine hull

This file develops algebraic and ordered coordinate constructions for `stdSimplex R ι`.
The affine coordinate chart is available over a commutative ring, while statements involving
simplex inequalities use a compatible partial order. The final section gives the topological
properties of these coordinate charts over `ℝ`.

For a finite index type `ι` and a chosen coordinate `i : ι`, the affine hyperplane
`∑ j, u j = 1` is parametrized by the remaining `card ι - 1` coordinates, with the omitted
coordinate reconstructed as `1 - ∑ j, u j`. The file also defines coordinate aggregation maps.

The declarations are placed in the root namespace alongside the existing API in
`Mathlib.Analysis.Convex.StdSimplex`, rather than in a measure-theory namespace.

## Main definitions and results

* `stdSimplexAffineSet`: the affine hyperplane `∑ j, u j = 1`.
* `stdSimplexCoordEquiv`: its parametrization by `card ι - 1` free coordinates.
* `stdSimplexFreeCoords`: the filled simplex in free coordinates.
* `stdSimplexAggregate`: aggregation of coordinates along a finite map.
-/

open Fintype Set

noncomputable section StdSimplexCoordinates

/- Defining the standard index set as a `Type*`. -/
variable {ι : Type*} [Fintype ι]
variable {R : Type*}

/-- Allow `ι` to have noncomputable equality. -/
local instance coordinatesDecidableEq : DecidableEq ι := Classical.decEq ι

/- DESIGN QUESTION: should we use `[DecidableEq ι]` as a `variable` hypothesis instead
of introducing the classical `local instance`?
Risk of the `local instance` style: instance diamond against the standard computable
`DecidableEq` for concrete types like `Fin k`.
In favour of the `local instance` style: may allow theorems to be applied, for example, to a
quotient space lacking computable equality.
Raised on Zulip: <link once posted>.
-/

section OrderedSemiring

variable [Semiring R] [PartialOrder R]

/-- The standard simplex is invariant under precomposition by a permutation of its coordinates. -/
@[simp] theorem preimage_stdSimplex_perm (σ : Equiv.Perm ι) :
  (fun u : ι → R => u ∘ σ) ⁻¹' stdSimplex R ι = stdSimplex R ι := by
  ext u
  simp only [Set.mem_preimage, stdSimplex, Set.mem_ofPred_eq, Function.comp_apply,
    Equiv.sum_comp σ u]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i => by simpa using h1 (σ.symm i), h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun i => h1 (σ i), h2⟩⟩

end OrderedSemiring

section Ring

variable [CommRing R]

/-- The affine hyperplane `{x | ∑ j, x j = 1}` (affine hull of the standard simplex)
defined as a plain set. -/
def stdSimplexAffineSet : Set (ι → R) := {x | ∑ j, x j = 1}

/-- The linear functional summing all coordinates. -/
def stdSimplexSumLinearMap : (ι → R) →ₗ[R] R :=
  ∑ j, LinearMap.proj j

/-- `stdSimplexSumLinearMap`, viewed as an affine map. -/
def stdSimplexSumAffineMap : (ι → R) →ᵃ[R] R :=
  stdSimplexSumLinearMap.toAffineMap

/-- Two ways of summing over all coordinates give the same result. -/
private theorem sum_eq_apply_add_sum_ne (u : ι → R) (i : ι) :
    ∑ j, u j = u i + ∑ j : {j : ι // j ≠ i}, u j := by
  classical
  simpa using (Fintype.sum_eq_add_sum_subtype_ne u i)

/-- The affine hyperplane `{x | ∑ j, x j = 1}` as an `AffineSubspace`: the preimage of the
point `1` under `stdSimplexSumAffineMap`. -/
def stdSimplexAffineSubspace : AffineSubspace R (ι → R) :=
  AffineSubspace.comap stdSimplexSumAffineMap (AffineSubspace.mk' (1 : R) ⊥)

/-- The elements of the affine subspace are exactly the elements of the affine set. -/
@[simp] theorem mem_stdSimplexAffineSubspace_iff (x : ι → R) :
    x ∈ stdSimplexAffineSubspace (R := R) ↔ x ∈ stdSimplexAffineSet := by
  simp [stdSimplexAffineSubspace, stdSimplexAffineSet,
    stdSimplexSumAffineMap, stdSimplexSumLinearMap, sub_eq_zero]

/-- The coordinate projection that eliminates coordinate `i`. -/
def stdSimplexCoordProj (i : ι) (u : ι → R) :
    {j : ι // j ≠ i} → R :=
  fun j => u j

/-- Map from the free-coordinate space that omits coordinate `i` to `stdSimplexAffineSet`,
constructed as the inverse function of `Equiv.funSplitAt i R`. -/
def stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → R) : ι → R := by
  exact (Equiv.funSplitAt i R).symm (1 - ∑ j, x j, x)

/-- The value of the dependent coordinate `i` is `1 - ∑ j, x j`. -/
@[simp] theorem stdSimplexCoordMap_apply_self (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x i = 1 - ∑ j, x j := by
  simp [stdSimplexCoordMap]

/-- The value of a free coordinate `j ≠ i` remains unchanged under the coordinate map. -/
@[simp] theorem stdSimplexCoordMap_apply_of_ne (i j : ι) (h : j ≠ i)
    (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x j = x ⟨j, h⟩ := by
  simp [stdSimplexCoordMap, h]

/-- The coordinate map maps to `stdSimplexAffineSet`. -/
@[simp] theorem sum_stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x ∈ stdSimplexAffineSet := by
  rw [stdSimplexAffineSet, Set.mem_ofPred_eq, sum_eq_apply_add_sum_ne _ i,
    stdSimplexCoordMap_apply_self]
  have h : (∑ j : {j : ι // j ≠ i}, stdSimplexCoordMap i x j) = ∑ j, x j := by
    apply Finset.sum_congr rfl
    intro j _
    exact stdSimplexCoordMap_apply_of_ne i j j.property x
  rw [h]
  ring

/-- Projecting after applying the coordinate map recovers the free coordinates. -/
@[simp] theorem stdSimplexCoordProj_coordMap
    (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordProj i (stdSimplexCoordMap i x) = x := by
  ext ⟨j, hj⟩
  simp [stdSimplexCoordProj, stdSimplexCoordMap, hj]

/-- Applying the coordinate map after projecting recovers the vector on
`stdSimplexAffineSet`. -/
theorem stdSimplexCoordMap_coordProj
    (i : ι) {u : ι → R}
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
    rw [hsum]
    ring
  · simp [stdSimplexCoordMap_apply_of_ne,
      stdSimplexCoordProj, hji]

/-- The range of `stdSimplexCoordMap` is the affine hyperplane `stdSimplexAffineSet`. -/
theorem range_stdSimplexCoordMap (i : ι) :
    Set.range (stdSimplexCoordMap (R := R) i) = stdSimplexAffineSet := by
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
    (x : {j : ι // j ≠ σ i} → R) :
  stdSimplexCoordMap (σ i) x ∘ σ =
    stdSimplexCoordMap i (fun ⟨j, hj⟩ ↦
      x ⟨σ j, fun h ↦ hj (σ.injective h)⟩) := by
  have hu : stdSimplexCoordMap (σ i) x ∘ σ ∈ stdSimplexAffineSet := by
    simpa [stdSimplexAffineSet, Equiv.sum_comp] using
      sum_stdSimplexCoordMap (σ i) x
  symm
  rw [← stdSimplexCoordMap_coordProj i hu]
  congr 1
  funext ⟨j, hj⟩
  change x ⟨σ j, _⟩ = stdSimplexCoordMap (σ i) x (σ j)
  rw [stdSimplexCoordMap_apply_of_ne (σ i) (σ j) (fun h => hj (σ.injective h))]

/-- The linear part of the change of free coordinates induced by swapping the omitted
coordinate `i` with a different coordinate `j`. -/
def stdSimplexFreeCoordSwapLinear (i j : ι) (hij : i ≠ j) :
    ({q : ι // q ≠ i} → R) →ₗ[R] ({q : ι // q ≠ i} → R) :=
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  { toFun := fun x q => if q = ji then - ∑ r, x r else x q
    map_add' := by
      intro x y
      funext q
      by_cases hq : q = ji
      · simp [hq, Finset.sum_add_distrib]
        ring
      · simp [hq]
    map_smul' := by
      intro c x
      funext q
      by_cases hq : q = ji
      · simp [hq, Finset.mul_sum]
      · simp [hq] }

/-- The sum of the coordinates after applying `stdSimplexFreeCoordSwapLinear` is the
negative of the coordinate belonging to `j`. -/
lemma sum_stdSimplexFreeCoordSwapLinear (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) :
    ∑ q, stdSimplexFreeCoordSwapLinear i j hij x q = -x ⟨j, Ne.symm hij⟩ := by
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  let L := stdSimplexFreeCoordSwapLinear (R := R) i j hij
  calc
    ∑ q, L x q = (∑ q ∈ Finset.univ.erase ji, L x q) + L x ji :=
      (Finset.sum_erase_add Finset.univ (fun q => L x q) (Finset.mem_univ ji)).symm
    _ = (∑ q ∈ Finset.univ.erase ji, x q) + (-∑ q, x q) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        simp [L, stdSimplexFreeCoordSwapLinear, ji, Finset.ne_of_mem_erase hq]
      · simp [L, stdSimplexFreeCoordSwapLinear, ji]
    _ = -x ji := by
      have hx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ ji)
      rw [← hx]
      abel

/-- The affine change of free coordinates induced by swapping `i` and `j` in the ambient
coordinate space. -/
def stdSimplexFreeCoordSwap (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) : {q : ι // q ≠ i} → R :=
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  (fun q => if q = ji then 1 else 0) + stdSimplexFreeCoordSwapLinear i j hij x

/-- Swapping `i` and `j` in ambient coordinates corresponds to
`stdSimplexFreeCoordSwap` in the chart omitting `i`. -/
theorem stdSimplexCoordMap_comp_freeCoordSwap (i j : ι) (hij : i ≠ j) :
    (fun u : ι → R => u ∘ Equiv.swap i j) ∘ stdSimplexCoordMap i =
      stdSimplexCoordMap i ∘ stdSimplexFreeCoordSwap i j hij := by
  let α := {q : ι // q ≠ i}
  let ji : α := ⟨j, Ne.symm hij⟩
  funext x q
  by_cases hqi : q = i
  · subst q
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    rw [stdSimplexCoordMap_apply_of_ne i j (Ne.symm hij), stdSimplexCoordMap_apply_self]
    change x ji = 1 - ∑ q, stdSimplexFreeCoordSwap i j hij x q
    have hc : ∑ q : α, (if q = ji then (1 : R) else 0) = 1 := by
      simpa using Finset.sum_ite_eq' Finset.univ ji (fun _ => (1 : R))
    simp_rw [stdSimplexFreeCoordSwap, Pi.add_apply]
    rw [Finset.sum_add_distrib, hc, sum_stdSimplexFreeCoordSwapLinear]
    ring
  · by_cases hqj : q = j
    · subst q
      simp only [Function.comp_apply, Equiv.swap_apply_right, stdSimplexCoordMap_apply_self]
      rw [stdSimplexCoordMap_apply_of_ne i j (Ne.symm hij)]
      change 1 - ∑ q, x q = stdSimplexFreeCoordSwap i j hij x ji
      simp [stdSimplexFreeCoordSwap, stdSimplexFreeCoordSwapLinear, ji]
      ring
    · rw [Function.comp_apply, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hqi hqj]
      rw [stdSimplexCoordMap_apply_of_ne i q hqi]
      change x ⟨q, hqi⟩ =
        stdSimplexCoordMap i (stdSimplexFreeCoordSwap i j hij x) q
      rw [stdSimplexCoordMap_apply_of_ne i q hqi]
      have hsub : (⟨q, hqi⟩ : α) ≠ ji := by
        intro h
        exact hqj (congrArg Subtype.val h)
      simp [stdSimplexFreeCoordSwap, stdSimplexFreeCoordSwapLinear, ji, hsub]

/-- The free coordinates obtained by omitting `i` are equivalent to
`stdSimplexAffineSet`. -/
def stdSimplexCoordEquiv (i : ι) :
    ({j : ι // j ≠ i} → R) ≃ stdSimplexAffineSet (R := R) (ι := ι) where
  toFun x :=
    ⟨stdSimplexCoordMap i x, sum_stdSimplexCoordMap i x⟩
  invFun u :=
    stdSimplexCoordProj i u.1
  left_inv x := by
    simp
  right_inv u := by
    apply Subtype.ext
    exact stdSimplexCoordMap_coordProj i u.property

/-- The coordinate map is injective. -/
theorem injective_stdSimplexCoordMap (i : ι) :
    Function.Injective (stdSimplexCoordMap (R := R) i) := by
  intro x y hxy
  have h := congrArg (stdSimplexCoordProj i) hxy
  simpa using h

end Ring

section OrderedRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- The filled `(card ι - 1)`-dimensional simplex of free coordinates corresponding to
points of `stdSimplex R ι`. (Not to be confused with `stdSimplex R {j // j ≠ i}`.) -/
def stdSimplexFreeCoords (i : ι) :
    Set ({j : ι // j ≠ i} → R) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1}

/-- The preimage of `stdSimplex R ι` under `stdSimplexCoordMap i` is
`stdSimplexFreeCoords i`. -/
@[simp] theorem preimage_stdSimplexCoordMap (i : ι) :
    stdSimplexCoordMap i ⁻¹' stdSimplex R ι =
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

/-- The pointwise preimage of the coordinate map: `stdSimplexCoordMap i x ∈ stdSimplex R ι`
iff `x ∈ stdSimplexFreeCoords i`. -/
@[simp] theorem stdSimplexCoordMap_mem_stdSimplex_iff
    (i : ι) (x : {j : ι // j ≠ i} → R) :
  stdSimplexCoordMap i x ∈ stdSimplex R ι ↔
    x ∈ stdSimplexFreeCoords i := by
  change x ∈ stdSimplexCoordMap i ⁻¹' stdSimplex R ι ↔ _
  rw [preimage_stdSimplexCoordMap]

end OrderedRing

section Aggregation

variable [Semiring R]

/-- Coordinate aggregation sends `u : ι → R` to its block sums under a map `f : ι → κ`.
This is an application-oriented functional name for `FunOnFinite.linearMap`. -/
abbrev stdSimplexAggregate {κ : Type*} [Finite κ]
    (f : ι → κ) : (ι → R) → (κ → R) :=
  FunOnFinite.linearMap R R f

end Aggregation

section OrderedAggregation

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

omit [IsOrderedRing R] in
/-- Aggregating positive parameters along a surjective partition gives positive
parameters. -/
theorem stdSimplexAggregate_pos [AddLeftStrictMono R] [IsOrderedCancelAddMonoid R]
    {κ : Type*} [Finite κ] [DecidableEq κ]
    {f : ι → κ} (hf : Function.Surjective f)
    {u : ι → R} (hu : ∀ i, 0 < u i) :
    ∀ k, 0 < stdSimplexAggregate f u k := by
  intro k
  change 0 < (FunOnFinite.linearMap R R f u) k
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_pos
  · intro i _
    exact hu i
  · rcases hf k with ⟨i, hi⟩
    use i
    simp [hi]

/-- The aggregation map sends the standard simplex on `ι` into the standard simplex on
`κ`. -/
theorem stdSimplexAggregate_mem_stdSimplex {κ : Type*} [Fintype κ] [DecidableEq κ]
    {f : ι → κ} {u : ι → R} (hu : u ∈ stdSimplex R ι) :
    stdSimplexAggregate f u ∈ stdSimplex R κ :=
  stdSimplex.image_linearMap f ⟨u, hu, rfl⟩

end OrderedAggregation

/-- Fiber cardinality of an aggregation map. -/
def stdSimplexAggregateFiberCard {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (k : κ) : ℕ :=
  Fintype.card {i : ι // f i = k}

section RealTopology

/-- `stdSimplexAffineSet` is closed over the reals. -/
theorem isClosed_stdSimplexAffineSet :
    IsClosed (stdSimplexAffineSet (R := ℝ) (ι := ι)) := by
  have heq : stdSimplexAffineSet (R := ℝ) (ι := ι) =
      stdSimplexSumLinearMap (R := ℝ) ⁻¹' {1} := by
    ext x
    simp [stdSimplexAffineSet, stdSimplexSumLinearMap]
  rw [heq]
  exact isClosed_singleton.preimage
    (stdSimplexSumLinearMap (R := ℝ)).continuous_of_finiteDimensional

/-- The free-coordinate swap is continuous over the reals. -/
theorem continuous_stdSimplexFreeCoordSwap (i j : ι) (hij : i ≠ j) :
    Continuous (stdSimplexFreeCoordSwap (R := ℝ) i j hij) := by
  apply continuous_pi
  intro q
  unfold stdSimplexFreeCoordSwap stdSimplexFreeCoordSwapLinear
  dsimp
  split_ifs <;> fun_prop

/-- The real coordinate map is continuous. -/
theorem continuous_stdSimplexCoordMap (i : ι) :
    Continuous (stdSimplexCoordMap (R := ℝ) i) := by
  unfold stdSimplexCoordMap
  exact (Homeomorph.funSplitAt ℝ i).symm.continuous.comp
    (continuous_const.sub (continuous_finsetSum _ (fun j _ => continuous_apply j))
      |>.prodMk continuous_id)

omit [Fintype ι] in
/-- The real coordinate projection is continuous. -/
theorem continuous_stdSimplexCoordProj (i : ι) :
    Continuous (stdSimplexCoordProj (R := ℝ) i) := by
  exact continuous_pi (fun j => continuous_apply j.val)

/-- The real free-coordinate equivalence with `stdSimplexAffineSet` is a homeomorphism. -/
def stdSimplexCoordHomeomorph (i : ι) :
    ({j : ι // j ≠ i} → ℝ) ≃ₜ stdSimplexAffineSet (R := ℝ) (ι := ι) where
  toEquiv := stdSimplexCoordEquiv (R := ℝ) i
  continuous_toFun :=
    (continuous_stdSimplexCoordMap i).subtype_mk _
  continuous_invFun :=
    (continuous_stdSimplexCoordProj i).comp continuous_subtype_val

/-- The real coordinate map gives a closed embedding. -/
theorem isClosedEmbedding_stdSimplexCoordMap (i : ι) :
    Topology.IsClosedEmbedding (stdSimplexCoordMap (R := ℝ) i) := by
  have h₁ := (stdSimplexCoordHomeomorph i).isClosedEmbedding
  have h₂ := (isClosed_stdSimplexAffineSet (ι := ι)).isClosedEmbedding_subtypeVal
  change Topology.IsClosedEmbedding
    (fun x => ((stdSimplexCoordHomeomorph i) x : ι → ℝ))
  exact h₂.comp h₁

end RealTopology

end StdSimplexCoordinates
