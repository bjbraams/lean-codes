/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import StdSimplexMeasure.Aggregation
public import StdSimplexMeasure.Coordinates

/-!
# Coordinate realization of the standard simplex

This file relates the explicit coordinate charts in `StdSimplexMeasure.Coordinates` to the
older realization `stdSimplex R ι : Set (ι → R)`. That realization remains useful for ambient
Lebesgue measure and integration, although Mathlib is transitioning its abstract simplex API to
the intrinsic type `Convexity.StdSimplex R ι`.

The dependence on the older lowercase `stdSimplex` API is intentionally isolated here. After
the topology of `Convexity.StdSimplex` is available in a stable Mathlib release, the principal
homeomorphism in this file can be replaced by one targeting the intrinsic simplex.
-/

@[expose] public noncomputable section StdSimplexCoordinateRealization

variable {ι : Type*} [Fintype ι]
variable {R : Type*}

open scoped Classical

section OrderedSemiring

variable [Semiring R] [PartialOrder R]

/-- The coordinate realization of the standard simplex is invariant under precomposition by a
permutation of its coordinates. -/
@[simp] theorem preimage_stdSimplex_perm (σ : Equiv.Perm ι) :
    (fun u : ι → R => u ∘ σ) ⁻¹' stdSimplex R ι = stdSimplex R ι := by
  ext u
  simp only [Set.mem_preimage, stdSimplex, Set.mem_ofPred_eq, Function.comp_apply,
    Equiv.sum_comp σ u]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i => by simpa using h1 (σ.symm i), h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun i => h1 (σ i), h2⟩⟩

end OrderedSemiring

section OrderedRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- The preimage of the coordinate realization of the standard simplex under
`stdSimplexCoordMap i` is `stdSimplexFreeCoords i`. -/
@[simp] theorem preimage_stdSimplexCoordMap (i : ι) :
    stdSimplexCoordMap i ⁻¹' stdSimplex R ι = stdSimplexFreeCoords i := by
  ext x
  simp only [Set.mem_preimage, stdSimplex, stdSimplexFreeCoords, Set.mem_ofPred_eq]
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
      · simpa [stdSimplexCoordMap_apply_of_ne, hji] using hpos ⟨j, hji⟩
    · exact sum_stdSimplexCoordMap i x

/-- Pointwise form of `preimage_stdSimplexCoordMap`. -/
@[simp] theorem stdSimplexCoordMap_mem_stdSimplex_iff
    (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x ∈ stdSimplex R ι ↔ x ∈ stdSimplexFreeCoords i := by
  change x ∈ stdSimplexCoordMap i ⁻¹' stdSimplex R ι ↔ _
  rw [preimage_stdSimplexCoordMap]

/-- Coordinate aggregation sends the coordinate realization of the standard simplex on `ι`
into the coordinate realization on `κ`. -/
theorem stdSimplexAggregate_mem_stdSimplex {κ : Type*} [Fintype κ]
    {f : ι → κ} {u : ι → R} (hu : u ∈ stdSimplex R ι) :
    stdSimplexAggregate f u ∈ stdSimplex R κ :=
  stdSimplex.image_linearMap f ⟨u, hu, rfl⟩

end OrderedRing

section RealTopology

/-- Restricting the omitted-coordinate chart gives a homeomorphism from the filled simplex in
free coordinates to the coordinate realization of the standard simplex. -/
def stdSimplexFreeCoordsHomeomorph (i : ι) :
    stdSimplexFreeCoords (R := ℝ) i ≃ₜ stdSimplex ℝ ι where
  toFun x :=
    ⟨stdSimplexCoordMap i x.1,
      (stdSimplexCoordMap_mem_stdSimplex_iff i x.1).2 x.2⟩
  invFun u := by
    refine ⟨stdSimplexCoordProj i u.1, ?_⟩
    apply (stdSimplexCoordMap_mem_stdSimplex_iff i _).1
    have huAffine : u.1 ∈ stdSimplexAffineSet (R := ℝ) := by
      exact mem_fintypeAffineCoords_iff_sum.mpr u.2.2
    rw [stdSimplexCoordMap_coordProj i huAffine]
    exact u.2
  left_inv x := by
    apply Subtype.ext
    exact stdSimplexCoordProj_coordMap i x.1
  right_inv u := by
    apply Subtype.ext
    apply stdSimplexCoordMap_coordProj i
    exact mem_fintypeAffineCoords_iff_sum.mpr u.2.2
  continuous_toFun :=
    (continuous_stdSimplexCoordMap i).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (continuous_stdSimplexCoordProj i).comp continuous_subtype_val |>.subtype_mk _

/-- The forward map of `stdSimplexFreeCoordsHomeomorph` is `stdSimplexCoordMap`. -/
@[simp] theorem coe_stdSimplexFreeCoordsHomeomorph_apply
    (i : ι) (x : stdSimplexFreeCoords (R := ℝ) i) :
    (stdSimplexFreeCoordsHomeomorph i x : ι → ℝ) = stdSimplexCoordMap i x.1 :=
  rfl

/-- The inverse map of `stdSimplexFreeCoordsHomeomorph` is `stdSimplexCoordProj`. -/
@[simp] theorem coe_stdSimplexFreeCoordsHomeomorph_symm_apply
    (i : ι) (u : stdSimplex ℝ ι) :
    ((stdSimplexFreeCoordsHomeomorph i).symm u : {j : ι // j ≠ i} → ℝ) =
      stdSimplexCoordProj i u.1 :=
  rfl

end RealTopology

end StdSimplexCoordinateRealization
