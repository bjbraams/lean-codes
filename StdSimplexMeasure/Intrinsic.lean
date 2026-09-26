/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The intrinsic simplex and its finite coordinate realization

`Convexity.StdSimplex` is the simplex object. Its `coordinateSet` is the carrier
of its realization in the ambient vector space, used for measures, restrictions,
and neighborhoods. The membership description is kept explicit for ambient
calculus; `range_coordinates` identifies it with the intrinsic object.

The intrinsic simplex uses Mathlib's topology and compactness instance. For finite
index types, Mathlib's coordinate embedding identifies this topology with the
topology induced by the weights.

## Main results

* `Convexity.StdSimplex.mem_coordinateSet`: Membership in the coordinate set: nonnegative
  coordinates summing to one.
* `Convexity.StdSimplex.isEmbedding_coordinates`: The coordinate map is a topological embedding
  of the intrinsic simplex.
* `Convexity.StdSimplex.continuous_coordinates`: The coordinate map of the intrinsic simplex is
  continuous.
* `Convexity.StdSimplex.isClosedEmbedding_coordinates`: The coordinate map is a closed embedding
  of the intrinsic simplex.
* `Convexity.StdSimplex.measurableEmbedding_coordinates`: The coordinate map is a measurable
  embedding of the real intrinsic simplex.

## References

* `Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex`: formal background used by this module.
* `Mathlib.Topology.Algebra.Module.FiniteDimension`: formal background used by this module.
* `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`: formal background used by this module.
-/

@[expose] public noncomputable section
namespace Convexity.StdSimplex
section Semiring
variable {R : Type*} [Semiring R] [PartialOrder R]
variable {ι : Type*} [Fintype ι]

/-- The ambient coordinate function of an intrinsic simplex point. -/
def coordinates (s : StdSimplex R ι) : ι → R := fun i => s.weights i

/-- The coordinate carrier of the intrinsic simplex, not a second simplex type. -/
def coordinateSet (R : Type*) (ι : Type*) [Semiring R] [PartialOrder R] [Fintype ι] :
    Set (ι → R) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1}

/-- Membership in the coordinate set: nonnegative coordinates summing to one. -/
theorem mem_coordinateSet {u : ι → R} :
    u ∈ coordinateSet R ι ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 := Iff.rfl

/-- The coordinates of an intrinsic point lie in the coordinate set. -/
theorem coordinates_mem (s : StdSimplex R ι) : coordinates s ∈ coordinateSet R ι := by
  refine ⟨s.nonneg, ?_⟩
  simp [coordinates]

/-- Recover an intrinsic point from its ambient coordinates and membership proof. -/
def ofCoordinates (u : ι → R) (hu : u ∈ coordinateSet R ι) : StdSimplex R ι where
  weights := Finsupp.equivFunOnFinite.symm u
  nonneg i := by simpa using hu.1 i
  total := by simpa [Finsupp.sum_fintype] using hu.2

/-- Reading the coordinates of the point built from a coordinate vector returns that vector. -/
@[simp] theorem coordinates_ofCoordinates (u : ι → R) (hu : u ∈ coordinateSet R ι) :
    coordinates (ofCoordinates u hu) = u := rfl

/-- Rebuilding a point from its own coordinates returns the point. -/
@[simp] theorem ofCoordinates_coordinates (s : StdSimplex R ι) :
    ofCoordinates (coordinates s) (coordinates_mem s) = s := by
  ext i
  rfl

omit [Fintype ι] in
/-- The coordinate map of the intrinsic simplex is injective. -/
theorem coordinates_injective : Function.Injective (coordinates (R := R) (ι := ι)) := by
  intro s t h
  ext i
  exact congrFun h i

/-- The coordinate map has the coordinate set as its range. -/
theorem range_coordinates :
    Set.range (coordinates (R := R) (ι := ι)) = coordinateSet R ι := by
  ext u
  exact ⟨fun ⟨s, h⟩ => h ▸ coordinates_mem s,
    fun hu => ⟨ofCoordinates u hu, coordinates_ofCoordinates u hu⟩⟩

/-- The intrinsic simplex is equivalent to its coordinate carrier. -/
def coordinateEquiv : StdSimplex R ι ≃ coordinateSet R ι where
  toFun s := ⟨coordinates s, coordinates_mem s⟩
  invFun u := ofCoordinates u.1 u.2
  left_inv := ofCoordinates_coordinates
  right_inv _ := rfl

/-- Every coordinate of a point of the coordinate set lies between zero and one. -/
theorem mem_Icc_of_mem_coordinateSet [IsOrderedAddMonoid R]
    {u : ι → R} (hu : u ∈ coordinateSet R ι) (i : ι) : u i ∈ Set.Icc 0 1 :=
  ⟨hu.1 i, hu.2 ▸ Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)⟩

/-- With an empty index type the coordinate set is empty. -/
theorem coordinateSet_empty [Nontrivial R] [IsEmpty ι] : coordinateSet R ι = ∅ := by
  ext u
  simp [coordinateSet]

section Topology
variable [TopologicalSpace R] [OrderClosedTopology R] [ContinuousAdd R]

variable (R ι) in
/-- The coordinate set is closed. -/
theorem isClosed_coordinateSet : IsClosed (coordinateSet R ι) := by
  have hset : coordinateSet R ι =
      (⋂ i, {u : ι → R | 0 ≤ u i}) ∩ {u | ∑ i, u i = 1} := by ext; simp [coordinateSet]
  rw [hset]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (by fun_prop) continuous_const)

variable (R ι) in
/-- The coordinate set is compact. -/
theorem isCompact_coordinateSet [CompactIccSpace R] [IsOrderedAddMonoid R] :
    IsCompact (coordinateSet R ι) :=
  isCompact_Icc.of_isClosed_subset (isClosed_coordinateSet R ι)
    (fun _ hu => ⟨fun i => hu.1 i, fun i => (mem_Icc_of_mem_coordinateSet hu i).2⟩)

/-- The coordinate realization of the finite standard simplex is compact when closed intervals in
the ordered coefficient space are compact. -/
instance [CompactIccSpace R] [IsOrderedAddMonoid R] : CompactSpace (coordinateSet R ι) :=
  isCompact_iff_compactSpace.mp (isCompact_coordinateSet R ι)

end Topology

end Semiring

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι]

/-- The coordinate map is a topological embedding of the intrinsic simplex. -/
theorem isEmbedding_coordinates :
    Topology.IsEmbedding (coordinates (R := R) (ι := ι)) :=
  isEmbedding_toFun_comp_weights R ι

/-- The coordinate map of the intrinsic simplex is continuous. -/
@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates (R := R) (ι := ι)) :=
  isEmbedding_coordinates.continuous

/-- The intrinsic simplex and its coordinate realization have the same topology. -/
def coordinateHomeomorph : StdSimplex R ι ≃ₜ coordinateSet R ι where
  toEquiv := coordinateEquiv
  continuous_toFun := continuous_coordinates.subtype_mk _
  continuous_invFun := by
    apply isEmbedding_coordinates.isInducing.continuous_iff.mpr
    exact continuous_subtype_val

/-- The coordinate map is a closed embedding of the intrinsic simplex. -/
theorem isClosedEmbedding_coordinates [OrderClosedTopology R] :
    Topology.IsClosedEmbedding (coordinates (R := R) (ι := ι)) :=
  isClosedEmbedding_toFun_comp_weights R ι

/-- The Borel σ-algebra of the intrinsic real standard simplex. -/
instance measurableSpace : MeasurableSpace (StdSimplex ℝ ι) := borel _

/-- The intrinsic real standard simplex is a Borel space. -/
instance borelSpace : BorelSpace (StdSimplex ℝ ι) := ⟨rfl⟩

/-- The coordinate map is a measurable embedding of the real intrinsic simplex. -/
theorem measurableEmbedding_coordinates :
    MeasurableEmbedding (coordinates (R := ℝ) (ι := ι)) :=
  isClosedEmbedding_coordinates.measurableEmbedding

end Convexity.StdSimplex
end
