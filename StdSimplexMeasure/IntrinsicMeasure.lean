/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The coordinate-normalized measure on the intrinsic simplex

The ambient `MeasureTheory.Measure.stdSimplexMeasure` is unchanged: it is a
measure on the whole affine hyperplane, not merely on the simplex. This file
pulls it back along the intrinsic coordinate embedding. Its pushforward is
exactly the ambient measure restricted to the coordinate carrier.

No probability normalization is applied: for a nonempty index type the mass
is `1 / (card ι - 1)!`. Empty and singleton index types are included explicitly.
-/

open MeasureTheory MeasureTheory.Measure
@[expose] public noncomputable section
namespace Convexity.StdSimplex
variable {ι : Type*} [Fintype ι]

/-- The intrinsic simplex measure, with the same free-coordinate normalization
as the ambient hyperplane measure. -/
def coordinateMeasure : Measure (StdSimplex ℝ ι) :=
  stdSimplexMeasure.comap coordinates

/-- Embedding the intrinsic measure recovers the restricted ambient measure. -/
theorem map_coordinates_coordinateMeasure :
    Measure.map coordinates (coordinateMeasure (ι := ι)) =
      stdSimplexMeasure.restrict (coordinateSet ℝ ι) := by
  rw [coordinateMeasure, measurableEmbedding_coordinates.map_comap, range_coordinates]

/-- The coordinate map carries the intrinsic measure to the restricted ambient measure. -/
theorem measurePreserving_coordinates :
    MeasurePreserving coordinates (coordinateMeasure (ι := ι))
      (stdSimplexMeasure.restrict (coordinateSet ℝ ι)) :=
  ⟨measurableEmbedding_coordinates.measurable, map_coordinates_coordinateMeasure⟩

/-- The intrinsic measure of a set is the ambient measure of its coordinate image. -/
theorem coordinateMeasure_apply (s : Set (StdSimplex ℝ ι)) :
    coordinateMeasure s = stdSimplexMeasure (coordinates '' s) :=
  measurableEmbedding_coordinates.comap_apply _ _

instance : IsFiniteMeasure (coordinateMeasure (ι := ι)) := by
  have hm : IsFiniteMeasure (Measure.map coordinates (coordinateMeasure (ι := ι))) := by
    rw [map_coordinates_coordinateMeasure]
    infer_instance
  exact Measure.isFiniteMeasure_of_map measurableEmbedding_coordinates.measurable.aemeasurable

/-- The total intrinsic mass is `1 / (card ι - 1)!` for a nonempty index type. -/
@[simp] theorem coordinateMeasure_univ [Nonempty ι] :
    coordinateMeasure (Set.univ : Set (StdSimplex ℝ ι)) =
      1 / (Nat.factorial (Fintype.card ι - 1) : ENNReal) := by
  rw [coordinateMeasure_apply, Set.image_univ, range_coordinates, stdSimplexMeasure_stdSimplex]

/-- With an empty index type the intrinsic measure is zero. -/
@[simp] theorem coordinateMeasure_empty [IsEmpty ι] :
    coordinateMeasure (ι := ι) = 0 := by
  simp [coordinateMeasure, stdSimplexMeasure_empty]

/-- On a singleton index type the intrinsic simplex has total mass one. -/
theorem coordinateMeasure_univ_unique [Unique ι] :
    coordinateMeasure (Set.univ : Set (StdSimplex ℝ ι)) = 1 := by simp

/-- Integrating an ambient function over the intrinsic simplex is precisely the
existing restricted hyperplane integral. -/
theorem integral_coordinateMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (ι → ℝ) → E) :
    ∫ s, f (coordinates s) ∂(coordinateMeasure (ι := ι)) =
      ∫ u in coordinateSet ℝ ι, f u ∂stdSimplexMeasure :=
  measurePreserving_coordinates.integral_comp measurableEmbedding_coordinates f

end Convexity.StdSimplex
end
