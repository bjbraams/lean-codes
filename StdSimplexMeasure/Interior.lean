/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import StdSimplexMeasure.Measure

/-!
# The positive-coordinate interior of the standard simplex

The definition and measurability result are independent of Dirichlet parameters.
The historical `ProbabilityTheory` declaration names are retained for compatibility.
-/

@[expose] public noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The interior of `stdSimplex ℝ ι` relative to its affine hull. -/
def stdSimplexInterior : Set (ι → ℝ) :=
  {u | u ∈ stdSimplex ℝ ι ∧ ∀ i, 0 < u i}

/-- The `stdSimplexInterior` is a measurable set. -/
theorem measurableSet_stdSimplexInterior :
    MeasurableSet (stdSimplexInterior (ι := ι)) := by
  have hpos : IsOpen {u : ι → ℝ | ∀ i, 0 < u i} := by
    rw [show {u : ι → ℝ | ∀ i, 0 < u i} =
        ⋂ i, {u : ι → ℝ | 0 < u i} by
      ext u
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)
  change MeasurableSet (stdSimplex ℝ ι ∩ {u : ι → ℝ | ∀ i, 0 < u i})
  exact (isClosed_stdSimplex ℝ ι).measurableSet.inter hpos.measurableSet

/-- Permuting coordinates preserves the positive-coordinate simplex interior. -/
theorem mem_stdSimplexInterior_perm (σ : Equiv.Perm ι) (u : ι → ℝ) :
    (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
  have hsimp : (u ∘ σ) ∈ stdSimplex ℝ ι ↔ u ∈ stdSimplex ℝ ι := by
    change u ∈ (fun v ↦ v ∘ σ) ⁻¹' stdSimplex ℝ ι ↔ _
    rw [preimage_stdSimplex_perm]
  constructor
  · rintro ⟨hu, hp⟩
    exact ⟨hsimp.mp hu, fun i ↦ by simpa using hp (σ.symm i)⟩
  · rintro ⟨hu, hp⟩
    exact ⟨hsimp.mpr hu, fun i ↦ hp (σ i)⟩

/-- Almost every point of the simplex is in its positive-coordinate interior.
For an empty index type the simplex measure is zero. -/
theorem ae_mem_stdSimplexInterior :
    ∀ᵐ u ∂MeasureTheory.Measure.stdSimplexMeasure.restrict (stdSimplex ℝ ι),
      u ∈ stdSimplexInterior := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (μ := MeasureTheory.Measure.stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet,
        MeasureTheory.Measure.ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hp
      exact ⟨hu, hp⟩

end ProbabilityTheory

end
