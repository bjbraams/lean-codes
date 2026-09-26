/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Integral.Basic

/-!
# The two-coordinate simplex as an interval

The affine parametrization `x ↦ ![x, 1 - x]` identifies the coordinate measure with
Lebesgue measure, and the closed simplex with the closed unit interval. The integral
formula applies to arbitrary functions into a normed real vector space.

## Main results

* `MeasureTheory.map_volume_pair_sub_eq_stdSimplexMeasure`: Lebesgue measure parametrizes the
  two-coordinate affine simplex without a scale factor.
* `MeasureTheory.integral_stdSimplex_fin_two`: The two-coordinate simplex integral is the
  integral over the closed unit interval.

## References

* `StdSimplexMeasure.Integral.Basic`: formal background used by this module.
-/

public noncomputable section
open MeasureTheory MeasureTheory.Measure Set

namespace MeasureTheory

/-- Lebesgue measure parametrizes the two-coordinate affine simplex without a scale factor. -/
theorem map_volume_pair_sub_eq_stdSimplexMeasure :
    Measure.map (fun x : ℝ => (![x, 1 - x] : Fin 2 → ℝ)) volume = stdSimplexMeasure := by
  rw [← map_stdSimplexMeasure_fin_two,
    Measure.map_map
      (show Measurable (fun x : ℝ => (![x, 1 - x] : Fin 2 → ℝ)) by fun_prop)
      (show Measurable (fun u : Fin 2 → ℝ => u 0) from measurable_pi_apply 0)]
  trans Measure.map (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) stdSimplexMeasure
  · apply Measure.map_congr
    have hmem : ∀ᵐ u ∂(stdSimplexMeasure (ι := Fin 2)),
        u ∈ stdSimplexAffineSet (R := ℝ) := by
      rw [stdSimplexMeasure_restrict_stdSimplexAffineSet]
      exact self_mem_ae_restrict isClosed_stdSimplexAffineSet.measurableSet
    filter_upwards [hmem] with u hu
    have hs : u 0 + u 1 = 1 := by
      simpa only [Fin.sum_univ_two] using mem_fintypeAffineCoords_iff_sum.mp hu
    funext i
    fin_cases i
    · rfl
    · change 1 - u 0 = u 1
      linarith
  · exact Measure.map_id

/-- The two-coordinate simplex integral is the integral over the closed unit interval. -/
theorem integral_stdSimplex_fin_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin 2 → ℝ) → E) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin 2), f u ∂stdSimplexMeasure =
      ∫ x in Icc (0 : ℝ) 1, f ![x, 1 - x] := by
  have he : Topology.IsClosedEmbedding (fun x : ℝ => (![x, 1 - x] : Fin 2 → ℝ)) :=
    (show Function.LeftInverse (fun u : Fin 2 → ℝ => u 0)
      (fun x : ℝ => (![x, 1 - x] : Fin 2 → ℝ)) from fun _ => rfl).isClosedEmbedding
        (continuous_apply 0) (by fun_prop)
  have hpre : (fun x : ℝ => (![x, 1 - x] : Fin 2 → ℝ)) ⁻¹'
      Convexity.StdSimplex.coordinateSet ℝ (Fin 2) = Icc 0 1 := by
    ext x
    change ((∀ i : Fin 2, 0 ≤ (![x, 1 - x] : Fin 2 → ℝ) i) ∧
      ∑ i : Fin 2, (![x, 1 - x] : Fin 2 → ℝ) i = 1) ↔ _
    simp [Fin.forall_fin_two, sub_nonneg]
  rw [← map_volume_pair_sub_eq_stdSimplexMeasure, he.setIntegral_map, hpre]

end MeasureTheory
