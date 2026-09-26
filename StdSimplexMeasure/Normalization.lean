/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Intrinsic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Normalization by the coordinate sum

The angular coordinate of a finite real vector is obtained by dividing by its sum.
This map is defined at sum zero and recovers a simplex point from any positive scaling.

## Main results

* `Convexity.StdSimplex.measurable_normalizeCoordinates`: Normalization by the coordinate sum is
  measurable, including at sum zero.
* `Convexity.StdSimplex.sum_normalizeCoordinates_smul`: Radial coordinates recover a simplex
  point and its positive scale.

## References

* `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic`: formal background used by this module.
-/

@[expose] public noncomputable section
namespace Convexity.StdSimplex
variable {ι : Type*} [Fintype ι]

/-- Normalize a vector by its coordinate sum. At sum zero this is the zero vector,
following Lean's convention for division by zero. -/
def normalizeCoordinates (x : ι → ℝ) : ι → ℝ := fun i => x i / ∑ j, x j

/-- Normalization by the coordinate sum is measurable, including at sum zero. -/
@[fun_prop] theorem measurable_normalizeCoordinates : Measurable (normalizeCoordinates (ι := ι))
    := by
  unfold normalizeCoordinates
  fun_prop

/-- Radial coordinates recover a simplex point and its positive scale. -/
theorem sum_normalizeCoordinates_smul {t : ℝ} (ht : 0 < t) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (∑ i, (t • u) i, normalizeCoordinates (t • u)) = (t, u) := by
  have hs : ∑ i, (t • u) i = t := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hu.2, mul_one]
  simp only [Prod.mk.injEq, hs, true_and]
  ext i
  change (t • u) i / (∑ j, (t • u) j) = u i
  rw [hs]
  exact mul_div_cancel_left₀ _ ht.ne'

end Convexity.StdSimplex
end
