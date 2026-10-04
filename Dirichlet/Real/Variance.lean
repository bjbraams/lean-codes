/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Average

/-!
# Second moments of Dirichlet affine combinations

The second moment of an affine combination is explicit for arbitrary real nodes.
At concentration `c` with normalized weights it is the square of the weighted
mean plus the weighted node variance divided by `c + 1`.
-/

open MeasureTheory Set
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The second moment of any real affine combination under a positive Dirichlet law. -/
theorem integral_dirichletMeasure_affine_sq {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (x : ι → ℝ) :
    (∫ u, (∑ i, u i * x i) ^ 2 ∂dirichletMeasure b) =
      ((∑ i, b i * x i) ^ 2 + ∑ i, b i * x i ^ 2) /
        ((∑ i, b i) * ((∑ i, b i) + 1)) := by
  have he (u : ι → ℝ) : (∑ i, u i * x i) ^ 2 =
      ∑ i, x i * (u i * ∑ j, u j * x j) := by
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [show (fun u : ι → ℝ => (∑ i, u i * x i) ^ 2) =
    (fun u => ∑ i, x i * (u i * ∑ j, u j * x j)) from funext he]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_dirichletMeasure_of_continuousOn hb (by fun_prop))]
  simp_rw [integral_const_mul, integral_dirichletMeasure_coordinate_mul_affine hb,
    ← mul_div_assoc, ← Finset.sum_div]
  congr 1
  have hterm (i : ι) : x i * (b i * ((∑ j, b j * x j) + x i)) =
      (b i * x i) * (∑ j, b j * x j) + b i * x i ^ 2 := by ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, sq]

/-- At normalized concentration, the second moment is mean square plus node variance
 divided by one plus concentration. No positivity of the nodes is required. -/
theorem integral_dirichletMeasure_concentration_affine_sq {c : ℝ} (hc : 0 < c)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (x : ι → ℝ) :
    (∫ u, (∑ i, u i * x i) ^ 2 ∂dirichletMeasure (fun i => c * w i)) =
      (∑ i, w i * x i) ^ 2 +
        ((∑ i, w i * x i ^ 2) - (∑ i, w i * x i) ^ 2) / (c + 1) := by
  rw [integral_dirichletMeasure_affine_sq (fun i => mul_pos hc (hw i))]
  simp_rw [mul_assoc, ← Finset.mul_sum, hw1, mul_one]
  have hc1 : c + 1 ≠ 0 := by positivity
  field_simp
  ring

end ProbabilityTheory
