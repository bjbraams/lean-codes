/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Properties

/-!
# Real ratio means

Positive real ratio means inherit homogeneity from R. At distinct orders their
comparison with one reduces to comparing the two R-averages. These facts provide
the normalization used in the Beckenbach–Dresher inequality.
-/

open ProbabilityTheory
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- A real ratio mean is positive, including on the diagonal. -/
theorem carlsonRatioMeanReal_pos (s t : ℝ) (b x : ι → ℝ) :
    0 < carlsonRatioMeanReal s t b x := Real.exp_pos _

/-- Away from the diagonal, the ratio mean is the positive root of the ratio of R-averages. -/
theorem carlsonRatioMeanReal_eq_rpow {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRatioMeanReal s t b x = (carlsonRReal t b x / carlsonRReal s b x) ^ (t - s)⁻¹ := by
  rw [Real.rpow_def_of_pos (div_pos (carlsonRReal_pos t hb hx) (carlsonRReal_pos s hb hx)),
    Real.log_div (carlsonRReal_pos t hb hx).ne' (carlsonRReal_pos s hb hx).ne']
  simp only [carlsonRatioMeanReal, ite_eq_right hst, div_eq_mul_inv]

/-- The ratio mean is homogeneous of degree one at distinct real orders. -/
theorem carlsonRatioMeanReal_mul {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) {a : ℝ} (ha : 0 < a) :
    carlsonRatioMeanReal s t b (fun i => a * x i) = a * carlsonRatioMeanReal s t b x := by
  simp only [carlsonRatioMeanReal, ite_eq_right hst, carlsonRReal_mul _ hx ha,
    Real.log_mul (Real.rpow_pos_of_pos ha _).ne' (carlsonRReal_pos _ hb hx).ne',
    Real.log_rpow ha]
  have he : (t * Real.log a + Real.log (carlsonRReal t b x) -
      (s * Real.log a + Real.log (carlsonRReal s b x))) / (t - s) =
      Real.log a + (Real.log (carlsonRReal t b x) - Real.log (carlsonRReal s b x)) / (t - s) := by
    field_simp [sub_ne_zero.mpr hst.symm]
    ring
  rw [he, Real.exp_add, Real.exp_log ha]

/-- A ratio mean is one exactly when the R-averages at its two distinct orders agree. -/
theorem carlsonRatioMeanReal_eq_one_iff {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRatioMeanReal s t b x = 1 ↔ carlsonRReal t b x = carlsonRReal s b x := by
  simp only [carlsonRatioMeanReal, ite_eq_right hst, Real.exp_eq_one_iff, div_eq_zero_iff,
    sub_eq_zero, sub_ne_zero.mpr hst.symm, or_false]
  exact Real.log_injOn_pos.eq_iff (carlsonRReal_pos t hb hx) (carlsonRReal_pos s hb hx)

/-- At increasing orders, comparing the ratio mean with one compares the R-averages. -/
theorem carlsonRatioMeanReal_lt_one_iff {s t : ℝ} (hst : s < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRatioMeanReal s t b x < 1 ↔ carlsonRReal t b x < carlsonRReal s b x := by
  rw [carlsonRatioMeanReal, ite_eq_right hst.ne, Real.exp_lt_one_iff,
    div_lt_iff₀ (sub_pos.mpr hst), zero_mul, sub_neg]
  exact Real.log_lt_log_iff (carlsonRReal_pos t hb hx) (carlsonRReal_pos s hb hx)

/-- Dividing the nodes by their ratio mean normalizes that mean to one. -/
theorem carlsonRatioMeanReal_normalize {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRatioMeanReal s t b (fun i => (carlsonRatioMeanReal s t b x)⁻¹ * x i) = 1 := by
  rw [carlsonRatioMeanReal_mul hst hb hx (inv_pos.mpr (carlsonRatioMeanReal_pos s t b x)),
    inv_mul_cancel₀ (carlsonRatioMeanReal_pos s t b x).ne']

/-- Normalizing a ratio mean equalizes the two R-averages. -/
theorem carlsonRReal_ratio_normalize {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal t b (fun i => (carlsonRatioMeanReal s t b x)⁻¹ * x i) =
      carlsonRReal s b (fun i => (carlsonRatioMeanReal s t b x)⁻¹ * x i) :=
  (carlsonRatioMeanReal_eq_one_iff hst hb
    (fun i => mul_pos (inv_pos.mpr (carlsonRatioMeanReal_pos s t b x)) (hx i))).mp
    (carlsonRatioMeanReal_normalize hst hb hx)

end Carlson
