/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Average

/-!
# Essential bounds of Dirichlet affine combinations

Positive Dirichlet laws have the same null sets as simplex volume. An almost-sure
upper bound for an affine combination therefore bounds every node, including
nodes at vertices of measure zero. No nontriviality assumption on the index type
is needed.
-/

open MeasureTheory Set
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Simplex volume is absolutely continuous with respect to any positive Dirichlet law. -/
theorem absolutelyContinuous_stdSimplexMeasure_dirichletMeasure {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    (Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) ≪
      dirichletMeasure b := by
  rw [← dirichletMeasure_restrict b, dirichletMeasure,
    restrict_withDensity (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  apply withDensity_absolutelyContinuous' (measurable_dirichletPdf b).aemeasurable
  filter_upwards [ae_mem_stdSimplexInterior] with u hu
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  rw [dirichletPdfReal, indicator_of_mem hu]
  exact mul_pos (one_div_pos.mpr (mvRealBeta_pos hb))
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hu.2 i) _)

/-- Every Dirichlet law is absolutely continuous with respect to each positive Dirichlet law. -/
theorem absolutelyContinuous_dirichletMeasure_dirichletMeasure (a : ι → ℝ) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) : dirichletMeasure a ≪ dirichletMeasure b := by
  have h := (absolutelyContinuous_dirichletMeasure a).restrict
    (Convexity.StdSimplex.coordinateSet ℝ ι)
  rw [dirichletMeasure_restrict] at h
  exact h.trans (absolutelyContinuous_stdSimplexMeasure_dirichletMeasure hb)

/-- An affine combination is almost surely bounded above exactly when all its nodes are. -/
theorem ae_dirichlet_affine_le_iff {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (r : ℝ) :
    (∀ᵐ u ∂dirichletMeasure b, ∑ i, u i * x i ≤ r) ↔ ∀ i, x i ≤ r := by
  classical
  constructor
  · intro h i
    by_contra hi
    have hi : r < x i := lt_of_not_ge hi
    let C := ∑ j, b j
    let B := ∑ j, b j * x j
    let a := (|r * C - B| + 1) / (x i - r)
    have ha : 0 < a := div_pos (by positivity) (sub_pos.mpr hi)
    let b' := fun j => b j + if j = i then a else 0
    have hb' : b' ∈ mvRealBetaDomain := by
      intro j
      exact add_pos_of_pos_of_nonneg (hb j) (by split_ifs <;> positivity)
    let := isProbabilityMeasure_dirichletMeasure hb'
    have hs : ∑ j, b' j = C + a := by simp [b', C, Finset.sum_add_distrib]
    have hn : ∑ j, b' j * x j = B + a * x i := by
      simp [b', B, add_mul, Finset.sum_add_distrib, ite_mul]
    have ht := integral_mono_ae (integrable_dirichletMeasure_of_continuousOn hb' (by fun_prop))
      (integrable_const r)
      ((absolutelyContinuous_dirichletMeasure_dirichletMeasure b' hb).ae_le h)
    rw [integral_dirichletMeasure_affine hb', integral_const, probReal_univ, one_smul] at ht
    simp_rw [div_mul_eq_mul_div] at ht
    rw [← Finset.sum_div, hs, hn] at ht
    have hC : 0 < C := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
    have ht := (div_le_iff₀ (add_pos hC ha)).mp ht
    have he : a * (x i - r) = |r * C - B| + 1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hi.ne')
    have habs := le_abs_self (r * C - B)
    nlinarith
  · intro h
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    exact dirichlet_affine_mem (convex_Iic r) h hu

/-- An affine combination is almost surely bounded below exactly when all its nodes are. -/
theorem ae_le_dirichlet_affine_iff {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (r : ℝ) :
    (∀ᵐ u ∂dirichletMeasure b, r ≤ ∑ i, u i * x i) ↔ ∀ i, r ≤ x i := by
  have h := ae_dirichlet_affine_le_iff (x := fun i => -x i) hb (-r)
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] using h

end ProbabilityTheory
