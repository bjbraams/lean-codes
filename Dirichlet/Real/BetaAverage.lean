/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Marginals
public import Dirichlet.Real.Average
public import ToMathlib.Analysis.SpecialFunctions.BetaConcentration

/-!
# Two-node Dirichlet averages and concentration

The two-coordinate marginal identity converts Dirichlet averages into beta
averages. Strict convexity of the test function then gives strict decrease in
concentration whenever the two nodes are distinct.
-/

open MeasureTheory Set
public noncomputable section
namespace ProbabilityTheory

/-- A two-node Dirichlet average is an ordinary beta average of an affine function. -/
theorem integral_dirichletMeasure_fin_two_affine {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ u : Fin 2 → ℝ, f (∑ i, u i * (![x, y] : Fin 2 → ℝ) i)
      ∂dirichletMeasure (![a, b])) =
    ∫ u, f (u * x + (1 - u) * y) ∂betaMeasure a b := by
  have hm : Measurable (fun u : ℝ => f (u * x + (1 - u) * y)) := hf.comp (by fun_prop)
  rw [← map_dirichletMeasure_fin_two ha hb,
    integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure (![a, b])] with u hu
  have hs : u 0 + u 1 = 1 := by simpa [Fin.sum_univ_two] using hu.2
  congr 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show u 1 = 1 - u 0 by linarith]

/-- A nonconstant affine parameterization preserves strict convexity on a convex domain. -/
private theorem strictConvexOn_segment {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    StrictConvexOn ℝ (Icc 0 1) (fun u => f (u * x + (1 - u) * y)) := by
  have hmem (u : ℝ) (hu : u ∈ Icc 0 1) : u * x + (1 - u) * y ∈ s := by
    exact hf.1 hx hy hu.1 (sub_nonneg.mpr hu.2) (by ring)
  refine ⟨convex_Icc _ _, ?_⟩
  intro u hu v hv huv p q hp hq hpq
  have hne : u * x + (1 - u) * y ≠ v * x + (1 - v) * y := by
    intro he
    have h : (u - v) * (x - y) = 0 := by nlinarith
    exact huv (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hxy)))
  have h := hf.2 (hmem u hu) (hmem v hv) hne hp hq hpq
  simp only [smul_eq_mul] at h ⊢
  have he : (p * u + q * v) * x + (1 - (p * u + q * v)) * y =
      p * (u * x + (1 - u) * y) + q * (v * x + (1 - v) * y) := by
    linear_combination -y * hpq
  rwa [he]

/-- A strictly convex two-node average strictly decreases as concentration increases. -/
theorem integral_dirichletMeasure_fin_two_lt_of_concentration {a b c d x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcd : c < d)
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    (hfcont : ContinuousOn f s) (hfmeas : Measurable f)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    (∫ u : Fin 2 → ℝ, f (∑ i, u i * (![x, y] : Fin 2 → ℝ) i)
      ∂dirichletMeasure (![d * a, d * b])) <
    ∫ u : Fin 2 → ℝ, f (∑ i, u i * (![x, y] : Fin 2 → ℝ) i)
      ∂dirichletMeasure (![c * a, c * b]) := by
  rw [integral_dirichletMeasure_fin_two_affine (mul_pos (hc.trans hcd) ha)
    (mul_pos (hc.trans hcd) hb) _ _ hfmeas,
    integral_dirichletMeasure_fin_two_affine (mul_pos hc ha) (mul_pos hc hb) _ _ hfmeas]
  apply integral_betaMeasure_lt_of_concentration ha hb hc hcd
    (strictConvexOn_segment hf hx hy hxy)
  apply hfcont.comp (by fun_prop)
  intro u hu
  exact hf.1 hx hy hu.1 (sub_nonneg.mpr hu.2) (by ring)

/-- A strictly concave two-node average strictly increases as concentration increases. -/
theorem integral_dirichletMeasure_fin_two_lt_of_concentration_concave {a b c d x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcd : c < d)
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f)
    (hfcont : ContinuousOn f s) (hfmeas : Measurable f)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    (∫ u : Fin 2 → ℝ, f (∑ i, u i * (![x, y] : Fin 2 → ℝ) i)
      ∂dirichletMeasure (![c * a, c * b])) <
    ∫ u : Fin 2 → ℝ, f (∑ i, u i * (![x, y] : Fin 2 → ℝ) i)
      ∂dirichletMeasure (![d * a, d * b]) := by
  have h := integral_dirichletMeasure_fin_two_lt_of_concentration ha hb hc hcd
    hf.neg hfcont.neg hfmeas.neg hx hy hxy
  simpa only [Pi.neg_apply, integral_neg, neg_lt_neg_iff] using h

end ProbabilityTheory
