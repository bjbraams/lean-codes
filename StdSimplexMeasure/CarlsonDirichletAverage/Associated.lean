/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.CarlsonDirichletAverage.Deriv
public import SeveralComplexVariables.ParametricIntegral

import Mathlib.Topology.MetricSpace.Thickening

/-!
# Associated Carlson Dirichlet averages

This file develops the parameter-shift relations of [Carl77, Section 5.6].  We state the
relations first for the Gamma-regularized average.  In this normalization Carlson's weights
`b i / ∑ j, b j` are absorbed by the Gamma factors, leaving coefficients `b i`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.6,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonAssociated

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's affine form, regarded as a continuous complex-linear map in its node variables. -/
private noncomputable def carlsonAffineFormCLM (u : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (u i : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)

/-- Evaluation of the continuous-linear version of Carlson's affine form. -/
private lemma carlsonAffineFormCLM_apply (u : ι → ℝ) (z : ι → ℂ) :
    carlsonAffineFormCLM u z = carlsonAffineForm z u := by
  simp [carlsonAffineFormCLM, carlsonAffineForm]

/-- On the standard simplex, the operator norm of Carlson's affine form is at most one. -/
private lemma norm_carlsonAffineFormCLM_le_one {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) : ‖carlsonAffineFormCLM u‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [carlsonAffineFormCLM_apply]
  calc
    ‖carlsonAffineForm z u‖ ≤ ∑ i, u i * ‖z i‖ := by
      unfold carlsonAffineForm
      calc
        ‖∑ i, (u i : ℂ) * z i‖ ≤ ∑ i, ‖(u i : ℂ) * z i‖ := norm_sum_le _ _
        _ = ∑ i, u i * ‖z i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    _ ≤ ∑ i, u i * ‖z‖ := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (hu.1 i)
    _ = ‖z‖ := by rw [← Finset.sum_mul, hu.2, one_mul]
    _ = 1 * ‖z‖ := by rw [one_mul]

/-- Moving the node vector moves every simplex affine combination by at most the supremum-norm
distance between the node vectors. -/
private lemma dist_carlsonAffineForm_le_norm_sub (z w : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
    dist (carlsonAffineForm w u) (carlsonAffineForm z u) ≤ ‖w - z‖ := by
  rw [← carlsonAffineFormCLM_apply u w, ← carlsonAffineFormCLM_apply u z]
  rw [dist_eq_norm, ← map_sub]
  calc
    ‖carlsonAffineFormCLM u (w - z)‖ ≤ ‖carlsonAffineFormCLM u‖ * ‖w - z‖ :=
      (carlsonAffineFormCLM u).le_opNorm _
    _ ≤ 1 * ‖w - z‖ := mul_le_mul_of_nonneg_right
      (norm_carlsonAffineFormCLM_le_one hu) (norm_nonneg _)
    _ = ‖w - z‖ := one_mul _

/-- The Dirichlet parameter vector obtained by increasing coordinate `i` by one. -/
def addDirichletUnit (b : ι → ℂ) (i : ι) : ι → ℂ :=
  Function.update b i (b i + 1)

/-- Carlson's native (unregularized) Dirichlet average on the convergence region. -/
def carlsonDirichletAverage (b z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonDirichletAverage b z f

omit [Fintype ι] in
/-- A positive unit shift preserves the native convergence region. -/
theorem addDirichletUnit_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) :
    addDirichletUnit b i ∈ mvBetaConvergent := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [addDirichletUnit] using add_pos_of_pos_of_nonneg (hb i) (by norm_num : 0 ≤ (1 : ℝ))
  · simpa [addDirichletUnit, hji] using hb j

/-- Increasing one Dirichlet parameter by one multiplies the regularized density by the
corresponding simplex coordinate, up to the factor `b i`. -/
theorem mul_regDirichletDensity_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (u : ι → ℝ) :
    b i * regDirichletDensity (addDirichletUnit b i) u =
      (u i : ℂ) * regDirichletDensity b u := by
  classical
  by_cases hu : u ∈ stdSimplexInterior
  · rw [regDirichletDensity, Set.indicator_of_mem hu]
    rw [regDirichletDensity, Set.indicator_of_mem hu]
    have hbi : b i ≠ 0 := ne_zero_of_re_pos (hb i)
    have hui : (u i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu.2 i).ne'
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
        Gamma (addDirichletUnit b i j))]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (b j - 1) / Gamma (b j))]
    have hoff :
        ∏ j ∈ Finset.univ \ {i},
            (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
              Gamma (addDirichletUnit b i j) =
          ∏ j ∈ Finset.univ \ {i}, (u j : ℂ) ^ (b j - 1) / Gamma (b j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        simp at hj
      simp [addDirichletUnit, hji]
    rw [hoff]
    simp only [addDirichletUnit, Function.update_self]
    rw [Gamma_add_one (b i) hbi]
    rw [show (u i : ℂ) ^ (b i + 1 - 1) = (u i : ℂ) ^ b i by ring_nf]
    rw [cpow_sub _ _ hui, cpow_one]
    field_simp
  · simp [regDirichletDensity, hu]

/-- Integral form of the regularized one-coordinate parameter-shift identity. -/
theorem mul_regDirichletIntegral_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (f : (ι → ℝ) → ℂ) :
    b i * regDirichletIntegral (addDirichletUnit b i) f =
      regDirichletIntegral b (fun u ↦ (u i : ℂ) * f u) := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
  intro u _
  dsimp only
  rw [← mul_assoc, mul_regDirichletDensity_addDirichletUnit hb]
  ring

/-- Regularized form of Carlson's relation 5.6-1(4): an average is the sum of its
one-coordinate positive parameter shifts. -/
theorem regCarlsonDirichletAverage_eq_sum_addDirichletUnit
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (stdSimplex ℝ ι)) :
    regCarlsonDirichletAverage b z f =
      ∑ i, b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f := by
  simp_rw [regCarlsonDirichletAverage,
    mul_regDirichletIntegral_addDirichletUnit hb]
  unfold regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
    intro u hu
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_mul]
    have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
    rw [hsum, one_mul]
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf)

/-- Carlson's relation 5.6-1(4) in its original normalization: an average is the weighted
sum of its positive unit shifts, with weights `b i / ∑ j, b j`. -/
theorem carlsonDirichletAverage_eq_sum_addDirichletUnit [Nonempty ι]
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (stdSimplex ℝ ι)) :
    carlsonDirichletAverage b z f =
      ∑ i, (b i / ∑ j, b j) * carlsonDirichletAverage (addDirichletUnit b i) z f := by
  let c : ℂ := ∑ i, b i
  have hcpos : 0 < c.re := by
    simpa [c] using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  have hc : c ≠ 0 := ne_zero_of_re_pos hcpos
  have hsum (i : ι) : ∑ j, addDirichletUnit b i j = c + 1 := by
    rw [sum_eq_apply_add_sum_ne _ i]
    have hoff : ∑ j : {j // j ≠ i}, addDirichletUnit b i j =
        ∑ j : {j // j ≠ i}, b j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [addDirichletUnit, j.property]
    rw [hoff]
    rw [show c = b i + ∑ j : {j // j ≠ i}, b j by
      simpa [c] using sum_eq_apply_add_sum_ne b i]
    simp [addDirichletUnit]
    ring
  unfold carlsonDirichletAverage
  rw [regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z f hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsum, Gamma_add_one c hc]
  change Gamma c * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f) =
    (b i / c) * (c * Gamma c * regCarlsonDirichletAverage (addDirichletUnit b i) z f)
  field_simp [hc]

/-! ## Differentiation and associated averages -/

/-- Differentiation under a regularized Carlson average under a local uniform bound for the
derivative on the affine combinations met by the simplex. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update_of_bound
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} {s : Set ℂ} (hs : s ∈ nhds (z i))
    (hf : ∀ w ∈ s, ∀ u ∈ stdSimplex ℝ ι,
      HasDerivAt f (f' (carlsonAffineForm (Function.update z i w) u))
        (carlsonAffineForm (Function.update z i w) u))
    (hf'_continuous : ∀ w ∈ s, ContinuousOn f'
      (carlsonAffineForm (Function.update z i w) '' stdSimplex ℝ ι)) {C : ℝ}
    (hf'_bound : ∀ w ∈ s, ∀ u ∈ stdSimplex ℝ ι,
      ‖f' (carlsonAffineForm (Function.update z i w) u)‖ ≤ C) :
    HasDerivAt
      (fun w ↦ regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * f' (carlsonAffineForm z u)))
      (z i) := by
  let μ : Measure (ι → ℝ) :=
    (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let F : ℂ → (ι → ℝ) → ℂ := fun w u ↦
    regDirichletDensity b u * f (carlsonAffineForm (Function.update z i w) u)
  let F' : ℂ → (ι → ℝ) → ℂ := fun w u ↦
    regDirichletDensity b u * ((u i : ℂ) * f' (carlsonAffineForm
      (Function.update z i w) u))
  let bound : (ι → ℝ) → ℝ := fun u ↦ C * ‖regDirichletDensity b u‖
  have hzi : z i ∈ s := mem_of_mem_nhds hs
  have hf_comp (w : ℂ) (hw : w ∈ s) :
      ContinuousOn (fun u : ι → ℝ ↦
        f (carlsonAffineForm (Function.update z i w) u)) (stdSimplex ℝ ι) := by
    have hfon : ContinuousOn f
        (carlsonAffineForm (Function.update z i w) '' stdSimplex ℝ ι) := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact (hf w hw u hu).continuousAt.continuousWithinAt
    exact hfon.comp (continuous_carlsonAffineForm _).continuousOn
      (fun u hu ↦ ⟨u, hu, rfl⟩)
  have hF_meas : ∀ᶠ w in nhds (z i), AEStronglyMeasurable (F w) μ := by
    filter_upwards [hs] with w hw
    exact (integrableOn_regDirichletDensity_mul b hb
      (hf_comp w hw)).1
  have hF_int : Integrable (F (z i)) μ := by
    dsimp only [F, μ]
    rw [Function.update_eq_self]
    change IntegrableOn (fun u ↦ regDirichletDensity b u * f (carlsonAffineForm z u))
      (stdSimplex ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa using integrableOn_regDirichletDensity_mul b hb
      (by simpa using hf_comp (z i) hzi)
  have hF'_meas : AEStronglyMeasurable (F' (z i)) μ := by
    have hf'_comp : ContinuousOn (fun u : ι → ℝ ↦
        f' (carlsonAffineForm z u)) (stdSimplex ℝ ι) := by
      change ContinuousOn (f' ∘ carlsonAffineForm z) (stdSimplex ℝ ι)
      exact (hf'_continuous (z i) hzi).comp
        (continuous_carlsonAffineForm z).continuousOn
          (fun u hu ↦ ⟨u, hu, by rw [Function.update_eq_self]⟩)
    have hcont : ContinuousOn (fun u : ι → ℝ ↦
        (u i : ℂ) * f' (carlsonAffineForm z u)) (stdSimplex ℝ ι) :=
      (Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf'_comp
    simpa [F', μ] using
      (integrableOn_regDirichletDensity_mul b hb hcont).1
  have hbound_int : Integrable bound μ := by
    have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ := by
      change IntegrableOn (fun u ↦ regDirichletDensity b u)
        (stdSimplex ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
      simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
        (continuousOn_const : ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ))
          (stdSimplex ℝ ι))
    exact hdens.norm.const_mul C
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ s, ‖F' w u‖ ≤ bound u := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    intro w hw
    simp only [F', bound, norm_mul]
    calc
      ‖regDirichletDensity b u‖ *
          (‖(u i : ℂ)‖ * ‖f' (carlsonAffineForm (Function.update z i w) u)‖)
          ≤ ‖regDirichletDensity b u‖ * (1 * C) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul
            · simpa [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)] using
                (show u i ≤ 1 by
                  calc
                    u i ≤ ∑ j, u j := Finset.single_le_sum
                      (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
                    _ = 1 := hu.2)
            · exact hf'_bound w hw u hu
            · exact norm_nonneg _
            · norm_num
      _ = C * ‖regDirichletDensity b u‖ := by ring
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ s, HasDerivAt (F · u) (F' w u) w := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu w hw
    dsimp only [F, F']
    simpa [F, F'] using (HasDerivAt.comp_carlsonAffineForm_update i
      (hf w hw u hu)).const_mul
        (regDirichletDensity b u)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (x₀ := z i) hs hF_meas hF_int hF'_meas
      hbound hbound_int hdiff |>.2
  simpa [regCarlsonDirichletAverage, regDirichletIntegral, F, F', μ] using h

/-- Differentiation under a regularized Carlson average when the derivative of the
univariate function is globally bounded. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    HasDerivAt
      (fun w ↦ regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * f' (carlsonAffineForm z u)))
      (z i) := by
  apply hasDerivAt_regCarlsonDirichletAverage_update_of_bound hb i Filter.univ_mem
    (fun w hw u hu ↦ hf _) (fun w hw ↦ hf'_continuous.continuousOn)
  intro w hw u hu
  exact hf'_bound _

set_option maxHeartbeats 1000000 in
/-- Differentiation under a regularized Carlson average when the averaged function is
holomorphic on a convex neighborhood of all the nodes. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i : ι) :
    HasDerivAt
      (fun w => regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u => (u i : ℂ) * deriv f (carlsonAffineForm z u)))
      (z i) := by
  let K : Set ℂ := convexHull ℝ (Set.range z)
  have hKcompact : IsCompact K := (Set.finite_range z).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ₁, hδ₁, hδ₁compact⟩ := hKcompact.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hδ₂Ω⟩ := hKcompact.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδcompact : IsCompact (Metric.cthickening δ K) :=
    hδ₁compact.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono (min_le_left _ _) K)
  have hδΩ : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hδ₂Ω
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
  obtain ⟨C₀, hC₀⟩ := hδcompact.bddAbove_image (hderivCont.mono hδΩ).norm
  let C : ℝ := max C₀ 0
  have hC : ∀ q ∈ Metric.cthickening δ K, ‖deriv f q‖ ≤ C := fun q hq =>
    (hC₀ (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  let s : Set ℂ := Metric.ball (z i) δ
  have hs : s ∈ nhds (z i) := Metric.ball_mem_nhds _ hδ
  have hui_le_one {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) : u i ≤ 1 := by
    calc
      u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
      _ = 1 := hu.2
  have hnear {w : ℂ} (hw : w ∈ s) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
      carlsonAffineForm (Function.update z i w) u ∈ Metric.cthickening δ K := by
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    apply Metric.mem_cthickening_of_dist_le _ _ δ K hbase
    have hwi : ‖w - z i‖ < δ := by
      simpa [s, Metric.mem_ball, dist_eq_norm] using hw
    rw [carlsonAffineForm_update, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hui_le_one hu)).trans hwi.le
  apply hasDerivAt_regCarlsonDirichletAverage_update_of_bound hb i hs
  · intro w hw u hu
    exact (hf _ (hδΩ (hnear hw hu))).differentiableAt.hasDerivAt
  · intro w hw
    exact hderivCont.mono fun q hq => by
      obtain ⟨u, hu, rfl⟩ := hq
      exact hδΩ (hnear hw hu)
  · intro w hw u hu
    exact hC _ (hnear hw hu)

/-- **Carlson 5.3-2, first-order form.** For a function holomorphic on a convex node domain,
differentiation with respect to node `i` raises the corresponding Dirichlet parameter. -/
theorem carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i : ι) :
    carlsonPartialDeriv i (fun w => regCarlsonDirichletAverage b w f) z =
      b i * regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f) := by
  rw [carlsonPartialDeriv,
    (hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
      hΩopen hΩconv hf hb hz i).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u => deriv f (carlsonAffineForm z u))).symm

/-- Regularized form of Carlson's relation 5.6-1(5): differentiating with respect to `z i`
produces the associated average with parameter `b i` increased by one. -/
theorem carlsonPartialDeriv_regCarlsonDirichletAverage
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    carlsonPartialDeriv i (fun z ↦ regCarlsonDirichletAverage b z f) z =
      b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f' := by
  rw [carlsonPartialDeriv]
  rw [(hasDerivAt_regCarlsonDirichletAverage_update hb i hf
    hf'_continuous hf'_bound).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ f' (carlsonAffineForm z u))).symm

/-- Iteration of `addDirichletUnit` in the order matching
`carlsonIteratedPartialDeriv`. -/
private def iteratedAddDirichletUnit : List ι → (ι → ℂ) → (ι → ℂ)
  | [], b => b
  | i :: is, b => addDirichletUnit (iteratedAddDirichletUnit is b) i

/-- The product of the successive Dirichlet parameters introduced by repeated parameter
shifts. -/
private def iteratedDirichletShiftCoeff : List ι → (ι → ℂ) → ℂ
  | [], _ => 1
  | i :: is, b =>
      iteratedDirichletShiftCoeff is b * iteratedAddDirichletUnit is b i

omit [Fintype ι] in
/-- Iterated positive unit shifts preserve the native Dirichlet convergence region. -/
private lemma iteratedAddDirichletUnit_mem {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (is : List ι) :
    iteratedAddDirichletUnit is b ∈ mvBetaConvergent := by
  induction is with
  | nil => exact hb
  | cons i is ih => exact addDirichletUnit_mem_mvBetaConvergent ih i

/-- Repeated density shifts convert a product of simplex coordinates into successive
positive unit shifts of the Dirichlet parameters. -/
private lemma iteratedDirichletShiftCoeff_mul_regDirichletIntegral
    (is : List ι) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (g : (ι → ℝ) → ℂ) :
    iteratedDirichletShiftCoeff is b *
        regDirichletIntegral (iteratedAddDirichletUnit is b) g =
      regDirichletIntegral b (fun u =>
        (is.map fun i => (u i : ℂ)).prod * g u) := by
  induction is generalizing g with
  | nil => simp [iteratedDirichletShiftCoeff, iteratedAddDirichletUnit]
  | cons i is ih =>
      rw [iteratedDirichletShiftCoeff, iteratedAddDirichletUnit, mul_assoc,
        mul_regDirichletIntegral_addDirichletUnit
          (iteratedAddDirichletUnit_mem hb is) i,
        ih (g := fun u => (u i : ℂ) * g u)]
      apply regDirichletIntegral_congr
      intro u hu
      simp only [List.map_cons, List.prod_cons]
      ring

omit [Fintype ι] in
/-- Updating one node to another point of the node domain preserves containment of the node
range in that domain. -/
private lemma range_update_subset {Ω : Set ℂ} {z : ι → ℂ}
    (hz : Set.range z ⊆ Ω) {i : ι} {w : ℂ} (hw : w ∈ Ω) :
    Set.range (Function.update z i w) ⊆ Ω := by
  intro q hq
  obtain ⟨j, rfl⟩ := hq
  by_cases hji : j = i
  · subst j
    simpa using hw
  · simpa [hji] using hz (Set.mem_range_self j)

set_option maxHeartbeats 1000000 in
/-- An iterated node derivative is an average with successively shifted parameters and the
corresponding iterated derivative of the averaged function. -/
private lemma carlsonIteratedPartialDeriv_eq_iteratedShift
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (is : List ι) :
    carlsonIteratedPartialDeriv is
        (fun w => regCarlsonDirichletAverage b w f) z =
      iteratedDirichletShiftCoeff is b *
        regCarlsonDirichletAverage (iteratedAddDirichletUnit is b) z
          (iteratedDeriv is.length f) := by
  induction is generalizing z with
  | nil => simp [carlsonIteratedPartialDeriv, iteratedDirichletShiftCoeff,
      iteratedAddDirichletUnit]
  | cons i is ih =>
      rw [carlsonIteratedPartialDeriv]
      unfold carlsonPartialDeriv
      have hzi : z i ∈ Ω := hz (Set.mem_range_self i)
      have heq :
          (fun w => carlsonIteratedPartialDeriv is
            (fun y => regCarlsonDirichletAverage b y f) (Function.update z i w)) =ᶠ[nhds (z i)]
          (fun w => iteratedDirichletShiftCoeff is b *
            regCarlsonDirichletAverage (iteratedAddDirichletUnit is b)
              (Function.update z i w) (iteratedDeriv is.length f)) := by
        filter_upwards [hΩopen.mem_nhds hzi] with w hw
        exact ih (range_update_subset hz hw)
      rw [heq.deriv_eq]
      have hfiter : AnalyticOnNhd ℂ (iteratedDeriv is.length f) Ω := by
        simpa [iteratedDeriv_eq_iterate] using hf.iterated_deriv is.length
      have hder := hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
        hΩopen hΩconv hfiter (iteratedAddDirichletUnit_mem hb is) hz i
      rw [(hder.const_mul (iteratedDirichletShiftCoeff is b)).deriv]
      rw [← mul_regDirichletIntegral_addDirichletUnit
        (iteratedAddDirichletUnit_mem hb is) i]
      simp only [List.length_cons, iteratedDirichletShiftCoeff,
        iteratedAddDirichletUnit, iteratedDeriv_succ]
      rw [regCarlsonDirichletAverage]
      ring

/-- **Carlson 5.3-2, regularized complex form.** Successive partial differentiation may be
taken under a Carlson average when the nodes lie in a convex domain of holomorphy. -/
theorem carlsonIteratedPartialDeriv_regCarlsonDirichletAverage
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (is : List ι) :
    carlsonIteratedPartialDeriv is
        (fun w => regCarlsonDirichletAverage b w f) z =
      regDirichletIntegral b (fun u =>
        (is.map fun i => (u i : ℂ)).prod *
          iteratedDeriv is.length f (carlsonAffineForm z u)) := by
  rw [carlsonIteratedPartialDeriv_eq_iteratedShift hΩopen hΩconv hf hb hz]
  exact iteratedDirichletShiftCoeff_mul_regDirichletIntegral is hb
    (fun u => iteratedDeriv is.length f (carlsonAffineForm z u))

/-- **Carlson 5.3-3, node-variable part.** On a convex domain of holomorphy, a regularized
Carlson average is analytic in all node variables throughout the corresponding product domain. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (fun z => regCarlsonDirichletAverage b z f)
      {z : ι → ℂ | Set.range z ⊆ Ω} := by
  classical
  let U : Set (ι → ℂ) := {z | Set.range z ⊆ Ω}
  have hU : IsOpen U := by
    rw [show U = Set.pi Set.univ (fun _ => Ω) by
      ext z
      simp [U, Set.range_subset_iff]]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hΩopen
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let F : (ι → ℂ) → (ι → ℝ) → ℂ := fun z u =>
    regDirichletDensity b u * f (carlsonAffineForm z u)
  let L : (ι → ℝ) → ((ι → ℂ) →L[ℂ] ℂ) := carlsonAffineFormCLM
  refine analyticOnNhd_integral_of_dominated_of_fderiv_le
    (μ := μ) (U := U) (F := F) hU ?_
  intro z hz
  let K : Set ℂ := convexHull ℝ (Set.range z)
  have hKcompact : IsCompact K := (Set.finite_range z).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ₁, hδ₁, hδ₁compact⟩ := hKcompact.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hδ₂Ω⟩ := hKcompact.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδcompact : IsCompact (Metric.cthickening δ K) :=
    hδ₁compact.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono (min_le_left _ _) K)
  have hδΩ : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hδ₂Ω
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
  obtain ⟨C₀, hC₀⟩ := hδcompact.bddAbove_image (hderivCont.mono hδΩ).norm
  let C : ℝ := max C₀ 0
  have hC : ∀ q ∈ Metric.cthickening δ K, ‖deriv f q‖ ≤ C := fun q hq =>
    (hC₀ (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  let s : Set (ι → ℂ) := Metric.ball z δ
  have hs : s ∈ nhds z := Metric.ball_mem_nhds z hδ
  let bound : (ι → ℝ) → ℝ := fun u => C * ‖regDirichletDensity b u‖
  let F' : (ι → ℂ) → (ι → ℝ) → ((ι → ℂ) →L[ℂ] ℂ) := fun y u =>
    regDirichletDensity b u • ((deriv f (carlsonAffineForm y u)) • L u)
  have hdens : Integrable (fun u => regDirichletDensity b u) μ := by
    change IntegrableOn (fun u => regDirichletDensity b u)
      (stdSimplex ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ => (1 : ℂ)) (stdSimplex ℝ ι))
  refine ⟨s, bound, F', hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hs] with y hy
    have hyU : Set.range y ⊆ Ω := by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      have hiK : z i ∈ K := by
        apply subset_convexHull ℝ
        exact Set.mem_range_self i
      have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
      apply hδΩ
      exact Metric.mem_cthickening_of_dist_le (y i) (z i) δ K hiK
        ((dist_le_pi_dist y z i).trans (le_of_lt hy'))
    have hcont : ContinuousOn (fun u => f (carlsonAffineForm y u)) (stdSimplex ℝ ι) :=
      hf.continuousOn.comp (continuous_carlsonAffineForm y).continuousOn fun u hu =>
        (convexHull_min hyU hΩconv) (carlsonAffineForm_mem_convexHull y hu)
    exact (integrableOn_regDirichletDensity_mul b hb hcont).aestronglyMeasurable
  · change IntegrableOn (fun u => regDirichletDensity b u * f (carlsonAffineForm z u))
      (stdSimplex ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    exact integrableOn_regDirichletDensity_mul b hb
      (hf.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn fun u hu =>
        hKΩ (carlsonAffineForm_mem_convexHull z hu))
  · have hcomp : ContinuousOn (fun u => deriv f (carlsonAffineForm z u))
        (stdSimplex ℝ ι) :=
      hderivCont.comp (continuous_carlsonAffineForm z).continuousOn fun u hu =>
        hKΩ (carlsonAffineForm_mem_convexHull z hu)
    have hL : Continuous (fun u : ι → ℝ => L u) := by
      dsimp only [L, carlsonAffineFormCLM]
      fun_prop
    have hcont : ContinuousOn (fun u =>
        (deriv f (carlsonAffineForm z u)) • L u) (stdSimplex ℝ ι) :=
      hcomp.smul hL.continuousOn
    exact hdens.aestronglyMeasurable.smul
      (hcont.aestronglyMeasurable (isClosed_stdSimplex ℝ ι).measurableSet)
  · filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    intro y hy
    have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    have hnear : carlsonAffineForm y u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le _ _ δ K hbase
        ((dist_carlsonAffineForm_le_norm_sub z y hu).trans (by
          simpa [dist_eq_norm] using le_of_lt hy'))
    dsimp only [F', bound]
    rw [norm_smul, norm_smul]
    calc
      ‖regDirichletDensity b u‖ *
          (‖deriv f (carlsonAffineForm y u)‖ * ‖L u‖) ≤
          ‖regDirichletDensity b u‖ * (C * 1) := by
            gcongr
            · exact hC _ hnear
            · exact norm_carlsonAffineFormCLM_le_one hu
      _ = C * ‖regDirichletDensity b u‖ := by ring
  · exact hdens.norm.const_mul C
  · filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    intro y hy
    have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    have hnear : carlsonAffineForm y u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le _ _ δ K hbase
        ((dist_carlsonAffineForm_le_norm_sub z y hu).trans (by
          simpa [dist_eq_norm] using le_of_lt hy'))
    have hf' : HasDerivAt f (deriv f (carlsonAffineForm y u))
        (carlsonAffineForm y u) :=
      (hf _ (hδΩ hnear)).differentiableAt.hasDerivAt
    have hfL : HasDerivAt f (deriv f (carlsonAffineForm y u)) (L u y) := by
      simpa only [L, carlsonAffineFormCLM_apply] using hf'
    have hcomp := hfL.comp_hasFDerivAt y (L u).hasFDerivAt
    have hmul := hcomp.const_mul (regDirichletDensity b u)
    simpa only [F, F', L, Function.comp_apply, carlsonAffineFormCLM_apply,
      smul_eq_mul] using hmul

/-- **Carlson 5.3-3, joint form.** The regularized Carlson average is jointly analytic in
the Dirichlet parameters and nodes on the native convergence domain and a convex node domain. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonDirichletAverage p.1 p.2 f)
      {p | p.1 ∈ mvBetaConvergent ∧ Set.range p.2 ⊆ Ω} := by
  /- Separate analyticity is now available: the node-variable component is the preceding
  theorem, and the parameter-variable component is `regDirichletIntegral_analyticOn`.
  Joint analyticity on the product domain follows by Osgood on `ι ⊕ ι` (via
  `ContinuousLinearEquiv.sumPiEquivProdPi`) after a locally dominated joint-continuity
  argument for the parametric integral. -/
  sorry

/-- Carlson's relation 5.6-1(5) in its original normalization.  The coefficient is the
weight `b i / ∑ j, b j`. -/
theorem carlsonPartialDeriv_carlsonDirichletAverage [Nonempty ι]
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    carlsonPartialDeriv i (fun z ↦ carlsonDirichletAverage b z f) z =
      (b i / ∑ j, b j) * carlsonDirichletAverage (addDirichletUnit b i) z f' := by
  let c : ℂ := ∑ j, b j
  have hcpos : 0 < c.re := by
    simpa [c] using Finset.sum_pos (fun j _ ↦ hb j) Finset.univ_nonempty
  have hc : c ≠ 0 := ne_zero_of_re_pos hcpos
  have hsum : ∑ j, addDirichletUnit b i j = c + 1 := by
    rw [sum_eq_apply_add_sum_ne _ i]
    have hoff : ∑ j : {j // j ≠ i}, addDirichletUnit b i j =
        ∑ j : {j // j ≠ i}, b j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [addDirichletUnit, j.property]
    rw [hoff]
    rw [show c = b i + ∑ j : {j // j ≠ i}, b j by
      simpa [c] using sum_eq_apply_add_sum_ne b i]
    simp [addDirichletUnit]
    ring
  have hder := hasDerivAt_regCarlsonDirichletAverage_update (z := z) hb i hf
    hf'_continuous hf'_bound
  unfold carlsonPartialDeriv carlsonDirichletAverage
  rw [deriv_const_mul _ hder.differentiableAt, hder.deriv]
  rw [← mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ f' (carlsonAffineForm z u))]
  rw [hsum, Gamma_add_one c hc]
  change Gamma c * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f') =
    (b i / c) * (c * Gamma c * regCarlsonDirichletAverage (addDirichletUnit b i) z f')
  field_simp [hc]

/-- Compatibility spelling for the density-shift lemma used by the earlier `R`-function
development. -/
theorem mul_regDirichletDensity_update_add_one {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (u : ι → ℝ) :
    b i * regDirichletDensity (Function.update b i (b i + 1)) u =
      (u i : ℂ) * regDirichletDensity b u := by
  simpa [addDirichletUnit] using mul_regDirichletDensity_addDirichletUnit hb i u

/-- Compatibility spelling for the integral parameter-shift lemma. -/
theorem mul_regDirichletIntegral_update_add_one {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (f : (ι → ℝ) → ℂ) :
    b i * regDirichletIntegral (Function.update b i (b i + 1)) f =
      regDirichletIntegral b (fun u ↦ (u i : ℂ) * f u) := by
  simpa [addDirichletUnit] using mul_regDirichletIntegral_addDirichletUnit hb i f

end DirichletTransform

end CarlsonAssociated
