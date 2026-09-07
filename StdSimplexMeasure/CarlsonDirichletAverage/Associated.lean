/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage.Deriv

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

public noncomputable section CarlsonAssociated

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

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
