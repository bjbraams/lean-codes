/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.DifferentialOperators
public import Dirichlet.Complex.Analytic
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

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonAssociated

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]



/-- The Dirichlet parameter vector obtained by increasing coordinate `i` by one. -/
def addDirichletUnit (b : ι → ℂ) (i : ι) : ι → ℂ :=
  Function.update b i (b i + 1)

/-- A unit parameter shift increases the total parameter by one. -/
@[simp] theorem sum_addDirichletUnit (b : ι → ℂ) (i : ι) :
    ∑ j, addDirichletUnit b i j = (∑ j, b j) + 1 := by
  unfold addDirichletUnit
  rw [Fintype.sum_eq_add_sum_subtype_ne (Function.update b i (b i + 1)) i,
    Fintype.sum_eq_add_sum_subtype_ne b i]
  simp [add_assoc, add_comm, add_left_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Function.update_of_ne j.property _ _

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
  have hsum (i : ι) : ∑ j, addDirichletUnit b i j = c + 1 := sum_addDirichletUnit b i
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
  obtain ⟨δ, hδ, hδΩ, C, hCnonneg, hC⟩ :=
    hf.exists_cthickening_deriv_bound hΩopen hKcompact hKΩ
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
  let s : Set ℂ := Metric.ball (z i) δ
  have hs : s ∈ nhds (z i) := Metric.ball_mem_nhds _ hδ
  have hnear {w : ℂ} (hw : w ∈ s) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
      carlsonAffineForm (Function.update z i w) u ∈ Metric.cthickening δ K := by
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    apply Metric.mem_cthickening_of_dist_le _ _ δ K hbase
    have hwi : ‖w - z i‖ < δ := by
      simpa [s, Metric.mem_ball, dist_eq_norm] using hw
    rw [carlsonAffineForm_update, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mem_Icc_of_mem_stdSimplex hu i).2).trans hwi.le
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
  obtain ⟨δ, hδ, hδΩ, C, hCnonneg, hC⟩ :=
    hf.exists_cthickening_deriv_bound hΩopen hKcompact hKΩ
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
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

/-- Joint continuity follows from a common integrable Dirichlet majorant near each
parameter and node vector. -/
private lemma continuousAt_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {p : (ι → ℂ) × (ι → ℂ)}
    (hb : p.1 ∈ mvBetaConvergent) (hz : Set.range p.2 ⊆ Ω) :
    ContinuousAt (fun q : (ι → ℂ) × (ι → ℂ) => regCarlsonDirichletAverage q.1 q.2 f) p := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    simpa [regCarlsonDirichletAverage, regDirichletIntegral, stdSimplexMeasure_empty] using
      (continuousAt_const : ContinuousAt (fun _ : (ι → ℂ) × (ι → ℂ) => (0 : ℂ)) p)
  let := hι
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let K := convexHull ℝ (Set.range p.2)
  have hK : IsCompact K := (Set.finite_range p.2).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ₁, hδ₁, hc₁⟩ := hK.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hK.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hc : IsCompact (Metric.cthickening δ K) := hc₁.of_isClosed_subset
    Metric.isClosed_cthickening (Metric.cthickening_mono (min_le_left _ _) K)
  have hsub : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hc₂
  obtain ⟨C, hC⟩ := hc.bddAbove_image (hf.mono hsub).norm
  let a : ι → ℂ := fun i => ((p.1 i).re / 2 : ℝ)
  have ha : a ∈ mvBetaConvergent := fun i => by simpa [a] using half_pos (hb i)
  have hevent : ∀ᶠ q : (ι → ℂ) × (ι → ℂ) in nhds p,
      (∀ i, (a i).re < (q.1 i).re) ∧ dist q.2 p.2 < δ := by
    apply Filter.Eventually.and
    · apply Filter.eventually_all.mpr
      intro i
      apply (isOpen_lt continuous_const
        (Complex.continuous_re.comp ((continuous_apply i).comp continuous_fst))).eventually_mem
      simpa [a] using half_lt_self (hb i)
    · exact (continuous_snd.continuousAt.dist continuousAt_const).eventually_lt_const
        (by simpa using hδ)
  have hnear {q : (ι → ℂ) × (ι → ℂ)} (hq : dist q.2 p.2 < δ)
      {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
      carlsonAffineForm q.2 u ∈ Metric.cthickening δ K :=
    Metric.mem_cthickening_of_dist_le _ _ δ K (carlsonAffineForm_mem_convexHull p.2 hu)
      ((dist_carlsonAffineForm_le_norm_sub p.2 q.2 hu).trans (by simpa [dist_eq_norm] using hq.le))
  let F := fun (q : (ι → ℂ) × (ι → ℂ)) (u : ι → ℝ) =>
    (∏ i, (u i : ℂ) ^ (q.1 i - 1)) * f (carlsonAffineForm q.2 u)
  have hG : ContinuousAt (fun q => ∫ u, F q u ∂μ) p := by
    apply continuousAt_of_dominated (bound := fun u => ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ * max C 0)
    · filter_upwards [hevent] with q hq
      exact ((integrableOn_mvBetaMonomial q.1 (fun i => (ha i).trans (hq.1 i))).mul_continuousOn
        (hf.comp (continuous_carlsonAffineForm q.2).continuousOn (fun u hu => hsub (hnear hq.2 hu)))
        (isCompact_stdSimplex ℝ ι)).aestronglyMeasurable
    · filter_upwards [hevent] with q hq
      filter_upwards [self_mem_ae_restrict (μ := MeasureTheory.Measure.stdSimplexMeasure)
        (isClosed_stdSimplex ℝ ι).measurableSet, ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
      have hm : ‖∏ i, (u i : ℂ) ^ (q.1 i - 1)‖ ≤ ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ := by
        simp only [norm_prod]
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i _
        rw [norm_cpow_eq_rpow_re_of_pos (hupos i), norm_cpow_eq_rpow_re_of_pos (hupos i)]
        apply Real.rpow_le_rpow_of_exponent_ge (hupos i)
          ((Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans_eq hu.2)
        simpa only [sub_re, one_re] using sub_le_sub_right (hq.1 i).le 1
      have hfu : ‖f (carlsonAffineForm q.2 u)‖ ≤ max C 0 :=
        (hC (Set.mem_image_of_mem _ (hnear hq.2 hu))).trans (le_max_left _ _)
      exact (norm_mul _ _).trans_le (mul_le_mul hm hfu (norm_nonneg _) (norm_nonneg _))
    · exact (integrableOn_mvBetaMonomial a ha).norm.mul_const _
    · filter_upwards [self_mem_ae_restrict (μ := MeasureTheory.Measure.stdSimplexMeasure)
        (isClosed_stdSimplex ℝ ι).measurableSet, ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
      have hm := (hasFDerivAt_mvBetaMonomial hupos p.1).continuousAt.comp continuous_fst.continuousAt
      have hfu : ContinuousAt f (carlsonAffineForm p.2 u) :=
        (hf _ (hKΩ (carlsonAffineForm_mem_convexHull p.2 hu))).continuousAt
          (hΩopen.mem_nhds (hKΩ (carlsonAffineForm_mem_convexHull p.2 hu)))
      have hL : ContinuousAt (fun q : (ι → ℂ) × (ι → ℂ) => carlsonAffineForm q.2 u) p := by
        simpa only [Function.comp_def, carlsonAffineFormCLM_apply] using
          ((carlsonAffineFormCLM u).continuous.comp continuous_snd).continuousAt (x := p)
      exact hm.mul (hfu.comp_of_eq hL rfl)
  have hnorm := (analyticOnNhd_prod_invGamma p.1 (Set.mem_univ _)).continuousAt.comp continuous_fst.continuousAt
  convert hnorm.mul hG using 1
  funext q
  exact regDirichletIntegral_eq_prod_invGamma_mul q.1 (fun u => f (carlsonAffineForm q.2 u))

set_option maxHeartbeats 800000 in
/-- **Carlson 5.3-3, joint form.** Separate analyticity and local dominated continuity
give joint analyticity by the finite-product Osgood theorem. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonDirichletAverage p.1 p.2 f)
      {p | p.1 ∈ mvBetaConvergent ∧ Set.range p.2 ⊆ Ω} := by
  classical
  let L := ContinuousLinearEquiv.sumPiEquivProdPi ℂ ι ι (fun _ => ℂ)
  have hLapply (q : (ι ⊕ ι) → ℂ) : L q = ((fun i => q (.inl i)), (fun i => q (.inr i))) := rfl
  let U : Set ((ι ⊕ ι) → ℂ) := {q | (L q).1 ∈ mvBetaConvergent ∧ Set.range (L q).2 ⊆ Ω}
  let G : ((ι ⊕ ι) → ℂ) → ℂ := fun q => regCarlsonDirichletAverage (L q).1 (L q).2 f
  have hU : IsOpen U := by
    have hzopen : IsOpen {z : ι → ℂ | Set.range z ⊆ Ω} := by
      simp only [Set.range_subset_iff, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => hΩopen.preimage (continuous_apply i)
    exact (isOpen_mvBetaConvergent.preimage (continuous_fst.comp L.continuous)).inter
      (hzopen.preimage (continuous_snd.comp L.continuous))
  have hG : AnalyticOnNhd ℂ G U := by
    apply SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU
    · intro q hq
      exact ((continuousAt_regCarlsonDirichletAverage_parameters_nodes hΩopen hΩconv hf.continuousOn
        hq.1 hq.2).comp L.continuous.continuousAt).continuousWithinAt
    · intro q hq k
      have hupdate (v : ι → ℂ) (i : ι) (w : ℂ) :
          Function.update v i w = fun j => if j = i then w else v j := by
        funext j
        simp only [Function.update_apply]
      have hup (v : ι → ℂ) (i : ι) : AnalyticAt ℂ (fun w => Function.update v i w) (v i) := by
        apply AnalyticAt.pi
        intro j
        by_cases hji : j = i
        · subst j; simpa using! (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) (v i))
        · simpa [hji] using! (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => v j) (v i))
      cases k with
      | inl i =>
        have hcont : ContinuousOn (fun u => f (carlsonAffineForm (L q).2 u)) (stdSimplex ℝ ι) :=
          hf.continuousOn.comp (continuous_carlsonAffineForm _).continuousOn
            (fun u hu => convexHull_min hq.2 hΩconv (carlsonAffineForm_mem_convexHull _ hu))
        have H := (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
          (regDirichletIntegral_analyticOn hcont) _ hq.1).comp_of_eq (hup (L q).1 i) (by simp)
        change AnalyticAt ℂ (fun w => regCarlsonDirichletAverage
          (Function.update (fun j => q (.inl j)) i w) (fun j => q (.inr j)) f) (q (.inl i)) at H
        dsimp only [G]
        simp only [hLapply]
        simpa only [hupdate, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false] using! H
      | inr i =>
        have H := (analyticOnNhd_regCarlsonDirichletAverage_nodes hΩopen hΩconv hf hq.1 _ hq.2).comp_of_eq
          (hup (L q).2 i) (by simp)
        change AnalyticAt ℂ (fun w => regCarlsonDirichletAverage
          (fun j => q (.inl j)) (Function.update (fun j => q (.inr j)) i w) f) (q (.inr i)) at H
        dsimp only [G]
        simp only [hLapply]
        simpa only [hupdate, Function.update_apply, Sum.inr.injEq, reduceCtorEq, if_false] using! H
  intro p hp
  have hmem : L.symm p ∈ U := by simpa [U] using hp
  have H := (hG _ hmem).comp_of_eq (L.symm.analyticAt p) rfl
  simpa [G] using! H

/-- The unregularized coordinate derivative on a convex domain of holomorphy.
Unlike the globally bounded derivative specialization, this applies to general holomorphic
kernels, including exponentials and powers on their branch domains. -/
theorem carlsonPartialDeriv_carlsonDirichletAverage_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω) (i : ι) :
    carlsonPartialDeriv i (fun z => carlsonDirichletAverage b z f) z =
      (b i / ∑ j, b j) *
        carlsonDirichletAverage (addDirichletUnit b i) z (deriv f) := by
  let : Nonempty ι := ⟨i⟩
  have hcpos : 0 < (∑ j, b j).re := by
    simpa using Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hc : (∑ j, b j) ≠ 0 := ne_zero_of_re_pos hcpos
  have hder := hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
    hΩopen hΩconv hf hb hz i
  unfold carlsonPartialDeriv carlsonDirichletAverage
  rw [deriv_const_mul _ hder.differentiableAt, hder.deriv,
    ← mul_regDirichletIntegral_addDirichletUnit hb i
      (fun u => deriv f (carlsonAffineForm z u))]
  rw [sum_addDirichletUnit, Gamma_add_one _ hc]
  change Gamma (∑ j, b j) *
      (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f)) =
    (b i / ∑ j, b j) *
      ((∑ j, b j) * Gamma (∑ j, b j) *
        regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f))
  field_simp [hc]

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
  have hsum : ∑ j, addDirichletUnit b i j = c + 1 := sum_addDirichletUnit b i
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
