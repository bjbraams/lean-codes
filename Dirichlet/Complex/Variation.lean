/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Bridge
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import ToMathlib.Analysis.SpecialFunctions.GammaBounds
public import ToMathlib.Analysis.SpecialFunctions.GammaRatio

/-!
# Complex Dirichlet measures and their variation

The native complex density defines a bundled complex vector measure on the closed
simplex. Its variation is `B(re b) / ‖B(b)‖` times the real Dirichlet probability
measure, and its total variation mass is this finite constant. These are Carlson
(1977), (4.4-3), (4.4-4), with coordinate-volume normalization.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The native complex Dirichlet measure, defined by its normalized density on the simplex.
Its probability-like normalization requires nonempty indices and positive real parts. -/
def complexDirichletMeasure (b : ι → ℂ) : VectorMeasure (ι → ℝ) ℂ :=
  (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).withDensityᵥ
    (complexDirichletDensity b)

/-- The normalized density is the unregularized monomial divided by the beta function. -/
theorem complexDirichletDensity_eq_div (b : ι → ℂ) (u : ι → ℝ) :
    complexDirichletDensity b u =
      stdSimplexInterior.indicator (fun u => ∏ i, (u i : ℂ) ^ (b i - 1)) u / mvBeta b := by
  classical
  by_cases hu : u ∈ stdSimplexInterior
  · rw [complexDirichletDensity, regDirichletDensity, Set.indicator_of_mem hu,
      Finset.prod_div_distrib, Set.indicator_of_mem hu]
    simp [mvBeta, div_eq_mul_inv, mul_comm, mul_assoc]
  · simp [complexDirichletDensity, regDirichletDensity, hu]

/-- **Carlson 4.4-3, density form.** The modulus of the complex density is a fixed
multiple of the real Dirichlet probability density at the real parts of the parameters. -/
theorem norm_complexDirichletDensity [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (u : ι → ℝ) :
    ‖complexDirichletDensity b u‖ =
      (mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖) *
        dirichletPdfReal (fun i => (b i).re) u := by
  classical
  rw [complexDirichletDensity_eq_div]
  by_cases hu : u ∈ stdSimplexInterior
  · simp only [Set.indicator_of_mem hu, norm_div, norm_prod, dirichletPdfReal]
    simp_rw [norm_cpow_eq_rpow_re_of_pos (hu.2 _), sub_re, one_re]
    field_simp [(mvRealBeta_pos hb).ne']
  · simp [dirichletPdfReal, hu]

/-- The native normalized complex density is integrable throughout the convergence region. -/
theorem integrableOn_complexDirichletDensity {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    IntegrableOn (complexDirichletDensity b) (Convexity.StdSimplex.coordinateSet ℝ ι)
      stdSimplexMeasure :=
  (integrableOn_regDirichletDensity b hb).const_mul _

/-- **Carlson 4.4-3.** The variation measure is the real Dirichlet law times the ratio
`B(re b) / ‖B(b)‖`, as an equality of measures, not only of total masses. -/
theorem variation_complexDirichletMeasure [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    (complexDirichletMeasure b).variation =
      ENNReal.ofReal (mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖) •
        dirichletMeasure (fun i => (b i).re) := by
  rw [complexDirichletMeasure, Measure.variation_withDensityᵥ (integrableOn_complexDirichletDensity hb)]
  have he : (fun u => ‖complexDirichletDensity b u‖ₑ) =
      fun u => ENNReal.ofReal (mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖) *
        dirichletPdf (fun i => (b i).re) u := by
    funext u
    rw [← ofReal_norm, norm_complexDirichletDensity hb]
    exact ENNReal.ofReal_mul (div_nonneg (mvRealBeta_pos hb).le (norm_nonneg _))
  rw [he]
  change ((stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).withDensity
    (ENNReal.ofReal (mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖) •
      dirichletPdf (fun i => (b i).re))) = _
  rw [withDensity_smul _ (measurable_dirichletPdf _)]
  congr 1
  rw [← restrict_withDensity (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  exact dirichletMeasure_restrict _

/-- **Carlson 4.4-4.** The total variation mass of the complex Dirichlet measure. -/
theorem variation_complexDirichletMeasure_univ [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    (complexDirichletMeasure b).variation univ =
      ENNReal.ofReal (mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖) := by
  let _ := isProbabilityMeasure_dirichletMeasure hb
  rw [variation_complexDirichletMeasure hb]
  simp

/-- Complex Dirichlet measures in the convergence region have finite variation. -/
theorem variation_complexDirichletMeasure_ne_top [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : (complexDirichletMeasure b).variation univ ≠ ∞ := by
  rw [variation_complexDirichletMeasure_univ hb]
  exact ENNReal.ofReal_ne_top

/-- The complex Dirichlet measure has total mass one in its native convergence domain. -/
theorem complexDirichletMeasure_univ [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : complexDirichletMeasure b univ = 1 := by
  rw [complexDirichletMeasure,
    withDensityᵥ_apply (integrableOn_complexDirichletDensity hb) MeasurableSet.univ,
    setIntegral_univ]
  change (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
    Gamma (∑ i, b i) * regDirichletDensity b u ∂stdSimplexMeasure) = 1
  rw [integral_const_mul, regDirichletIntegral_normalization b hb]
  rw [one_div]
  exact mul_inv_cancel₀ (Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb))

/-- **Carlson Exercise 4.4-8.** When every real part is at least one half, the
variation multiplier is bounded by the exponential of half pi times the sum of
the absolute imaginary parts. -/
theorem complexDirichletVariationFactor_le_exp [Nonempty ι] {b : ι → ℂ}
    (hb : ∀ i, 1 / 2 ≤ (b i).re) :
    mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖ ≤
      Real.exp (Real.pi / 2 * ∑ i, |(b i).im|) := by
  have hb' : b ∈ mvBetaConvergent := fun i => lt_of_lt_of_le (by norm_num) (hb i)
  have hs : 0 < (∑ i, b i).re := sum_re_pos_of_mem_mvBetaConvergent hb'
  have hG : Real.Gamma (∑ i, (b i).re) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by simpa only [re_sum] using hs)).ne'
  have hpn : (∏ i, ‖Gamma (b i)‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (hb' i))
  have hsn : ‖Gamma (∑ i, b i)‖ ≠ 0 := norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos hs)
  have he : mvRealBeta (fun i => (b i).re) / ‖mvBeta b‖ =
      (‖Gamma (∑ i, b i)‖ / Real.Gamma (∑ i, (b i).re)) *
        ∏ i, (Real.Gamma (b i).re / ‖Gamma (b i)‖) := by
    simp only [mvRealBeta, mvBeta, norm_div, norm_prod, Finset.prod_div_distrib]
    field_simp
  rw [he]
  have hfirst : ‖Gamma (∑ i, b i)‖ / Real.Gamma (∑ i, (b i).re) ≤ 1 := by
    apply (div_le_one (Real.Gamma_pos_of_pos (by simpa only [re_sum] using hs))).mpr
    simpa only [re_sum] using norm_Gamma_le_Gamma_re hs
  calc
    _ ≤ ∏ i, (Real.Gamma (b i).re / ‖Gamma (b i)‖) := by
      exact mul_le_of_le_one_left
        (Finset.prod_nonneg fun i _ => div_nonneg (Real.Gamma_pos_of_pos (hb' i)).le
          (norm_nonneg _)) hfirst
    _ ≤ ∏ i, Real.exp (Real.pi * |(b i).im| / 2) := by
      apply Finset.prod_le_prod₀
        (fun i _ => div_nonneg (Real.Gamma_pos_of_pos (hb' i)).le (norm_nonneg _))
      intro i _
      simpa only [re_add_im] using Gamma_div_norm_Gamma_le_exp (hb i) (b i).im
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The exponential bound of Exercise 4.4-8 as a bound on the bundled variation measure. -/
theorem variation_complexDirichletMeasure_univ_le_exp [Nonempty ι] {b : ι → ℂ}
    (hb : ∀ i, 1 / 2 ≤ (b i).re) :
    (complexDirichletMeasure b).variation univ ≤
      ENNReal.ofReal (Real.exp (Real.pi / 2 * ∑ i, |(b i).im|)) := by
  rw [variation_complexDirichletMeasure_univ (fun i => lt_of_lt_of_le (by norm_num) (hb i))]
  exact ENNReal.ofReal_le_ofReal (complexDirichletVariationFactor_le_exp hb)

end Dirichlet
