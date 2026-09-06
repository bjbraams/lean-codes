/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage.Real
import StdSimplexMeasure.CarlsonDirichletAverage.Basic

/-!
# Bridge between real and complex Carlson averages

This file identifies the probability average at positive real parameters with the regularized
complex Carlson integral.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonDirichletBridge

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- For positive real parameters, the regularized complex density is the real Dirichlet
probability density divided by the Gamma factor of the total parameter. -/
theorem regDirichletDensity_ofReal_eq [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (u : ι → ℝ) :
    regDirichletDensity (fun i ↦ (b i : ℂ)) u =
      (dirichletPdfReal b u : ℂ) / Gamma (∑ i, (b i : ℂ)) := by
  by_cases hu : u ∈ stdSimplexInterior
  · rw [regDirichletDensity, Set.indicator_of_mem hu]
    rw [dirichletPdfReal, Set.indicator_of_mem hu]
    have hexp (i : ι) : (b i : ℂ) - 1 = ((b i - 1 : ℝ) : ℂ) := by norm_num
    have hpow (i : ι) : (u i : ℂ) ^ ((b i - 1 : ℝ) : ℂ) =
        (u i ^ (b i - 1) : ℝ) :=
      (Complex.ofReal_cpow (le_of_lt (hu.2 i)) _).symm
    simp_rw [hexp, hpow, Complex.Gamma_ofReal]
    rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, ← Complex.ofReal_prod]
    rw [show Gamma (∑ i, (b i : ℂ)) = (Real.Gamma (∑ i, b i) : ℂ) by
      rw [← Complex.ofReal_sum, Complex.Gamma_ofReal]]
    simp only [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_div]
    unfold mvRealBeta
    have hprod : (∏ i, Real.Gamma (b i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ ne_of_gt (Real.Gamma_pos_of_pos (hb i))
    have hsum : Real.Gamma (∑ i, b i) ≠ 0 := by
      apply ne_of_gt
      exact Real.Gamma_pos_of_pos
        (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty)
    have hprodC : (∏ i, (Real.Gamma (b i) : ℂ)) ≠ 0 := by
      simpa only [← Complex.ofReal_prod, Complex.ofReal_ne_zero] using hprod
    have hsumC : (Real.Gamma (∑ i, b i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsum
    rw [Complex.ofReal_div]
    field_simp [hprodC, hsumC]
  · simp [regDirichletDensity, dirichletPdfReal, hu]

/-- On positive real parameters, the regularized complex Carlson integral is the Dirichlet
probability average divided by the Gamma factor of the total parameter. -/
theorem regCarlsonDirichletAverage_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage (fun i ↦ (b i : ℂ)) z f =
      realCarlsonDirichletAverage b z f / Gamma (∑ i, (b i : ℂ)) := by
  rw [realCarlsonDirichletAverage_eq_integral hb]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with u
  rw [regDirichletDensity_ofReal_eq hb]
  ring

end DirichletTransform

end CarlsonDirichletBridge
