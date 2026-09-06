/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.Dirichlet
import StdSimplexMeasure.CarlsonDirichletAverage.Kernel

/-!
# Carlson's Dirichlet average with real positive parameters

This file provides the probability-theoretic form of Carlson's average.  Its parameters are
strictly positive real numbers and integration is against `dirichletMeasure`.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Classical

public noncomputable section RealCarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's probability average for positive real Dirichlet parameters. -/
def realCarlsonDirichletAverage (b : ι → ℝ) (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ u, f (carlsonAffineForm z u) ∂dirichletMeasure b

/-- A complex-valued integral against a real Dirichlet measure can be written using its real
density and the standard-simplex measure. -/
theorem integral_dirichletMeasure_complex [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (f : (ι → ℝ) → ℂ) :
    ∫ u, f u ∂dirichletMeasure b =
      ∫ u in stdSimplex ℝ ι, (dirichletPdfReal b u : ℂ) * f u
        ∂stdSimplexMeasure := by
  rw [dirichletMeasure]
  have hlt : ∀ᵐ u ∂stdSimplexMeasure, dirichletPdf b u < ⊤ := by
    filter_upwards with u
    simp [dirichletPdf]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_dirichletPdf b) hlt f]
  rw [← integral_indicator (isClosed_stdSimplex ℝ ι).measurableSet]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ stdSimplex ℝ ι
  · have hnonneg := dirichletPdfReal_nonneg hb u
    simp [hu, dirichletPdf, ENNReal.toReal_ofReal hnonneg, Complex.real_smul]
  · simp [hu, dirichletPdf, dirichletPdfReal, stdSimplexInterior]

/-- The probability-theoretic Carlson average has the expected density representation. -/
theorem realCarlsonDirichletAverage_eq_integral [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) (f : ℂ → ℂ) :
    realCarlsonDirichletAverage b z f =
      ∫ u in stdSimplex ℝ ι,
        (dirichletPdfReal b u : ℂ) * f (carlsonAffineForm z u)
          ∂stdSimplexMeasure :=
  integral_dirichletMeasure_complex hb _

end DirichletTransform

end RealCarlsonDirichletAverage
