/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.Dirichlet
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Complex Dirichlet measure on the standard simplex

(Implemented as a complex density.)

## Main definitions and results

## References
[Carl77] Carlson, Bille Chandler. "Special functions of applied mathematics." Academic Press, 1977.
-/

open Complex Fintype MeasureTheory MeasureTheory.Measure

public noncomputable section ComplexDirichlet

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The product of Gamma functions. -/
def mvGamma (b : ι → ℂ) : ℂ :=
    ∏ i, b i

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    mvGamma b / Gamma (∑ i, b i)

/-- Domain for `b` where the Beta function is defined as an integral. -/
def mvBetaConvergent : Set (ι → ℂ) :=
  {b | ∀ i, 0 < (b i).re}

/-- The integral representation of `mvBeta`. -/
theorem mvBeta_eq_integral {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = ∫ u in stdSimplex ℝ ι, ∏ i, (u i : ℂ) ^ (b i - 1) ∂stdSimplexMeasure := by
  sorry

/-- The regularized Dirichlet density with parameters `b` on `stdSimplexInterior`.
This is an entire function of `b`. -/
def regDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  stdSimplexInterior.indicator (fun u ↦ ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The Dirichlet density with parameters `b` on `stdSimplexInterior`. -/
def dirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  Gamma (∑ i, b i) * regDirichletDensity b u

/-- The regularized Dirichlet density is a measurable function. -/
theorem measurable_regDirichletDensity (b : ι → ℂ) :
    Measurable (regDirichletDensity b) := by
  sorry

/-- The regularized Dirichlet density integrated over the standard simplex. -/
theorem RegDirichletIntegral_normalization (b : ι → ℂ) (hb : b ∈ mvBetaConvergent):
    ∫ u in stdSimplex ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure =
    1 / Gamma (∑ i, b i) := by
  sorry

/-- Continuous functions are integrable over the standard simplex with respect to the
regularized Dirichlet density. -/
theorem integrableOn_regDirichletDensity_mul
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn
      (fun u => regDirichletDensity b u * f u)
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  sorry

/-- Integration of function `f` over the standard simplex with respect to the regularized
Dirichlet density. -/
def RegDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in stdSimplex ℝ ι, regDirichletDensity b u * f u
    ∂stdSimplexMeasure

/-- `RegDirichletIntegral` is additive. -/
theorem RegDirichletIntegral_add (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hg : ContinuousOn g (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    RegDirichletIntegral b (fun u => f u + g u) =
    RegDirichletIntegral b f + RegDirichletIntegral b g := by
  sorry

/-- `RegDirichletIntegral` commutes with complex scalar multiplication. -/
theorem RegDirichletIntegral_smul (b : ι → ℂ) {f : (ι → ℝ) → ℂ} (c : ℂ)
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    RegDirichletIntegral b (fun u => c * f u) =
    c * RegDirichletIntegral b f := by
  sorry

/-- The integral of `f` depends only on the values of `f` on the standard Simplex. -/
theorem RegDirichletIntegral_congr
    (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    RegDirichletIntegral b f =
      RegDirichletIntegral b g := by
  sorry

end ProbabilityTheory

end ComplexDirichlet
