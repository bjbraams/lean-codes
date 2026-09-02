/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.Dirichlet
import StdSimplexMeasure.MvBeta

/-!
# Regularized complex Dirichlet integrals on the standard simplex

This file defines regularized complex Dirichlet densities and their associated integral
functionals. These are complex-valued densities, not measures in the sense of Mathlib's
nonnegative `Measure` type.

## Main definitions and results

* `Complex.mvBeta_eq_integral`: the simplex integral representation of the multivariate Beta
  function.
* `regDirichletDensity`: the pointwise entire regularized Dirichlet density.
* `complexDirichletDensity`: the corresponding normalized complex density.
* `regDirichletIntegral`: integration against the regularized density.
* `regDirichletIntegral_monomial`: evaluation of the functional on monomials.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex Fintype MeasureTheory MeasureTheory.Measure

public noncomputable section ComplexDirichlet

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The absolutely convergent simplex integral representation of the multivariate Beta
function. -/
theorem mvBeta_eq_integral {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = ∫ u in stdSimplex ℝ ι, ∏ i, (u i : ℂ) ^ (b i - 1) ∂stdSimplexMeasure := by
  sorry

end Complex

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The regularized Dirichlet density with parameters `b` on `stdSimplexInterior`. For each
fixed `u`, this is an entire function of `b`. -/
def regDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  stdSimplexInterior.indicator (fun u ↦ ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The normalized complex Dirichlet density with parameters `b` on
`stdSimplexInterior`. -/
def complexDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  Gamma (∑ i, b i) * regDirichletDensity b u

/-- Simultaneously permuting the parameters and coordinates leaves the regularized Dirichlet
density unchanged. -/
theorem regDirichletDensity_perm (b : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    regDirichletDensity (b ∘ σ) (u ∘ σ) = regDirichletDensity b u := by
  sorry

/-- The regularized Dirichlet density is a measurable function. -/
theorem measurable_regDirichletDensity (b : ι → ℂ) :
    Measurable (regDirichletDensity b) := by
  sorry

/-- The regularized Dirichlet density integrated over the standard simplex. -/
theorem regDirichletIntegral_normalization (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
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
def regDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in stdSimplex ℝ ι, regDirichletDensity b u * f u
    ∂stdSimplexMeasure

/-- `regDirichletIntegral` is additive. -/
theorem regDirichletIntegral_add (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hg : ContinuousOn g (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => f u + g u) =
    regDirichletIntegral b f + regDirichletIntegral b g := by
  sorry

/-- `regDirichletIntegral` commutes with complex scalar multiplication. -/
theorem regDirichletIntegral_smul (b : ι → ℂ) {f : (ι → ℝ) → ℂ} (c : ℂ)
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => c * f u) =
    c * regDirichletIntegral b f := by
  sorry

/-- The integral of `f` depends only on the values of `f` on the standard Simplex. -/
theorem regDirichletIntegral_congr
    (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    regDirichletIntegral b f =
      regDirichletIntegral b g := by
  sorry

/-- The `regDirichletIntegral` of a monomial. -/
theorem regDirichletIntegral_monomial
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (m : ι → ℕ) :
    regDirichletIntegral b (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (m i)) =
      (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) /
        Gamma (∑ i, (b i + m i : ℂ)) := by
  sorry

end ProbabilityTheory

end ComplexDirichlet
