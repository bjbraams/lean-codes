/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.TauCetiBridge
public import TauCeti.Probability.Distributions.Dirichlet.Marginal
public import Mathlib.Probability.Distributions.Beta

/-!
# Beta marginals of the real Dirichlet distribution

With two coordinates the Dirichlet distribution is Mathlib's beta distribution: the first
coordinate of a `Fin 2`-indexed Dirichlet random vector has the beta law with the same
parameters. More generally each coordinate marginal is a beta law; this is transferred through
`Dirichlet.TauCetiBridge` from `TauCeti.Probability.Distributions.Dirichlet.Marginal`, by the
Tau Ceti contributors.

## Main results

* `ProbabilityTheory.mvRealBeta_fin_two`: the two-parameter multivariate beta function is the
  ordinary beta function.
* `ProbabilityTheory.betaMarginal`: each coordinate marginal is a beta law.
* `ProbabilityTheory.map_dirichletMeasure_fin_two`: the first-coordinate marginal is
  `ProbabilityTheory.betaMeasure`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
* `TauCeti.Probability.Distributions.Dirichlet.Marginal`.
-/

open Dirichlet
open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]


/- Specializations to the two-variable Dirichlet (Beta) density and measure that is defined
in Mathlib `ProbabilityTheory.betaMeasure`. -/

/-- For two parameters, `mvRealBetaDomain` is just positivity of both parameters. -/
@[simp] theorem mem_mvRealBetaDomain_fin_two (α β : ℝ) :
    (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain ↔
      0 < α ∧ 0 < β := by
  simp [mvRealBetaDomain]

/-- In the two-variable case, `mvRealBeta` is the ordinary beta function. -/
@[simp] theorem mvRealBeta_fin_two (α β : ℝ) :
    mvRealBeta (![α, β] : Fin 2 → ℝ) = beta α β := by
  simp [mvRealBeta, beta]

/-- The two-variable real Dirichlet density is the beta density under the
parametrization `x ↦ ![x, 1 - x]`. -/
@[simp] theorem dirichletPdfReal_fin_two (α β x : ℝ) :
    dirichletPdfReal (![α, β] : Fin 2 → ℝ) ![x, 1 - x] =
      betaPDFReal α β x := by
  rw [dirichletPdfReal, betaPDFReal, mvRealBeta_fin_two]
  by_cases hx : 0 < x ∧ x < 1
  · simp [hx, mul_assoc]
  · rw [ite_eq_right hx]
    simp [mem_stdSimplexInterior_fin_two, hx]

/-- The two-variable `ENNReal`-valued Dirichlet density is the beta density. -/
@[simp] theorem dirichletPdf_fin_two (α β x : ℝ) :
    dirichletPdf (![α, β] : Fin 2 → ℝ) ![x, 1 - x] = betaPDF α β x := by
  simp [dirichletPdf, betaPDF]

open scoped Classical in
/-- Marginalization of the Dirichlet density with respect to the `i` coordinate, transferred
from `TauCeti.Probability.map_eval_dirichletMeasure` by the Tau Ceti contributors. -/
theorem betaMarginal [Nontrivial ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    Measure.map (fun u ↦ u i) (dirichletMeasure b) =
      betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) := by
  classical
  rw [dirichletMeasure_eq_map_tauCeti hb, Measure.map_map (measurable_pi_apply i) (by fun_prop),
    ← Finset.filter_ne']
  exact TauCeti.Probability.map_eval_dirichletMeasure hb i

/-- The push-forward of the two-variable Dirichlet measure under the first
coordinate is the beta measure. -/
theorem map_dirichletMeasure_fin_two
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![α, β])) = betaMeasure α β := by
  have hb : (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain := by
    simpa using And.intro hα hβ
  simpa using
    (betaMarginal (b := (![α, β] : Fin 2 → ℝ)) hb (0 : Fin 2))

/- The Gamma-ratio characterization is proved in `Dirichlet.Gamma` as
`ProbabilityTheory.iIndepFun.hasLaw_dirichlet_of_gamma`, for any common positive rate.
That file also proves the law of the total and its independence from the ratios. -/

end ProbabilityTheory

end DirichletDistribution
