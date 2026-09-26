/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Bridge
public import Dirichlet.Average.Real
public import Dirichlet.Average.Basic

/-!
# Bridge between real and complex Carlson averages

This file identifies the probability average at positive real parameters with the regularized
complex Carlson integral.

## Main results

* `Dirichlet.regCarlsonDirichletAverage_ofReal`: On positive real parameters, the regularized
  complex Carlson integral is the Dirichlet probability average divided by the Gamma factor of
  the total parameter.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonDirichletBridge

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- On positive real parameters, the regularized complex Carlson integral is the Dirichlet
probability average divided by the Gamma factor of the total parameter. -/
theorem regCarlsonDirichletAverage_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage (fun i ↦ (b i : ℂ)) z f =
      realCarlsonDirichletAverage b z f / Gamma (∑ i, (b i : ℂ)) := by
  exact regDirichletIntegral_ofReal hb (fun u ↦ f (carlsonAffineForm z u))

end Dirichlet

end CarlsonDirichletBridge
