/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Transform.Series

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Averages of uniformly summable series

This file supplies the dominated-convergence form of Carlson's Representation 5.7-2.  A
summable numerical majorant, uniform on the standard simplex, permits termwise application of
the regularized Carlson Dirichlet average.


## Main results

* `Dirichlet.hasSum_regCarlsonDirichletAverage`: A uniformly summably dominated series may be
  averaged term by term with respect to the regularized Dirichlet density. This is the general
  analytic core of Carlson's Representation 5.7-2.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.7,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonPowerSeries

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- A uniformly summably dominated series may be averaged term by term with respect to the
regularized Dirichlet density.  This is the general analytic core of Carlson's
Representation 5.7-2. -/
theorem hasSum_regCarlsonDirichletAverage
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    (g : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (M : ℕ → ℝ)
    (hg : ∀ n, ContinuousOn (fun u : ι → ℝ ↦ g n (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hM : Summable M)
    (hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → ‖g n (carlsonAffineForm z u)‖ ≤ M
        n)
    (hsum : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
      HasSum (fun n ↦ g n (carlsonAffineForm z u)) (f (carlsonAffineForm z u))) :
    HasSum (fun n ↦ regCarlsonDirichletAverage b z (g n))
      (regCarlsonDirichletAverage b z f) := by
  exact hasSum_regDirichletIntegral hb (fun n u => g n (carlsonAffineForm z u))
    (fun u => f (carlsonAffineForm z u)) M hg hM hbound hsum

end Dirichlet

end CarlsonPowerSeries
