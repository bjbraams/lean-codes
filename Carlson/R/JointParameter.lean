/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Exponent
public import Carlson.R.Relations
public import SeveralComplexVariables.SeparateAnalytic

/-!
# Joint dependence on the exponent and Dirichlet parameters

The exponent occupies the `none` coordinate, and the Dirichlet parameters the `some`
coordinates. Native joint analyticity follows from separate analyticity by Hartogs' theorem.
The joint analyticity of the explicit function `regCarlsonR` for all parameters is proved
in `Carlson.R.Explicit`.

## Main results

* `Carlson.analyticOnNhd_regCarlsonRIntegral_exponent_parameters`: Joint analyticity of the
  native regularized integral in its exponent and parameters.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex ProbabilityTheory MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Joint analyticity of the native regularized integral in its exponent and parameters. -/
theorem analyticOnNhd_regCarlsonRIntegral_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonRIntegral (p none) (fun i => p (some i)) z)
      {p | (fun i => p (some i)) ∈ mvBetaConvergent} := by
  classical
  apply SeveralComplexVariables.analyticOnNhd_of_separately_analytic
    (isOpen_mvBetaConvergent.preimage (by fun_prop))
  intro p hp k
  cases k with
  | none =>
    have H := analyticOnNhd_regCarlsonRIntegral_exponent hp hz (p none) (mem_univ _)
    simpa only [Function.update_self, Function.update_of_ne (Option.some_ne_none _)] using H
  | some i =>
    have hcont : ContinuousOn (fun u => carlsonAffineForm z u ^ p none)
        (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      (continuous_carlsonAffineForm z).continuousOn.cpow_const
        (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)
    have H := (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
      (regDirichletIntegral_analyticOn hcont)).analyticAt_update hp i
    change AnalyticAt ℂ (fun w => regCarlsonRIntegral (p none)
      (Function.update (fun j => p (some j)) i w) z) (p (some i)) at H
    have hup (v : ι → ℂ) (w : ℂ) : Function.update v i w = fun j => if j = i then w else v j := by
      ext j
      simp only [Function.update_apply]
    simpa only [hup, Function.update_apply, Option.some.injEq, reduceCtorEq, ite_false] using! H

end Carlson
end
