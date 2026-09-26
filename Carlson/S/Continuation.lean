/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.S.Analytic

/-!
# Named ordinary and regularized S-functions

The existing exponential series is exposed with the uniform argument order `(b, z)`.
Regularization gives an entire function in both vectors; multiplying by Gamma of the
total parameter recovers the ordinary normalization away from its possible poles.

## Main results

* `Carlson.analyticAt_regCarlsonS_comp`: joint entire dependence under analytic substitutions.
* `Carlson.regCarlsonS_eq_integral`: native agreement for convergent parameters.
* `Carlson.carlsonS_eq_integral`: ordinary native agreement.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.8.
-/

open Complex Dirichlet Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The regularized S-function with parameters before nodes, matching the R, L and T APIs. -/
abbrev regCarlsonS (b z : ι → ℂ) : ℂ := regCarlsonSSeries z b

/-- The ordinary S-function obtained by restoring Gamma of the total parameter.
At Gamma poles this is a totalized product, not an assertion of a removable value. -/
def carlsonS (b z : ι → ℂ) : ℂ := Gamma (∑ i, b i) * regCarlsonS b z

/-- Analytic substitutions in parameters and nodes preserve the entire S-function. -/
theorem analyticAt_regCarlsonS_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b z : E → ι → ℂ} {p : E} (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p) :
    AnalyticAt ℂ (fun q => regCarlsonS (b q) (z q)) p := by
  have hm : AnalyticAt ℂ (fun q => Sum.elim (b q) (z q)) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | inl i => exact (analyticAt_pi_iff.mp hb) i
    | inr i => exact (analyticAt_pi_iff.mp hz) i
  simpa only [regCarlsonS, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
    (analyticOnNhd_regCarlsonSSeries_joint (Sum.elim (b p) (z p)) (mem_univ _)).comp
      (f := fun q => Sum.elim (b q) (z q)) hm

/-- The regularized S-function agrees with its native exponential average. -/
theorem regCarlsonS_eq_integral {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonS b z = regCarlsonSIntegral b z := regCarlsonSSeries_eq_regCarlsonSIntegral z hb

/-- The ordinary S-function agrees with its native exponential average. -/
theorem carlsonS_eq_integral {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    carlsonS b z = carlsonSIntegral b z := by
  rw [carlsonS, carlsonSIntegral, regCarlsonS_eq_integral hb]

end Carlson
