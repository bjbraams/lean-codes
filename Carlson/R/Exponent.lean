/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Deriv
public import ComplexAnalysis.ParametricIntegral

/-!
# Analytic dependence on the exponent of Carlson's R-integral

Unlike the Dirichlet parameters, the exponent has no convergence restriction on the
right-half-plane node domain. This is the continuation input for fixed-parameter
recurrences initially obtained from a convergent single-integral representation.
-/

open Dirichlet
open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- Differentiation in the exponent inserts the logarithm of the affine form into
the regularized Dirichlet integral. -/
theorem hasDerivAt_regCarlsonRIntegral_exponent (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s ↦ regCarlsonRIntegral s b z)
      (regDirichletIntegral b
        (fun u ↦ carlsonAffineForm z u ^ t * log (carlsonAffineForm z u))) t := by
  have hpow : ContinuousOn
      (fun p : ℂ × (ι → ℝ) => carlsonAffineForm z p.2 ^ p.1)
      (Set.univ ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    ((continuous_carlsonAffineForm z).comp continuous_snd).continuousOn.cpow
      continuous_fst.continuousOn (fun p hp => carlsonAffineForm_mem_slitPlane hz hp.2)
  have hlog : ContinuousOn (fun u => log (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) := by
    intro u hu
    exact ((continuousAt_clog (carlsonAffineForm_mem_slitPlane hz hu)).comp
      (continuous_carlsonAffineForm z).continuousAt).continuousWithinAt
  exact hasDerivAt_integral_mul_of_continuousOn_compact
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    (integrableOn_regDirichletDensity b hb) isOpen_univ (Set.mem_univ t) hpow
    (hpow.mul (hlog.comp continuous_snd.continuousOn (fun _ hp => hp.2)))
    (fun s _ u hu => (Complex.hasStrictDerivAt_const_cpow
      (Or.inl (slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)))).hasDerivAt)

/-- The regularized native R-integral is entire in its exponent. -/
theorem analyticOnNhd_regCarlsonRIntegral_exponent {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun t ↦ regCarlsonRIntegral t b z) Set.univ := by
  intro t _
  rw [analyticAt_iff_eventually_differentiableAt]
  exact Filter.Eventually.of_forall fun s ↦
    (hasDerivAt_regCarlsonRIntegral_exponent s hb hz).differentiableAt

/-- The normalized native R-integral is entire in its exponent. -/
theorem analyticOnNhd_carlsonRIntegral_exponent {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun t ↦ carlsonRIntegral t b z) Set.univ := by
  exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonRIntegral_exponent hb hz)

end Carlson

end
