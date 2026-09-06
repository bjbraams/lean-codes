/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonR.Integral

/-! # Carlson's R-function: continuation in the Dirichlet parameters -/

open Complex ProbabilityTheory
public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A candidate is an entire regularized continuation of Carlson's `R_t` if it agrees with the
native regularized integral on the ordinary convergence region. -/
def IsRegCarlsonRContinuation (t : ℂ) (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation (fun w ↦ w ^ t) z G

/-- A regularized Carlson `R_t` continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonRContinuation.analyticOnNhd {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G) :
    AnalyticOnNhd ℂ G Set.univ := hG.1

/-- A regularized Carlson continuation agrees with the native integral on its convergence
domain. -/
theorem IsRegCarlsonRContinuation.eq_integral {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonRIntegral t b z := hG.2 hb

/-- An entire regularized continuation of Carlson's `R_t`, if it exists, is unique. -/
theorem IsRegCarlsonRContinuation.eq {t : ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G)
    (hH : IsRegCarlsonRContinuation t z H) : G = H :=
  IsRegCarlsonContinuation.eq hG hH

end DirichletTransform
end CarlsonR
