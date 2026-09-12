/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Integral

/-! # Carlson's R-function: continuation in the Dirichlet parameters -/

open Complex ProbabilityTheory
@[expose] public noncomputable section CarlsonR
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

/-- At a natural exponent, the regularized R-polynomial supplies the entire continuation in
the Dirichlet parameters.  Thus the general R-function continuation extends, rather than
replaces, the polynomial theory of Section 5.7. -/
theorem isRegCarlsonRContinuation_natCast (n : ℕ) (z : ι → ℂ) :
    IsRegCarlsonRContinuation (n : ℂ) z (regCarlsonR n z) := by
  refine ⟨analyticOnNhd_regCarlsonR n z, ?_⟩
  intro b hb
  exact (regCarlsonRIntegral_natCast n z hb).symm

/-- Any entire regularized continuation at a natural exponent equals the corresponding
regularized R-polynomial. -/
theorem IsRegCarlsonRContinuation.eq_regCarlsonR_natCast
    {n : ℕ} {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonRContinuation (n : ℂ) z G) :
    G = regCarlsonR n z :=
  hG.eq (isRegCarlsonRContinuation_natCast n z)

end DirichletTransform
end CarlsonR
