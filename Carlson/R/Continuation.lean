/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Integral

/-!
# Carlson's R-function: continuation in the Dirichlet parameters

`IsRegCarlsonRContinuation t z G` says that `G` is entire in the Dirichlet parameters and
agrees with the native regularized integral on its convergence region. Such a continuation
is unique, and the smooth-kernel Dirichlet continuation theorem shows that one exists for
every complex exponent and right-half-plane nodes. The explicit function `regCarlsonR` of
`Carlson.R.Explicit` is shown there to be this continuation. At natural exponents the
continuation is the regularized R-polynomial.
-/

open Dirichlet
open Complex ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace Carlson
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

/-- A complex power of the affine form is smooth near the simplex on the right-half-plane
node domain. This supplies the hypothesis of the general Dirichlet continuation theorem. -/
theorem contDiffNearStdSimplex_cpow_carlsonAffineForm (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (N : ℕ) :
    ContDiffNearStdSimplex N (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t) := by
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ ↦ w ^ t) slitPlane := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem hw] with v hv
    exact differentiableAt_id.cpow_const hv
  have haffine : ContDiff ℝ N (fun u : ι → ℝ ↦ carlsonAffineForm z u) := by
    unfold carlsonAffineForm
    exact ContDiff.sum fun i _ ↦
      (Complex.ofRealCLM.contDiff.comp
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff).mul contDiff_const
  refine ⟨carlsonAffineForm z ⁻¹' slitPlane,
    isOpen_slitPlane.preimage (continuous_carlsonAffineForm z),
    fun u hu ↦ carlsonAffineForm_mem_slitPlane hz hu, ?_⟩
  exact (hpow.contDiffOn_of_completeSpace.restrict_scalars ℝ).comp
    haffine.contDiffOn (fun _ hu ↦ hu)

/-- Every complex exponent has an entire regularized continuation in the Dirichlet
parameters, for nodes in the right half-plane. No contour representation is needed. -/
theorem exists_isRegCarlsonRContinuation (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    ∃ G : (ι → ℂ) → ℂ, IsRegCarlsonRContinuation t z G := by
  obtain ⟨G, hG, hEq⟩ := exists_entire_regDirichletContinuation_of_contDiffNear
    (contDiffNearStdSimplex_cpow_carlsonAffineForm t hz)
  exact ⟨G, hG, fun b hb ↦ hEq hb⟩

/-- At a natural exponent, the regularized R-polynomial supplies the entire continuation in
the Dirichlet parameters.  Thus the general R-function continuation extends, rather than
replaces, the polynomial theory of Section 5.7. -/
theorem isRegCarlsonRContinuation_natCast (n : ℕ) (z : ι → ℂ) :
    IsRegCarlsonRContinuation (n : ℂ) z (regCarlsonRPolynomial n · z) := by
  refine ⟨analyticOnNhd_regCarlsonRPolynomial n z, ?_⟩
  intro b hb
  exact (regCarlsonRIntegral_natCast n z hb).symm

/-- Any entire regularized continuation at a natural exponent equals the corresponding
regularized R-polynomial. -/
theorem IsRegCarlsonRContinuation.eq_regCarlsonR_natCast
    {n : ℕ} {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonRContinuation (n : ℂ) z G) :
    G = (regCarlsonRPolynomial n · z) :=
  hG.eq (isRegCarlsonRContinuation_natCast n z)

end Carlson
end CarlsonR
