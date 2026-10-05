/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import StdSimplexMeasure.MomentDetermination

/-!
# Uniqueness for the regularized Dirichlet transform

A continuous kernel on the standard simplex is determined by its regularized Dirichlet
transform. Indeed, it is determined by the values of the transform at the parameters
`b = m + 1` with `m : ι → ℕ`: these are, up to factorials, the monomial moments
`∫_Δ uᵐ g(u) du`, and a finite measure supported on the simplex is determined by its moments.

## Main results

* `Dirichlet.integral_monomial_mul_eq_factorial_mul`: the monomial moments of a kernel are
  values of its transform at positive integer parameters.
* `Dirichlet.IsRegDirichletContinuation.eqOn_of_eq_natCast_add_one`: two continuous kernels
  whose transforms agree at all positive integer parameters agree on the simplex.
* `Dirichlet.IsRegDirichletContinuation.eqOn_of_eq`: two continuous kernels with the same
  entire transform agree on the simplex.
* `Dirichlet.eqOn_of_regDirichletTransform_eq`: the same for the selected transform of smooth
  kernels.

## References

* `TauCeti.Probability.Moments.CompactDeterminacy`: moment determinacy for compactly supported
  measures, used through `StdSimplexMeasure.MomentDetermination`.
-/

open Complex MeasureTheory Set
open MeasureTheory.Measure

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The positive integer parameter `m + 1`. -/
private abbrev succParam (m : ι → ℕ) : ι → ℂ := fun k => (m k : ℂ) + 1

omit [Fintype ι] in
/-- Positive integer parameters lie in the convergence region. -/
private theorem succParam_mem (m : ι → ℕ) : succParam m ∈ mvBetaConvergent := fun k => by
  simp only [succParam, add_re, natCast_re, one_re]
  positivity

/-- **Moments as transform values.** The monomial moment `∫_Δ uᵐ g(u) du` of a kernel is
`∏ mᵢ!` times its regularized transform at the positive integer parameter `m + 1`. -/
theorem integral_monomial_mul_eq_factorial_mul {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (m : ι → ℕ) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ((∏ k, u k ^ m k : ℝ) : ℂ) * g u
        ∂stdSimplexMeasure =
      (∏ k, ((m k).factorial : ℂ)) * F (fun k => (m k : ℂ) + 1) := by
  rw [hF.eq_native (succParam_mem m), regDirichletIntegral_eq_prod_inv_Gamma_mul, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [add_sub_cancel_right, cpow_natCast, Gamma_nat_eq_factorial]
  rw [Finset.prod_eq_one fun k _ => mul_inv_cancel₀ (by exact_mod_cast (m k).factorial_ne_zero),
    one_mul]
  push_cast
  rfl

/-- The monomial multiples of a kernel continuous on the simplex are integrable for the simplex
measure. -/
private theorem integrable_restrict {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Integrable g (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
  have h := hg.integrableOn_compact
    (μ := stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
  rwa [IntegrableOn, Measure.restrict_restrict
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet, inter_self] at h

/-- **Uniqueness from positive integer parameters.** Two kernels continuous on the simplex whose
regularized transforms agree at every positive integer parameter `m + 1` agree on the simplex. -/
theorem IsRegDirichletContinuation.eqOn_of_eq_natCast_add_one {g h : (ι → ℝ) → ℂ}
    {F H : (ι → ℂ) → ℂ} (hF : IsRegDirichletContinuation g F)
    (hH : IsRegDirichletContinuation h H)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hh : ContinuousOn h (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hFH : ∀ m : ι → ℕ, F (fun k => (m k : ℂ) + 1) = H (fun k => (m k : ℂ) + 1)) :
    EqOn g h (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hν : (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι) =
      stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) := by
    rw [Measure.restrict_restrict hS, inter_self]
  have hgi := integrable_restrict hg
  have hhi := integrable_restrict hh
  have hae := ae_eq_zero_of_forall_monomial_integral_mul_eq_zero_of_restrict_stdSimplex hν
    (hgi.sub hhi) fun m => by
      simp only [Pi.sub_apply, mul_sub]
      rw [integral_sub (integrable_monomial_mul_of_restrict_stdSimplex hν hgi m)
        (integrable_monomial_mul_of_restrict_stdSimplex hν hhi m),
        integral_monomial_mul_eq_factorial_mul hF, integral_monomial_mul_eq_factorial_mul hH,
        hFH, sub_self]
  intro u hu
  exact sub_eq_zero.mp (eqOn_zero_of_ae_eq_zero_stdSimplexMeasure (hg.sub hh) hae hu)

/-- **Uniqueness.** Two kernels continuous on the simplex with the same entire regularized
transform agree on the simplex. -/
theorem IsRegDirichletContinuation.eqOn_of_eq {g h : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (hH : IsRegDirichletContinuation h F)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hh : ContinuousOn h (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    EqOn g h (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  hF.eqOn_of_eq_natCast_add_one hH hg hh fun _ => rfl

/-- A kernel continuous on the simplex whose regularized transform vanishes identically
vanishes on the simplex. -/
theorem IsRegDirichletContinuation.eqOn_zero {g : (ι → ℝ) → ℂ}
    (hF : IsRegDirichletContinuation g 0)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    EqOn g 0 (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  have h0 : IsRegDirichletContinuation (0 : (ι → ℝ) → ℂ) 0 :=
    ⟨analyticOnNhd_const, fun b _ => by simp [regDirichletIntegral]⟩
  exact hF.eqOn_of_eq h0 hg continuousOn_const

/-- **Injectivity of the transform.** Smooth kernels with the same regularized Dirichlet
transform agree on the simplex. -/
theorem eqOn_of_regDirichletTransform_eq {g h : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (hh : SmoothNearStdSimplex h) (hgh : regDirichletTransform g hg = regDirichletTransform h hh) :
    EqOn g h (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  have hH := isRegDirichletContinuation_transform hh
  rw [← hgh] at hH
  exact (isRegDirichletContinuation_transform hg).eqOn_of_eq hH hg.continuousOn hh.continuousOn

end Dirichlet

end
