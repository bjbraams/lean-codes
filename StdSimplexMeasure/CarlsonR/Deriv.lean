/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonR.Continuation
import StdSimplexMeasure.CarlsonDirichletAverage.Deriv

/-!
# Carlson's R-function: analyticity and differentiation

This file supplies the pointwise analytic and differential kernel identities underlying
Carlson's Theorem 5.9-2.  Their integral counterparts require differentiation under the
Dirichlet integral and are developed from these statements.
-/

open Complex
open scoped Classical
public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- For a fixed simplex point, Carlson's power kernel is analytic in all variables throughout
the right-half-plane domain.  This is the pointwise input to Theorem 5.9-2(a). -/
theorem analyticOnNhd_cpow_carlsonAffineForm (t : ℂ) (u : ι → ℝ)
    (hu : u ∈ stdSimplex ℝ ι) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ ↦ carlsonAffineForm z u ^ t)
      carlsonRVariableDomain := by
  intro z hz
  have haffine : AnalyticAt ℂ (carlsonAffineForm · u) z := by
    unfold carlsonAffineForm
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt z)
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ w ^ t) (carlsonAffineForm z u) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonAffineForm_mem_slitPlane hz hu)] with w hw
    exact (differentiableAt_id.cpow_const hw)
  exact hpow.comp_of_eq haffine rfl

/-- The coordinate derivative of Carlson's power kernel.  This is the pointwise form of
Theorem 5.9-2(b). -/
theorem hasDerivAt_cpow_carlsonAffineForm_update (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (i : ι) :
    HasDerivAt (fun w ↦ carlsonAffineForm (Function.update z i w) u ^ t)
      ((u i : ℂ) * (t * carlsonAffineForm z u ^ (t - 1))) (z i) := by
  exact HasDerivAt.comp_carlsonAffineForm_update i
    (Complex.hasStrictDerivAt_cpow_const
      (carlsonAffineForm_mem_slitPlane hz hu)).hasDerivAt

/-- Euler's differential identity for the pointwise power kernel, corresponding to
Theorem 5.9-2(c). -/
theorem sum_mul_deriv_cpow_carlsonAffineForm (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
    ∑ i, z i * deriv (fun w ↦ carlsonAffineForm (Function.update z i w) u ^ t) (z i) =
      t * carlsonAffineForm z u ^ t := by
  simp_rw [(hasDerivAt_cpow_carlsonAffineForm_update t hz hu _).deriv]
  have hne : carlsonAffineForm z u ≠ 0 :=
    slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)
  rw [show ∑ i, z i * ((u i : ℂ) *
      (t * carlsonAffineForm z u ^ (t - 1))) =
      (∑ i, (u i : ℂ) * z i) *
        (t * carlsonAffineForm z u ^ (t - 1)) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [show ∑ i, (u i : ℂ) * z i = carlsonAffineForm z u by rfl]
  calc
    carlsonAffineForm z u * (t * carlsonAffineForm z u ^ (t - 1)) =
        t * (carlsonAffineForm z u ^ (t - 1) * carlsonAffineForm z u) := by ring
    _ = t * carlsonAffineForm z u ^ ((t - 1) + 1) := by
      rw [cpow_add _ _ hne, cpow_one]
    _ = t * carlsonAffineForm z u ^ t := by ring_nf

/- The integral forms of Theorem 5.9-2(a)--(c) require a locally uniform domination theorem for
the `z`-derivatives of the complex-power kernel.  The three results above isolate all pointwise
analytic inputs; the remaining work is the parametric Bochner-integral argument. -/

end DirichletTransform
end CarlsonR
