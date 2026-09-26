/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Pow
public import Carlson.R.Deriv
public import Dirichlet.Average.Associated

/-!
# Carlson's R-function: homogeneity and associated-function relations

This file proves the regularized forms of Carlson's formulas 5.9-3, 5.9-5, and 5.9-6 on
the native convergence region and right-half-plane node domain. The third associated
relation follows by summing the tangential integration-by-parts relation.
The extension of the three associated relations to all complex parameters and slit-plane
nodes is in `Carlson.R.Explicit`. Node derivatives are stated for the native integral.

## Main results

* `Carlson.regCarlsonRIntegral_eq_sum_update_add_one`: Carlson's first associated-function
  relation 5.9-5, in regularized form. Gamma regularization absorbs Carlson's weights and leaves
  the coefficients `b i`.
* `Carlson.regCarlsonRIntegral_smul_of_pos`: Carlson's homogeneity formula 5.9-3 for the native
  regularized integral, stated with positive real scaling so that Mathlib's principal branch is
  preserved.
* `Carlson.carlsonRIntegral_smul_of_pos`: The corresponding unregularized homogeneity formula.
* `Carlson.regCarlsonRIntegral_smul_of_re_pos`: Complex homogeneity on the right half-plane,
  with explicit principal-branch control. The scaled variables need not themselves be in the
  right half-plane.
* `Carlson.carlsonRIntegral_smul_of_re_pos`: Unregularized complex homogeneity with the same
  principal-branch hypotheses.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Carlson's first associated-function relation 5.9-5, in regularized form.  Gamma
regularization absorbs Carlson's weights and leaves the coefficients `b i`. -/
theorem regCarlsonRIntegral_eq_sum_update_add_one (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b z =
      ∑ i, b i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  simpa only [regCarlsonRIntegral, addDirichletUnit] using
    regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z (fun w => w ^ t) hpow

open scoped Classical in
/-- Carlson's second associated-function relation 5.9-5, in regularized form. -/
theorem regCarlsonRIntegral_add_one_eq_sum_mul_update (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (t + 1) b z =
      ∑ i, b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  have hterm (i : ι) :
      b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z =
        regDirichletIntegral b
          (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) := by
    calc
      b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z =
          z i * (b i * regDirichletIntegral (Function.update b i (b i + 1))
            (fun u ↦ carlsonAffineForm z u ^ t)) := by
              simp only [regCarlsonRIntegral, regCarlsonDirichletAverage]
              ring
      _ = z i * regDirichletIntegral b
          (fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t) := by
            rw [show Function.update b i (b i + 1) = addDirichletUnit b i from rfl,
              mul_regDirichletIntegral_addDirichletUnit hb]
      _ = regDirichletIntegral b
          (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) := by
            have hfun :
                ((Complex.ofReal ∘ fun u : ι → ℝ ↦ u i) *
                    fun u ↦ carlsonAffineForm z u ^ t) =
                  fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t := by
              funext u
              rfl
            rw [← hfun]
            exact (regDirichletIntegral_smul b
              (fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t) (z i)).symm
  rw [show (∑ i, b i * z i *
      regCarlsonRIntegral t (Function.update b i (b i + 1)) z) =
      ∑ i, regDirichletIntegral b
        (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i]
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    dsimp only
    have hne : carlsonAffineForm z u ≠ 0 :=
      slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)
    rw [cpow_add _ _ hne, cpow_one]
    rw [← Finset.mul_sum]
    congr 1
    rw [show ∑ i, z i * ((u i : ℂ) * carlsonAffineForm z u ^ t) =
        (∑ i, (u i : ℂ) * z i) * carlsonAffineForm z u ^ t by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    unfold carlsonAffineForm
    ring
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const.mul
        ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hpow))

/-- The tangential contiguous relation for the power kernel, including equal indices. -/
theorem regCarlsonRIntegral_tangent (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    (z i - z j) * (t *
      regCarlsonRIntegral (t - 1) (addDirichletUnit (addDirichletUnit b i) j) z) =
      regCarlsonRIntegral t (addDirichletUnit b i) z -
        regCarlsonRIntegral t (addDirichletUnit b j) z := by
  by_cases hij : i = j
  · subst j
    simp
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ ↦ w ^ t) carlsonRightHalfPlane := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonRightHalfPlane_subset_slitPlane hw)] with v hv
    exact differentiableAt_id.cpow_const hv
  have hderiv (q : ι → ℂ) :
      regCarlsonDirichletAverage q z (deriv (fun w : ℂ ↦ w ^ t)) =
        t * regCarlsonRIntegral (t - 1) q z := by
    rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_const_mul]
    apply regDirichletIntegral_congr
    intro u hu
    exact Complex.deriv_cpow_const (carlsonAffineForm_mem_slitPlane hz hu)
  have H := regCarlsonDirichletAverage_tangent convex_carlsonRightHalfPlane hpow hb
    (Set.range_subset_iff.mpr hz) i j hij
  rw [hderiv] at H
  have hcomm : addDirichletUnit (addDirichletUnit b j) i =
      addDirichletUnit (addDirichletUnit b i) j := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, Function.update_apply]
  simpa only [hcomm, regCarlsonRIntegral] using H

/-- Raising one parameter by one adds the corresponding summand to a weighted coordinate sum. -/
private lemma sum_addDirichletUnit_mul (b : ι → ℂ) (i : ι) (f : ι → ℂ) :
    ∑ j, addDirichletUnit b i j * f j = (∑ j, b j * f j) + f i := by
  classical
  have hterm (j : ι) : addDirichletUnit b i j * f j =
      b j * f j + if j = i then f i else 0 := by
    by_cases hji : j = i <;> simp [addDirichletUnit, hji, add_mul]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

/-- Carlson's third associated-function relation 5.9-5, equation (7), in regularized form.
No parameter is lowered, so the ordinary convergence hypothesis suffices. -/
theorem regCarlsonRIntegral_eq_update_add_one (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonRIntegral t b z =
      ((∑ j, b j) + t) * regCarlsonRIntegral t (addDirichletUnit b i) z -
        t * z i * regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
  let q := addDirichletUnit b i
  let F : ι → ℂ := fun j ↦ regCarlsonRIntegral (t - 1) (addDirichletUnit q j) z
  have hq := addDirichletUnit_mem_mvBetaConvergent hb i
  have hfirst := regCarlsonRIntegral_eq_sum_update_add_one (t - 1) hq hz
  have hsecond := regCarlsonRIntegral_add_one_eq_sum_mul_update (t - 1) hq hz
  change regCarlsonRIntegral (t - 1) q z = ∑ j, q j * F j at hfirst
  change regCarlsonRIntegral (t - 1 + 1) q z = ∑ j, q j * z j * F j at hsecond
  rw [sub_add_cancel] at hsecond
  rw [sum_addDirichletUnit_mul b i F] at hfirst
  simp_rw [mul_assoc] at hsecond
  rw [sum_addDirichletUnit_mul b i (fun j ↦ z j * F j)] at hsecond
  have htangent := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ ↦ congrArg (fun w : ℂ ↦ b j * w)
      (regCarlsonRIntegral_tangent t hb hz i j))
  change (∑ j, b j * ((z i - z j) * (t * F j))) =
    ∑ j, b j * (regCarlsonRIntegral t q z -
      regCarlsonRIntegral t (addDirichletUnit b j) z) at htangent
  have hsum := regCarlsonRIntegral_eq_sum_update_add_one t hb hz
  change regCarlsonRIntegral t b z =
    ∑ j, b j * regCarlsonRIntegral t (addDirichletUnit b j) z at hsum
  have hleft : (∑ j, b j * ((z i - z j) * (t * F j))) =
      t * z i * (∑ j, b j * F j) - t * ∑ j, b j * (z j * F j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft] at htangent
  simp_rw [mul_sub] at htangent
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hsum] at htangent
  change regCarlsonRIntegral t b z =
    ((∑ j, b j) + t) * regCarlsonRIntegral t q z -
      t * z i * regCarlsonRIntegral (t - 1) q z
  linear_combination t * z i * hfirst - t * hsecond + htangent

/-- Carlson's second differential relation 5.9-6, equation (10), in regularized form.
The first relation, equation (9), is `carlsonPartialDeriv_regCarlsonRIntegral`. -/
theorem mul_carlsonPartialDeriv_add_mul_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    z i * carlsonPartialDeriv i (regCarlsonRIntegral t b) z +
      b i * regCarlsonRIntegral t b z =
        b i * ((∑ j, b j) + t) * regCarlsonRIntegral t (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz]
  linear_combination b i * regCarlsonRIntegral_eq_update_add_one t hb hz i

/-- Carlson's translation differential identity, the first equation of Theorem 5.9-2. -/
theorem sum_carlsonPartialDeriv_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, carlsonPartialDeriv i (regCarlsonRIntegral t b) z =
      t * regCarlsonRIntegral (t - 1) b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact (regCarlsonRIntegral_eq_sum_update_add_one (t - 1) hb hz).symm

/-- Carlson's Euler differential identity, the second equation of Theorem 5.9-2, for the
native regularized `R` integral. -/
theorem sum_mul_carlsonPartialDeriv_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, z i * carlsonPartialDeriv i (regCarlsonRIntegral t b) z =
      t * regCarlsonRIntegral t b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz]
  calc
    ∑ i, z i * (t * b i *
        regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z) =
        t * ∑ i, b i * z i *
          regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = t * regCarlsonRIntegral ((t - 1) + 1) b z := by
      congr 1
      simpa [addDirichletUnit] using
        (regCarlsonRIntegral_add_one_eq_sum_mul_update (t - 1) hb hz).symm
    _ = t * regCarlsonRIntegral t b z := by ring_nf

/-- Pointwise homogeneity of Carlson's power kernel for positive real scaling. -/
theorem cpow_carlsonAffineForm_smul (t : ℂ) {a : ℝ} (ha : 0 < a)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm (fun i ↦ (a : ℂ) * z i) u ^ t =
      (a : ℂ) ^ t * carlsonAffineForm z u ^ t := by
  rw [show carlsonAffineForm (fun i ↦ (a : ℂ) * z i) u =
      (a : ℂ) * carlsonAffineForm z u by
    unfold carlsonAffineForm
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  exact ofReal_pos_mul_cpow t _ ha
    (slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu))

/-- Carlson's homogeneity formula 5.9-3 for the native regularized integral, stated with
positive real scaling so that Mathlib's principal branch is preserved. -/
theorem regCarlsonRIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonRIntegral t b (fun i ↦ (a : ℂ) * z i) =
      (a : ℂ) ^ t * regCarlsonRIntegral t b z := by
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [cpow_carlsonAffineForm_smul t ha hz hu]
  ring

/-- The corresponding unregularized homogeneity formula. -/
theorem carlsonRIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    carlsonRIntegral t b (fun i ↦ (a : ℂ) * z i) =
      (a : ℂ) ^ t * carlsonRIntegral t b z := by
  unfold carlsonRIntegral
  rw [regCarlsonRIntegral_smul_of_pos t hz ha]
  ring

/-- Complex homogeneity on the right half-plane, with explicit principal-branch control.
The scaled variables need not themselves be in the right half-plane. -/
theorem regCarlsonRIntegral_smul_of_re_pos (t : ℂ) {a : ℂ} (ha : 0 < a.re)
    {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b (fun i => a * z i) =
      a ^ t * regCarlsonRIntegral t b z := by
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  have hform : carlsonAffineForm (fun i => a * z i) u = a * carlsonAffineForm z u := by
    simp only [carlsonAffineForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hform, mul_cpow_of_re_pos ha (carlsonAffineForm_mem_rightHalfPlane hz hu)]
  ring

/-- Unregularized complex homogeneity with the same principal-branch hypotheses. -/
theorem carlsonRIntegral_smul_of_re_pos (t : ℂ) {a : ℂ} (ha : 0 < a.re)
    {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    carlsonRIntegral t b (fun i => a * z i) = a ^ t * carlsonRIntegral t b z := by
  unfold carlsonRIntegral
  rw [regCarlsonRIntegral_smul_of_re_pos t ha hz]
  ring

end Carlson
end CarlsonR
