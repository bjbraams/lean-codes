/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Deriv
public import Dirichlet.Average.Associated

/-!
# Carlson's R-function: homogeneity and associated-function relations

This file begins the regularized forms of Carlson's formulas 5.9-3, 5.9-5, and 5.9-6.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Carlson's first associated-function relation 5.9-5, in regularized form.  Gamma
regularization absorbs Carlson's weights and leaves the coefficients `b i`. -/
theorem regCarlsonRIntegral_eq_sum_update_add_one (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b z =
      ∑ i, b i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (stdSimplex ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  simpa only [regCarlsonRIntegral, addDirichletUnit] using
    regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z (fun w => w ^ t) hpow

/-- Carlson's second associated-function relation 5.9-5, in regularized form. -/
theorem regCarlsonRIntegral_add_one_eq_sum_mul_update (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (t + 1) b z =
      ∑ i, b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (stdSimplex ℝ ι) :=
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
            rw [mul_regDirichletIntegral_update_add_one hb]
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
  · apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
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

/-- Carlson's Euler differential identity, Theorem 5.9-2(c), for the native regularized
`R` integral. -/
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

/-- Positive-real scaling commutes with the principal complex power. -/
theorem ofReal_pos_mul_cpow (t w : ℂ) {a : ℝ} (ha : 0 < a) (hw : w ≠ 0) :
    ((a : ℂ) * w) ^ t = (a : ℂ) ^ t * w ^ t := by
  have hloga : log (a : ℂ) = (Real.log a : ℂ) := by
    simpa using (log_ofReal_mul ha (x := 1) one_ne_zero)
  rw [cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hw)]
  rw [mul_comm (a : ℂ) w, log_mul_ofReal a ha w hw, add_mul, exp_add]
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')]
  rw [cpow_def_of_ne_zero hw]
  rw [hloga]

/-- Pointwise homogeneity of Carlson's power kernel for positive real scaling. -/
theorem cpow_carlsonAffineForm_smul (t : ℂ) {a : ℝ} (ha : 0 < a)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
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
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
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

/- Carlson's third relation 5.9-5 and the remaining relations 5.9-6 can now be developed from
the integral differentiation theorem and the first two associated-function relations above. -/

/-- Two factors in the right half-plane have compatible principal logarithms. -/
theorem mul_cpow_of_re_pos {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) (t : ℂ) :
    (a * w) ^ t = a ^ t * w ^ t := by
  have ha0 := slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane ha)
  have hw0 := slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane hw)
  have haarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hwarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hlog : log (a * w) = log a + log w :=
    Complex.log_mul ha0 hw0 ⟨by linarith [haarg.1, hwarg.1],
      by linarith [haarg.2, hwarg.2]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero ha0 hw0), cpow_def_of_ne_zero ha0,
    cpow_def_of_ne_zero hw0, hlog, add_mul, exp_add]

/-- Complex homogeneity on the right half-plane, with explicit principal-branch control.
The scaled variables need not themselves be in the right half-plane. -/
theorem regCarlsonRIntegral_smul_of_re_pos (t : ℂ) {a : ℂ} (ha : 0 < a.re)
    {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b (fun i => a * z i) =
      a ^ t * regCarlsonRIntegral t b z := by
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
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

end DirichletTransform
end CarlsonR
