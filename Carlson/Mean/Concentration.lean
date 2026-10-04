/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.ConcentrationZero
public import Dirichlet.Real.Concentration

/-!
# Concentration limits for hypergeometric means

For positive normalized weights and positive nodes, the limit at zero concentration
is the ordinary weighted power mean (geometric at order zero). At infinite
concentration every real-order hypergeometric mean tends to the weighted arithmetic
mean. The latter follows from Dirichlet concentration on the compact simplex.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 1.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- R is continuous in positive concentration for every real order. -/
theorem continuousOn_carlsonRReal_concentration (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) :
    ContinuousOn (fun c : ℝ => carlsonRReal t (fun i => c * w i) x) (Ioi 0) := by
  have h : ContinuousOn (fun c : ℝ => (carlsonR (t : ℂ)
      (fun i => (c : ℂ) * (w i : ℂ)) (fun i => (x i : ℂ))).re) (Ioi 0) := by
    intro c hc
    have ha := analyticAt_carlsonR_comp (t := fun _ : ℂ => (t : ℂ))
      (b := fun c : ℂ => fun i => c * (w i : ℂ))
      (z := fun _ : ℂ => fun i => (x i : ℂ)) (p := (c : ℂ)) analyticAt_const
      (analyticAt_pi_iff.mpr fun _ => analyticAt_id.mul analyticAt_const) analyticAt_const
      (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
      (fun n => by simpa only [Complex.ofReal_mul] using
        sum_ofReal_parameters_ne_neg_nat (fun i => mul_pos hc (hw i)) n)
    exact (Complex.continuous_re.continuousAt.comp
      (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  apply h.congr
  intro c hc
  simp only [← Complex.ofReal_mul, ← ofReal_carlsonRReal t (fun i => mul_pos hc (hw i)) hx,
    Complex.ofReal_re]

/-- L is continuous in positive concentration for every real order. -/
theorem continuousOn_carlsonLReal_concentration (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) :
    ContinuousOn (fun c : ℝ => carlsonLReal t (fun i => c * w i) x) (Ioi 0) := by
  have h : ContinuousOn (fun c : ℝ => (carlsonL (t : ℂ)
      (fun i => (c : ℂ) * (w i : ℂ)) (fun i => (x i : ℂ))).re) (Ioi 0) := by
    intro c hc
    have ha := analyticAt_carlsonL_comp (t := fun _ : ℂ => (t : ℂ))
      (b := fun c : ℂ => fun i => c * (w i : ℂ))
      (z := fun _ : ℂ => fun i => (x i : ℂ)) (p := (c : ℂ)) analyticAt_const
      (analyticAt_pi_iff.mpr fun _ => analyticAt_id.mul analyticAt_const) analyticAt_const
      (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
      (fun n => by simpa only [Complex.ofReal_mul] using
        sum_ofReal_parameters_ne_neg_nat (fun i => mul_pos hc (hw i)) n)
    exact (Complex.continuous_re.continuousAt.comp
      (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  apply h.congr
  intro c hc
  simp only [← Complex.ofReal_mul, ← ofReal_carlsonLReal t (fun i => mul_pos hc (hw i)) hx,
    Complex.ofReal_re]

/-- The mean is continuous in positive concentration, including at order zero. -/
theorem continuousOn_carlsonMeanReal_concentration (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) :
    ContinuousOn (fun c : ℝ => carlsonMeanReal t (fun i => c * w i) x) (Ioi 0) := by
  by_cases ht : t = 0
  · subst t
    simpa only [carlsonMeanReal, ↓reduceIte, Function.comp_def] using
      Real.continuous_exp.comp_continuousOn (continuousOn_carlsonLReal_concentration 0 hw hx)
  · simpa only [carlsonMeanReal, ht, ↓reduceIte, Function.comp_def] using
      Real.continuous_exp.comp_continuousOn (((continuousOn_carlsonRReal_concentration t hw hx).log
        (fun c hc => (carlsonRReal_pos t (fun i => mul_pos hc (hw i)) hx).ne')).div_const t)

/-- R tends to the power of the weighted arithmetic mean at infinite concentration. -/
theorem tendsto_carlsonRReal_concentration_atTop (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonRReal t (fun i => c * w i) x) atTop
      (𝓝 ((∑ i, w i * x i) ^ t)) := by
  apply tendsto_integral_dirichletMeasure_concentration_of_contDiff hw hw1
  exact ContDiffOn.rpow_const_of_ne (by fun_prop)
    (fun u hu => (dirichlet_affine_mem (convex_Ioi 0) hx hu).ne')

/-- L tends to the power-log kernel at the weighted arithmetic mean at infinite concentration. -/
theorem tendsto_carlsonLReal_concentration_atTop (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonLReal t (fun i => c * w i) x) atTop
      (𝓝 ((∑ i, w i * x i) ^ t * Real.log (∑ i, w i * x i))) := by
  apply tendsto_integral_dirichletMeasure_concentration_of_contDiff hw hw1
  exact (ContDiffOn.rpow_const_of_ne (by fun_prop)
    (fun u hu => (dirichlet_affine_mem (convex_Ioi 0) hx hu).ne')).mul
      (ContDiffOn.log (by fun_prop)
        (fun u hu => (dirichlet_affine_mem (convex_Ioi 0) hx hu).ne'))

/-- Every real-order hypergeometric mean tends to the weighted arithmetic mean
as concentration tends to infinity, including order zero and negative orders. -/
theorem tendsto_carlsonMeanReal_concentration_atTop (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonMeanReal t (fun i => c * w i) x) atTop
      (𝓝 (∑ i, w i * x i)) := by
  have hA : 0 < ∑ i, w i * x i :=
    Finset.sum_pos (fun i _ => mul_pos (hw i) (hx i)) Finset.univ_nonempty
  by_cases ht : t = 0
  · subst t
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_carlsonLReal_concentration_atTop 0 hw hw1 hx)
    simpa only [Real.rpow_zero, one_mul, Real.exp_log hA, carlsonMeanReal, ↓reduceIte,
      Function.comp_def] using h
  · have h := (Real.continuousAt_rpow_const _ t⁻¹
        (Or.inl (Real.rpow_pos_of_pos hA t).ne')).tendsto.comp
      (tendsto_carlsonRReal_concentration_atTop t hw hw1 hx)
    rw [Real.rpow_rpow_inv hA.le ht] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact (carlsonMeanReal_eq_rpow ht (fun i => mul_pos hc (hw i)) hx).symm

end Carlson
