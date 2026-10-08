/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Inequalities
public import Carlson.R.IntegerReduction
public import Carlson.L.Relations

/-!
# The zero-concentration limit

The parameter-shift identity removes the apparent singularity of `R_t(c w, z)`
at concentration zero when the weights sum to one. The limit is the weighted
power sum. The analogous L-limit gives the weighted logarithmic kernel.
These limits hold for complex orders, weights, and slit-plane nodes.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 1.
-/

open Complex Dirichlet Filter Set ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- With one unit parameter, the regularized logarithmic average is the power-log kernel. -/
theorem regCarlsonL_single_one [DecidableEq ι] (t : ℂ) (i : ι) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t (Pi.single i 1) z = z i ^ t * log (z i) := by
  have h := hasDerivAt_regCarlsonR_L t (Pi.single i 1) hz
  have he : (fun s => regCarlsonR s (Pi.single i 1) z) = fun s => z i ^ s := by
    funext s
    simp [regCarlsonR_single s 1 i hz]
  rw [he] at h
  simpa only [mul_one, id_eq]
      using h.unique ((hasDerivAt_id t).const_cpow (Or.inl (Complex.slitPlane_ne_zero (hz i))))

omit [Fintype ι] in
/-- A unit shift of the zero concentration vector is a single unit parameter. -/
private theorem addDirichletUnit_zero_concentration [DecidableEq ι] (w : ι → ℂ) (i : ι) :
    addDirichletUnit (fun j => (0 : ℂ) * w j) i = Pi.single i 1 := by
  funext j
  simp [addDirichletUnit_apply, Pi.single_apply]

/-- The shifted concentration vector depends analytically on complex concentration. -/
private theorem analyticAt_addDirichletUnit_concentration (w : ι → ℂ) (i : ι) (c : ℂ) :
    AnalyticAt ℂ (fun a => addDirichletUnit (fun j => a * w j) i) c := by
  apply analyticAt_pi_iff.mpr
  intro j
  simp only [addDirichletUnit_apply]
  exact (analyticAt_id.mul analyticAt_const).add analyticAt_const

/-- The apparent pole of the ordinary R-family at concentration zero is removable,
with a weighted power-sum limit, for complex normalized weights and slit-plane nodes. -/
theorem tendsto_carlsonR_concentration_zero (t : ℂ) {w z : ι → ℂ}
    (hw : ∑ i, w i = 1) (hz : z ∈ carlsonRSlitDomain) :
    Tendsto (fun c : ℂ => carlsonR t (fun i => c * w i) z) (𝓝[≠] 0)
      (𝓝 (∑ i, w i * z i ^ t)) := by
  classical
  have hsum : ContinuousAt (fun c : ℂ =>
      ∑ i, w i * regCarlsonR t (addDirichletUnit (fun j => c * w j) i) z) 0 := by
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const
      (analyticAt_addDirichletUnit_concentration w i 0) analyticAt_const hz)
  have h := tendsto_self_mul_Gamma_nhds_zero.mul (hsum.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [Gamma_one, addDirichletUnit_zero_concentration,
    regCarlsonR_single t 1 _ hz, inv_one, mul_one, one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hs : ∑ i, c * w i = c := by rw [← Finset.mul_sum, hw, mul_one]
  rw [carlsonR, hs, regCarlsonR_eq_sum_addDirichletUnit t _ hz]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- The complex logarithmic average has the corresponding weighted power-log limit
as the concentration tends to zero. -/
theorem tendsto_carlsonL_concentration_zero (t : ℂ) {w z : ι → ℂ}
    (hw : ∑ i, w i = 1) (hz : z ∈ carlsonRSlitDomain) :
    Tendsto (fun c : ℂ => carlsonL t (fun i => c * w i) z) (𝓝[≠] 0)
      (𝓝 (∑ i, w i * (z i ^ t * log (z i)))) := by
  classical
  have hsum : ContinuousAt (fun c : ℂ =>
      ∑ i, w i * regCarlsonL t (addDirichletUnit (fun j => c * w j) i) z) 0 := by
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul (analyticAt_regCarlsonL_comp analyticAt_const
      (analyticAt_addDirichletUnit_concentration w i 0) analyticAt_const hz)
  have h := tendsto_self_mul_Gamma_nhds_zero.mul (hsum.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [addDirichletUnit_zero_concentration,
    regCarlsonL_single_one t _ hz, one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hs : ∑ i, c * w i = c := by rw [← Finset.mul_sum, hw, mul_one]
  rw [carlsonL, hs, regCarlsonL_eq_sum_addDirichletUnit t _ hz]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- Positive real concentrations approach the punctured complex origin. -/
private theorem tendsto_ofReal_concentration_zero :
    Tendsto (fun c : ℝ => (c : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with c hc
    change (c : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hc : c ≠ 0)

/-- Weights summing to one live on a nonempty index type. -/
private theorem nonempty_of_sum_eq_one {w : ι → ℝ} (hw1 : ∑ i, w i = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  simp at hw1

/-- Real R-averages tend to the weighted power sum as the positive concentration vanishes. -/
theorem tendsto_carlsonRReal_concentration_zero (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonRReal t (fun i => c * w i) x) (𝓝[>] 0)
      (𝓝 (∑ i, w i * x i ^ t)) := by
  have : Nonempty ι := nonempty_of_sum_eq_one hw1
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((tendsto_carlsonR_concentration_zero (t : ℂ)
      (w := fun i => (w i : ℂ)) (by exact_mod_cast hw1)
      (z := fun i => (x i : ℂ)) (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))).comp
        tendsto_ofReal_concentration_zero)
  simp only [← Complex.ofReal_cpow (hx _).le, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  simp only [Function.comp_def, ← Complex.ofReal_mul,
    ← ofReal_carlsonRReal t (fun i => mul_pos hc (hw i)) hx, Complex.ofReal_re]

/-- Real logarithmic averages tend to the weighted power-logarithm sum at zero concentration. -/
theorem tendsto_carlsonLReal_concentration_zero (t : ℝ) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonLReal t (fun i => c * w i) x) (𝓝[>] 0)
      (𝓝 (∑ i, w i * (x i ^ t * Real.log (x i)))) := by
  have : Nonempty ι := nonempty_of_sum_eq_one hw1
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((tendsto_carlsonL_concentration_zero (t : ℂ)
      (w := fun i => (w i : ℂ)) (by exact_mod_cast hw1)
      (z := fun i => (x i : ℂ)) (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))).comp
        tendsto_ofReal_concentration_zero)
  simp only [← Complex.ofReal_cpow (hx _).le, ← Complex.ofReal_log (hx _).le,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  simp only [Function.comp_def, ← Complex.ofReal_mul,
    ← ofReal_carlsonLReal t (fun i => mul_pos hc (hw i)) hx, Complex.ofReal_re]

/-- At nonzero order, the zero-concentration limit is the ordinary weighted power mean. -/
theorem tendsto_carlsonMeanReal_concentration_zero {t : ℝ} (ht : t ≠ 0)
    {w x : ι → ℝ} (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonMeanReal t (fun i => c * w i) x) (𝓝[>] 0)
      (𝓝 ((∑ i, w i * x i ^ t) ^ t⁻¹)) := by
  have : Nonempty ι := nonempty_of_sum_eq_one hw1
  have hp : 0 < ∑ i, w i * x i ^ t :=
    Finset.sum_pos (fun i _ => mul_pos (hw i) (Real.rpow_pos_of_pos (hx i) t)) Finset.univ_nonempty
  have h := (Real.continuousAt_rpow_const _ t⁻¹ (Or.inl hp.ne')).tendsto.comp
    (tendsto_carlsonRReal_concentration_zero t hw hw1 hx)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (carlsonMeanReal_eq_rpow ht (fun i => mul_pos hc (hw i)) hx).symm

/-- At order zero, the zero-concentration limit is the ordinary weighted geometric mean. -/
theorem tendsto_carlsonMeanReal_zero_concentration_zero {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    Tendsto (fun c : ℝ => carlsonMeanReal 0 (fun i => c * w i) x) (𝓝[>] 0)
      (𝓝 (Real.exp (∑ i, w i * Real.log (x i)))) := by
  simpa only [carlsonMeanReal, ↓reduceIte, Real.rpow_zero, one_mul, Function.comp_def] using
    (Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_carlsonLReal_concentration_zero 0 hw hw1 hx))

end Carlson
