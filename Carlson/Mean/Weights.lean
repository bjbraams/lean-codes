/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Basic
public import Carlson.L.SlitDeriv
public import Carlson.R.SlitDeriv
public import ToMathlib.Analysis.Calculus.MeanWeights

/-!
# Complex weights of hypergeometric means

The derivative-defined weights are `b i / ∑ j, b j`, even for complex parameters.
Only the poles of the ordinary normalization are excluded. No positivity assumption
or restriction on the complex order is required at the all-one vector.
-/

open Complex Dirichlet Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The node derivative of ordinary R at the all-one vector, at every complex order. -/
theorem hasDerivAt_carlsonR_update_one (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonR t b (Function.update 1 i w))
      (t * b i / ∑ j, b j) 1 := by
  simp only [Pi.one_def]
  have hc : (∑ j, b j) ≠ 0 := by simpa using hb 0
  have h := (hasDerivAt_regCarlsonR_update t b (z := fun _ => 1)
    (fun _ => one_mem_slitPlane) i).const_mul (Gamma (∑ j, b j))
  simp only [regCarlsonR_const_node _ _ (by norm_num : 0 < (1 : ℂ).re),
    one_cpow, one_mul, sum_addDirichletUnit, Gamma_add_one _ hc] at h
  convert h using 1
  · rfl
  · field_simp [Gamma_ne_zero hb]

open scoped Classical in
/-- The node derivative of ordinary L at the all-one vector is independent of its order. -/
theorem hasDerivAt_carlsonL_update_one (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonL t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
  simp only [Pi.one_def]
  have hc : (∑ j, b j) ≠ 0 := by simpa using hb 0
  have h := ((analyticOnNhd_regCarlsonL t b).analyticAt_update
    (z := fun _ => 1) (fun _ => one_mem_slitPlane) i).differentiableAt.hasDerivAt
  change HasDerivAt _ (carlsonPartialDeriv i (regCarlsonL t b) (fun _ => 1)) 1 at h
  rw [carlsonPartialDeriv_regCarlsonL t b (fun _ => one_mem_slitPlane) i] at h
  have h' := h.const_mul (Gamma (∑ j, b j))
  simp only [regCarlsonL_one, mul_zero, zero_add,
    regCarlsonR_const_node _ _ (by norm_num : 0 < (1 : ℂ).re), one_cpow, one_mul,
    sum_addDirichletUnit, Gamma_add_one _ hc] at h'
  convert h' using 1
  · rfl
  · field_simp [Gamma_ne_zero hb]

open scoped Classical in
/-- The logarithm defining M has the same coordinate derivative at the diagonal for all
orders, including zero. -/
theorem hasDerivAt_carlsonMeanLog_update_one (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonMeanLog t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
  by_cases ht : t = 0
  · subst t
    simpa only [carlsonMeanLog, ↓reduceIte] using hasDerivAt_carlsonL_update_one 0 hb i
  · have h := ((hasDerivAt_carlsonR_update_one t hb i).clog
      (by simp [Function.update_eq_self, Pi.one_def, carlsonR_one_nodes t hb])).div_const t
    simp only [Function.update_eq_self, Pi.one_def, carlsonR_one_nodes t hb, div_one] at h
    simp only [carlsonMeanLog, ht, ↓reduceIte]
    convert h using 1
    field_simp [ht]

open scoped Classical in
/-- The complex hypergeometric mean has derivative `b i / c` in coordinate `i` at the
all-one vector, including at order zero. -/
theorem hasDerivAt_carlsonMean_update_one (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonMean t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
  have h := (hasDerivAt_carlsonMeanLog_update_one t hb i).cexp
  simpa [carlsonMean, carlsonMeanLog, carlsonL, Pi.one_def, carlsonR_one_nodes t hb] using h

/-- Brenner–Carlson (3.13): the weights of M are the normalized complex parameters. -/
theorem meanWeight_carlsonMean (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    Function.meanWeight ℂ (carlsonMean t b) i = b i / ∑ j, b j := by
  classical
  have ha := analyticAt_carlsonMean_comp t (b := fun _ : ι → ℂ => b)
    (z := id) (p := 1) analyticAt_const analyticAt_id (fun _ => one_mem_slitPlane) hb
    (fun _ => by simp [Pi.one_def, carlsonR_one_nodes t hb])
  exact (SeveralComplexVariables.hasDerivAt_update_of_differentiableAt
    ha.differentiableAt i).unique (hasDerivAt_carlsonMean_update_one t hb i)

/-- The complex hypergeometric weights sum to one. -/
theorem sum_meanWeight_carlsonMean (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) :
    ∑ i, Function.meanWeight ℂ (carlsonMean t b) i = 1 := by
  simp_rw [meanWeight_carlsonMean t hb, ← Finset.sum_div]
  exact div_self (by simpa using hb 0)

open scoped Classical in
/-- The ratio mean has the same complex coordinate weights, including coincident orders. -/
theorem hasDerivAt_carlsonRatioMean_update_one (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonRatioMean s t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
  have hR a := hasDerivAt_carlsonR_update_one a hb i
  have hlog a := (hR a).clog (by simp [Pi.one_def, carlsonR_one_nodes a hb])
  by_cases h : s = t
  · subst s
    have hd := ((hasDerivAt_carlsonL_update_one t hb i).div (hR t)
      (by simp [Pi.one_def, carlsonR_one_nodes t hb])).cexp
    simpa [carlsonRatioMean_self, carlsonL, Pi.one_def, carlsonR_one_nodes t hb] using hd
  · have hd := (((hlog t).sub (hlog s)).div_const (t - s)).cexp
    simp only [Pi.sub_apply, Function.update_eq_self, Pi.one_def, carlsonR_one_nodes _ hb,
      div_one, log_one, sub_self, zero_div, exp_zero, one_mul] at hd
    simp only [carlsonRatioMean, carlsonRatioMeanLog, h, ↓reduceIte]
    convert hd using 1
    field_simp [sub_ne_zero.mpr (Ne.symm h)]

/-- The complex ratio means have weights `b i / c`, independent of both orders. -/
theorem meanWeight_carlsonRatioMean (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    Function.meanWeight ℂ (carlsonRatioMean s t b) i = b i / ∑ j, b j := by
  classical
  have ha := analyticAt_carlsonRatioMean_comp s t (b := fun _ : ι → ℂ => b)
    (z := id) (p := 1) analyticAt_const analyticAt_id (fun _ => one_mem_slitPlane) hb
    (by simp [Pi.one_def, carlsonR_one_nodes s hb])
    (by simp [Pi.one_def, carlsonR_one_nodes t hb])
  exact (SeveralComplexVariables.hasDerivAt_update_of_differentiableAt
    ha.differentiableAt i).unique (hasDerivAt_carlsonRatioMean_update_one s t hb i)

open scoped Classical in
/-- The power-transformed mean has normalized parameter weights at all complex orders
and powers, including either zero parameter. -/
theorem hasDerivAt_carlsonPowerMean_update_one (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    HasDerivAt (fun w => carlsonPowerMean s t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
  by_cases hs : s = 0
  · subst s
    have h := (((hasDerivAt_id (1 : ℂ)).clog one_mem_slitPlane).const_mul
      (b i / ∑ j, b j)).cexp
    simpa [carlsonPowerMean_zero, Function.update_apply, apply_ite, mul_ite] using h
  · have hp : HasDerivAt (fun w : ℂ => w ^ s) s 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).cpow_const (c := s) one_mem_slitPlane
    have hm : HasDerivAt (fun w => carlsonMeanLog t b (Function.update 1 i w))
        (b i / ∑ j, b j) ((1 : ℂ) ^ s) := by
      simpa using hasDerivAt_carlsonMeanLog_update_one t hb i
    have hd := ((hm.comp 1 hp).div_const s).cexp
    have hu (w : ℂ) : (fun j => Function.update (1 : ι → ℂ) i w j ^ s) =
        Function.update (1 : ι → ℂ) i (w ^ s) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    simp only [carlsonPowerMean, carlsonPowerMeanLog, hs, ↓reduceIte, hu]
    simpa [hs, carlsonMeanLog, carlsonL,
      Pi.one_def, carlsonR_one_nodes t hb, Function.comp_def] using hd

/-- Brenner–Carlson (3.19) has the same derivative-defined weights as the original mean. -/
theorem meanWeight_carlsonPowerMean (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    Function.meanWeight ℂ (carlsonPowerMean s t b) i = b i / ∑ j, b j := by
  classical
  have ha := analyticAt_carlsonPowerMean_comp s t (b := fun _ : ι → ℂ => b)
    (z := id) (p := 1) analyticAt_const analyticAt_id (fun _ => one_mem_slitPlane) hb
    (fun _ _ => by simp) (fun _ _ => by simp [Pi.one_def, carlsonR_one_nodes t hb])
  exact (SeveralComplexVariables.hasDerivAt_update_of_differentiableAt
    ha.differentiableAt i).unique (hasDerivAt_carlsonPowerMean_update_one s t hb i)

/-- The logarithm defining M has the same diagonal weights as M itself. -/
theorem meanWeight_carlsonMeanLog (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (i : ι) :
    Function.meanWeight ℂ (carlsonMeanLog t b) i = b i / ∑ j, b j := by
  classical
  have ha := analyticAt_carlsonMeanLog_comp t (b := fun _ : ι → ℂ => b)
    (z := id) (p := 1) analyticAt_const analyticAt_id (fun _ => one_mem_slitPlane) hb
    (fun _ => by simp [Pi.one_def, carlsonR_one_nodes t hb])
  exact (SeveralComplexVariables.hasDerivAt_update_of_differentiableAt
    ha.differentiableAt i).unique (hasDerivAt_carlsonMeanLog_update_one t hb i)

/-- Differentiating powered nodes at power zero gives the weighted sum of their complex
logarithms. This identifies the zero-power limit of the transformed family. -/
theorem hasDerivAt_carlsonMeanLog_power_zero (t : ℂ) {b z : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (hz : z ∈ carlsonRSlitDomain) :
    HasDerivAt (fun s : ℂ => carlsonMeanLog t b (fun i => z i ^ s))
      (∑ i, (b i / ∑ j, b j) * log (z i)) 0 := by
  have ha := analyticAt_carlsonMeanLog_comp t (b := fun _ : ι → ℂ => b)
    (z := id) (p := 1) analyticAt_const analyticAt_id (fun _ => one_mem_slitPlane) hb
    (fun _ => by simp [Pi.one_def, carlsonR_one_nodes t hb])
  have hn : HasDerivAt (fun s : ℂ => fun i => z i ^ s) (fun i => log (z i)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using (hasDerivAt_id (0 : ℂ)).const_cpow (c := z i) (Or.inl (slitPlane_ne_zero (hz i)))
  have hf : HasFDerivAt (carlsonMeanLog t b) (fderiv ℂ (carlsonMeanLog t b) 1)
      (fun i => z i ^ (0 : ℂ)) := by
    simpa only [cpow_zero, ← Pi.one_def, id_eq] using ha.differentiableAt.hasFDerivAt
  have h := hf.comp_hasDerivAt 0 hn
  rw [Function.fderiv_one_eq_sum_meanWeight] at h
  simpa only [meanWeight_carlsonMeanLog t hb, mul_comm, Function.comp_def] using h

/-- The zero-power definition is the removable analytic extension in the complex power,
for arbitrary complex order and nonexceptional complex parameters. -/
theorem analyticAt_carlsonPowerMean_power_zero (t : ℂ) {b z : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) (hz : z ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun s : ℂ => carlsonPowerMean s t b z) 0 := by
  let g : ℂ → ℂ := fun s => carlsonMeanLog t b (fun i => z i ^ s)
  have hg : AnalyticAt ℂ g 0 := by
    change AnalyticAt ℂ (fun s => carlsonMeanLog t b (fun i => z i ^ s)) 0
    apply analyticAt_carlsonMeanLog_comp t (b := fun _ : ℂ => b)
      (z := fun s i => z i ^ s) (p := 0) analyticAt_const
      (analyticAt_pi_iff.mpr fun i => analyticAt_const.cpow analyticAt_id (hz i))
      (fun i => by simp) hb
    intro _
    simpa only [cpow_zero, carlsonR_one_nodes t hb] using one_mem_slitPlane
  obtain ⟨p, hp⟩ := hg
  have ha := hp.has_fpower_series_dslope_fslope.analyticAt.cexp'
  have heq : (fun s => carlsonPowerMean s t b z) = (fun s => exp (dslope g 0 s)) := by
    funext s
    by_cases hs : s = 0
    · subst s
      rw [dslope_same, carlsonPowerMean_zero]
      exact congrArg exp (hasDerivAt_carlsonMeanLog_power_zero t hb hz).deriv.symm
    · simp [carlsonPowerMean, carlsonPowerMeanLog, hs, dslope_of_ne _ hs,
        slope_def_field, g, carlsonMeanLog, carlsonL, carlsonR_one_nodes t hb]
  rw [heq]
  exact ha

end Carlson
