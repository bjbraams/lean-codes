/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Continuation
public import Carlson.Aggregation
public import Carlson.R.ZeroParameter
public import Carlson.L.Deriv

/-!
# Symmetry, aggregation, and scaling of Carlson's L-function

Carlson (1987), (2.2)–(2.5), for all complex exponents and Dirichlet parameters and all nodes in
the product slit plane. Each identity is first proved for right-half-plane nodes by
continuation in the parameters from the native integral, then extended to slit-plane nodes by
permanence of functional relations. Positive real scaling is branch-safe on the whole slit
plane; arbitrary complex scaling would require additional branch assumptions. Zero-parameter
deletion retains a nonempty remaining index type. Coincident-node and singleton formulas also
cover Gamma zeros in the regularized normalization.


## Main results

* `Carlson.regCarlsonLIntegral_empty`: The empty-index native integral vanishes.
* `Carlson.regCarlsonL_one`: The regularized slit L-function vanishes at the all-one node
  vector.
* `Carlson.regCarlsonL_unique`: The singleton convention, including the reciprocal Gamma
  regularization.
* `Carlson.carlsonRSlitDomain_smul_pos`: Positive real scaling preserves the principal-branch
  node domain.
* `Carlson.regCarlsonL_smul_of_pos`: Equation (2.5) on slit-plane nodes: scaling contributes the
  logarithmic R-term.

## References

* B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM J. Math. Anal. 18 (1987), 550–565.
-/

open Dirichlet
open Complex Filter Set ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The empty-index native integral vanishes. -/
@[simp] theorem regCarlsonLIntegral_empty [IsEmpty ι] (t : ℂ) (b z : ι → ℂ) :
    regCarlsonLIntegral t b z = 0 := by
  simp [regCarlsonLIntegral, regCarlsonDirichletAverage, regDirichletIntegral]

omit [Fintype ι] in
/-- Positive real scaling preserves the node domain. -/
theorem carlsonRVariableDomain_smul_pos {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {a : ℝ} (ha : 0 < a) : (fun i => (a : ℂ) * z i) ∈ carlsonRVariableDomain := by
  intro i
  change 0 < ((a : ℂ) * z i).re
  simpa using mul_pos ha (hz i)

/-- Equation (2.5) for the native integral, including the logarithmic correction. -/
theorem regCarlsonLIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain)
    {a : ℝ} (ha : 0 < a) :
    regCarlsonLIntegral t b (fun i => (a : ℂ) * z i) =
      (a : ℂ) ^ t * (regCarlsonLIntegral t b z + regCarlsonRIntegral t b z * log (a : ℂ)) := by
  have h := hasDerivAt_regCarlsonRIntegral_L t hb (carlsonRVariableDomain_smul_pos hz ha)
  have heq : (fun s => regCarlsonRIntegral s b (fun i => (a : ℂ) * z i)) =
      (fun s => (a : ℂ) ^ s * regCarlsonRIntegral s b z) :=
    funext fun s => regCarlsonRIntegral_smul_of_pos s hz ha
  rw [heq] at h
  have hp : HasDerivAt (fun s : ℂ => (a : ℂ) ^ s)
      ((a : ℂ) ^ t * log (a : ℂ)) t :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))).hasDerivAt
  have H := h.unique (hp.mul (hasDerivAt_regCarlsonRIntegral_L t hb hz))
  linear_combination H

/-- Equation (2.4): equal nodes may be aggregated by any surjective partition. -/
private theorem regCarlsonL_aggregate_of_mem_variableDomain {κ : Type*} [Fintype κ]
    {q : ι → κ} (hq : Function.Surjective q) (t : ℂ)
    {z : κ → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : ι → ℂ) :
    regCarlsonL t b (z ∘ q) =
      regCarlsonL t (stdSimplexAggregate q b) z := by
  unfold regCarlsonL
  congr 1
  funext s
  exact regCarlsonR_aggregate hq s hz b

/-- Equation (2.3): a zero parameter and its node can be deleted. The remaining
index type is nonempty, as in the existing R-deletion theorem used here. -/
private theorem regCarlsonL_option_zero_of_mem_variableDomain [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonL t b z =
      regCarlsonL t (b ∘ some) (z ∘ some) := by
  unfold regCarlsonL
  congr 1
  funext s
  exact regCarlsonR_option_zero s hb hz

/-- Equation (2.2), for arbitrary complex Dirichlet parameters. -/
private theorem regCarlsonL_perm_of_mem_variableDomain (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (σ : Equiv.Perm ι) :
    regCarlsonL t (b ∘ σ) (z ∘ σ) =
      regCarlsonL t b z := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ?_
    (analyticOnNhd_regCarlsonL_parameters t (carlsonRVariableDomain_subset_slitDomain hz)) ?_) b
  · intro b _
    exact analyticAt_regCarlsonL_comp analyticAt_const (analyticAt_pi_iff.mpr (fun i =>
        (ContinuousLinearMap.proj (σ i) : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)) analyticAt_const
            (carlsonRVariableDomain_subset_slitDomain (fun i => hz (σ i)))
  · intro b hb
    calc
      _ = regCarlsonLIntegral t (b ∘ σ) (z ∘ σ) :=
        regCarlsonL_eq_regCarlsonLIntegral t (fun i => hb (σ i)) (fun i => hz (σ i))
      _ = regCarlsonLIntegral t b z := regCarlsonLIntegral_perm t b z σ
      _ = _ := (regCarlsonL_eq_regCarlsonLIntegral t hb hz).symm

/-- Coincident nodes reduce L to the elementary power-logarithm kernel. -/
private theorem regCarlsonL_const_of_mem_variableDomain (t w : ℂ) (hw : w ∈ carlsonRightHalfPlane)
    (b : ι → ℂ) :
    regCarlsonL t b (fun _ => w) =
      (w ^ t * log w) / Gamma (∑ i, b i) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonL_parameters t (carlsonRVariableDomain_subset_slitDomain (fun _
        => hw))) ?_ ?_) b
  · intro b _
    have hsum : AnalyticAt ℂ (fun c : ι → ℂ => ∑ i, c i) b :=
      Finset.analyticAt_fun_sum _ (fun i _ =>
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
    have hγ := Complex.differentiable_one_div_Gamma.analyticAt (∑ i, b i)
    simpa only [div_eq_mul_inv, one_mul, Function.comp_def, Pi.mul_apply] using!
      analyticAt_const.mul (hγ.comp hsum)
  · intro b hb
    dsimp only
    rw [regCarlsonL_eq_regCarlsonLIntegral t hb (fun _ => hw)]
    exact regCarlsonDirichletAverage_const (carlsonLKernel t) w hb

/-- Equation (2.5) for every complex Dirichlet parameter after regularization. -/
private theorem regCarlsonL_smul_of_pos_of_mem_variableDomain (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonL t b (fun i => (a : ℂ) * z i) =
      (a : ℂ) ^ t *
        (regCarlsonL t b z + regCarlsonR t b z * log (a : ℂ)) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonL_parameters t (carlsonRVariableDomain_subset_slitDomain
        (carlsonRVariableDomain_smul_pos hz ha)))
    (analyticOnNhd_const.mul ((analyticOnNhd_regCarlsonL_parameters t
        (carlsonRVariableDomain_subset_slitDomain hz)).add
      ((analyticOnNhd_regCarlsonR_parameters t (carlsonRVariableDomain_subset_slitDomain hz)).mul
          analyticOnNhd_const))) ?_) b
  intro b hb
  simp only [Pi.add_apply, regCarlsonL_eq_regCarlsonLIntegral _ hb hz,
    regCarlsonL_eq_regCarlsonLIntegral _ hb (carlsonRVariableDomain_smul_pos hz ha),
    regCarlsonR_eq_regCarlsonRIntegral _ hb hz]
  exact regCarlsonLIntegral_smul_of_pos t hb hz ha

/-- Equal nodes may be combined by any surjective partition, on the full slit domain. -/
theorem regCarlsonL_aggregate {κ : Type*} [Fintype κ]
    {q : ι → κ} (hq : Function.Surjective q) (t : ℂ) (b : ι → ℂ)
    {z : κ → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t b (z ∘ q) = regCarlsonL t (stdSimplexAggregate q b) z := by
  have hleft : AnalyticOnNhd ℂ (fun w : κ → ℂ => regCarlsonL t b (w ∘ q))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const _ (fun i => hw (q i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (q i) : (κ → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft (analyticOnNhd_regCarlsonL t _)
      ?_ hz
  intro w hw
  change regCarlsonL t b (w ∘ q) = regCarlsonL t (stdSimplexAggregate q b) w
  dsimp only [Function.comp_def]
  exact regCarlsonL_aggregate_of_mem_variableDomain hq t hw b

/-- A zero parameter and its node may be deleted if at least one node remains. -/
theorem regCarlsonL_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0) {z : Option ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t b z = regCarlsonL t (b ∘ some) (z ∘ some) := by
  have hright : AnalyticOnNhd ℂ (fun w : Option ι → ℂ =>
      regCarlsonL t (b ∘ some) (w ∘ some)) carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const _ (fun i => hw (some i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonL t b)
      hright ?_ hz
  intro w hw
  change regCarlsonL t b w = regCarlsonL t (b ∘ some) (w ∘ some)
  dsimp only [Function.comp_def]
  exact regCarlsonL_option_zero_of_mem_variableDomain t hb hw

/-- Simultaneous permutation of nodes and parameters leaves L unchanged. -/
theorem regCarlsonL_perm (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (σ : Equiv.Perm ι) :
    regCarlsonL t (b ∘ σ) (z ∘ σ) = regCarlsonL t b z := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ => regCarlsonL t (b ∘ σ) (w ∘ σ))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const _ (fun i => hw (σ i))
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (σ i) : (ι → ℂ) →L[ℂ] ℂ).analyticAt w
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft (analyticOnNhd_regCarlsonL t b)
      ?_ hz
  intro w hw
  change regCarlsonL t (b ∘ σ) (w ∘ σ) = regCarlsonL t b w
  dsimp only [Function.comp_def]
  exact regCarlsonL_perm_of_mem_variableDomain t b hw σ

/-- Coincident slit-plane nodes give the elementary power-logarithm kernel. -/
theorem regCarlsonL_const (t w : ℂ) (hw : w ∈ slitPlane) (b : ι → ℂ) :
    regCarlsonL t b (fun _ => w) = (w ^ t * log w) / Gamma (∑ i, b i) := by
  have hleft : AnalyticOnNhd ℂ (fun v : ℂ => regCarlsonL t b (fun _ => v)) slitPlane := by
    intro v hv
    exact analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun _ => analyticAt_id) (fun _ => hv)
  have hright := (analyticOnNhd_carlsonLKernel t).div_const (c := Gamma (∑ i, b i))
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright
    ((starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected)
    (by simp : (1 : ℂ) ∈ slitPlane) ?_ hw
  filter_upwards [isOpen_carlsonRightHalfPlane.mem_nhds
    (by norm_num [carlsonRightHalfPlane] : (1 : ℂ) ∈ carlsonRightHalfPlane)] with v hv
  change regCarlsonL t b (fun _ => v) = (v ^ t * log v) / Gamma (∑ i, b i)
  exact regCarlsonL_const_of_mem_variableDomain t v hv b

/-- The regularized slit L-function vanishes at the all-one node vector. -/
@[simp] theorem regCarlsonL_one (t : ℂ) (b : ι → ℂ) :
    regCarlsonL t b (fun _ => 1) = 0 := by
  simpa using regCarlsonL_const t 1 (by simp) b

/-- The singleton convention, including the reciprocal Gamma regularization. -/
theorem regCarlsonL_unique [Unique ι] (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t b z = (z default ^ t * log (z default)) / Gamma (b default) := by
  have heq : z = fun _ => z default := funext fun i => congrArg z (Subsingleton.elim i default)
  simpa only [← heq, Fintype.sum_unique] using regCarlsonL_const t (z default) (hz default) b

omit [Fintype ι] in
/-- Positive real scaling preserves the principal-branch node domain. -/
theorem carlsonRSlitDomain_smul_pos {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    {a : ℝ} (ha : 0 < a) : (fun i => (a : ℂ) * z i) ∈ carlsonRSlitDomain := by
  intro i
  rcases mem_slitPlane_iff.mp (hz i) with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using mul_pos ha h))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using mul_ne_zero ha.ne' h))

/-- Equation (2.5) on slit-plane nodes: scaling contributes the logarithmic R-term. -/
theorem regCarlsonL_smul_of_pos (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonL t b (fun i => (a : ℂ) * z i) =
      (a : ℂ) ^ t * (regCarlsonL t b z + regCarlsonR t b z * log (a : ℂ)) := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ => regCarlsonL t b (fun i => (a : ℂ) * w i))
      carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const _
      (carlsonRSlitDomain_smul_pos hw ha)
    exact analyticAt_pi_iff.mpr fun i =>
      analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)
  have hright : AnalyticOnNhd ℂ (fun w : ι → ℂ =>
      (a : ℂ) ^ t * (regCarlsonL t b w + regCarlsonR t b w * log (a : ℂ)))
      carlsonRSlitDomain :=
    analyticOnNhd_const.mul ((analyticOnNhd_regCarlsonL t b).add
      ((analyticOnNhd_regCarlsonR t b).mul analyticOnNhd_const))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft hright ?_ hz
  intro w hw
  change regCarlsonL t b (fun i => (a : ℂ) * w i) =
    (a : ℂ) ^ t * (regCarlsonL t b w + regCarlsonR t b w * log (a : ℂ))
  exact regCarlsonL_smul_of_pos_of_mem_variableDomain t b hw ha

end Carlson
end
