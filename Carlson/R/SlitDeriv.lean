/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import Carlson.R.SlitRelations
public import Carlson.R.Deriv
public import SeveralComplexVariables.Derivatives

/-!
# Differentiation of R on the full slit domain

Carlson's node derivative and the translation and Euler differential identities
hold for every complex exponent and Dirichlet parameter vector, and throughout
the product slit plane. Joint holomorphy of a node derivative permits continuation
first in the parameters, then in the nodes. No L-function theory is used.
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- A coordinate derivative of R is jointly holomorphic in all its arguments. -/
theorem analyticOnNhd_carlsonPartialDeriv_regCarlsonR_joint (i : ι) :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      carlsonPartialDeriv i (regCarlsonR (p none) (fun j => p (some (.inl j))))
        (fun j => p (some (.inr j))))
      {p | (fun j => p (some (.inr j))) ∈ carlsonRSlitDomain} := by
  classical
  have h := analyticOnNhd_regCarlsonR_joint (ι := ι) |>.partialDeriv
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop)) (some (Sum.inr i))
  have heq : SeveralComplexVariables.partialDeriv (some (Sum.inr i))
      (fun p : Option (ι ⊕ ι) → ℂ => regCarlsonR (p none)
        (fun j => p (some (.inl j))) (fun j => p (some (.inr j)))) =
      (fun p => carlsonPartialDeriv i (regCarlsonR (p none)
        (fun j => p (some (.inl j)))) (fun j => p (some (.inr j)))) := by
    funext p
    unfold SeveralComplexVariables.partialDeriv carlsonPartialDeriv
    congr 1
    funext w
    simp [Function.update_apply]
    congr 1
    funext j
    simp [Function.update_apply]
  rwa [heq] at h

/-- Composition rule for a node derivative of the regularized slit R-function along analytic
exponent, parameter, and node maps. -/
theorem analyticAt_carlsonPartialDeriv_regCarlsonR_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (i : ι) :
    AnalyticAt ℂ (fun q => carlsonPartialDeriv i (regCarlsonR (t q) (b q)) (z q)) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k => k.elim (t q) (Sum.elim (b q) (z q))
  suffices hf : AnalyticAt ℂ f p from
    (analyticOnNhd_carlsonPartialDeriv_regCarlsonR_joint i (f p) hslit).comp_of_eq hf rfl
  apply analyticAt_pi_iff.mpr
  intro k
  cases k with
  | none => exact ht
  | some k =>
    cases k with
    | inl j => exact (analyticAt_pi_iff.mp hb) j
    | inr j => exact (analyticAt_pi_iff.mp hz) j

private theorem partialDeriv_regCarlsonR_of_right (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonR t b) z =
      t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) z := by
  classical
  have hz' := carlsonRVariableDomain_subset_slitDomain hz
  have hleft : AnalyticOnNhd ℂ (fun b => carlsonPartialDeriv i (regCarlsonR t b) z) univ :=
    fun _ _ => analyticAt_carlsonPartialDeriv_regCarlsonR_comp
      analyticAt_const analyticAt_id analyticAt_const hz' i
  have hright : AnalyticOnNhd ℂ (fun b : ι → ℂ =>
      t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) z) univ := by
    intro b _
    have hshift : AnalyticAt ℂ (fun b : ι → ℂ => addDirichletUnit b i) b := by
      apply analyticAt_pi_iff.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [addDirichletUnit, Function.update_self] using!
          ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).add analyticAt_const
      · simpa only [addDirichletUnit, Function.update_of_ne hji] using!
          (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    exact (analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)).mul
      (analyticAt_regCarlsonR_comp analyticAt_const hshift analyticAt_const hz')
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hleft hright ?_) b
  intro b hb
  have hevent : regCarlsonR t b =ᶠ[nhds z] regCarlsonRIntegral t b := by
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hz] with w hw
    exact regCarlsonR_eq_regCarlsonRIntegral t hb hw
  have hD := SeveralComplexVariables.partialDeriv_congr hevent i
  change carlsonPartialDeriv i (regCarlsonR t b) z =
    carlsonPartialDeriv i (regCarlsonRIntegral t b) z at hD
  change carlsonPartialDeriv i (regCarlsonR t b) z =
    t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) z
  rw [hD, carlsonPartialDeriv_regCarlsonRIntegral t hb hz,
    regCarlsonR_eq_regCarlsonRIntegral _ (addDirichletUnit_mem_mvBetaConvergent hb i) hz]

/-- Relation 5.9-6(9), continued to all complex parameters and slit-plane nodes. -/
theorem carlsonPartialDeriv_regCarlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonR t b) z =
      t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) z := by
  classical
  have hleft : AnalyticOnNhd ℂ (carlsonPartialDeriv i (regCarlsonR t b)) carlsonRSlitDomain :=
    (analyticOnNhd_regCarlsonR t b).partialDeriv isOpen_carlsonRSlitDomain i
  have hright : AnalyticOnNhd ℂ (fun w =>
      t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) w) carlsonRSlitDomain :=
    analyticOnNhd_const.mul (analyticOnNhd_regCarlsonR (t - 1) _)
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft hright
    (fun _ hw => partialDeriv_regCarlsonR_of_right t b hw i) hz

open scoped Classical in
/-- The first derivative as a one-variable slice, without a convergence hypothesis. -/
theorem hasDerivAt_regCarlsonR_update (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    HasDerivAt (fun w => regCarlsonR t b (Function.update z i w))
      (t * b i * regCarlsonR (t - 1) (addDirichletUnit b i) z) (z i) := by
  have h := ((analyticOnNhd_regCarlsonR t b).analyticAt_update hz i).differentiableAt.hasDerivAt
  change HasDerivAt _ (carlsonPartialDeriv i (regCarlsonR t b) z) (z i) at h
  rwa [carlsonPartialDeriv_regCarlsonR t b hz i] at h

/-- Two successive node derivatives on the full slit domain. The shifted coefficient
also handles repeated indices, when it is `b i + 1` rather than `b i`. -/
theorem carlsonPartialDeriv_carlsonPartialDeriv_regCarlsonR
    (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonPartialDeriv i (carlsonPartialDeriv j (regCarlsonR t b)) z =
      t * b j * ((t - 1) * addDirichletUnit b j i *
        regCarlsonR (t - 2) (addDirichletUnit (addDirichletUnit b j) i) z) := by
  classical
  have heq : carlsonPartialDeriv j (regCarlsonR t b) =ᶠ[nhds z]
      (fun w => t * b j * regCarlsonR (t - 1) (addDirichletUnit b j) w) := by
    filter_upwards [isOpen_carlsonRSlitDomain.mem_nhds hz] with w hw
    exact carlsonPartialDeriv_regCarlsonR t b hw j
  rw [carlsonPartialDeriv_eq_partialDeriv,
    SeveralComplexVariables.partialDeriv_congr heq i]
  have h := (hasDerivAt_regCarlsonR_update (t - 1) (addDirichletUnit b j)
      hz i).const_mul (t * b j)
  simpa only [SeveralComplexVariables.partialDeriv, show t - 1 - 1 = t - 2 by ring] using! h.deriv

/-- The translation differential identity of Theorem 5.9-2 on the full domain. -/
theorem sum_carlsonPartialDeriv_regCarlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ i, carlsonPartialDeriv i (regCarlsonR t b) z = t * regCarlsonR (t - 1) b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonR t b hz, mul_assoc]
  rw [← Finset.mul_sum, ← regCarlsonR_eq_sum_addDirichletUnit (t - 1) b hz]

/-- Euler's differential identity of Theorem 5.9-2, including the empty index type. -/
theorem sum_mul_carlsonPartialDeriv_regCarlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ i, z i * carlsonPartialDeriv i (regCarlsonR t b) z = t * regCarlsonR t b z := by
  have hR := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz
  simp only [sub_add_cancel] at hR
  simp_rw [carlsonPartialDeriv_regCarlsonR t b hz]
  rw [hR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scalar translation is differentiable wherever the translated nodes avoid the cut. -/
theorem hasDerivAt_regCarlsonR_translate (t : ℂ) (b z : ι → ℂ) {x : ℂ}
    (hx : (fun i => x + z i) ∈ carlsonRSlitDomain) :
    HasDerivAt (fun y => regCarlsonR t b (fun i => y + z i))
      (t * regCarlsonR (t - 1) b (fun i => x + z i)) x := by
  classical
  have hd := (analyticOnNhd_regCarlsonR t b _ hx).differentiableAt
  have hvec : HasDerivAt (fun y : ℂ => fun i => y + z i) (fun _ => 1) x :=
    hasDerivAt_pi.mpr fun i => (hasDerivAt_id x).add_const (z i)
  have h := hd.hasFDerivAt.comp_hasDerivAt x hvec
  apply h.congr_deriv
  rw [SeveralComplexVariables.fderiv_eq_sum_partialDeriv hd]
  simpa only [one_smul, ← carlsonPartialDeriv_eq_partialDeriv] using
    sum_carlsonPartialDeriv_regCarlsonR t b hx

/-- Relation 5.9-6(10) on the full parameter and slit-node domain. -/
theorem mul_carlsonPartialDeriv_add_mul_regCarlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    z i * carlsonPartialDeriv i (regCarlsonR t b) z + b i * regCarlsonR t b z =
      b i * ((∑ j, b j) + t) * regCarlsonR t (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv_regCarlsonR t b hz]
  linear_combination b i * regCarlsonR_eq_addDirichletUnit t b hz i

end Carlson
