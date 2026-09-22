/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import Dirichlet.Transform.Parametric

/-!
# The Dirichlet transform with auxiliary holomorphic parameters

A joint continuation specification and its uniqueness and recognition theorems. The
auxiliary coordinate type is independent of the simplex coordinate type, and may encode
nodes, exponents, or any finite collection of additional parameters.
-/

open Complex MeasureTheory ProbabilityTheory Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A parametric continuation is jointly holomorphic and is a regularized Dirichlet
continuation on every auxiliary-parameter slice. Kernels are restricted to the real simplex. -/
def IsJointRegDirichletContinuation (U : Set (κ → ℂ))
    (H : ((κ → ℂ) × (ι → ℂ)) → ℂ) (F : ((ι → ℂ) × (κ → ℂ)) → ℂ) : Prop :=
  AnalyticOnNhd ℂ F (univ ×ˢ U) ∧
    ∀ z ∈ U, IsRegDirichletContinuation (fun u => H (z, fun i => (u i : ℂ))) (fun b => F (b, z))

/-- The jointly holomorphic continuation of a kernel exists on every admissible open domain. -/
theorem exists_isJointRegDirichletContinuation
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) :
    ∃ F, IsJointRegDirichletContinuation U H F := by
  obtain ⟨F, hF, heq⟩ := exists_entire_joint_regDirichletContinuation_kernel hU hWo hH hW
  refine ⟨F, hF, fun z hz => ⟨?_, heq z hz⟩⟩
  intro b _
  exact (hF (b, z) ⟨mem_univ _, hz⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

/-- Joint continuations are unique on their auxiliary domain, even when it is disconnected. -/
theorem IsJointRegDirichletContinuation.eqOn
    {U : Set (κ → ℂ)} {H : ((κ → ℂ) × (ι → ℂ)) → ℂ}
    {F G : ((ι → ℂ) × (κ → ℂ)) → ℂ}
    (hF : IsJointRegDirichletContinuation U H F) (hG : IsJointRegDirichletContinuation U H G) :
    EqOn F G (univ ×ˢ U) := by
  intro p hp
  exact congrFun ((hF.2 p.2 hp.2).eq (hG.2 p.2 hp.2)) p.1

/-- Any already selected family of entire transforms inherits joint holomorphy.
This lets applications retain their definitions while using the general kernel theorem. -/
theorem analyticOnNhd_joint_of_isRegDirichletContinuation
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {F : ((ι → ℂ) × (κ → ℂ)) → ℂ}
    (hF : ∀ z ∈ U, IsRegDirichletContinuation
      (fun u => H (z, fun i => (u i : ℂ))) (fun b => F (b, z))) :
    AnalyticOnNhd ℂ F (univ ×ˢ U) := by
  obtain ⟨G, hG⟩ := exists_isJointRegDirichletContinuation hU hWo hH hW
  exact hG.1.congr (isOpen_univ.prod hU)
    (fun p hp => congrFun ((hG.2 p.2 hp.2).eq (hF p.2 hp.2)) p.1)

/-- Every auxiliary slice agrees with the canonical smooth-kernel transform. -/
theorem IsJointRegDirichletContinuation.eq_transform
    {U : Set (κ → ℂ)} {H : ((κ → ℂ) × (ι → ℂ)) → ℂ}
    {F : ((ι → ℂ) × (κ → ℂ)) → ℂ} (hF : IsJointRegDirichletContinuation U H F)
    {z : κ → ℂ} (hz : z ∈ U)
    (hg : SmoothNearStdSimplex (fun u => H (z, fun i => (u i : ℂ)))) (b : ι → ℂ) :
    F (b, z) = regDirichletTransform (fun u => H (z, fun i => (u i : ℂ))) hg b :=
  congrFun ((hF.2 z hz).eq_transform hg) b

/-- Differentiate a complex simplex kernel in an auxiliary direction, holding the weights fixed. -/
def complexKernelParamDeriv (v : κ → ℂ) (H : ((κ → ℂ) × (ι → ℂ)) → ℂ)
    (p : (κ → ℂ) × (ι → ℂ)) : ℂ := fderiv ℂ H p (v, 0)

/-- Auxiliary differentiation preserves joint holomorphy of the kernel. -/
theorem analyticOnNhd_complexKernelParamDeriv
    {W : Set ((κ → ℂ) × (ι → ℂ))} {H : ((κ → ℂ) × (ι → ℂ)) → ℂ}
    (hH : AnalyticOnNhd ℂ H W) (v : κ → ℂ) :
    AnalyticOnNhd ℂ (complexKernelParamDeriv v H) W :=
  (ContinuousLinearMap.apply ℂ ℂ (v, (0 : ι → ℂ))).comp_analyticOnNhd hH.fderiv

/-- The auxiliary directional derivative of a native transform is the transform of the
corresponding kernel derivative. -/
theorem fderiv_regDirichletIntegral_kernel_apply
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {z : κ → ℂ} (hz : z ∈ U) (v : κ → ℂ) :
    fderiv ℂ (fun y => regDirichletIntegral b (fun u => H (y, fun i => (u i : ℂ)))) z v =
      regDirichletIntegral b (fun u => complexKernelParamDeriv v H (z, fun i => (u i : ℂ))) := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := (Measure.stdSimplexMeasure (ι := ι)).restrict K
  let D := fun u : ι → ℝ => (fderiv ℂ H (z, fun i => (u i : ℂ))).comp
    (ContinuousLinearMap.inl ℂ (κ → ℂ) (ι → ℂ))
  have hD : ContinuousOn D K :=
    (hH.fderiv.continuousOn.comp (by
        fun_prop) (fun u hu => hW z hz u hu)).clm_comp continuousOn_const
  have hK := Convexity.StdSimplex.isCompact_coordinateSet ℝ ι
  obtain ⟨M, hM⟩ := hK.bddAbove_image hD.norm
  have hd : Integrable (regDirichletDensity b) μ :=
    integrableOn_regDirichletDensity b hb
  have hi : Integrable (fun u => regDirichletDensity b u • D u) μ := by
    apply hd.smul_bdd M (hD.aestronglyMeasurable hK.measurableSet)
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact hM ⟨u, hu, rfl⟩
  rw [(hasFDerivAt_regDirichletIntegral_kernel hU hH hW hb z hz).fderiv]
  change (∫ u, regDirichletDensity b u • D u ∂μ) v = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

/-- Auxiliary differentiation commutes with the entire continued transform, including
zero and negative Dirichlet parameters. No continuation of the derivative is assumed. -/
theorem IsJointRegDirichletContinuation.paramDeriv
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {F : ((ι → ℂ) × (κ → ℂ)) → ℂ} (hF : IsJointRegDirichletContinuation U H F)
    {z : κ → ℂ} (hz : z ∈ U) (v : κ → ℂ) :
    IsRegDirichletContinuation (fun u => complexKernelParamDeriv v H (z, fun i => (u i : ℂ)))
      (fun b => fderiv ℂ F (b, z) (0, v)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro b _
    exact (((ContinuousLinearMap.apply ℂ ℂ ((0 : ι → ℂ), v)).comp_analyticOnNhd hF.1.fderiv)
      (b, z) ⟨mem_univ _, hz⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  · dsimp only
    have hs := ((hF.1 (b, z) ⟨mem_univ _, hz⟩).differentiableAt.hasFDerivAt).comp z
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) b z)
    have he : (fun y => F (b, y)) =ᶠ[nhds z]
        (fun y => regDirichletIntegral b (fun u => H (y, fun i => (u i : ℂ)))) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact (hF.2 y hy).eq_native hb
    have hslice := congrArg (fun L : (κ → ℂ) →L[ℂ] ℂ => L v) hs.fderiv
    change fderiv ℂ (fun y => F (b, y)) z v = fderiv ℂ F (b, z) (0, v) at hslice
    rw [← hslice, he.fderiv_eq]
    exact fderiv_regDirichletIntegral_kernel_apply hU hH hW hb hz v

/-- Differentiating a joint continuation yields the joint continuation of the kernel derivative.
This statement can be iterated for arbitrary mixed auxiliary derivatives. -/
theorem IsJointRegDirichletContinuation.paramDeriv_joint
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {F : ((ι → ℂ) × (κ → ℂ)) → ℂ} (hF : IsJointRegDirichletContinuation U H F)
    (v : κ → ℂ) :
    IsJointRegDirichletContinuation U (complexKernelParamDeriv v H)
      (fun p => fderiv ℂ F p (0, v)) :=
  ⟨(ContinuousLinearMap.apply ℂ ℂ ((0 : ι → ℂ), v)).comp_analyticOnNhd hF.1.fderiv,
    fun _ hz => hF.paramDeriv hU hH hW hz v⟩

end Dirichlet
end
