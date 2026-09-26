/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Complex.Analytic
public import ToMathlib.Analysis.Integral.Parametric
public import SeveralComplexVariables.SeparateAnalytic

/-!
# Holomorphic kernels in Dirichlet integrals

A kernel may depend holomorphically on extra parameters and on a complex neighborhood
of the real simplex. This interface is preserved by the tangential derivatives used in
Dirichlet-parameter continuation.

## Main results

* `Dirichlet.continuousOn_complexSimplexKernel`: Joint continuity after restricting the second
  complex variable to real simplex coordinates.
* `Dirichlet.hasFDerivAt_regDirichletIntegral_kernel`: Differentiation in auxiliary parameters
  passes through a convergent Dirichlet integral.
* `Dirichlet.analyticOnNhd_regDirichletIntegral_kernel`: A native Dirichlet integral preserves
  holomorphic dependence on auxiliary parameters.
* `Dirichlet.locallyBounded_regDirichletIntegral_kernel`: Compactness of the kernel and a common
  Dirichlet majorant give local boundedness simultaneously in Dirichlet and auxiliary
  parameters.
* `Dirichlet.analyticOnNhd_regDirichletIntegral_kernel_joint`: Joint holomorphy in the native
  Dirichlet parameters and all auxiliary variables.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set Metric
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- Joint continuity after restricting the second complex variable to real simplex coordinates. -/
theorem continuousOn_complexSimplexKernel
    {U : Set (κ → ℂ)} {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : ContinuousOn H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) :
    ContinuousOn (fun p : (κ → ℂ) × (ι → ℝ) => H (p.1, fun i => (p.2 i : ℂ)))
      (U ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
  hH.comp (by fun_prop) (fun p hp => hW p.1 hp.1 p.2 hp.2)

/-- Differentiation in auxiliary parameters passes through a convergent Dirichlet integral. -/
theorem hasFDerivAt_regDirichletIntegral_kernel
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : κ → ℂ) (hz : z ∈ U) :
    HasFDerivAt (fun y => regDirichletIntegral b (fun u => H (y, fun i => (u i : ℂ))))
      (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        regDirichletDensity b u • ((fderiv ℂ H (z, fun i => (u i : ℂ))).comp
          (ContinuousLinearMap.inl ℂ (κ → ℂ) (ι → ℂ))) ∂stdSimplexMeasure) z := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let D := fun (z : κ → ℂ) (u : ι → ℝ) => (fderiv ℂ H (z, fun i => (u i : ℂ))).comp
    (ContinuousLinearMap.inl ℂ (κ → ℂ) (ι → ℂ))
  have hK : IsCompact K := Convexity.StdSimplex.isCompact_coordinateSet ℝ ι
  have hc := continuousOn_complexSimplexKernel hH.continuousOn hW
  have hD : ContinuousOn (fun p : (κ → ℂ) × (ι → ℝ) => D p.1 p.2) (U ×ˢ K) := by
    exact (hH.fderiv.continuousOn.comp (by fun_prop)
      (fun p hp => hW p.1 hp.1 p.2 hp.2)).clm_comp continuousOn_const
  simpa only [regDirichletIntegral, smul_eq_mul, K, D, Function.comp_def] using!
    hasFDerivAt_integral_smul_of_continuousOn_compact hK
      (integrableOn_regDirichletDensity b hb) hU hz hc hD
      (fun y hy u hu => ((hH _ (hW y hy u hu)).differentiableAt.hasFDerivAt).comp y
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) y (fun i => (u i : ℂ))))

/-- A native Dirichlet integral preserves holomorphic dependence on auxiliary parameters. -/
theorem analyticOnNhd_regDirichletIntegral_kernel
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (fun z => regDirichletIntegral b (fun u => H (z, fun i => (u i : ℂ)))) U := by
  apply DifferentiableOn.analyticOnNhd_pi _ hU
  intro z hz
  exact (hasFDerivAt_regDirichletIntegral_kernel hU hH hW hb z
      hz).differentiableAt.differentiableWithinAt

/-- Compactness of the kernel and a common Dirichlet majorant give local boundedness
simultaneously in Dirichlet and auxiliary parameters. -/
theorem locallyBounded_regDirichletIntegral_kernel
    {U : Set (κ → ℂ)} (hU : IsOpen U)
    {F : (κ → ℂ) → (ι → ℝ) → ℂ}
    (hF : ContinuousOn (fun p : (κ → ℂ) × (ι → ℝ) => F p.1 p.2)
      (U ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι))
    {p : (ι → ℂ) × (κ → ℂ)} (hb : p.1 ∈ mvBetaConvergent) (hz : p.2 ∈ U) :
    ∃ M : ℝ, ∀ᶠ q in nhds p, ‖regDirichletIntegral q.1 (F q.2)‖ ≤ M := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, Filter.Eventually.of_forall (fun q => by
      simp [regDirichletIntegral, stdSimplexMeasure_empty])⟩
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict K
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p.2 r).prod
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)).bddAbove_image
      (hF.mono (Set.prod_mono hball Subset.rfl)).norm
  let a : ι → ℂ := fun i => ((p.1 i).re / 2 : ℝ)
  have ha : a ∈ mvBetaConvergent := fun i => by simpa [a] using half_pos (hb i)
  have hevent : ∀ᶠ q : (ι → ℂ) × (κ → ℂ) in nhds p,
      (∀ i, (a i).re < (q.1 i).re) ∧ q.2 ∈ closedBall p.2 r := by
    apply Filter.Eventually.and
    · apply Filter.eventually_all.mpr
      intro i
      apply (isOpen_lt continuous_const
        (Complex.continuous_re.comp ((continuous_apply i).comp continuous_fst))).eventually_mem
      simpa [a] using half_lt_self (hb i)
    · exact continuous_snd.continuousAt.tendsto.eventually (closedBall_mem_nhds p.2 hr)
  let D : ℝ := ∫ u, ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ * max C 0 ∂μ
  have hD : ∀ᶠ q in nhds p,
      ‖∫ u, (∏ i, (u i : ℂ) ^ (q.1 i - 1)) * F q.2 u ∂μ‖ ≤ D := by
    filter_upwards [hevent] with q hq
    apply norm_integral_le_of_norm_le ((integrableOn_mvBetaMonomial a ha).norm.mul_const _)
    filter_upwards [self_mem_ae_restrict (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet,
      ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
    have hm : ‖∏ i, (u i : ℂ) ^ (q.1 i - 1)‖ ≤ ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ := by
      simp only [norm_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      rw [norm_cpow_eq_rpow_re_of_pos (hupos i), norm_cpow_eq_rpow_re_of_pos (hupos i)]
      apply Real.rpow_le_rpow_of_exponent_ge (hupos i)
        ((Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans_eq hu.2)
      simpa only [sub_re, one_re] using sub_le_sub_right (hq.1 i).le 1
    exact (norm_mul _ _).trans_le (mul_le_mul hm
      ((hC (mem_image_of_mem _ (show (q.2, u) ∈ closedBall p.2 r ×ˢ K from
        ⟨hq.2, hu⟩))).trans (le_max_left _ _))
      (norm_nonneg _) (norm_nonneg _))
  let B : ℝ := ‖∏ i, (Gamma (p.1 i))⁻¹‖ + 1
  have hB := ((analyticOnNhd_prod_invGamma p.1 (Set.mem_univ _)).continuousAt.comp
    (continuous_fst.continuousAt (x := p))).norm.eventually_lt_const
      (lt_add_one ‖∏ i, (Gamma (p.1 i))⁻¹‖)
  refine ⟨B * max D 0, ?_⟩
  filter_upwards [hB, hD] with q hq hqD
  rw [regDirichletIntegral_eq_prod_invGamma_mul, norm_mul]
  exact mul_le_mul hq.le (hqD.trans (le_max_left _ _)) (norm_nonneg _)
    (by dsimp [B]; positivity)

/-- Joint holomorphy in the native Dirichlet parameters and all auxiliary variables. -/
theorem analyticOnNhd_regDirichletIntegral_kernel_joint
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) :
    AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (κ → ℂ) =>
      regDirichletIntegral p.1 (fun u => H (p.2, fun i => (u i : ℂ))))
      (mvBetaConvergent ×ˢ U) := by
  classical
  let L := ContinuousLinearEquiv.sumPiEquivProdPi ℂ ι κ (fun _ => ℂ)
  have hLapply (q : (ι ⊕ κ) → ℂ) : L q = ((fun i => q (.inl i)), (fun i => q (.inr i))) := rfl
  let V := L ⁻¹' (mvBetaConvergent ×ˢ U)
  let G := fun q : (ι ⊕ κ) → ℂ => regDirichletIntegral (L q).1
    (fun u => H ((L q).2, fun i => (u i : ℂ)))
  have hV : IsOpen V := (isOpen_mvBetaConvergent.prod hU).preimage L.continuous
  have hc := continuousOn_complexSimplexKernel hH.continuousOn hW
  have hG : AnalyticOnNhd ℂ G V := by
    apply SeveralComplexVariables.analyticOnNhd_of_separately_analytic hV
    intro q hq k
    have hupdateB (v : ι → ℂ) (i : ι) (w : ℂ) :
        Function.update v i w = fun j => if j = i then w else v j := by
      funext j
      simp only [Function.update_apply]
    have hupdateZ (v : κ → ℂ) (i : κ) (w : ℂ) :
        Function.update v i w = fun j => if j = i then w else v j := by
      funext j
      simp only [Function.update_apply]
    cases k with
    | inl i =>
      have hcont : ContinuousOn (fun u => H ((L q).2, fun i => (u i : ℂ)))
          (Convexity.StdSimplex.coordinateSet ℝ ι) :=
        hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hq.2, hu⟩)
      have h := (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
        (regDirichletIntegral_analyticOn hcont)).analyticAt_update hq.1 i
      change AnalyticAt ℂ (fun w => regDirichletIntegral
        (Function.update (fun j => q (.inl j)) i w)
        (fun u => H ((fun j => q (.inr j)), fun j => (u j : ℂ)))) (q (.inl i)) at h
      dsimp only [G]
      simp only [hLapply]
      simpa only [hupdateB, Function.update_apply, Sum.inl.injEq,
        reduceCtorEq, ite_false] using! h
    | inr i =>
      have h := (analyticOnNhd_regDirichletIntegral_kernel hU hH hW hq.1).analyticAt_update hq.2 i
      change AnalyticAt ℂ (fun w => regDirichletIntegral (fun j => q (.inl j))
        (fun u => H (Function.update (fun j => q (.inr j)) i w,
          fun j => (u j : ℂ)))) (q (.inr i)) at h
      dsimp only [G]
      simp only [hLapply]
      simpa only [hupdateZ, Function.update_apply, Sum.inr.injEq,
        reduceCtorEq, ite_false] using! h
  intro p hp
  have hmem : L.symm p ∈ V := by simpa [V] using hp
  have h := (hG _ hmem).comp_of_eq (L.symm.analyticAt p) rfl
  simpa [G] using! h

end Dirichlet
end
