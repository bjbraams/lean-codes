/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Complex
public import SeveralComplexVariables.Analyticity
public import SeveralComplexVariables.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Analytic dependence of convergent Dirichlet integrals

This module proves parameter analyticity on the domain of absolute convergence.
Continuation beyond that domain is developed separately in `Dirichlet.Transform`.

## Main results

* `Dirichlet.analyticOnNhd_prod_invGamma`: The product of reciprocal Gamma factors used to
  regularize a Dirichlet integral is entire in the parameter vector.
* `Dirichlet.hasFDerivAt_mvBetaMonomial`: The Dirichlet monomial `∏ i, (u i) ^ (b i - 1)` is
  entire in the parameter vector at every interior simplex point.
* `Dirichlet.norm_mvBetaMonomial_le_of_re_le`: Monotonicity of the Dirichlet monomial in the
  real parts of the exponents, at a point with coordinates in `(0, 1]`.
* `Dirichlet.regDirichletIntegral_analyticOn`: If `f` is continuous on the closed standard
  simplex, then `b ↦ regDirichletIntegral b f` is analytic on the domain of absolute
  convergence. The proof differentiates under the integral sign, dominating the derivative
  kernel near each parameter vector by the logarithmic majorant at the halved real parts.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex Fintype Filter MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The product of reciprocal Gamma factors used to regularize a Dirichlet integral is entire
in the parameter vector. -/
theorem analyticOnNhd_prod_invGamma :
    AnalyticOnNhd ℂ (fun b : ι → ℂ ↦ ∏ i, (Gamma (b i))⁻¹) Set.univ := by
  classical
  apply DifferentiableOn.analyticOnNhd_pi _ isOpen_univ
  intro b _
  apply DifferentiableAt.differentiableWithinAt
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hi := Complex.differentiable_one_div_Gamma.differentiableAt.comp b
        (ContinuousLinearMap.proj i).differentiableAt
      change DifferentiableAt ℂ (fun b : ι → ℂ ↦ (Gamma (b i))⁻¹) b at hi
      rw [show (fun b : ι → ℂ ↦ ∏ j ∈ insert i s, (Gamma (b j))⁻¹) =
          (fun b ↦ (Gamma (b i))⁻¹) * (fun b ↦ ∏ j ∈ s, (Gamma (b j))⁻¹) by
        funext x
        exact Finset.prod_insert his]
      exact hi.mul ih

/-- The Dirichlet monomial `∏ i, (u i) ^ (b i - 1)` is entire in the parameter vector at
every interior simplex point. -/
theorem hasFDerivAt_mvBetaMonomial {u : ι → ℝ} (hu : ∀ i, 0 < u i) (b : ι → ℂ) :
    HasFDerivAt (fun c : ι → ℂ ↦ ∏ i, (u i : ℂ) ^ (c i - 1))
      (∑ i, ((Complex.log (u i : ℂ) * ∏ j, (u j : ℂ) ^ (b j - 1)) •
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ))) b := by
  classical
  let p : ι → ((ι → ℂ) →L[ℂ] ℂ) :=
    fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
  let g : ι → (ι → ℂ) → ℂ := fun i c ↦ (u i : ℂ) ^ (c i - 1)
  let g' : ι → (ι → ℂ) →L[ℂ] ℂ := fun i ↦
    ((u i : ℂ) ^ (b i - 1) * Complex.log (u i : ℂ)) • p i
  have hg i : HasFDerivAt (g i) (g' i) b := by
    have hproj : HasFDerivAt (fun c : ι → ℂ ↦ c i) (p i) b := (p i).hasFDerivAt
    have hsub : HasFDerivAt (fun c : ι → ℂ ↦ c i - 1) (p i) b := hproj.sub_const 1
    have h0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hu i).ne'
    simpa [g, g', mul_comm] using hsub.const_cpow (Or.inl h0)
  have hprod :=
    HasFDerivAt.finsetProd (u := (Finset.univ : Finset ι)) (fun i _ ↦ hg i)
  refine hprod.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [g, g', p, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hprod_erase :
      (∏ j, (u j : ℂ) ^ (b j - 1)) =
        (u i : ℂ) ^ (b i - 1) *
          ∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j - 1) :=
    (Finset.mul_prod_erase Finset.univ (fun j ↦ (u j : ℂ) ^ (b j - 1))
      (Finset.mem_univ i)).symm
  rw [hprod_erase]
  ring

/-- Monotonicity of the Dirichlet monomial in the real parts of the exponents, at a point with
coordinates in `(0, 1]`. -/
theorem norm_mvBetaMonomial_le_of_re_le {u : ι → ℝ} (hu : ∀ i, 0 < u i) (hu1 : ∀ i, u i ≤ 1)
    {a c : ι → ℂ} (hac : ∀ i, (a i).re ≤ (c i).re) :
    ‖∏ i, (u i : ℂ) ^ (c i - 1)‖ ≤ ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ := by
  simp only [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_
  rw [norm_cpow_eq_rpow_re_of_pos (hu j), norm_cpow_eq_rpow_re_of_pos (hu j)]
  simp only [sub_re, one_re]
  exact Real.rpow_le_rpow_of_exponent_ge (hu j) (hu1 j) (sub_le_sub_right (hac j) 1)

/-- The parameter derivative of the Dirichlet monomial kernel multiplied by a fixed integrand
value: the operator `v ↦ ∑ i, log (u i) * (∏ j, u j ^ (c j - 1)) * f u * v i`. -/
private def mvBetaMonomialDeriv (f : (ι → ℝ) → ℂ) (c : ι → ℂ) (u : ι → ℝ) :
    (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, ((Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (c j - 1)) * f u) •
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ))

/-- Measurability of the monomial derivative kernel in the simplex variable. -/
private theorem aestronglyMeasurable_mvBetaMonomialDeriv {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) {c : ι → ℂ}
    (hc : c ∈ mvBetaConvergent) :
    AEStronglyMeasurable (mvBetaMonomialDeriv f c)
      (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
  change AEStronglyMeasurable (fun u ↦ ∑ i,
    ((Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (c j - 1)) * f u) •
      (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ))) _
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  have hmono := (integrableOn_mvBetaMonomial_mul_log c hc i).aestronglyMeasurable
  have hfmeas := hf.aestronglyMeasurable (μ := stdSimplexMeasure)
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hscal : AEStronglyMeasurable
      (fun u ↦ Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (c j - 1)) * f u)
      (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) :=
    (hmono.mul hfmeas).congr <| Eventually.of_forall fun u ↦ by simp [mul_comm]
  exact hscal.smul_const _

/-- The coordinate projections have operator norm at most one. -/
private theorem norm_proj_le (i : ι) : ‖(ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [ContinuousLinearMap.proj_apply, one_mul]
    exact norm_le_pi_norm v i

/-- Domination of the monomial derivative kernel at a positive simplex point, uniformly over
parameters whose real parts dominate those of `a`. -/
private theorem norm_mvBetaMonomialDeriv_le {f : (ι → ℝ) → ℂ} {C : ℝ} {u : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hu1 : ∀ i, u i ≤ 1) (hfu : ‖f u‖ ≤ C)
    {a c : ι → ℂ} (hac : ∀ i, (a i).re ≤ (c i).re) :
    ‖mvBetaMonomialDeriv f c u‖ ≤
      C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖ := by
  have hmon := norm_mvBetaMonomial_le_of_re_le hu hu1 hac
  have hsum : ‖mvBetaMonomialDeriv f c u‖ ≤
      ∑ i, ‖Complex.log (u i : ℂ)‖ * ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ := by
    unfold mvBetaMonomialDeriv
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [norm_smul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (norm_proj_le i) (by positivity) |>.trans_eq ?_
    ring
  refine hsum.trans ?_
  calc
    ∑ i, ‖Complex.log (u i : ℂ)‖ * ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ ≤
      ∑ i, ‖Complex.log (u i : ℂ)‖ * ‖∏ j, (u j : ℂ) ^ (a j - 1)‖ * C := by
      gcongr
    _ = C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖ := by
      simp [mul_comm, Finset.mul_sum]

/-- The parameter derivative of the Dirichlet monomial kernel times a fixed integrand value. -/
private theorem hasFDerivAt_mvBetaMonomial_mul (f : (ι → ℝ) → ℂ) {u : ι → ℝ}
    (hu : ∀ i, 0 < u i) (c : ι → ℂ) :
    HasFDerivAt (fun c : ι → ℂ ↦ (∏ i, (u i : ℂ) ^ (c i - 1)) * f u)
      (mvBetaMonomialDeriv f c u) c := by
  have hmon := hasFDerivAt_mvBetaMonomial hu c
  have hfconst : HasFDerivAt (fun _ : ι → ℂ ↦ f u) (0 : (ι → ℂ) →L[ℂ] ℂ) c :=
    hasFDerivAt_const (f u) c
  refine (hmon.mul hfconst).congr_fderiv ?_
  have hz : ((∏ i, (u i : ℂ) ^ (c i - 1)) • (0 : (ι → ℂ) →L[ℂ] ℂ)) = 0 := by
    ext v; simp
  rw [hz, zero_add]
  unfold mvBetaMonomialDeriv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul]
  simp [mul_comm]

/-- If `f` is continuous on the closed standard simplex, then
`b ↦ regDirichletIntegral b f` is analytic on the domain of absolute convergence. The proof
differentiates under the integral sign, dominating the derivative kernel near each parameter
vector by the logarithmic majorant at the halved real parts. -/
theorem regDirichletIntegral_analyticOn {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    AnalyticOn ℂ (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      have hconst : (fun b : ι → ℂ ↦ regDirichletIntegral b f) = fun _ ↦ 0 := by
        funext b
        simp [regDirichletIntegral, stdSimplexMeasure_empty]
      rw [hconst]
      exact analyticOn_const
  | inr hι =>
    let _ := hι
    let μ := stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
    have hG : AnalyticOnNhd ℂ (fun b ↦ ∫ u, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u ∂μ)
        mvBetaConvergent := by
      refine analyticOnNhd_integral_of_dominated_of_fderiv_le
        (μ := μ) (U := mvBetaConvergent) (F := fun b u ↦
          (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
        Complex.isOpen_mvBetaConvergent ?_
      intro b hb
      let a : ι → ℂ := fun i ↦ ((b i).re / 2 : ℝ)
      have ha : a ∈ mvBetaConvergent := fun i ↦ by simpa [a] using half_pos (hb i)
      let s : Set (ι → ℂ) := {c | ∀ i, (a i).re < (c i).re}
      have hsopen : IsOpen s := by
        rw [show s = ⋂ i, {c : ι → ℂ | (a i).re < (c i).re} by ext c; simp [s]]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply i))
      have hs_nhds : s ∈ 𝓝 b :=
        hsopen.mem_nhds fun i ↦ by simpa [a] using half_lt_self (hb i)
      obtain ⟨Cf, hCf⟩ := bddAbove_def.mp
        ((Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).bddAbove_image hf.norm)
      have hf_le : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ‖f u‖ ≤ max Cf 0 :=
        fun u hu ↦ (hCf _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
      have hsimplex := self_mem_ae_restrict (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      refine ⟨s, fun u ↦ max Cf 0 * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖,
        mvBetaMonomialDeriv f, hs_nhds, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · filter_upwards [hs_nhds] with c hc
        have hc' : c ∈ mvBetaConvergent := fun i ↦ (ha i).trans (hc i)
        exact ((integrableOn_mvBetaMonomial c hc').mul_continuousOn hf
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)).1
      · change IntegrableOn (fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
            (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure
        exact (integrableOn_mvBetaMonomial b hb).mul_continuousOn hf
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
      · exact aestronglyMeasurable_mvBetaMonomialDeriv hf hb
      · filter_upwards [hsimplex, ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c hc
        exact norm_mvBetaMonomialDeriv_le hupos
          (fun i ↦ hu.2.symm ▸ Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i))
          (hf_le u hu) fun i ↦ (hc i).le
      · have hterm i := (integrableOn_mvBetaMonomial_mul_log a ha i).norm
        have hsum := integrable_finsetSum (s := Finset.univ) fun i _ ↦ hterm i
        simpa using hsum.const_mul (max Cf 0)
      · filter_upwards [hsimplex, ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c _
        exact hasFDerivAt_mvBetaMonomial_mul f hupos c
    have hEq : (fun b ↦ regDirichletIntegral b f) =
        fun b ↦ (∏ i, (Gamma (b i))⁻¹) * ∫ u, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u ∂μ := by
      funext b
      exact regDirichletIntegral_eq_prod_invGamma_mul b f
    rw [hEq]
    exact ((analyticOnNhd_prod_invGamma.mono (Set.subset_univ _)).mul hG).analyticOn

end Dirichlet

end
