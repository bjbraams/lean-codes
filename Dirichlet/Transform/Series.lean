/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import SeveralComplexVariables.LocallyUniform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Series of simplex kernels

Uniform summable domination on the simplex permits termwise transformation on the
native convergence region. No uniform-continuity claim outside that region is made.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- A uniformly summably dominated series of simplex kernels may be integrated termwise. -/
theorem hasSum_regDirichletIntegral
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (g : ℕ → (ι → ℝ) → ℂ) (f : (ι → ℝ) → ℂ) (M : ℕ → ℝ)
    (hg : ∀ n, ContinuousOn (fun u : ι → ℝ ↦ g n u)
      (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hM : Summable M)
    (hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → ‖g n u‖ ≤ M n)
    (hsum : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
      HasSum (fun n ↦ g n u) (f u)) :
    HasSum (fun n ↦ regDirichletIntegral b (g n))
      (regDirichletIntegral b f) := by
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι)
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * g n u
  let G : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * f u
  let B : ℕ → (ι → ℝ) → ℝ := fun n u ↦ M n * ‖regDirichletDensity b u‖
  have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ :=
    integrableOn_regDirichletDensity b hb
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (integrableOn_regDirichletDensity_mul b hb (hg n)).1
  have hB (n : ℕ) : ∀ᵐ u ∂μ, ‖F n u‖ ≤ B n u := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, B, norm_mul]
    rw [mul_comm (M n)]
    exact mul_le_mul_of_nonneg_left (hbound n u hu) (norm_nonneg _)
  have hB_summable : ∀ᵐ u ∂μ, Summable fun n ↦ B n u := by
    filter_upwards with u
    exact hM.mul_right _
  have hB_integrable : Integrable (fun u ↦ ∑' n, B n u) μ := by
    have heq : (fun u ↦ ∑' n, B n u) =
        fun u ↦ (∑' n, M n) * ‖regDirichletDensity b u‖ := by
      funext u
      simp only [B]
      rw [tsum_mul_right]
    rw [heq]
    exact hdens.norm.const_mul _
  have hlim : ∀ᵐ u ∂μ, HasSum (fun n ↦ F n u) (G u) := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact (hsum u hu).mul_left (regDirichletDensity b u)
  simpa [F, G, μ, regDirichletIntegral] using
    hasSum_integral_of_dominated_convergence B hF_meas hB hB_summable hB_integrable hlim

/-- A locally uniformly convergent series of entire transforms represents the continued
transform of the summed kernel, provided native integration is justified by domination.
Local uniform convergence of the transformed series is an explicit hypothesis. -/
theorem isRegDirichletContinuation_of_hasSumLocallyUniformlyOn
    {g : ℕ → (ι → ℝ) → ℂ} {h : (ι → ℝ) → ℂ}
    {F : ℕ → (ι → ℂ) → ℂ} {H : (ι → ℂ) → ℂ}
    (hF : ∀ n, IsRegDirichletContinuation (g n) (F n))
    (hlim : HasSumLocallyUniformlyOn F H univ)
    (hg : ∀ n, ContinuousOn (g n) (Convexity.StdSimplex.coordinateSet ℝ ι))
    (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → ‖g n u‖ ≤ M n)
    (hsum : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → HasSum (fun n => g n u) (h u)) :
    IsRegDirichletContinuation h H := by
  classical
  refine ⟨hlim.analyticOnNhd_pi (fun n => (hF n).1) isOpen_univ, fun b hb => ?_⟩
  have hn := hasSum_regDirichletIntegral hb g h M hg hM hbound hsum
  have he : (fun n => F n b) = (fun n => regDirichletIntegral b (g n)) :=
    funext fun n => (hF n).eq_native hb
  have hl := hlim.hasSum (mem_univ b)
  rw [he] at hl
  exact hl.unique hn

end Dirichlet
end
