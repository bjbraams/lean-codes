/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Average
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Large concentration of Dirichlet distributions

With positive normalized weights `w`, the distribution with parameters `c w`
concentrates at `w` as `c` tends to infinity. Coordinate variances give an explicit
bound for Lipschitz averages, and therefore convergence for continuously
differentiable kernels on the compact simplex.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The coordinate variance at concentration `c` is `w i * (1 - w i) / (c + 1)`. -/
theorem integral_dirichletMeasure_concentration_coordinate_sq {c : ℝ} (hc : 0 < c)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : ι) :
    (∫ u, (u i - w i) ^ 2 ∂dirichletMeasure (fun j => c * w j)) = w i * (1 - w i) / (c + 1) := by
  have hs : ∑ j, c * w j = c := by rw [← Finset.mul_sum, hw1, mul_one]
  have h := variance_dirichletMeasure_coordinate (fun j => mul_pos hc (hw j)) i
  rw [hs, mul_div_cancel_left₀ _ hc.ne'] at h
  rw [h]
  field_simp

/-- The mean absolute coordinate deviation is bounded by the square root of its variance. -/
theorem integral_dirichletMeasure_concentration_abs_coordinate_le {c : ℝ} (hc : 0 < c)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : ι) :
    (∫ u, |u i - w i| ∂dirichletMeasure (fun j => c * w j)) ≤
      Real.sqrt (w i * (1 - w i) / (c + 1)) := by
  have hb : (fun j => c * w j) ∈ mvRealBetaDomain := fun j => mul_pos hc (hw j)
  let := isProbabilityMeasure_dirichletMeasure hb
  have hi : MemLp (fun u : ι → ℝ => u i - w i) 2 (dirichletMeasure (fun j => c * w j)) :=
    (memLp_dirichletMeasure_coordinate hb i 2).sub (memLp_const _)
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq hpq (by simpa using hi)
    (memLp_const (1 : ℝ) : MemLp (fun _ : ι → ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
      (dirichletMeasure (fun j => c * w j)))
  simpa only [norm_one, mul_one, Real.norm_eq_abs, Real.rpow_two, sq_abs,
    integral_const, probReal_univ, smul_eq_mul, one_mul, one_pow, Real.one_rpow,
    integral_dirichletMeasure_concentration_coordinate_sq hc hw hw1 i, ← Real.sqrt_eq_rpow,
        Real.sqrt_one, mul_one] using h

/-- Each coordinate's mean absolute deviation tends to zero at large concentration. -/
theorem tendsto_integral_dirichletMeasure_abs_coordinate {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : ι) :
    Tendsto (fun c : ℝ => ∫ u, |u i - w i| ∂dirichletMeasure (fun j => c * w j))
      atTop (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => w i * (1 - w i) / (c + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  rw [Real.sqrt_zero] at hs
  apply squeeze_zero'
      (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ hs
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact integral_dirichletMeasure_concentration_abs_coordinate_le hc hw hw1 i

/-- A Lipschitz kernel on the simplex has a quantitative concentration bound. -/
theorem integral_dirichletMeasure_concentration_error_le {c : ℝ} (hc : 0 < c)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    {f : (ι → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    |(∫ u, f u ∂dirichletMeasure (fun j => c * w j)) - f w| ≤
      K * ∑ i, ∫ u, |u i - w i| ∂dirichletMeasure (fun j => c * w j) := by
  have hb : (fun j => c * w j) ∈ mvRealBetaDomain := fun j => mul_pos hc (hw j)
  let := isProbabilityMeasure_dirichletMeasure hb
  have hw' : w ∈ Convexity.StdSimplex.coordinateSet ℝ ι := ⟨fun i => (hw i).le, hw1⟩
  have hi := integrable_dirichletMeasure_of_continuousOn hb hf.continuousOn
  have hg i : Integrable (fun u : ι → ℝ => |u i - w i|) (dirichletMeasure (fun j => c * w j)) :=
    integrable_dirichletMeasure_of_continuousOn hb (by fun_prop)
  have hbound : ∀ᵐ u ∂dirichletMeasure (fun j => c * w j),
      ‖f u - f w‖ ≤ (K : ℝ) * ∑ i, |u i - w i| := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure (fun j => c * w j)] with u hu
    have h := hf.dist_le_mul u hu w hw'
    rw [dist_eq_norm, dist_eq_norm] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))).mpr
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (Finset.single_le_sum (fun j _ => abs_nonneg (u j - w j)) (Finset.mem_univ i))
  have h := norm_integral_le_of_norm_le
    ((integrable_finsetSum _ (fun i _ => hg i)).const_mul (K : ℝ)) hbound
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_finsetSum _ (fun i _ => hg i), Real.norm_eq_abs] at h
  exact h

/-- Dirichlet averages of a Lipschitz simplex kernel converge to its value at the
normalized parameter vector as concentration tends to infinity. -/
theorem tendsto_integral_dirichletMeasure_concentration_of_lipschitz {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    {f : (ι → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Tendsto (fun c : ℝ => ∫ u, f u ∂dirichletMeasure (fun j => c * w j)) atTop (𝓝 (f w)) := by
  have h := (tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_dirichletMeasure_abs_coordinate hw hw1 i)).const_mul (K : ℝ)
  simp only [Finset.sum_const_zero, mul_zero] at h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simpa only [Real.norm_eq_abs] using integral_dirichletMeasure_concentration_error_le hc hw hw1 hf

/-- Every continuously differentiable simplex kernel has the large-concentration limit. -/
theorem tendsto_integral_dirichletMeasure_concentration_of_contDiff {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) {f : (ι → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Tendsto (fun c : ℝ => ∫ u, f u ∂dirichletMeasure (fun j => c * w j)) atTop (𝓝 (f w)) := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (by
      intro x hx y hy a c ha hc hac
      exact ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hc (hy.1 i)), by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hx.2, hy.2, mul_one, hac]⟩)
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
  exact tendsto_integral_dirichletMeasure_concentration_of_lipschitz hw hw1 hK

end ProbabilityTheory
