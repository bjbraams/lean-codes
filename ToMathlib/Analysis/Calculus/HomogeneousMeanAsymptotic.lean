/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Calculus.MeanWeights
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Large translates of smooth homogeneous means

Brenner–Carlson (1987), Theorem 1. A normalized positively homogeneous mean that
is twice continuously differentiable near the diagonal has a weighted arithmetic
first approximation, with an error of order the reciprocal translation.
-/

open Filter Set Asymptotics
open scoped Topology
@[expose] public noncomputable section

namespace ContDiffAt

/-- A twice continuously differentiable real function has a quadratic first-order
remainder on a sufficiently small interval to the right of zero. -/
theorem exists_abs_sub_linear_le_sq {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc 0 δ,
      |f h - f 0 - h * deriv f 0| ≤ C * h ^ 2 := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := 2) le_rfl (by norm_num)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hsub : Icc 0 (r / 2) ⊆ s := by
    intro x hx
    apply hrs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 1)
    (show (0 : ℝ) ≤ r / 2 by positivity) (hfs.mono hsub)
  have hd := (hf.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt
    (s := Icc 0 (r / 2))
  have hd' := hd.derivWithin (uniqueDiffOn_Icc (by positivity) 0 (by simp; positivity))
  refine ⟨C, r / 2, by positivity, fun h hh => ?_⟩
  simpa [taylorWithinEval_succ, iteratedDerivWithin_one, hd', smul_eq_mul, sub_add_eq_sub_sub,
    Real.norm_eq_abs] using hC h hh

end ContDiffAt

namespace Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Brenner–Carlson Theorem 1 (1987).** Translating every input of a normalized
smooth homogeneous mean by `x` gives `x + ∑ wᵢ aᵢ + O(1/x)`. Homogeneity is
needed only on positive inputs and for positive scaling factors. -/
theorem isBigO_homogeneous_mean_translate {M : (ι → ℝ) → ℝ}
    (hM : ContDiffAt ℝ 2 M 1) (h1 : M 1 = 1)
    (hhom : ∀ r : ℝ, 0 < r → ∀ z : ι → ℝ, (∀ i, 0 < z i) →
      M (fun i => r * z i) = r * M z) (a : ι → ℝ) :
    (fun x : ℝ => M (fun i => x + a i) - x - ∑ i, meanWeight ℝ M i * a i)
      =O[atTop] (fun x : ℝ => x⁻¹) := by
  let g : ℝ → ℝ := fun h => M (fun i => 1 + h * a i)
  have hone : (fun _ : ι => (1 : ℝ)) = 1 := rfl
  have hmap : ContDiffAt ℝ 2 (fun h : ℝ => fun i => 1 + h * a i) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fun_prop
  have hm : ContDiffAt ℝ 2 M (fun i => 1 + (0 : ℝ) * a i) := by
    simpa only [zero_mul, add_zero, hone] using hM
  have hg : ContDiffAt ℝ 2 g 0 := hm.comp 0 hmap
  have hD : HasDerivAt g (∑ i, meanWeight ℝ M i * a i) 0 := by
    have hd := (hm.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_pi.mpr fun i => ((hasDerivAt_id 0).mul_const (a i)).const_add 1)
    simpa [g, Function.comp_def, hone, fderiv_one_eq_sum_meanWeight, mul_comm] using hd
  obtain ⟨C, δ, hδ, hC⟩ := hg.exists_abs_sub_linear_le_sq
  have hsmall : ∀ᶠ x : ℝ in atTop, x⁻¹ ∈ Icc 0 δ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      tendsto_inv_atTop_zero.eventually (gt_mem_nhds hδ)] with x hx hxd
    exact ⟨inv_nonneg.mpr hx.le, hxd.le⟩
  have hpos : ∀ᶠ x : ℝ in atTop, ∀ i, 0 < 1 + x⁻¹ * a i := by
    apply eventually_all.mpr
    intro i
    have ht : Tendsto (fun x : ℝ => 1 + x⁻¹ * a i) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.mul_const (a i))
    exact ht.eventually (lt_mem_nhds zero_lt_one)
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [hsmall, hpos, eventually_gt_atTop (0 : ℝ)] with x hx hp hx0
  have hb := mul_le_mul_of_nonneg_left (hC x⁻¹ hx) hx0.le
  have he : M (fun i => x + a i) = x * g x⁻¹ := by
    rw [← hhom x hx0 _ hp]
    congr 1
    ext i
    field_simp
  rw [he, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  have hg0 : g 0 = 1 := by simpa only [g, zero_mul, add_zero, hone] using h1
  rw [hg0, hD.deriv] at hb
  calc
    |x * g x⁻¹ - x - ∑ i, meanWeight ℝ M i * a i| =
        x * |g x⁻¹ - 1 - x⁻¹ * ∑ i, meanWeight ℝ M i * a i| := by
      have heq : x * g x⁻¹ - x - ∑ i, meanWeight ℝ M i * a i =
          x * (g x⁻¹ - 1 - x⁻¹ * ∑ i, meanWeight ℝ M i * a i) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hx0]
    _ ≤ x * (C * x⁻¹ ^ 2) := hb
    _ = C * x⁻¹ := by field_simp

end Function
