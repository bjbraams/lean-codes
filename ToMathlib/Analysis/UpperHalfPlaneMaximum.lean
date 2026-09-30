/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A minimum principle for the imaginary part on the upper half-plane

Let `f` be holomorphic on the upper half-plane, continuous on its closure, with a limit `L` at
infinity in the closed half-plane. If `im f ≥ 0` on the real axis and `im L ≥ 0`, then
`im f ≥ 0` throughout the upper half-plane. The proof applies the maximum modulus principle to
`exp (i f)` on large half-disks.

## Main results

* `Complex.im_nonneg_of_boundary_upperHalfPlane`: the minimum principle.
-/

@[expose] public section

open Complex Set Filter Topology Metric

/-- **Minimum principle for `im f` on the upper half-plane.** -/
theorem Complex.im_nonneg_of_boundary_upperHalfPlane {f : ℂ → ℂ} {L : ℂ}
    (hd : DifferentiableOn ℂ f {z | 0 < z.im}) (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hlim : Tendsto f (Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 L)) (hL : 0 ≤ L.im)
    (hb : ∀ t : ℝ, 0 ≤ (f t).im) {z : ℂ} (hz : 0 < z.im) : 0 ≤ (f z).im := by
  set F : ℂ → ℂ := fun w => exp (I * f w) with hF_def
  have hF : ∀ w, ‖F w‖ = Real.exp (-(f w).im) := by
    intro w; simp [F, norm_exp]
  suffices h : ‖F z‖ ≤ 1 by
    rw [hF] at h
    have := Real.exp_le_one_iff.mp h
    linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hFL : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 (exp (I * L))) :=
    (continuous_exp.tendsto _).comp (hlim.const_mul I)
  have hnorm : ‖exp (I * L)‖ ≤ 1 := by
    rw [norm_exp]
    simpa using hL
  have hev := hFL.norm.eventually (eventually_lt_nhds (show ‖exp (I * L)‖ < 1 + ε / 2 by linarith))
  rw [eventually_inf_principal] at hev
  obtain ⟨R, -, hR⟩ := (Filter.hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp hev
  set R' := max R (‖z‖ + 1)
  set U : Set ℂ := {w : ℂ | 0 < w.im} ∩ ball 0 R' with hU_def
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_im).inter isOpen_ball
  have hzU : z ∈ U := ⟨hz, by simp [R']⟩
  have hbdd : Bornology.IsBounded U := isBounded_ball.subset inter_subset_right
  have hcl : closure U ⊆ {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R' := by
    refine closure_minimal ?_
      ((isClosed_le continuous_const continuous_im).inter isClosed_closedBall)
    exact fun w hw => ⟨show 0 ≤ w.im from le_of_lt hw.1, ball_subset_closedBall hw.2⟩
  have hdc : DiffContOnCl ℂ F U := by
    refine ⟨?_, ?_⟩
    · exact differentiable_exp.comp_differentiableOn
        ((hd.mono inter_subset_left).const_mul I)
    · exact continuous_exp.comp_continuousOn
        ((hc.mono (hcl.trans inter_subset_left)).const_mul I)
  have hfr : ∀ w ∈ frontier U, ‖F w‖ ≤ 1 + ε / 2 := by
    intro w hw
    rw [hUo.frontier_eq] at hw
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨hwim, hwR⟩ := hcl hw1
    have hwim : 0 ≤ w.im := hwim
    by_cases him : w.im = 0
    · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hF, hw']
      have := hb w.re
      have : Real.exp (-(f (w.re : ℂ)).im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · have hwim' : 0 < w.im := lt_of_le_of_ne hwim (Ne.symm him)
      have hnot : ¬ ‖w‖ < R' := fun h => hw2 ⟨hwim', by simpa using h⟩
      have hRw : R ≤ ‖w‖ := le_trans (le_max_left _ _) (not_lt.mp hnot)
      exact (hR hRw hwim).le
  have := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdc hfr (subset_closure hzU)
  linarith
