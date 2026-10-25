/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF4
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic scalar families of Appell F₄

Absolute convergence at slightly larger positive radii supplies a local
summable majorant. Mathlib's Weierstrass theorem then proves holomorphy
under analytic scalar substitutions throughout the full square-root region.
-/

open Complex Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- Strictly larger positive radii still fit inside the F₄ convergence region. -/
private theorem exists_larger_F4_radii {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXY : Real.sqrt X + Real.sqrt Y < 1) :
    ∃ S T : ℝ, X < S ∧ Y < T ∧ 0 ≤ S ∧ 0 ≤ T ∧ Real.sqrt S + Real.sqrt T < 1 := by
  let r := (1 - (Real.sqrt X + Real.sqrt Y)) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨(Real.sqrt X + r) ^ 2, (Real.sqrt Y + r) ^ 2, ?_, ?_,
    sq_nonneg _, sq_nonneg _, ?_⟩
  · nlinarith [Real.sq_sqrt hX, Real.sqrt_nonneg X, sq_pos_of_pos hr]
  · nlinarith [Real.sq_sqrt hY, Real.sqrt_nonneg Y, sq_pos_of_pos hr]
  · rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
    dsimp [r]
    linarith

/-- Holomorphy of regularized F₄ under scalar analytic substitutions, for every parameter,
throughout the full square-root convergence region of its defining series. -/
theorem analyticAt_regularizedAppellF4_comp (a b c d : ℂ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hfg : Real.sqrt ‖f z‖ + Real.sqrt ‖g z‖ < 1) :
    AnalyticAt ℂ (fun w => regularizedAppellF4 a b c d (f w) (g w)) z := by
  obtain ⟨S, T, hS, hT, hS0, hT0, hST⟩ :=
    exists_larger_F4_radii (norm_nonneg _) (norm_nonneg _) hfg
  have hnear := (hf.eventually_analyticAt.and hg.eventually_analyticAt).and
    ((hf.continuousAt.norm.eventually (Iio_mem_nhds hS)).and
      (hg.continuousAt.norm.eventually (Iio_mem_nhds hT)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hsum := summable_norm_regularizedAppellF4 a b c d (x := (S : ℂ)) (y := (T : ℂ)) (by
    simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hS0, abs_of_nonneg hT0] using hST)
  have hu : Summable (fun p : ℕ × ℕ => ‖regularizedAppellF4Coeff a b c d p‖ * S ^ p.1 *
      T ^ p.2) := by
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hS0, abs_of_nonneg hT0] using hsum
  have hd := differentiableOn_tsum_of_summable_norm hu
    (F := fun p w => regularizedAppellF4Coeff a b c d p * f w ^ p.1 * g w ^ p.2)
    (U := Metric.ball z ε) (fun p w hw =>
      ((analyticAt_const.mul ((hball (by simpa using hw)).1.1.pow p.1)).mul
        ((hball (by simpa using hw)).1.2.pow p.2)).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun p w hw => by
      simp only [norm_mul, norm_pow]
      gcongr
      · exact (hball (by simpa using hw)).2.1.le
      · exact (hball (by simpa using hw)).2.2.le)
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hε))

end Complex
