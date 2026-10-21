/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Strict log-convexity of Gamma

The recurrence writes `log Γ(x)` as the sum of the convex function `log Γ(x + 1)`
and the strictly convex function `-log x`. This upgrades Mathlib's log-convexity
without an equality-case analysis of Hölder's inequality. Gamma consequently has
a unique minimum on the positive half-line, as in Carlson (1977), §§3.5, 3.10.
-/

open Set

public noncomputable section

namespace Real

/-- The Gamma function is strictly log-convex on the positive half-line. -/
theorem strictConvexOn_log_Gamma : StrictConvexOn ℝ (Ioi 0) (log ∘ Gamma) := by
  have hc : ConvexOn ℝ (Ioi 0) (fun x : ℝ => log (Gamma (x + 1))) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro x hx y hy a b ha hb hab
    change 0 < x at hx
    change 0 < y at hy
    have h := convexOn_log_Gamma.2 (by change 0 < x + 1; linarith : x + 1 ∈ Ioi (0 : ℝ))
      (by change 0 < y + 1; linarith : y + 1 ∈ Ioi (0 : ℝ)) ha hb hab
    simp only [Function.comp_apply, smul_eq_mul] at h ⊢
    convert h using 1
    congr 2
    nlinarith
  apply (hc.sub_strictConcaveOn strictConcaveOn_log_Ioi).congr
  intro x hx
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [Gamma_add_one (ne_of_gt hx), log_mul (ne_of_gt hx) (Gamma_pos_of_pos hx).ne']
  ring

/-- The positive Gamma function is strictly convex. -/
theorem strictConvexOn_Gamma : StrictConvexOn ℝ (Ioi 0) Gamma := by
  refine ((convexOn_exp.subset (subset_univ _) ?_).comp_strictConvexOn
    strictConvexOn_log_Gamma (exp_strictMono.strictMonoOn _)).congr ?_
  · rw [convex_iff_isPreconnected]
    refine isPreconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt ?_
    refine (differentiableAt_Gamma fun m => ?_).continuousAt.log (Gamma_pos_of_pos hx).ne'
    exact (neg_lt_iff_pos_add.mpr (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg m))).ne'
  · intro x hx
    exact exp_log (Gamma_pos_of_pos hx)

/-- Gamma has exactly one global minimizer on the positive half-line, lying between one and two. -/
theorem existsUnique_isMinOn_Gamma_Ioi :
    ∃! x, x ∈ Ioi (0 : ℝ) ∧ IsMinOn Gamma (Ioi 0) x := by
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_Gamma_Ioi
  refine ⟨x, ⟨lt_trans zero_lt_one hx.1, hmin⟩, ?_⟩
  intro y hy
  exact strictConvexOn_Gamma.eq_of_isMinOn hy.2 hmin hy.1 (lt_trans zero_lt_one hx.1)

end Real
