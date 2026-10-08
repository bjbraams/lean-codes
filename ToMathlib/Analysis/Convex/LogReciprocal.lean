/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Log-convexity of a constant plus a reciprocal

The function `a + b / (x + k)` is strictly decreasing and strictly log-convex on the real line
where its denominator is positive, for `a ≥ 0` and `b > 0`; its derivative is computed over any
nontrivially normed field. This includes the
individual factors of concentration-dependent Pochhammer ratios.
-/

open Set
public section

/-- The derivative of a constant plus a reciprocal, over any nontrivially normed field. -/
theorem hasDerivAt_add_div {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a b k x : 𝕜}
    (hx : x + k ≠ 0) :
    HasDerivAt (fun y : 𝕜 ↦ a + b / (y + k)) (-b / (x + k) ^ 2) x := by
  simpa only [zero_mul, mul_one, zero_sub, id_eq, Pi.div_apply] using
    ((hasDerivAt_const x b).div ((hasDerivAt_id x).add_const k) hx).const_add a

namespace Real

/-- The logarithmic derivative of a nonnegative constant plus a positive reciprocal. -/
theorem hasDerivAt_log_add_div {a b k x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hx : 0 < x + k) :
    HasDerivAt (fun y : ℝ ↦ log (a + b / (y + k)))
      (-b / ((x + k) * (a * (x + k) + b))) x := by
  have hp : 0 < a + b / (x + k) := add_pos_of_nonneg_of_pos ha (div_pos hb hx)
  convert (hasDerivAt_add_div (a := a) (b := b) hx.ne').log hp.ne' using 1
  field_simp

/-- A positive reciprocal plus a constant is strictly decreasing where its denominator is
positive. -/
theorem strictAntiOn_add_div {a b k : ℝ} (hb : 0 < b) :
    StrictAntiOn (fun x : ℝ ↦ a + b / (x + k)) (Ioi (-k)) := by
  intro x hx y hy hxy
  have hx : -k < x := hx
  simpa only [add_comm] using add_lt_add_left (div_lt_div_of_pos_left hb (by linarith : 0 < x + k)
    (by linarith : x + k < y + k)) a

/-- A nonnegative constant plus a positive reciprocal is strictly log-convex. -/
theorem strictConvexOn_log_add_div {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    StrictConvexOn ℝ (Ioi (-k)) (fun x : ℝ ↦ log (a + b / (x + k))) := by
  have hd (x : ℝ) (hx : x ∈ Ioi (-k)) :=
    hasDerivAt_log_add_div ha hb (by have hx : -k < x := hx; linarith : 0 < x + k)
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi _)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
  rw [isOpen_Ioi.interior_eq]
  intro x hx y hy hxy
  rw [(hd x hx).deriv, (hd y hy).deriv]
  have hx : -k < x := hx
  have hy : -k < y := hy
  have hxk : 0 < x + k := by linarith
  have hyk : 0 < y + k := by linarith
  have hax : 0 < a * (x + k) + b := add_pos_of_nonneg_of_pos (mul_nonneg ha hxk.le) hb
  have hay : 0 < a * (y + k) + b := add_pos_of_nonneg_of_pos (mul_nonneg ha hyk.le) hb
  have hfac : a * (x + k) + b ≤ a * (y + k) + b := by nlinarith
  have hden : (x + k) * (a * (x + k) + b) < (y + k) * (a * (y + k) + b) :=
    (mul_lt_mul_of_pos_right (by linarith : x + k < y + k) hax).trans_le
      (mul_le_mul_of_nonneg_left hfac hyk.le)
  exact (div_lt_div_iff₀ (mul_pos hxk hax) (mul_pos hyk hay)).mpr (by nlinarith)

end Real
