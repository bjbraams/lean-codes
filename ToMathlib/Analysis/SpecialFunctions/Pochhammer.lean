/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import ToMathlib.Analysis.Convex.LogReciprocal

/-!
# Concentration comparisons for Pochhammer ratios

For `0 < w < 1`, the ratio `(c w)ₙ / (c)ₙ` is positive, decreasing and
log-convex on `c > 0`. Decrease and log-convexity are strict for `n ≥ 2`;
the orders zero and one give the constants one and `w` respectively.

The proof factors the ratio into positive functions
`w + k * (1 - w) / (c + k)`. These are the scalar factors in the
Carlson–Tobey concentration argument.
-/

open Set Polynomial
public noncomputable section
namespace Real

/-- Raising the Pochhammer order adds one rational factor to the concentration ratio. -/
theorem ascPochhammer_ratio_succ (c w : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval (c * w) / (ascPochhammer ℝ (n + 1)).eval c =
      ((ascPochhammer ℝ n).eval (c * w) / (ascPochhammer ℝ n).eval c) *
        ((c * w + n) / (c + n)) := by
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, mul_div_mul_comm]

/-- Each concentration factor is a constant plus a positive reciprocal. -/
theorem concentration_factor_eq {c k : ℝ} (hck : c + k ≠ 0) (w : ℝ) :
    (c * w + k) / (c + k) = w + k * (1 - w) / (c + k) := by
  field_simp
  ring

/-- Every Pochhammer concentration ratio with positive weight is positive. -/
theorem ascPochhammer_ratio_pos {c w : ℝ} (hc : 0 < c) (hw : 0 < w) (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (c * w) / (ascPochhammer ℝ n).eval c :=
  div_pos (ascPochhammer_pos n _ (mul_pos hc hw)) (ascPochhammer_pos n c hc)

/-- Each noninitial factor in a concentration ratio is strictly decreasing. -/
private theorem strictAntiOn_concentration_factor {w k : ℝ}
    (hw : w < 1) (hk : 0 < k) :
    StrictAntiOn (fun c : ℝ ↦ (c * w + k) / (c + k)) (Ioi 0) := by
  intro c hc d hd hcd
  have hc : 0 < c := hc
  have hd : 0 < d := hd
  dsimp only
  rw [concentration_factor_eq (by positivity) w, concentration_factor_eq (by positivity) w]
  exact strictAntiOn_add_div (mul_pos hk (sub_pos.mpr hw))
    (show c ∈ Ioi (-k) by change -k < c; linarith [show 0 < c from hc])
    (show d ∈ Ioi (-k) by change -k < d; linarith [show 0 < d from hd]) hcd

/-- Each noninitial factor in a concentration ratio is strictly log-convex. -/
private theorem strictConvexOn_log_concentration_factor {w k : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) (hk : 0 < k) :
    StrictConvexOn ℝ (Ioi 0) (fun c : ℝ ↦ log ((c * w + k) / (c + k))) := by
  apply ((strictConvexOn_log_add_div hw0 (mul_pos hk (sub_pos.mpr hw1))).subset
    (fun c hc ↦ by change -k < c; linarith [show 0 < c from hc]) (convex_Ioi 0)).congr
  intro c hc
  have hc : 0 < c := hc
  dsimp only
  rw [concentration_factor_eq (by positivity) w]

/-- Pochhammer concentration ratios are decreasing at every natural order. -/
theorem antitoneOn_ascPochhammer_ratio {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (n : ℕ) :
    AntitoneOn (fun c : ℝ ↦ (ascPochhammer ℝ n).eval (c * w) /
      (ascPochhammer ℝ n).eval c) (Ioi 0) := by
  induction n with
  | zero => simp [antitoneOn_const]
  | succ n ih =>
    cases n with
    | zero =>
      intro c hc d hd _
      simp only [Nat.zero_add, ascPochhammer_one, eval_X]
      rw [mul_div_cancel_left₀ _ (show c ≠ 0 from ne_of_gt hc),
        mul_div_cancel_left₀ _ (show d ≠ 0 from ne_of_gt hd)]
    | succ n =>
      intro c hc d hd hcd
      have hc : 0 < c := hc
      have hd : 0 < d := hd
      dsimp only
      rw [ascPochhammer_ratio_succ d w (n + 1), ascPochhammer_ratio_succ c w (n + 1)]
      simp only [Nat.cast_add, Nat.cast_one]
      exact mul_le_mul (ih hc hd hcd)
        ((strictAntiOn_concentration_factor hw1 (by positivity : (0 : ℝ) < n + 1)).antitoneOn
          hc hd hcd)
        (by positivity) (ascPochhammer_ratio_pos hc hw0 _).le

/-- Pochhammer concentration ratios are log-convex at every natural order. -/
theorem convexOn_log_ascPochhammer_ratio {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (n : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun c : ℝ ↦ log ((ascPochhammer ℝ n).eval (c * w) /
      (ascPochhammer ℝ n).eval c)) := by
  induction n with
  | zero => simpa using convexOn_const (c := (0 : ℝ)) (convex_Ioi (0 : ℝ))
  | succ n ih =>
    cases n with
    | zero =>
      apply (convexOn_const (c := log w) (convex_Ioi (0 : ℝ))).congr
      intro c hc
      have hc : 0 < c := hc
      simp only [Nat.zero_add, ascPochhammer_one, eval_X]
      rw [mul_div_cancel_left₀ _ (show c ≠ 0 from ne_of_gt hc)]
    | succ n =>
      apply (ih.add (strictConvexOn_log_concentration_factor hw0.le hw1
        (by positivity : (0 : ℝ) < n + 1)).convexOn).congr
      intro c hc
      have hc : 0 < c := hc
      dsimp only [Pi.add_apply]
      rw [ascPochhammer_ratio_succ c w (n + 1), Real.log_mul (ascPochhammer_ratio_pos hc hw0 _).ne'
        (by positivity : (c * w + ((n + 1 : ℕ) : ℝ)) / (c + ((n + 1 : ℕ) : ℝ)) ≠ 0)]
      simp only [Nat.cast_add, Nat.cast_one]

/-- Pochhammer concentration ratios decrease strictly at orders at least two. -/
theorem strictAntiOn_ascPochhammer_ratio {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    {n : ℕ} (hn : 2 ≤ n) :
    StrictAntiOn (fun c : ℝ ↦ (ascPochhammer ℝ n).eval (c * w) /
      (ascPochhammer ℝ n).eval c) (Ioi 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro c hc d hd hcd
  have hc : 0 < c := hc
  have hd : 0 < d := hd
  dsimp only
  rw [show 2 + n = (n + 1) + 1 by omega, ascPochhammer_ratio_succ d w (n + 1),
    ascPochhammer_ratio_succ c w (n + 1)]
  have hf := strictAntiOn_concentration_factor hw1 (by positivity : (0 : ℝ) < n + 1) hc hd hcd
  have hr := antitoneOn_ascPochhammer_ratio hw0 hw1 (n + 1) hc hd hcd.le
  exact mul_lt_mul_of_le_of_lt_of_pos_of_nonneg hr (by simpa using hf)
    (ascPochhammer_ratio_pos hd hw0 _) (by positivity)

/-- Pochhammer concentration ratios are strictly log-convex at orders at least two. -/
theorem strictConvexOn_log_ascPochhammer_ratio {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    {n : ℕ} (hn : 2 ≤ n) :
    StrictConvexOn ℝ (Ioi 0) (fun c : ℝ ↦ log ((ascPochhammer ℝ n).eval (c * w) /
      (ascPochhammer ℝ n).eval c)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply ((convexOn_log_ascPochhammer_ratio hw0 hw1 (n + 1)).add_strictConvexOn
    (strictConvexOn_log_concentration_factor hw0.le hw1 (by positivity : (0 : ℝ) < n + 1))).congr
  intro c hc
  have hc : 0 < c := hc
  dsimp only [Pi.add_apply]
  rw [show 2 + n = (n + 1) + 1 by omega, ascPochhammer_ratio_succ c w (n + 1),
    Real.log_mul (ascPochhammer_ratio_pos hc hw0 _).ne'
      (by positivity : (c * w + ((n + 1 : ℕ) : ℝ)) / (c + ((n + 1 : ℕ) : ℝ)) ≠ 0)]
  simp only [Nat.cast_add, Nat.cast_one]

end Real
