/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform root limits from geometric bounds

If nonnegative functions are bounded above and below by fixed positive multiples of
`r(x)^n`, uniformly in `x`, and `r` is bounded, then their `n`th roots converge uniformly
to `r`. No topological assumptions on the parameter set are needed.
-/

open Filter Set
open scoped Topology

@[expose] public noncomputable section

namespace Real

/-- Uniform geometric upper and lower bounds imply uniform convergence of the `n`th roots. -/
theorem tendstoUniformlyOn_rpow_of_geometric_bounds {X : Type*} {s : Set X}
    {f : ℕ → X → ℝ} {r : X → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hr : ∀ x ∈ s, 0 ≤ r x ∧ r x ≤ M)
    (hf : ∀ n x, x ∈ s → 0 ≤ f n x)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, a * r x ^ n ≤ f n x ∧ f n x ≤ b * r x ^ n) :
    TendstoUniformlyOn (fun n : ℕ => fun x => f n x ^ (1 / (n : ℝ))) r atTop s := by
  have hroot (c : ℝ) (hc : 0 < c) :
      Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow hc.ne').tendsto.comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (M + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have haevent := (hroot a ha).eventually (lt_mem_nhds (by linarith : 1 - δ < 1))
  have hbevent := (hroot b hb).eventually (gt_mem_nhds (by linarith : 1 < 1 + δ))
  filter_upwards [hbound, haevent, hbevent, eventually_gt_atTop (0 : ℕ)] with n hn han hbn hn₀
  intro x hx
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₀.ne'
  have hpow : (r x ^ n) ^ (1 / (n : ℝ)) = r x := by
    rw [← Real.rpow_natCast_mul (hr x hx).1,
      mul_one_div_cancel hnR, Real.rpow_one]
  have hpow₀ : 0 ≤ r x ^ n := pow_nonneg (hr x hx).1 n
  have hlo := Real.rpow_le_rpow (mul_nonneg ha.le hpow₀) (hn x hx).1
    (by positivity : 0 ≤ 1 / (n : ℝ))
  have hhi := Real.rpow_le_rpow (hf n x hx) (hn x hx).2
    (by positivity : 0 ≤ 1 / (n : ℝ))
  rw [Real.mul_rpow ha.le hpow₀, hpow] at hlo
  rw [Real.mul_rpow hb.le hpow₀, hpow] at hhi
  have hδM : δ * M < ε := by
    have he : δ * (M + 1) = ε := by dsimp [δ]; field_simp
    nlinarith
  have hδr : δ * r x ≤ δ * M := mul_le_mul_of_nonneg_left (hr x hx).2 hδ.le
  rw [Real.dist_eq, abs_lt]
  constructor
  · have h := mul_le_mul_of_nonneg_right han.le (hr x hx).1
    nlinarith [(hr x hx).2]
  · have h := mul_le_mul_of_nonneg_right hbn.le (hr x hx).1
    nlinarith [(hr x hx).2]

end Real
