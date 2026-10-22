/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.DuplicationError

/-!
# The three-dimensional Carlson capacity bound

Carlson (1966), Theorem 3 and the lower bound in (4.7), in dimension three.
Duplication decreases the arithmetic mean of the square roots, strictly unless
all three nodes coincide. Its common limit is the reciprocal of R_F.
-/

open Filter Set
open scoped Topology Real
@[expose] public noncomputable section
namespace Carlson

/-- The loss of arithmetic mean in duplication is a sum of three squares. -/
theorem dupMean_sub_step_eq {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    dupMean (x, y, z) - dupMean (dupStep (x, y, z)) =
      ((√(x + y) - √(x + z)) ^ 2 + (√(y + x) - √(y + z)) ^ 2 +
        (√(z + x) - √(z + y)) ^ 2) / 12 := by
  have hxy := Real.sq_sqrt (add_nonneg hx hy)
  have hxz := Real.sq_sqrt (add_nonneg hx hz)
  have hyz := Real.sq_sqrt (add_nonneg hy hz)
  simp only [dupMean, dupStep, add_comm y x, add_comm z x, add_comm z y]
  nlinarith

/-- Duplication decreases the arithmetic mean of nonnegative square roots. -/
theorem dupMean_step_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    dupMean (dupStep (x, y, z)) ≤ dupMean (x, y, z) := by
  have h := dupMean_sub_step_eq hx hy hz
  have hs : 0 ≤ ((√(x + y) - √(x + z)) ^ 2 + (√(y + x) - √(y + z)) ^ 2 +
      (√(z + x) - √(z + y)) ^ 2) / 12 := by positivity
  linarith

/-- The decrease is strict as soon as two square roots differ. -/
theorem dupMean_step_lt {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hne : ¬ (x = y ∧ y = z)) :
    dupMean (dupStep (x, y, z)) < dupMean (x, y, z) := by
  have he := dupMean_sub_step_eq hx hy hz
  have hn : √(x + y) ≠ √(x + z) ∨ √(z + x) ≠ √(z + y) := by
    by_contra h
    push Not at h
    apply hne
    have h1 := congrArg (fun t : ℝ => t ^ 2) h.1
    have h2 := congrArg (fun t : ℝ => t ^ 2) h.2
    rw [Real.sq_sqrt (add_nonneg hx hy), Real.sq_sqrt (add_nonneg hx hz)] at h1
    rw [Real.sq_sqrt (add_nonneg hz hx), Real.sq_sqrt (add_nonneg hz hy)] at h2
    exact ⟨by linarith, by linarith⟩
  rcases hn with hn | hn
  · have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hn)
    nlinarith [sq_nonneg (√(y + x) - √(y + z)), sq_nonneg (√(z + x) - √(z + y))]
  · have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hn)
    nlinarith [sq_nonneg (√(x + y) - √(x + z)), sq_nonneg (√(y + x) - √(y + z))]

/-- Every duplication iterate has nonnegative coordinates when the initial values do. -/
theorem dupSeq_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ (dupSeq x y z n).1 ∧ 0 ≤ (dupSeq x y z n).2.1 ∧
      0 ≤ (dupSeq x y z n).2.2 := by
  induction n with
  | zero => exact ⟨hx, hy, hz⟩
  | succ n ih =>
    rw [dupSeq, Function.iterate_succ_apply']
    exact ⟨by dsimp [dupStep]; positivity, by dsimp [dupStep]; positivity,
      by dsimp [dupStep]; positivity⟩

/-- The arithmetic means along the duplication sequence are antitone. -/
theorem antitone_dupMean_dupSeq {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Antitone (fun n => dupMean (dupSeq x y z n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp := dupSeq_nonneg hx hy hz n
  rw [show dupSeq x y z (n + 1) = dupStep (dupSeq x y z n) from
    Function.iterate_succ_apply' dupStep n (x, y, z)]
  simpa only [Prod.eta] using dupMean_step_le hp.1 hp.2.1 hp.2.2

/-- The limiting square root is bounded by every arithmetic-mean iterate. -/
theorem dupMean_limit_le {x y z L : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hL : Tendsto (fun n => dupMean (dupSeq x y z n)) atTop (𝓝 L)) (n : ℕ) :
    L ≤ dupMean (dupSeq x y z n) := by
  apply le_of_tendsto hL
  filter_upwards [eventually_ge_atTop n] with j hj
  exact antitone_dupMean_dupSeq hx hy hz hj

/-- **Carlson (1966), Theorem 3 for three positive nodes.** The reciprocal R_F
is at most the arithmetic mean of the square roots. -/
theorem inv_dupMean_le_carlsonRF_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (dupMean (x, y, z))⁻¹ ≤
      (carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re := by
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := tendsto_dupSeq hx hy hz
  have ht : Tendsto (fun n => dupMean (dupSeq x y z n)) atTop (𝓝 L) := by
    have he : (L + L + L) / 3 = L := by ring
    simpa only [dupMean, he] using ((h1.add h2).add h3).div_const 3
  have hb := dupMean_limit_le hx.le hy.le hz.le ht 0
  have he := congrArg Complex.re hRF
  simp only [Complex.ofReal_re] at he
  rw [he]
  exact inv_anti₀ hL (by simpa [dupSeq] using hb)

/-- The strict capacity lower bound for R_F on three positive nonconstant nodes. -/
theorem inv_dupMean_lt_carlsonRF_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : ¬ (x = y ∧ y = z)) :
    (dupMean (x, y, z))⁻¹ <
      (carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re := by
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := tendsto_dupSeq hx hy hz
  have ht : Tendsto (fun n => dupMean (dupSeq x y z n)) atTop (𝓝 L) := by
    have he : (L + L + L) / 3 = L := by ring
    simpa only [dupMean, he] using ((h1.add h2).add h3).div_const 3
  have hb := dupMean_limit_le hx.le hy.le hz.le ht 1
  have hs := dupMean_step_lt hx.le hy.le hz.le hne
  have hlt : L < dupMean (x, y, z) := hb.trans_lt (by simpa [dupSeq] using hs)
  have he := congrArg Complex.re hRF
  simp only [Complex.ofReal_re] at he
  rw [he]
  exact inv_strictAnti₀ hL hlt

/-- The displayed strict lower bound (4.7) for three positive arguments. -/
theorem carlsonRF_capacity_lower_bound {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : ¬ (x = y ∧ y = z)) :
    3 / (√x + √y + √z) < (carlsonRF x y z).re := by
  have hs : ¬ (√x = √y ∧ √y = √z) := by
    intro h
    apply hne
    constructor
    · exact (Real.sqrt_inj hx.le hy.le).mp h.1
    · exact (Real.sqrt_inj hy.le hz.le).mp h.2
  have h := inv_dupMean_lt_carlsonRF_sq (Real.sqrt_pos.mpr hx)
    (Real.sqrt_pos.mpr hy) (Real.sqrt_pos.mpr hz) hs
  simpa only [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le,
    dupMean, inv_div, one_mul] using h

/-- The capacity lower bound at one zero argument, expressed through the finite
boundary value `(π/2) R_K` rather than an evaluation of the slit-domain R_F. -/
theorem carlsonRK_capacity_lower_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    3 / (√x + √y) <
      ((Real.pi / 2 : ℂ) * TwoVariable.carlsonRK x y).re := by
  obtain ⟨L, hL, h1, h2, h3, hRK⟩ :=
    tendsto_dupSeq_zero (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy)
  have ht : Tendsto (fun n => dupMean (dupSeq (√x) (√y) 0 n)) atTop (𝓝 L) := by
    have he : (L + L + L) / 3 = L := by ring
    simpa only [dupMean, he] using ((h1.add h2).add h3).div_const 3
  have hb := dupMean_limit_le (Real.sqrt_nonneg x) (Real.sqrt_nonneg y) le_rfl ht 1
  have hs := dupMean_step_lt (Real.sqrt_nonneg x) (Real.sqrt_nonneg y) le_rfl
    (show ¬ (√x = √y ∧ √y = 0) from fun h => (Real.sqrt_pos.mpr hy).ne' h.2)
  have hlt : L < dupMean (√x, √y, 0) :=
    hb.trans_lt (by simpa [dupSeq] using hs)
  have he := congrArg Complex.re hRK
  simp only [Complex.ofReal_re, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le] at he
  have h := inv_strictAnti₀ hL hlt
  simpa only [dupMean, add_zero, inv_div, one_mul, ← he] using h

end Carlson
