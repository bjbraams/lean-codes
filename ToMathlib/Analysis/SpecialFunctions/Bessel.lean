/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Series and bounds for Bessel functions of integer order, and the modified Bessel function

The regularized `₀F₁` is the sum of its series `∑ zᵏ / (k! Γ(c + k))`, and for `c = n + 1` it is
bounded by `exp ‖z‖ / n!`. Consequently `‖Jₘ(x)‖ ≤ exp (‖x‖²/4) (‖x‖/2)^{|m|} / |m|!` for every
integer `m`.

## Main results

* `Complex.hasSum_regularizedHGFun_zero_singleton`: the series of the regularized `₀F₁`.
* `Complex.norm_besselJ_intCast_le`: the bound for integer orders.
* `Complex.hasSum_regularizedHGFun`: the series of an entire regularized hypergeometric function.
* `Complex.besselI`: the modified Bessel function `Iₐ`, with `Jₘ(ix) = iᵐ Iₘ(x)`
  (`Complex.besselJ_intCast_I_mul`) and `I₋ₘ = Iₘ` (`Complex.besselI_neg_int`) for integers `m`.
-/

@[expose] public noncomputable section

namespace Complex

/-- The regularized `₀F₁` is the sum of its power series `∑ zⁿ / (n! Γ(c + n))`. -/
theorem hasSum_regularizedHGFun_zero_singleton (c z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial * Gamma (c + n)))
      (regularizedHGFun 0 {c} z) := by
  have h := (regularizedHGFunSeries 0 {c}).hasSum
    (x := z) (by simp [radius_regularizedHGFunSeries_zero_eq_top])
  show HasSum _ ((regularizedHGFunSeries 0 {c}).sum z)
  convert h using 1
  funext n
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp [regularizedHGFunCoeff, div_eq_mul_inv, mul_comm]


/-- The regularized `₀F₁(n + 1; z)` is bounded by `exp ‖z‖ / n!`. -/
theorem norm_regularizedHGFun_natCast_add_one_le (n : ℕ) (z : ℂ) :
    ‖regularizedHGFun 0 {(n : ℂ) + 1} z‖ ≤ Real.exp ‖z‖ / n.factorial := by
  have hg := (NormedSpace.expSeries_div_hasSum_exp ‖z‖).div_const (n.factorial : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at hg
  refine (hasSum_regularizedHGFun_zero_singleton _ z).norm_le_of_bounded hg fun k => ?_
  rw [show (n : ℂ) + 1 + k = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
    norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_div]
  gcongr
  omega

/-- A bound for the Bessel functions of natural order. -/
theorem norm_besselJ_natCast_le (n : ℕ) (x : ℂ) :
    ‖besselJ n x‖ ≤ Real.exp (‖x‖ ^ 2 / 4) * ((‖x‖ / 2) ^ n / n.factorial) := by
  simp only [besselJ_def, cpow_natCast]
  rw [ norm_mul, norm_pow, norm_div, RCLike.norm_ofNat]
  have h := norm_regularizedHGFun_natCast_add_one_le n (-(x / 2) ^ 2)
  rw [norm_neg, norm_pow, norm_div, RCLike.norm_ofNat] at h
  calc (‖x‖ / 2) ^ n * ‖regularizedHGFun 0 {(n : ℂ) + 1} (-(x / 2) ^ 2)‖
      ≤ (‖x‖ / 2) ^ n * (Real.exp ((‖x‖ / 2) ^ 2) / n.factorial) := by gcongr
    _ = _ := by rw [div_pow]; ring_nf

/-- A bound for the Bessel functions of integer order. -/
theorem norm_besselJ_intCast_le (m : ℤ) (x : ℂ) :
    ‖besselJ m x‖ ≤ Real.exp (‖x‖ ^ 2 / 4) * ((‖x‖ / 2) ^ m.natAbs / m.natAbs.factorial) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using norm_besselJ_natCast_le k x
  · rw [show ((-(k : ℤ) : ℤ) : ℂ) = -((k : ℤ) : ℂ) by push_cast; ring, besselJ_neg_int,
      norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
    simpa using norm_besselJ_natCast_le k x

/-- The regularized hypergeometric series sums to its function throughout its convergence ball. -/
theorem hasSum_regularizedHGFun_of_mem_eball {a b : Multiset ℂ} {z : ℂ}
    (hz : z ∈ Metric.eball 0 (regularizedHGFunSeries a b).radius) :
    HasSum (fun n : ℕ => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have h := (regularizedHGFunSeries a b).hasSum hz
  show HasSum _ ((regularizedHGFunSeries a b).sum z)
  convert h using 1
  funext n
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- In the entire case the regularized hypergeometric series converges at every point. -/
theorem hasSum_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n : ℕ => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) :=
  hasSum_regularizedHGFun_of_mem_eball (by simp [radius_regularizedHGFunSeries_eq_top h])

/-- The modified Bessel function of the first kind,
`Iₐ(x) = (x/2)^a ₀F₁(a + 1; (x/2)²)`, with the regularized `₀F₁`. -/
def besselI (a x : ℂ) : ℂ := (x / 2) ^ a * regularizedHGFun 0 {a + 1} ((x / 2) ^ 2)

/-- `J_a(i x) = iᵃ I_a(x)` for integer orders. -/
theorem besselJ_intCast_I_mul (a : ℤ) (x : ℂ) :
    besselJ a (I * x) = I ^ a * besselI a x := by
  rw [besselJ_def, besselI]
  simp only [cpow_intCast]
  rw [show I * x / 2 = I * (x / 2) by ring, mul_zpow, mul_pow, I_sq]
  ring_nf

/-- `I₋ₐ = Iₐ` for integer orders. -/
theorem besselI_neg_int (a : ℤ) (x : ℂ) : besselI (-a) x = besselI a x := by
  have h1 := besselJ_intCast_I_mul (-a) x
  push_cast at h1
  rw [besselJ_neg_int, besselJ_intCast_I_mul, zpow_neg] at h1
  have hI : (I ^ a : ℂ) ≠ 0 := zpow_ne_zero _ I_ne_zero
  rw [(inv_mul_eq_iff_eq_mul₀ hI).mp h1.symm, ← mul_assoc, ← mul_assoc, ← mul_zpow, ← mul_zpow,
    show I * -1 * I = 1 by rw [mul_neg_one, neg_mul, I_mul_I, neg_neg], one_zpow, one_mul]

end Complex
