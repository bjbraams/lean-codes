/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.Gamma
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Growth of the reciprocal beta normalization under simultaneous shifts

The reciprocal beta factor `Γ(a+n+b+n)/(Γ(a+n)Γ(b+n))` has consecutive ratio
tending to four. This elementary consequence of the Gamma recurrence supplies
summable geometric majorants without invoking Stirling's formula. Arbitrary
complex parameters are allowed: sufficiently large integer shifts put both
parameters in the right half-plane.

## Main results

* `betaShiftNormalization_succ`: the rational recurrence in the convergence range.
* `tendsto_betaShiftNormalization_ratio`: the consecutive ratio tends to four.
* `summable_norm_betaShiftNormalization_mul_pow`: geometric damping with ratio
  less than one quarter gives an absolutely summable sequence.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7 (normalization of the second-kind Jacobi functions).
-/

@[expose] public noncomputable section
namespace Complex
open Filter
open scoped Topology

/-- The reciprocal beta factor after raising both parameters by the same integer.
Values at Gamma poles use the ordinary totalized Gamma function. -/
def betaShiftNormalization (a b : ℂ) (n : ℕ) : ℂ :=
  Gamma (a + n + (b + n)) / (Gamma (a + n) * Gamma (b + n))

/-- Every fixed complex parameter eventually enters the right half-plane under
nonnegative integer shifts. -/
theorem eventually_re_add_nat_pos (a : ℂ) : ∀ᶠ n : ℕ in atTop, 0 < (a + n).re := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  simp only [add_re, natCast_re]
  linarith

/-- Raising both beta parameters gives an explicit rational recurrence. -/
theorem betaShiftNormalization_succ (a b : ℂ) (n : ℕ)
    (ha : 0 < (a + n).re) (hb : 0 < (b + n).re) :
    betaShiftNormalization a b (n + 1) =
      ((a + b + 2 * n) * (a + b + 2 * n + 1) / ((a + n) * (b + n))) *
        betaShiftNormalization a b n := by
  have ha0 : a + n ≠ 0 := ne_zero_of_re_pos ha
  have hb0 : b + n ≠ 0 := ne_zero_of_re_pos hb
  have hab : 0 < (a + n + (b + n)).re := by simpa only [add_re] using add_pos ha hb
  have hab0 := ne_zero_of_re_pos hab
  have hab1 : a + n + (b + n) + 1 ≠ 0 :=
    ne_zero_of_re_pos (by simpa only [add_re, one_re] using add_pos hab zero_lt_one)
  unfold betaShiftNormalization
  rw [show a + (n + 1 : ℕ) = (a + n) + 1 by push_cast; ring,
    show b + (n + 1 : ℕ) = (b + n) + 1 by push_cast; ring,
    show a + n + 1 + (b + n + 1) = (a + n + (b + n) + 1) + 1 by ring,
    Gamma_add_one _ hab1, Gamma_add_one _ hab0, Gamma_add_one _ ha0, Gamma_add_one _ hb0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The rational factor in the simultaneous beta shift tends to four. -/
theorem tendsto_betaShiftNormalization_factor (a b : ℂ) :
    Tendsto (fun n : ℕ =>
      (a + b + 2 * n) * (a + b + 2 * n + 1) / ((a + n) * (b + n)))
      atTop (𝓝 4) := by
  have h (c : ℂ) := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) c
  have H := (((h (a + b)).add_const 2).mul ((h (a + b + 1)).add_const 2)).div
    (((h a).add_const 1).mul ((h b).add_const 1)) (by norm_num)
  norm_num only [zero_add, mul_one, one_mul, div_one, show (2 : ℂ) * 2 = 4 by norm_num] at H
  apply H.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  change (((a + b) / n + 2) * ((a + b + 1) / n + 2)) /
    ((a / n + 1) * (b / n + 1)) = _
  field_simp
  ring

/-- The reciprocal beta normalization has consecutive ratio tending to four,
including when the initial parameters lie outside the integral convergence range. -/
theorem tendsto_betaShiftNormalization_ratio (a b : ℂ) :
    Tendsto (fun n => betaShiftNormalization a b (n + 1) / betaShiftNormalization a b n)
      atTop (𝓝 4) := by
  apply (tendsto_betaShiftNormalization_factor a b).congr'
  filter_upwards [eventually_re_add_nat_pos a, eventually_re_add_nat_pos b] with n ha hb
  have hn : betaShiftNormalization a b n ≠ 0 := by
    apply div_ne_zero
    · exact Gamma_ne_zero_of_re_pos (by simpa only [add_re] using add_pos ha hb)
    · exact mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hb)
  rw [betaShiftNormalization_succ a b n ha hb, mul_div_cancel_right₀ _ hn]

/-- Damping the reciprocal beta normalization by a geometric factor of ratio
less than one quarter gives a summable sequence of norms. -/
theorem summable_norm_betaShiftNormalization_mul_pow (a b : ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ht4 : 4 * t < 1) :
    Summable (fun n => ‖betaShiftNormalization a b n‖ * t ^ n) := by
  have hr : Tendsto (fun n : ℕ =>
      ‖(a + b + 2 * n) * (a + b + 2 * n + 1) / ((a + n) * (b + n))‖ * t)
      atTop (𝓝 (4 * t)) := by
    simpa using (tendsto_betaShiftNormalization_factor a b).norm.mul_const t
  obtain ⟨q, hq, hq1⟩ := exists_between ht4
  apply summable_of_ratio_norm_eventually_le hq1
  filter_upwards [hr.eventually_le_const hq, eventually_re_add_nat_pos a,
    eventually_re_add_nat_pos b] with n hn ha hb
  simp only [Real.norm_eq_abs, abs_norm, abs_pow, abs_of_nonneg ht,
    betaShiftNormalization_succ a b n ha hb, norm_mul, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hn
    (mul_nonneg (norm_nonneg (betaShiftNormalization a b n)) (pow_nonneg ht n))]

end Complex
