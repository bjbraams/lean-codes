/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic

/-!
# Elementary power identities and bounds

Small facts about powers and real parts that are used repeatedly in the Carlson library.

## Main results

* `Real.rpow_le_rpow_add_rpow`: a power between two others is bounded by their sum.
* `Complex.ofReal_cpow_eq_exp`: a positive real base to a complex power as an exponential.
* `Complex.ofReal_exp_cpow`: the special case of a real exponential base.
* `Complex.re_one_sub_pos`: `1 - v` has positive real part when `‖v‖ < 1`.
-/

public section

namespace Real

/-- A power between two others is bounded by their sum on the positive axis. -/
theorem rpow_le_rpow_add_rpow {x c₁ c c₂ : ℝ} (hx : 0 < x) (h₁ : c₁ ≤ c) (h₂ : c ≤ c₂) :
    x ^ c ≤ x ^ c₁ + x ^ c₂ := by
  rcases le_total x 1 with h | h
  · have := rpow_le_rpow_of_exponent_ge hx h h₁
    linarith [rpow_nonneg hx.le c₂]
  · have := rpow_le_rpow_of_exponent_le h h₂
    linarith [rpow_nonneg hx.le c₁]

end Real

namespace Complex

/-- A positive real base to a complex power, as an exponential. -/
theorem ofReal_cpow_eq_exp {q : ℝ} (hq : 0 < q) (c : ℂ) :
    ((q : ℝ) : ℂ) ^ c = exp (Real.log q * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← ofReal_log hq.le]

/-- A real exponential raised to a complex power. -/
theorem ofReal_exp_cpow (t : ℝ) (a : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ a = exp (a * t) := by
  rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp, mul_comm]

/-- A number `1 - v` with `‖v‖ < 1` has positive real part. -/
theorem re_one_sub_pos {v : ℂ} (hv : ‖v‖ < 1) : 0 < (1 - v).re := by
  have := re_le_norm v
  simp only [sub_re, one_re]
  linarith

end Complex
