/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthogonality of the cosines on `[0, π]`

## Main results

* `integral_cos_intCast_mul`: `∫₀^π cos (mθ) dθ = π δ_{m0}` for integers `m`.
* `integral_cos_mul_cos`: `∫₀^π cos (kθ) cos (nθ) dθ` is `π` if `k = n = 0`, `π/2` if
  `k = n ≠ 0`, and `0` otherwise.
-/

@[expose] public noncomputable section

open Real

/-- `∫₀^π cos (mθ) dθ` for an integer `m`. -/
theorem integral_cos_intCast_mul (m : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (m * θ) = if m = 0 then π else 0 := by
  split_ifs with hm
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos, mul_zero,
      Real.sin_zero, sub_zero, Real.sin_int_mul_pi, smul_zero]

/-- Orthogonality of the cosines on `[0, π]`. -/
theorem integral_cos_mul_cos (k n : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (k * θ) * Real.cos (n * θ) =
      if k = n then (if n = 0 then π else π / 2) else 0 := by
  have hprod : ∀ θ : ℝ, Real.cos (k * θ) * Real.cos (n * θ) =
      (Real.cos (((k : ℤ) - n : ℤ) * θ) + Real.cos (((k : ℤ) + n : ℤ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [hprod]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_intCast_mul, integral_cos_intCast_mul]
  by_cases hkn : k = n
  · subst hkn
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  · have h1 : ((k : ℤ) - n) ≠ 0 := by omega
    have h2 : ((k : ℤ) + n) ≠ 0 ∨ (k = 0 ∧ n = 0) := by omega
    rcases h2 with h2 | h2
    · simp [h1, h2, hkn]
    · omega
