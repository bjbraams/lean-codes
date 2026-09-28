/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A bound for `Γ(x)/|Γ(x + iy)|`

For `x ≥ 1/2`, `Γ(x)/|Γ(x + iy)| ≤ √(cosh (π y)) ≤ e^{π|y|/2}`. Termwise comparison of Euler's
limit sequences shows that the ratio is largest at `x = 1/2`, where the reflection formula gives
`|Γ(1/2 + iy)|² = π / cosh (π y)`.

## Main results

* `Complex.norm_Gamma_one_half_add_sq`: `|Γ(1/2 + iy)|² = π / cosh (π y)`.
* `Complex.Gamma_div_norm_Gamma_le`: `Γ(x)/|Γ(x + iy)| ≤ √(cosh (π y))` for `x ≥ 1/2`.
* `Complex.Gamma_div_norm_Gamma_le_exp`: the weaker bound `e^{π|y|/2}`.
-/

@[expose] public noncomputable section

open Filter Topology Real
open scoped ComplexConjugate

namespace Complex

/-- The norm of a term of Euler's limit sequence for `Γ`. -/
theorem norm_GammaSeq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq s n‖ = (n : ℝ) ^ s.re * n.factorial / ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_prod, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.norm_natCast]

/-- The finite form of the comparison of `Γ(x)/|Γ(x + iy)|` with its value at `x = 1/2`. -/
theorem norm_GammaSeq_mul_le {x y : ℝ} (hx : 1 / 2 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq (x : ℂ) n‖ * ‖GammaSeq (1 / 2 + y * I) n‖ ≤
      ‖GammaSeq (1 / 2 : ℂ) n‖ * ‖GammaSeq (x + y * I) n‖ := by
  rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn]
  have hre1 : ((x : ℂ)).re + (1 / 2 + y * I : ℂ).re = (1 / 2 : ℂ).re + ((x : ℂ) + y * I).re := by
    simp; ring
  have hpos : ∀ s : ℂ, 0 < s.re → 0 < ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := fun s hs =>
    Finset.prod_pos fun j _ => norm_pos_iff.mpr fun h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have h1 := hpos x (by simp; linarith)
  have h2 := hpos (1 / 2 + y * I) (by simp)
  have h3 := hpos (1 / 2) (by norm_num)
  have h4 := hpos (x + y * I) (by simp; linarith)
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (mul_pos h1 h2) (mul_pos h3 h4)]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℝ) ^ ((x : ℂ)).re * n.factorial *
      ((n : ℝ) ^ (1 / 2 + y * I : ℂ).re * n.factorial) =
      (n : ℝ) ^ (1 / 2 : ℂ).re * n.factorial * ((n : ℝ) ^ ((x : ℂ) + y * I).re * n.factorial) := by
    rw [show (n : ℝ) ^ ((x : ℂ)).re * n.factorial * ((n : ℝ) ^ (1 / 2 + y * I : ℂ).re *
        n.factorial) = (n : ℝ) ^ (((x : ℂ)).re + (1 / 2 + y * I : ℂ).re) * n.factorial ^ 2 by
      rw [Real.rpow_add hn']; ring, hre1, Real.rpow_add hn']; ring
  rw [hpow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  -- `(1/2 + j) |x + j + iy| ≤ (x + j) |1/2 + j + iy|`
  have ha : ‖(1 / 2 : ℂ) + j‖ = 1 / 2 + j := by
    rw [show (1 / 2 : ℂ) + j = ((1 / 2 + j : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hb : ‖(x : ℂ) + j‖ = x + j := by
    rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]
  have hc : ‖(1 / 2 + y * I : ℂ) + j‖ = Real.sqrt ((1 / 2 + j) ^ 2 + y ^ 2) := by
    rw [norm_def, normSq_apply]; congr 1; simp; ring
  have hd : ‖((x : ℂ) + y * I) + j‖ = Real.sqrt ((x + j) ^ 2 + y ^ 2) := by
    rw [norm_def, normSq_apply]; congr 1; simp; ring
  rw [ha, hb, hc, hd, mul_comm (x + (j : ℝ))]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hle : (1 / 2 + j) * Real.sqrt ((x + j) ^ 2 + y ^ 2) ≤
      (x + j) * Real.sqrt ((1 / 2 + j) ^ 2 + y ^ 2) := by
    have hA : 0 ≤ (1 / 2 + (j : ℝ)) * Real.sqrt ((x + j) ^ 2 + y ^ 2) := by positivity
    have hB : 0 ≤ (x + (j : ℝ)) * Real.sqrt ((1 / 2 + j) ^ 2 + y ^ 2) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    rw [← pow_le_pow_iff_left₀ hA hB two_ne_zero, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have : (1 / 2 + (j : ℝ)) ^ 2 ≤ (x + j) ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  linarith

/-- `|Γ(1/2 + iy)|² = π / cosh (π y)`. -/
theorem norm_Gamma_one_half_add_sq (y : ℝ) :
    ‖Gamma (1 / 2 + y * I)‖ ^ 2 = π / Real.cosh (π * y) := by
  have h := Gamma_mul_Gamma_one_sub (1 / 2 + y * I)
  have hc : (1 : ℂ) - (1 / 2 + y * I) = conj (1 / 2 + y * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [hc, Gamma_conj, mul_conj, show (π : ℂ) * (1 / 2 + y * I) = π / 2 + (π * y : ℝ) * I by
    push_cast; ring, sin_add, sin_pi_div_two, cos_pi_div_two, zero_mul, add_zero, one_mul,
    cos_mul_I, ← ofReal_cosh, ← ofReal_div] at h
  rw [← normSq_eq_norm_sq]
  exact_mod_cast h

/-- For `x ≥ 1/2`, `Γ(x) / |Γ(x + iy)| ≤ √(cosh (π y))`. -/
theorem Gamma_div_norm_Gamma_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    Real.Gamma x / ‖Gamma (x + y * I)‖ ≤ Real.sqrt (Real.cosh (π * y)) := by
  have hlim : ‖Gamma (x : ℂ)‖ * ‖Gamma (1 / 2 + y * I)‖ ≤
      ‖Gamma (1 / 2 : ℂ)‖ * ‖Gamma (x + y * I)‖ := by
    refine le_of_tendsto_of_tendsto (((GammaSeq_tendsto_Gamma _).norm).mul
      ((GammaSeq_tendsto_Gamma _).norm)) (((GammaSeq_tendsto_Gamma _).norm).mul
      ((GammaSeq_tendsto_Gamma _).norm)) ?_
    exact Filter.eventually_atTop.mpr ⟨1, fun n hn => norm_GammaSeq_mul_le hx (by omega)⟩
  have hGx : ‖Gamma (x : ℂ)‖ = Real.Gamma x := by
    rw [Gamma_ofReal, norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith)).le]
  have hGh : ‖Gamma (1 / 2 : ℂ)‖ = Real.sqrt π := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
      Real.Gamma_one_half_eq, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hch : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have hGy : ‖Gamma (1 / 2 + y * I)‖ = Real.sqrt (π / Real.cosh (π * y)) := by
    rw [← norm_Gamma_one_half_add_sq, Real.sqrt_sq (norm_nonneg _)]
  have hpos : 0 < ‖Gamma (x + y * I)‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by simp; linarith))
  rw [hGx, hGh, hGy] at hlim
  rw [div_le_iff₀ hpos]
  have hs : 0 < Real.sqrt (π / Real.cosh (π * y)) := Real.sqrt_pos.mpr (div_pos Real.pi_pos hch)
  have key : Real.sqrt π = Real.sqrt (Real.cosh (π * y)) * Real.sqrt (π / Real.cosh (π * y)) := by
    rw [← Real.sqrt_mul hch.le, mul_div_cancel₀ _ hch.ne']
  rw [key] at hlim
  nlinarith

/-- For `x ≥ 1/2`, `Γ(x) / |Γ(x + iy)| ≤ e^{π|y|/2}`. -/
theorem Gamma_div_norm_Gamma_le_exp {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    Real.Gamma x / ‖Gamma (x + y * I)‖ ≤ Real.exp (π * |y| / 2) := by
  refine (Gamma_div_norm_Gamma_le hx y).trans ?_
  rw [show π * |y| / 2 = (π * |y|) / 2 from rfl, Real.sqrt_le_left (Real.exp_pos _).le]
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (π * |y| / 2) = |π * y| by
    rw [abs_mul, abs_of_pos Real.pi_pos]; push_cast; ring]
  rw [Real.cosh_eq]
  rcases le_total 0 (π * y) with h | h
  · rw [abs_of_nonneg h]; nlinarith [Real.exp_le_exp.mpr (show -(π * y) ≤ π * y by linarith)]
  · rw [abs_of_nonpos h]; nlinarith [Real.exp_le_exp.mpr (show π * y ≤ -(π * y) by linarith)]

end Complex
