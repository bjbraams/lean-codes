/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The Laplace transform of `(1 - cos t)ⁿ`

Expanding `(1 - cos t)ⁿ` in exponentials and integrating term by term over `(2mπ, ∞)` reduces
the integral to the alternating partial-fraction sum `∑ⱼ (-1)ʲ (N choose j)/(y + j)`. That sum is
`N!/∏(y + j)`, which at `y = ix - n` gives Carlson's closed form.

## Main results

* `Complex.altBinomialInvSum_eq`: `∑_{j ≤ N} (-1)ʲ (N choose j)/(y + j) = N!/∏_{j ≤ N} (y + j)`.
* `Complex.integral_exp_mul_one_sub_cos_pow`: Carlson's Exercise 6.6-17,
  `∫_{2mπ}^∞ e^{-xt} (1 - cos t)ⁿ dt = 2⁻ⁿ (2n)! e^{-2mπx}/(x (x² + 1) ⋯ (x² + n²))`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Exercise 6.6-17.
-/

open Finset MeasureTheory Set

@[expose] public noncomputable section

namespace Complex

/-- The alternating binomial sum `∑_{j ≤ N} (-1)ʲ (N choose j)/(y + j)`. -/
def altBinomialInvSum (N : ℕ) (y : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (-1 : ℂ) ^ j * (N.choose j : ℂ) / (y + j)

/-- Pascal's rule for the alternating sums: `f_{N+1}(y) = f_N(y) - f_N(y + 1)`. -/
theorem altBinomialInvSum_succ (N : ℕ) (y : ℂ) :
    altBinomialInvSum (N + 1) y = altBinomialInvSum N y - altBinomialInvSum N (y + 1) := by
  unfold altBinomialInvSum
  rw [sum_range_succ' _ (N + 1)]
  simp_rw [Nat.choose_succ_succ, Nat.cast_add, mul_add, add_div, sum_add_distrib]
  have hA : ∑ j ∈ range (N + 1), (-1 : ℂ) ^ (j + 1) * (N.choose j : ℂ) / (y + (j + 1 : ℕ)) =
      -∑ j ∈ range (N + 1), (-1 : ℂ) ^ j * (N.choose j : ℂ) / (y + 1 + j) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j _ ↦ by push_cast; ring_nf
  have hB : ∑ j ∈ range (N + 1), (-1 : ℂ) ^ (j + 1) * (N.choose (j + 1) : ℂ) /
        (y + (j + 1 : ℕ)) + (-1 : ℂ) ^ 0 * ((N + 1).choose 0 : ℂ) / (y + (0 : ℕ)) =
      ∑ j ∈ range (N + 1), (-1 : ℂ) ^ j * (N.choose j : ℂ) / (y + j) := by
    rw [sum_range_succ (fun j ↦ (-1 : ℂ) ^ (j + 1) * (N.choose (j + 1) : ℂ) /
      (y + (j + 1 : ℕ))), Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_div, add_zero,
      sum_range_succ' (fun j ↦ (-1 : ℂ) ^ j * (N.choose j : ℂ) / (y + j))]
    simp
  simp only [Nat.succ_eq_add_one] at *
  push_cast at hA hB ⊢
  linear_combination hA + hB

/-- The rising product `∏_{j ≤ N} (y + j)`. -/
theorem prod_range_add_succ_left (N : ℕ) (y : ℂ) :
    ∏ j ∈ range (N + 2), (y + j) = y * ∏ j ∈ range (N + 1), (y + 1 + j) := by
  rw [prod_range_succ', mul_comm]
  congr 1
  · simp
  · exact prod_congr rfl fun j _ ↦ by push_cast; ring

/-- **Partial fractions for the reciprocal rising product**:
`∑_{j ≤ N} (-1)ʲ (N choose j)/(y + j) = N!/∏_{j ≤ N} (y + j)` when no `y + j` vanishes. -/
theorem altBinomialInvSum_eq (N : ℕ) {y : ℂ} (hy : ∀ j ≤ N, y + j ≠ 0) :
    altBinomialInvSum N y = (N.factorial : ℂ) / ∏ j ∈ range (N + 1), (y + j) := by
  induction N generalizing y with
  | zero => simp [altBinomialInvSum]
  | succ N ih =>
    have hy0 : y ≠ 0 := by simpa using hy 0 (Nat.zero_le _)
    have hy1 : ∀ j ≤ N, y + 1 + j ≠ 0 := fun j hj ↦ by
      have := hy (j + 1) (by omega); push_cast at this
      rwa [show y + 1 + j = y + (j + 1) by ring]
    have hyN : ∀ j ≤ N, y + j ≠ 0 := fun j hj ↦ hy j (by omega)
    have hlast : y + ((N + 1 : ℕ) : ℂ) ≠ 0 := hy (N + 1) le_rfl
    have hP0 : ∏ j ∈ range (N + 1), (y + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj ↦ hyN j (Nat.lt_succ_iff.mp (mem_range.mp hj))
    have hP1 : ∏ j ∈ range (N + 1), (y + 1 + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj ↦ hy1 j (Nat.lt_succ_iff.mp (mem_range.mp hj))
    have hR : ∏ j ∈ range (N + 2), (y + j) = (∏ j ∈ range (N + 1), (y + j)) * (y + (N + 1 : ℕ)) :=
      prod_range_succ _ _
    have hL := prod_range_add_succ_left N y
    rw [altBinomialInvSum_succ, ih hyN, ih hy1]
    rw [show N + 1 + 1 = N + 2 by ring]
    have key : (N.factorial : ℂ) / ∏ j ∈ range (N + 1), (y + j) -
        (N.factorial : ℂ) / ∏ j ∈ range (N + 1), (y + 1 + j) =
        (N.factorial : ℂ) * ((y + (N + 1 : ℕ)) - y) / ∏ j ∈ range (N + 2), (y + j) := by
      rw [mul_sub, sub_div]
      congr 1
      · rw [hR, mul_div_mul_right _ _ hlast]
      · rw [hL, mul_comm y, mul_div_mul_right _ _ hy0]
    rw [key, Nat.factorial_succ]
    push_cast
    ring_nf

/-- The exponential expansion
`(1 - cos t)ⁿ = (-1/2)ⁿ ∑_{j ≤ 2n} (-1)ʲ (2n choose j) e^{i(j - n)t}`. -/
theorem one_sub_cos_pow_eq_sum (n : ℕ) (t : ℂ) :
    (1 - cos t) ^ n = (-1 / 2 : ℂ) ^ n * ∑ j ∈ range (2 * n + 1),
      (-1 : ℂ) ^ j * ((2 * n).choose j : ℂ) * exp (((j : ℂ) - n) * t * I) := by
  have h1 : 1 - cos t = -1 / 2 * exp (-(t * I)) * (exp (t * I) - 1) ^ 2 := by
    rw [cos]
    have : exp (-(t * I)) * exp (t * I) = 1 := by rw [← exp_add]; simp
    have h2 : exp (-t * I) = exp (-(t * I)) := by ring_nf
    rw [h2]
    linear_combination (exp (t * I) / 2 - 1) * this
  rw [h1, mul_pow, mul_pow, ← pow_mul, sub_eq_add_neg, add_pow, mul_sum, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ 2 * n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hsign : (-1 : ℂ) ^ (2 * n - j) = (-1) ^ j := by
    rw [← mul_left_inj' (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero)), ← pow_add,
      Nat.sub_add_cancel hj', pow_mul, ← pow_add, ← two_mul, pow_mul]; norm_num
  have he : exp (-(t * I)) ^ n * exp (t * I) ^ j = exp (((j : ℂ) - n) * t * I) := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]; ring_nf
  rw [hsign, ← he]
  ring

/-- The rising product at `y = ix - n` over `2n + 1` factors:
`∏_{j ≤ 2n} (ix - n + j) = ix (-1)ⁿ ∏_{k < n} (x² + (k + 1)²)`. -/
theorem prod_range_I_mul_sub (n : ℕ) (x : ℂ) :
    ∏ j ∈ range (2 * n + 1), (I * x - n + j) =
      I * x * (-1) ^ n * ∏ k ∈ range n, (x ^ 2 + ((k : ℂ) + 1) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, prod_range_add_succ_left,
      prod_range_succ]
    have hshift : ∏ j ∈ range (2 * n + 1), (I * x - ((n + 1 : ℕ) : ℂ) + 1 + j) =
        ∏ j ∈ range (2 * n + 1), (I * x - n + j) :=
      prod_congr rfl fun j _ ↦ by push_cast; ring
    rw [hshift, ih, prod_range_succ]
    push_cast
    linear_combination (I * x * (-1) ^ n * (∏ k ∈ range n, (x ^ 2 + ((k : ℂ) + 1) ^ 2)) * x ^ 2) *
      I_sq

/-- **Exercise 6.6-17 of Carlson (1977)**: for `m ∈ ℤ`, `n ∈ ℕ` and `re x > 0`,
`∫_{2mπ}^∞ e^{-xt} (1 - cos t)ⁿ dt = 2⁻ⁿ (2n)! e^{-2mπx}/(x (x² + 1) ⋯ (x² + n²))`. -/
theorem integral_exp_mul_one_sub_cos_pow (n : ℕ) (m : ℤ) {x : ℂ} (hx : 0 < x.re) :
    ∫ t : ℝ in Ioi (2 * m * Real.pi), exp (-x * t) * (1 - cos t) ^ n =
      ((2 * n).factorial : ℂ) * exp (-2 * m * Real.pi * x) /
        (2 ^ n * x * ∏ k ∈ range n, (x ^ 2 + ((k : ℂ) + 1) ^ 2)) := by
  set c : ℝ := 2 * m * Real.pi
  set a : ℕ → ℂ := fun j ↦ -x + ((j : ℂ) - n) * I
  have ha : ∀ j, (a j).re < 0 := fun j ↦ by simp [a]; linarith
  have ha0 : ∀ j, a j ≠ 0 := fun j h ↦ by have := ha j; rw [h] at this; simp at this
  have hpt : ∀ t : ℝ, exp (-x * t) * (1 - cos t) ^ n = ∑ j ∈ range (2 * n + 1),
      (-1 / 2 : ℂ) ^ n * ((-1 : ℂ) ^ j * ((2 * n).choose j : ℂ)) * exp (a j * t) := fun t ↦ by
    rw [one_sub_cos_pow_eq_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [show a j * t = -x * t + ((j : ℂ) - n) * t * I by simp only [a]; ring, exp_add]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ ↦ (integrableOn_exp_mul_complex_Ioi (ha j) c).const_mul _]
  simp_rw [integral_const_mul, integral_exp_mul_complex_Ioi (ha _)]
  -- the boundary values
  have hexp : ∀ j : ℕ, exp (a j * c) = exp (-2 * m * Real.pi * x) := fun j ↦ by
    have hk : exp (((((j : ℤ) - n) * m : ℤ) : ℂ) * (2 * Real.pi * I)) = 1 :=
      exp_int_mul_two_pi_mul_I _
    rw [show a j * c = -2 * m * Real.pi * x + (((((j : ℤ) - n) * m : ℤ) : ℂ) * (2 * Real.pi * I))
      by simp only [a, c]; push_cast; ring, exp_add, hk, mul_one]
  simp_rw [hexp]
  -- the partial-fraction sum
  set y : ℂ := I * x - n
  have hy : ∀ j ≤ 2 * n, y + j ≠ 0 := fun j _ h ↦ by
    have := congrArg im h; simp [y] at this; linarith
  have hfrac : ∀ j : ℕ, -1 / a j = I / (y + j) := fun j ↦ by
    have hyj : y + j ≠ 0 := fun h ↦ by
      have := congrArg im h; simp [y] at this; linarith
    rw [div_eq_div_iff (ha0 j) hyj]
    simp only [a, y]; ring_nf; rw [I_sq]; ring
  have hsum : ∑ j ∈ range (2 * n + 1), (-1 / 2 : ℂ) ^ n * ((-1 : ℂ) ^ j * ((2 * n).choose j : ℂ)) *
      (-exp (-2 * m * Real.pi * x) / a j) = (-1 / 2 : ℂ) ^ n * exp (-2 * m * Real.pi * x) * I *
        altBinomialInvSum (2 * n) y := by
    unfold altBinomialInvSum
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [neg_div, ← neg_div, show -exp (-2 * m * Real.pi * x) / a j =
      exp (-2 * m * Real.pi * x) * (-1 / a j) by ring, hfrac]
    ring
  rw [hsum, altBinomialInvSum_eq _ hy, show y = I * x - n from rfl, prod_range_I_mul_sub]
  have hx0 : x ≠ 0 := fun h ↦ by rw [h] at hx; simp at hx
  have hP : ∏ k ∈ range n, (x ^ 2 + ((k : ℂ) + 1) ^ 2) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun k _ h ↦ ?_
    have h' : (x - ((k : ℂ) + 1) * I) * (x + ((k : ℂ) + 1) * I) = 0 := by
      rw [← h]; ring_nf; rw [I_sq]; ring
    rcases mul_eq_zero.mp h' with h'' | h''
    · have := congrArg re h''; simp at this; linarith
    · have := congrArg re h''; simp at this; linarith
  field_simp
  have h2 : (-(1 / 2) : ℂ) ^ n * 2 ^ n = (-1) ^ n := by rw [← mul_pow]; norm_num
  linear_combination ((2 * n).factorial : ℂ) * h2

end Complex
