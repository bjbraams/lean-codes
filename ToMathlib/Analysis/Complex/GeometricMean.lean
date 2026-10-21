/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The real part of a complex geometric mean

For two points in the right half-plane, the product of their principal square roots
has real part at least the geometric mean of their real parts. In particular, a common
positive lower bound on real parts is preserved by taking geometric means.
-/

open scoped ComplexOrder ComplexConjugate

@[expose] public noncomputable section

namespace Complex

/-- Principal square roots of right-half-plane numbers have positive real part. -/
private theorem re_half_pos {z : ℂ} (hz : 0 < z.re) : 0 < (z ^ (1 / 2 : ℂ)).re := by
  rw [show (1 / 2 : ℂ) = 2⁻¹ by norm_num, cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have := norm_nonneg z
  linarith

/-- For a right-half-plane argument, the imaginary part of its principal square root
is smaller in absolute value than its real part. -/
private theorem abs_im_half_lt_re {z : ℂ} (hz : 0 < z.re) :
    |(z ^ (1 / 2 : ℂ)).im| < (z ^ (1 / 2 : ℂ)).re := by
  have hsq : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    rw [one_div]
    exact cpow_nat_inv_pow z two_ne_zero
  have h := congrArg re hsq
  rw [sq, mul_re] at h
  have hr := re_half_pos hz
  nlinarith [sq_abs (z ^ (1 / 2 : ℂ)).im, abs_nonneg (z ^ (1 / 2 : ℂ)).im]

/-- The product of principal square roots of two right-half-plane arguments has
positive real part. -/
theorem re_cpow_half_mul_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    0 < (u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)).re := by
  have ha := abs_im_half_lt_re hu
  have hb := abs_im_half_lt_re hv
  have hr := re_half_pos hu
  have hs := re_half_pos hv
  have hprod : |(u ^ (1 / 2 : ℂ)).im| * |(v ^ (1 / 2 : ℂ)).im| <
      (u ^ (1 / 2 : ℂ)).re * (v ^ (1 / 2 : ℂ)).re := by
    calc
      _ ≤ |(u ^ (1 / 2 : ℂ)).im| * (v ^ (1 / 2 : ℂ)).re := by gcongr
      _ < _ := mul_lt_mul_of_pos_right ha hs
  rw [mul_re]
  have hle := le_abs_self ((u ^ (1 / 2 : ℂ)).im * (v ^ (1 / 2 : ℂ)).im)
  rw [abs_mul] at hle
  linarith

/-- The real part of a complex geometric mean dominates the geometric mean of the
real parts. Both square roots are principal. -/
theorem sqrt_re_mul_le_re_cpow_half_mul {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Real.sqrt (u.re * v.re) ≤ (u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)).re := by
  let w := u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)
  have hw : w ^ 2 = u * v := by
    rw [mul_pow]
    have hs (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
      rw [one_div]
      exact cpow_nat_inv_pow z two_ne_zero
    rw [hs, hs]
  have hn : ‖w‖ ^ 2 = ‖u‖ * ‖v‖ := by rw [← norm_pow, hw, norm_mul]
  have hs := congrArg re hw
  rw [sq] at hs
  rw [mul_re w w, mul_re u v] at hs
  have hc := (le_abs_self (u * conj v).re).trans (abs_re_le_norm (u * conj v))
  rw [norm_mul, norm_conj] at hc
  simp only [mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add] at hc
  have hn' := Complex.sq_norm w
  rw [normSq_apply] at hn'
  have hnonneg := (re_cpow_half_mul_pos hu hv).le
  change Real.sqrt (u.re * v.re) ≤ w.re
  apply Real.sqrt_le_iff.mpr ⟨hnonneg, ?_⟩
  nlinarith

end Complex
