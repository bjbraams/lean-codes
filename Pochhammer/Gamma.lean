/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Pochhammer.Identities

/-!
# Pochhammer identities for the Gamma function

This file is a temporary home for identities connecting Mathlib's Gamma function and ascending
Pochhammer polynomials.  The reciprocal formulation remains valid at the poles of `Gamma`.
-/

open Finset Polynomial

public noncomputable section

namespace Complex

/-- The natural-shift recurrence for reciprocal Gamma, valid at every complex argument.  This is
the pole-free counterpart of expressing an ascending Pochhammer symbol as a quotient of Gamma
functions. -/
theorem one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (z : ℂ) (n : ℕ) :
    (Gamma z)⁻¹ = (ascPochhammer ℂ n).eval z * (Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
      simp only [Nat.cast_succ, ascPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
      ring_nf

/-- Reciprocal Gamma after a natural shift, as a product of reciprocals, provided none of the
intermediate points is a non-positive integer. -/
theorem inv_Gamma_add_nat_of_ne_zero {s : ℂ} {n : ℕ}
    (h : ∀ k < n, s + k ≠ 0) :
    (Gamma (s + n))⁻¹ = (Gamma s)⁻¹ * ∏ k ∈ range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : s + n ≠ 0 := h n n.lt_succ_self
    have ih' := ih fun k hk => h k (lt_trans hk n.lt_succ_self)
    have hrec : (Gamma (s + n + 1))⁻¹ = (s + n)⁻¹ * (Gamma (s + n))⁻¹ := by
      have hz := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n)
      calc
        (Gamma (s + n + 1))⁻¹ =
            (s + n)⁻¹ * ((s + n) * (Gamma (s + n + 1))⁻¹) := by
          rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
        _ = (s + n)⁻¹ * (Gamma (s + n))⁻¹ := by rw [← hz]
    calc
      (Gamma (s + (n + 1 : ℕ)))⁻¹ = (Gamma (s + n + 1))⁻¹ := by
        rw [Nat.cast_succ, add_assoc]
      _ = (s + n)⁻¹ * (Gamma (s + n))⁻¹ := hrec
      _ = (s + n)⁻¹ * ((Gamma s)⁻¹ * ∏ k ∈ range n, (s + k)⁻¹) := by rw [ih']
      _ = (Gamma s)⁻¹ * ((∏ k ∈ range n, (s + k)⁻¹) * (s + n)⁻¹) := by ring
      _ = (Gamma s)⁻¹ * ∏ k ∈ range (n + 1), (s + k)⁻¹ := by rw [prod_range_succ]

/-- Splitting an ascending Pochhammer symbol and reflecting the remaining factors.

The multiplicative form remains valid when one of the Pochhammer factors vanishes, unlike the
corresponding quotient identity. -/
theorem ascPochhammer_eval_split_reflection (c : ℂ) {m n : ℕ} (hmn : m ≤ n) :
    (ascPochhammer ℂ n).eval c =
      (-1 : ℂ) ^ (n - m) * (ascPochhammer ℂ m).eval c *
        (ascPochhammer ℂ (n - m)).eval (1 - c - n) :=
  ascPochhammer_eval_split_reflect c hmn

end Complex

namespace Real

/-- A quotient of gamma values separated by a natural number equals the corresponding rising
factorial. -/
theorem gamma_add_nat_div_gamma_eq_ascPochhammer
    (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) / Gamma x = (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [ne_of_gt (Gamma_pos_of_pos hx)]
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show x + ((n : ℝ) + 1) = (x + n) + 1 by ring]
      rw [Gamma_add_one (by positivity : x + (n : ℝ) ≠ 0)]
      rw [ascPochhammer_succ_eval]
      rw [mul_div_assoc, ih]
      ring

end Real

end
