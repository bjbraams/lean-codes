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

Reciprocal Gamma identities express natural shifts using ascending Pochhammer polynomials and
remain meaningful at Gamma poles. The file also defines Gamma-regular parameters, proves
stability under positive integral shifts, and establishes factorial decay for reciprocal Gamma
along natural shifts.

## Main results

* `Complex.one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat`: The natural-shift
  recurrence for reciprocal Gamma, valid at every complex argument. This is the pole-free
  counterpart of expressing an ascending Pochhammer symbol as a quotient of Gamma functions.
* `Complex.IsCarlsonGammaRegular.ascPochhammer_ne_zero`: No ascending Pochhammer factor vanishes
  at a Gamma-regular argument.
* `Complex.norm_invGamma_add_nat_le`: Reciprocal Gamma gains at least factorial decay under
  positive integer shifts in the half-plane `1 ≤ re s`.
* `Complex.exists_uniform_norm_invGamma_add_nat`: Reciprocal Gamma has uniform factorial decay
  after a common natural shift on any compact set of complex arguments.
* `Complex.exists_uniform_norm_invGamma_sum_add_nat`: Uniform factorial decay for reciprocal
  Gamma after sufficiently many shifts of the total parameter on a compact set.

## References

* `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`: formal background used by this module.
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
factors `s + k`, for `k < n`, is zero. -/
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

/-! ## Gamma regularity and decay under natural shifts

Gamma-regular parameters avoid the nonpositive integers. Positive integral shifts preserve
regularity, and reciprocal Gamma decays factorially along natural shifts.
-/

open Complex
@[expose] public noncomputable section
namespace Complex

/-- Carlson's set `U`: complex numbers that are not nonpositive integers, equivalently the
finite points at which the Gamma function has no pole. -/
def IsCarlsonGammaRegular (w : ℂ) : Prop :=
  ∀ n : ℕ, w ≠ -(n : ℂ)

/-- Positive integral shifts preserve Gamma regularity. -/
theorem IsCarlsonGammaRegular.add_nat {w : ℂ} (hw : IsCarlsonGammaRegular w) (m : ℕ) :
    IsCarlsonGammaRegular (w + m) := by
  intro n h
  apply hw (n + m)
  push_cast
  linear_combination h

/-- No ascending Pochhammer factor vanishes at a Gamma-regular argument. -/
theorem IsCarlsonGammaRegular.ascPochhammer_ne_zero {w : ℂ}
    (hw : IsCarlsonGammaRegular w) (n : ℕ) :
    (ascPochhammer ℂ n).eval w ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨m, _, hm⟩
  apply hw m
  linear_combination hm

/-- Reciprocal Gamma gains at least factorial decay under positive integer shifts
in the half-plane `1 ≤ re s`. -/
theorem norm_invGamma_add_nat_le {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖(Gamma (s + n))⁻¹‖ ≤ ‖(Gamma s)⁻¹‖ / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : s + n ≠ 0 := ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
    have hnorm : (n + 1 : ℝ) ≤ ‖s + n‖ := by
      have H := re_le_norm (s + n)
      simp only [add_re, natCast_re] at H
      linarith
    have hrec : (Gamma (s + n + 1))⁻¹ = (s + n)⁻¹ * (Gamma (s + n))⁻¹ := by
      rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n)]
      field_simp
    rw [Nat.cast_succ, ← add_assoc, hrec, norm_mul, norm_inv]
    calc
      ‖s + n‖⁻¹ * ‖(Gamma (s + n))⁻¹‖ ≤ (n + 1 : ℝ)⁻¹ * (‖(Gamma s)⁻¹‖ / n.factorial) := by
        exact mul_le_mul (inv_anti₀ (by positivity) hnorm) ih (norm_nonneg _) (by positivity)
      _ = _ := by
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_eq_mul_inv,
            mul_inv_rev]; ring

end Complex

namespace Complex
open Set
public noncomputable section

/-- Reciprocal Gamma has uniform factorial decay after a common natural shift on any
compact set of complex arguments. -/
theorem exists_uniform_norm_invGamma_add_nat {K : Set ℂ} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma (b + (n + m)))⁻¹‖ ≤ C / n.factorial := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_id.norm.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt (B + 1)
  have hre (b : ℂ) (hb : b ∈ K) : 1 ≤ (b + m).re := by
    have hbnd : ‖b‖ ≤ B := hB (mem_image_of_mem _ hb)
    have hr := neg_le_of_abs_le (abs_re_le_norm b)
    simp only [add_re, natCast_re]
    linarith
  have hc : Continuous (fun b : ℂ => (Gamma (b + m))⁻¹) :=
    differentiable_one_div_Gamma.continuous.comp (continuous_id.add continuous_const)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
  refine ⟨m, max C 0, le_max_right _ _, fun b hb n => ?_⟩
  have h := (Complex.norm_invGamma_add_nat_le (hre b hb) n).trans
    (div_le_div_of_nonneg_right ((hC (mem_image_of_mem _ hb)).trans (le_max_left C 0))
      (by positivity))
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

/-- Uniform factorial decay for reciprocal Gamma after sufficiently many shifts
of the total parameter on a compact set. -/
theorem exists_uniform_norm_invGamma_sum_add_nat {ι : Type*} [Fintype ι]
    {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma ((∑ i, b i) + (n + m)))⁻¹‖ ≤ C / n.factorial := by
  have hS : Continuous (fun b : ι → ℂ => ∑ i, b i) := by fun_prop
  obtain ⟨m, C, hC, hbound⟩ := exists_uniform_norm_invGamma_add_nat (hK.image hS)
  exact ⟨m, C, hC, fun b hb n => hbound _ (Set.mem_image_of_mem _ hb) n⟩

end
end Complex
