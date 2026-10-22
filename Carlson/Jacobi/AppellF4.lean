/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF4
public import Carlson.Jacobi.EndpointBridge
public import Pochhammer.Gamma

/-!
# Appell F₄ as a Jacobi series

Carlson (1975), equation (2.2), and Carlson (1977), Exercise 7.1-13.
The total-degree coefficients are shifted two-node R-polynomial numerators.
This division-free form holds at every complex parameter. When the monic Jacobi
normalization is nondegenerate, it gives the corresponding Jacobi series.
Absolute convergence is supplied by the full square-root region for F₄.
-/

open Complex Polynomial Set Finset
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Reflection of a Pochhammer factor with a prescribed complementary degree. -/
private theorem pochhammer_reflect_complement (c : ℂ) (m n : ℕ) :
    (ascPochhammer ℂ m).eval (1 - c - (m + n : ℕ)) =
      (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (c + n) := by
  rw [show 1 - c - (m + n : ℕ) = 1 - (c + n) - m by push_cast; ring]
  exact ascPochhammer_eval_reflect (c + n) m

/-- A reciprocal-Gamma shift with a prescribed complementary degree. -/
private theorem inv_Gamma_add_complement (c : ℂ) (m n : ℕ) :
    (Gamma (c + m))⁻¹ =
      (ascPochhammer ℂ n).eval (c + m) * (Gamma (c + (m + n : ℕ)))⁻¹ := by
  simpa only [Nat.cast_add, add_assoc] using
    one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (c + m) n

/-- **Carlson (1975), (2.2), coefficient identity without division by parameter polynomials.**
Every homogeneous `F₄` coefficient is a shifted two-node R-polynomial numerator. -/
theorem regularizedAppellF4_antidiagonal_eq_numerator (a b c d x y : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, regularizedAppellF4Coeff a b c d p * x ^ p.1 * y ^ p.2 =
      ((-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
        ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))) *
        carlsonRPolynomialNumerator₂ N (1 - d - N) (1 - c - N) x y := by
  rw [carlsonRPolynomialNumerator₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  rw [regularizedAppellF4Coeff_eq, ← hdeg, Nat.cast_add_choose ℂ,
    pochhammer_reflect_complement]
  have hreflect : (ascPochhammer ℂ p.2).eval (1 - c - (p.1 + p.2 : ℕ)) =
      (-1 : ℂ) ^ p.2 * (ascPochhammer ℂ p.2).eval (c + p.1) := by
    simpa only [Nat.add_comm p.2 p.1] using pochhammer_reflect_complement c p.2 p.1
  rw [hreflect]
  have hgc := inv_Gamma_add_complement c p.1 p.2
  have hgd : (Gamma (d + p.2))⁻¹ = (ascPochhammer ℂ p.1).eval (d + p.2) *
      (Gamma (d + (p.1 + p.2 : ℕ)))⁻¹ := by
    simpa only [Nat.add_comm p.2 p.1] using inv_Gamma_add_complement d p.2 p.1
  have hsign : (-1 : ℂ) ^ (p.1 + p.2) * (-1) ^ p.1 * (-1) ^ p.2 = 1 := by
    rw [mul_assoc, ← pow_add, ← mul_pow]
    norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [hgc, hgd]
  have hfac : ((p.1 + p.2).factorial : ℂ) * ((p.1 + p.2).factorial : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero)
  let B := (ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ (p.1 + p.2)).eval b *
    (ascPochhammer ℂ p.1).eval (d + p.2) * (ascPochhammer ℂ p.2).eval (c + p.1) *
    (p.1.factorial : ℂ)⁻¹ * (p.2.factorial : ℂ)⁻¹ *
    (Gamma (c + (p.1 + p.2 : ℕ)))⁻¹ * (Gamma (d + (p.1 + p.2 : ℕ)))⁻¹ *
    x ^ p.1 * y ^ p.2
  linear_combination -B * hsign -
    B * ((-1 : ℂ) ^ (p.1 + p.2) * (-1) ^ p.1 * (-1) ^ p.2) * hfac

/-- **Carlson Exercise 7.1-13, regularized numerator form.** The R-polynomial series
represents `F₄` on its full convergence region without any parameter exclusions. -/
theorem hasSum_regularizedAppellF4_RPolynomial (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun N =>
      ((-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
        ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))) *
        carlsonRPolynomialNumerator₂ N (1 - d - N) (1 - c - N) x y)
      (regularizedAppellF4 a b c d x y) := by
  simpa only [regularizedAppellF4_antidiagonal_eq_numerator] using
    hasSum_regularizedAppellF4_antidiagonal a b c d hxy

/-- The shifted numerator is the monic Jacobi polynomial times its normalization factor. -/
private theorem appellF4_numerator_eq_jacobiOn (c d x y : ℂ) (N : ℕ)
    (hP : (ascPochhammer ℂ N).eval (c + d + N - 1) ≠ 0) :
    carlsonRPolynomialNumerator₂ N (1 - d - N) (1 - c - N) x y =
      (-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval (c + d + N - 1) *
        (jacobiOn (d - 1) (c - 1) (-x) (-y) N).eval 0 := by
  have hparam : (d - 1) + (c - 1) + N + 1 = c + d + N - 1 := by ring
  have h := eval_jacobiOn_eq_numerator (d - 1) (c - 1) (-x) (-y) 0 N (by rw [hparam]; exact hP)
  have hd : -(d - 1) - (c - 1) - 2 * N = 1 - (c + d + N - 1) - N := by ring
  rw [hd, ascPochhammer_eval_reflect] at h
  simp only [zero_sub, neg_neg] at h
  have hnodes : -(d - 1) - N = 1 - d - N ∧ -(c - 1) - N = 1 - c - N := by
    constructor <;> ring
  rw [hnodes.1, hnodes.2] at h
  have hden : (-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval (c + d + N - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hP
  rw [eq_div_iff hden] at h
  rw [← h]
  ring

/-- **Carlson (1975), (2.2); Exercise 7.1-13.** The regularized Jacobi series.
The explicit exclusion concerns only the monic Jacobi normalization. -/
theorem hasSum_regularizedAppellF4_jacobiOn (a b c d : ℂ)
    (hP : ∀ N : ℕ, (ascPochhammer ℂ N).eval (c + d + N - 1) ≠ 0)
    {x y : ℂ} (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun N =>
      ((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b *
        (ascPochhammer ℂ N).eval (c + d + N - 1) /
        ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))) *
        (jacobiOn (d - 1) (c - 1) (-x) (-y) N).eval 0)
      (regularizedAppellF4 a b c d x y) := by
  convert hasSum_regularizedAppellF4_RPolynomial a b c d hxy using 1
  funext N
  rw [appellF4_numerator_eq_jacobiOn c d x y N (hP N)]
  have hs : (-1 : ℂ) ^ N * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  linear_combination
    -(((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b *
      (ascPochhammer ℂ N).eval (c + d + N - 1) /
      ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))) *
      (jacobiOn (d - 1) (c - 1) (-x) (-y) N).eval 0) * hs

/-- The ordinary Jacobi series for `F₄`, with both denominator parameters away from poles
and the monic Jacobi normalization nondegenerate. -/
theorem hasSum_appellF4_jacobiOn (a b c d : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hd : ∀ k : ℕ, d ≠ -(k : ℂ))
    (hP : ∀ N : ℕ, (ascPochhammer ℂ N).eval (c + d + N - 1) ≠ 0)
    {x y : ℂ} (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun N =>
      ((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b *
        (ascPochhammer ℂ N).eval (c + d + N - 1) /
        ((N.factorial : ℂ) * (ascPochhammer ℂ N).eval c * (ascPochhammer ℂ N).eval d)) *
        (jacobiOn (d - 1) (c - 1) (-x) (-y) N).eval 0)
      (appellF4 a b c d x y) := by
  rw [appellF4]
  convert (hasSum_regularizedAppellF4_jacobiOn a b c d hP hxy).mul_left (Gamma c * Gamma d) using 1
  funext N
  rw [← Gamma_add_nat_div_Gamma_eq c hc, ← Gamma_add_nat_div_Gamma_eq d hd]
  have hG (s : ℂ) (hs : ∀ k : ℕ, s ≠ -(k : ℂ)) : Gamma (s + N) ≠ 0 :=
    Gamma_ne_zero (fun k hk => hs (k + N) (by push_cast at hk ⊢; linear_combination hk))
  field_simp [Gamma_ne_zero hc, Gamma_ne_zero hd, hG c hc, hG d hd]

end Carlson.TwoVariable
