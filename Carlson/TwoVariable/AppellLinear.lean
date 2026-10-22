/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF1
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import ToMathlib.Analysis.SpecialFunctions.AppellLinear

/-!
# Carlson's linear transformation of Appell's first series

Carlson (1976), *The need for a new classification of double hypergeometric series*,
equation (4). Grouping both absolutely convergent double series by total degree reduces
the identity to the already proved division-free polynomial translation formula.
The proof does not need the exclusions used in the article to distinguish Horn orders.
-/

open Complex Polynomial Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- A binomial coefficient divided by the total factorial is the reciprocal
of the two component factorials. -/
private theorem choose_div_factorial (m n : ℕ) :
    ((m + n).choose m : ℂ) / (m + n).factorial =
      ((m.factorial : ℂ) * n.factorial)⁻¹ := by
  rw [Nat.cast_choose ℂ (Nat.le_add_right m n), Nat.add_sub_cancel_left]
  field_simp [Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero]

/-- The coefficient of degree `N` in the original Appell series is an
R-polynomial numerator times its common scalar factor. -/
private theorem appellF1_degree (a b b' c x y : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, regularizedAppellF1Coeff a b b' c p * x ^ p.1 * y ^ p.2 =
      (ascPochhammer ℂ N).eval a /
        (Gamma (c + N) * N.factorial) * carlsonRPolynomialNumerator₂ N b b' x y := by
  rw [carlsonRPolynomialNumerator₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  rw [regularizedAppellF1Coeff_eq, hdeg]
  have hfac := choose_div_factorial p.1 p.2
  rw [hdeg] at hfac
  simp only [div_eq_mul_inv] at hfac ⊢
  rw [mul_inv_rev]
  linear_combination (ascPochhammer ℂ N).eval a * (Gamma (c + N))⁻¹ *
    (ascPochhammer ℂ p.1).eval b * (ascPochhammer ℂ p.2).eval b' *
    x ^ p.1 * y ^ p.2 * hfac.symm

/-- The transformed coefficient with its Pochhammer quotient cancelled. -/
private theorem appellLinear_coeff (a b b' c : ℂ) (m n : ℕ)
    (hB : (ascPochhammer ℂ m).eval (b + b') ≠ 0) :
    regularizedAppellLinearCoeff a b b' c (m, n) =
      (ascPochhammer ℂ (m + n)).eval a /
        (Gamma (c + (m + n : ℕ)) * (m + n).factorial) *
      ((m + n).choose m : ℂ) * (ascPochhammer ℂ m).eval b *
        (ascPochhammer ℂ n).eval (b + b' + m) := by
  simp only [regularizedAppellLinearCoeff, regularizedHGFunCoeff,
    Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  rw [ascPochhammer_add_eval (b + b')]
  simp only [div_eq_mul_inv, mul_inv_rev]
  have hc := mul_inv_cancel₀ hB
  linear_combination (ascPochhammer ℂ (m + n)).eval a *
    (ascPochhammer ℂ n).eval (b + b' + m) * ((m + n).choose m : ℂ) *
    (ascPochhammer ℂ m).eval b * ((m + n).factorial : ℂ)⁻¹ *
    (Gamma (c + (m + n : ℕ)))⁻¹ * hc

/-- The transformed total-degree coefficient is the same R-polynomial numerator. -/
private theorem appellLinear_degree (a b b' c X Y : ℂ) (N : ℕ)
    (hB : ∀ m : ℕ, (ascPochhammer ℂ m).eval (b + b') ≠ 0) :
    ∑ p ∈ antidiagonal N,
      regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2 =
      (ascPochhammer ℂ N).eval a /
        (Gamma (c + N) * N.factorial) * carlsonRPolynomialNumerator₂ N b b' (X + Y) Y := by
  rw [carlsonRPolynomialNumerator₂_eq_sum_sub, add_sub_cancel_right, Finset.mul_sum]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun m n => regularizedAppellLinearCoeff a b b' c (m, n) * X ^ m * Y ^ n)]
  apply Finset.sum_congr rfl
  intro m hm
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [appellLinear_coeff a b b' c m (N - m) (hB m), Nat.add_sub_of_le hmN]
  ring

/-- **Carlson (1976), equation (4), regularized.** A linear change of variables
turns Appell's first series into Carlson's third-order double series.
The split parameters are positive real; `a` and `c` may be arbitrary complex numbers. -/
theorem regularizedAppellF1_linear (a c : ℂ) {b b' : ℝ}
    (hb : 0 < b) (hb' : 0 < b') {x y : ℂ} (hxy : ‖x - y‖ + ‖y‖ < 1) :
    regularizedAppellF1 a b b' c x y =
      regularizedAppellLinear a b b' c (x - y) y := by
  have hx : ‖x‖ < 1 := calc
    ‖x‖ = ‖x - y + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    _ < 1 := hxy
  have hy : ‖y‖ < 1 := lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) hxy
  have hB (m : ℕ) : (ascPochhammer ℂ m).eval ((b : ℂ) + b') ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simp; linarith) m
  have hL := hasSum_regularizedAppellF1_antidiagonal
    (a := a) (b₁ := (b : ℂ)) (b₂ := (b' : ℂ)) (c := c) hx hy
  have hR := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_regularizedAppellLinear a c hb hb' hxy)
  have hR' := hR.sigma (fun _ => hasSum_fintype _)
  have heq : (fun N => ∑ p ∈ antidiagonal N,
      regularizedAppellF1Coeff a b b' c p * x ^ p.1 * y ^ p.2) =
      fun N => ∑ p : ↥(antidiagonal N),
        regularizedAppellLinearCoeff a b b' c p.val * (x - y) ^ p.val.1 * y ^ p.val.2 := by
    funext N
    rw [Finset.sum_coe_sort (antidiagonal N) (fun p : ℕ × ℕ =>
      regularizedAppellLinearCoeff a b b' c p * (x - y) ^ p.1 * y ^ p.2),
      appellF1_degree, appellLinear_degree _ _ _ _ _ _ _ hB,
      sub_add_cancel]
  rw [heq] at hL
  exact hL.unique hR'

/-- **Carlson (1976), equation (4)** with ordinary Gamma normalization.
Its usual Pochhammer interpretation excludes nonpositive integral `c`. -/
theorem appellF1_linear (a c : ℂ) {b b' : ℝ}
    (hb : 0 < b) (hb' : 0 < b') {x y : ℂ} (hxy : ‖x - y‖ + ‖y‖ < 1) :
    appellF1 a b b' c x y = appellLinear a b b' c (x - y) y := by
  simp only [appellF1, appellLinear, regularizedAppellF1_linear a c hb hb' hxy]

end Carlson.TwoVariable
