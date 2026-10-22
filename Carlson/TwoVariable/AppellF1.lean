/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.RPolynomial.GeneratingIdentities
public import ToMathlib.Analysis.SpecialFunctions.AppellF1

/-!
# Appell's first function as a Carlson average

Carlson (1977), Exercise 6.3-5. The proof follows the Gauss identification:
the continued average has its R-polynomial Taylor series for every parameter.
Adjoining a zero node leaves the numerator unchanged, and its two-node expansion
is exactly the total-degree grouping of Appell's absolutely convergent double series.
-/

open Complex Polynomial Filter Set Dirichlet
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

open TwoVariable

/-- The three Dirichlet parameters in the Appell identification; their sum is `c`. -/
def appellDirichletParameters (b₁ b₂ c : ℂ) : (Fin 2 ⊕ Unit) → ℂ :=
  Sum.elim (pair b₁ b₂) (fun _ => c - b₁ - b₂)

/-- The three nodes in the Appell identification. -/
def appellCarlsonNodes (x y : ℂ) : (Fin 2 ⊕ Unit) → ℂ :=
  Sum.elim (pair (1 - x) (1 - y)) (fun _ => 1)

/-- Adjoining a node zero leaves the Pochhammer numerator unchanged. -/
private theorem numerator_sumElim_zero {ι : Type*} [Fintype ι]
    (n : ℕ) (b z : ι → ℂ) (β : ℂ) :
    carlsonRPolynomialNumerator n (Sum.elim b (fun _ : Unit => β))
        (Sum.elim z (fun _ : Unit => 0)) = carlsonRPolynomialNumerator n b z := by
  apply (div_left_inj' (by exact_mod_cast n.factorial_ne_zero : (n.factorial : ℂ) ≠ 0)).mp
  rw [carlsonRPolynomialNumerator_sumElim_unit]
  rw [Finset.sum_eq_single n]
  · simp
  · intro m hm hmn
    have hlt : m < n := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) hmn
    simp [zero_pow (Nat.sub_pos_of_lt hlt).ne']
  · intro hn
    exact (hn (Finset.mem_range.mpr n.lt_succ_self)).elim

/-- The two-node numerator divided by `n!` is its factorial-normalized convolution. -/
private theorem numerator_pair_div_factorial (n : ℕ) (b₁ b₂ x y : ℂ) :
    carlsonRPolynomialNumerator n (pair b₁ b₂) (pair x y) / (n.factorial : ℂ) =
      ∑ p ∈ Finset.antidiagonal n,
        ((ascPochhammer ℂ p.1).eval b₁ / (p.1.factorial : ℂ)) *
          ((ascPochhammer ℂ p.2).eval b₂ / (p.2.factorial : ℂ)) * x ^ p.1 * y ^ p.2 := by
  rw [carlsonRPolynomialNumerator_pair, carlsonRPolynomialNumerator₂, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  have hfac : (n.choose p.1 : ℂ) * p.1.factorial * p.2.factorial = (n.factorial : ℂ) := by
    rw [← hdeg, Nat.add_comm p.1 p.2]
    have h : ((p.2 + p.1).choose p.1 : ℂ) * p.2.factorial * p.1.factorial =
        ((p.2 + p.1).factorial : ℂ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial p.2 p.1
    linear_combination h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero,
    Nat.cast_ne_zero.mpr p.1.factorial_ne_zero, Nat.cast_ne_zero.mpr p.2.factorial_ne_zero]
  linear_combination ((ascPochhammer ℂ p.1).eval b₁ * (ascPochhammer ℂ p.2).eval b₂ *
    x ^ p.1 * y ^ p.2) * hfac

/-- Each Taylor coefficient of the three-node average is the corresponding
antidiagonal sum of the Appell double series. -/
private theorem appell_taylor_coefficient (a b₁ b₂ c x y : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => w ^ (-a)) 1 / (n.factorial : ℂ) *
        regCarlsonRPolynomial n (appellDirichletParameters b₁ b₂ c)
          (fun i => appellCarlsonNodes x y i - 1) =
      ∑ p ∈ Finset.antidiagonal n, regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2 := by
  let b := appellDirichletParameters b₁ b₂ c
  let z := appellCarlsonNodes x y
  let v : (Fin 2 ⊕ Unit) → ℂ := Sum.elim (pair x y) (fun _ => 0)
  have hshift : (fun i => z i - 1) = fun i => (-1 : ℂ) * v i := by
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [z, v, appellCarlsonNodes, pair]
    | inr i => simp [z, v, appellCarlsonNodes]
  have hid : iteratedDeriv n (fun w : ℂ => w ^ (-a)) 1 =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval a := by
    rw [Complex.iteratedDeriv_cpow_const _ _ (by simp), one_cpow, mul_one]
    have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) (-a) n
    rw [neg_neg] at h
    rw [h, ← mul_assoc, ← mul_pow]
    simp
  have hsum : ∑ i, b i = c := by
    simp [b, appellDirichletParameters, Fintype.sum_sum_type, pair, Fin.sum_univ_two]
  rw [hid, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hshift,
    carlsonRPolynomialNumerator_smul, hsum]
  have hNv : carlsonRPolynomialNumerator n b v =
      carlsonRPolynomialNumerator n (pair b₁ b₂) (pair x y) :=
    numerator_sumElim_zero n _ _ _
  rw [hNv]
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have he : ((-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval a / (n.factorial : ℂ)) *
      ((-1 : ℂ) ^ n * carlsonRPolynomialNumerator n (pair b₁ b₂) (pair x y) *
        (Gamma (c + n))⁻¹) =
      ((ascPochhammer ℂ n).eval a * (Gamma (c + n))⁻¹) *
        (carlsonRPolynomialNumerator n (pair b₁ b₂) (pair x y) / (n.factorial : ℂ)) := by
    linear_combination (ascPochhammer ℂ n).eval a *
      carlsonRPolynomialNumerator n (pair b₁ b₂) (pair x y) *
      (n.factorial : ℂ)⁻¹ * (Gamma (c + n))⁻¹ * hs
  rw [he, numerator_pair_div_factorial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  rcases p with ⟨m, k⟩
  rw [regularizedAppellF1Coeff_eq, hdeg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- **Carlson Exercise 6.3-5, regularized.** Appell's double series is the
three-node Carlson average, for all complex parameters on the unit bidisc. -/
theorem regCarlsonR_eq_regularizedAppellF1 (a b₁ b₂ c : ℂ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    regCarlsonR (-a) (appellDirichletParameters b₁ b₂ c) (appellCarlsonNodes x y) =
      regularizedAppellF1 a b₁ b₂ c x y := by
  let b := appellDirichletParameters b₁ b₂ c
  let z := appellCarlsonNodes x y
  have hz : z ∈ carlsonRVariableDomain := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · change 0 < (1 - x).re
        simp only [sub_re, one_re]
        linarith [(re_le_norm x).trans_lt hx]
      · change 0 < (1 - y).re
        simp only [sub_re, one_re]
        linarith [(re_le_norm y).trans_lt hy]
    | inr i => norm_num [z, appellCarlsonNodes, carlsonRightHalfPlane]
  have hnorm : ‖fun i => z i - 1‖ < 1 := by
    rw [pi_norm_lt_iff zero_lt_one]
    intro i
    cases i with
    | inl i => fin_cases i <;> simp [z, appellCarlsonNodes, pair, norm_neg, hx, hy]
    | inr i => simp [z, appellCarlsonNodes]
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-a)) (Metric.ball 1 1) := by
    intro w hw
    have hr : 0 < w.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h := (abs_re_le_norm (w - 1)).trans_lt hw
      simp only [sub_re, one_re] at h
      linarith [neg_abs_le (w.re - 1)]
    exact analyticAt_id.cpow analyticAt_const (Or.inl hr)
  have H := (isRegCarlsonRContinuation_regCarlsonR (-a) hz).hasSum_taylor hf hnorm b
  have H₂ := hasSum_regularizedAppellF1_antidiagonal (a := a) (b₁ := b₁) (b₂ := b₂) (c := c) hx hy
  apply H.unique
  convert H₂ using 1
  funext n
  exact appell_taylor_coefficient a b₁ b₂ c x y n

/-- **Carlson Exercise 6.3-5**, with ordinary Gamma normalization. -/
theorem carlsonR_eq_appellF1 (a b₁ b₂ c : ℂ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    carlsonR (-a) (appellDirichletParameters b₁ b₂ c) (appellCarlsonNodes x y) =
      appellF1 a b₁ b₂ c x y := by
  rw [carlsonR, regCarlsonR_eq_regularizedAppellF1 a b₁ b₂ c hx hy, Complex.appellF1]
  congr 1
  congr 1
  simp [appellDirichletParameters, Fintype.sum_sum_type, pair, Fin.sum_univ_two]

end Carlson
