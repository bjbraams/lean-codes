/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Matrix
public import Pochhammer.Vandermonde

/-!
# The third-order double series for equal-denominator F₄

Carlson (1975), equation (2.5). We first allow independent split and denominator
parameters. A scalar regularized ₃F₂ majorant proves absolute convergence on the
full bidisk. The equal-denominator specialization follows by expanding the
polynomial moments of the two-by-two matrix. The regularized identity retains
the duplication ratio at its zeros, rather than dividing by a totalized zero.
-/

open Complex Polynomial Finset Set Dirichlet
open scoped NNReal ENNReal
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The Gamma-regularized coefficient of Carlson's third-order double series.
The binomial presentation also exposes its homogeneous polynomial numerator. -/
def appellThirdOrderCoeff (a b β β' c d : ℂ) (p : ℕ × ℕ) : ℂ :=
  ((ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ (p.1 + p.2)).eval b /
    ((p.1 + p.2).factorial * Gamma (c + (p.1 + p.2 : ℕ)) *
      Gamma (d + (p.1 + p.2 : ℕ)))) *
    ((p.1 + p.2).choose p.1 : ℂ) *
      (ascPochhammer ℂ p.1).eval β * (ascPochhammer ℂ p.2).eval β'

/-- Explicit Pochhammer coefficients, without any parameter exclusions. -/
theorem appellThirdOrderCoeff_eq (a b β β' c d : ℂ) (m n : ℕ) :
    appellThirdOrderCoeff a b β β' c d (m, n) =
      ((ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ (m + n)).eval b *
        (ascPochhammer ℂ m).eval β * (ascPochhammer ℂ n).eval β') /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + (m + n : ℕ)) *
          Gamma (d + (m + n : ℕ))) := by
  rw [appellThirdOrderCoeff, Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero]

/-- The absolutely convergent third-order double series. -/
def appellThirdOrder (a b β β' c d u v : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2

/-- A total-degree block is a scalar factor times a two-node R-polynomial numerator. -/
theorem appellThirdOrder_antidiagonal (a b β β' c d u v : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2 =
      ((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
        ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))) *
        carlsonRPolynomialNumerator₂ N β β' u v := by
  rw [carlsonRPolynomialNumerator₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [appellThirdOrderCoeff, mem_antidiagonal.mp hp]
  ring

/-- A scalar ₃F₂ coefficient bounds the absolute total-degree block. -/
private theorem sum_norm_appellThirdOrder_le (a b β β' c d u v : ℂ) (B N : ℕ)
    (hβ : ‖β‖ ≤ (B : ℝ)) (hβ' : ‖β'‖ ≤ (B : ℝ)) :
    ∑ p ∈ antidiagonal N, ‖appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2‖ ≤
      ‖regularizedHGFunCoeff {a, b, ((B : ℂ) + B)} {c, d} N‖ * (max ‖u‖ ‖v‖) ^ N := by
  let C : ℂ := (ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
    ((N.factorial : ℂ) * Gamma (c + N) * Gamma (d + N))
  have hterm (p : ℕ × ℕ) (hp : p ∈ antidiagonal N) :
      ‖appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2‖ ≤
        ‖C‖ * ((N.choose p.1 : ℝ) *
          ((ascPochhammer ℝ p.1).eval (B : ℝ) * (ascPochhammer ℝ p.2).eval (B : ℝ))) *
            (max ‖u‖ ‖v‖) ^ N := by
    have hdeg := mem_antidiagonal.mp hp
    have hn : ‖u‖ ^ p.1 * ‖v‖ ^ p.2 ≤ (max ‖u‖ ‖v‖) ^ N := by
      rw [← hdeg, pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (by positivity) (by positivity)
    simp only [appellThirdOrderCoeff, hdeg, norm_mul, norm_pow, Complex.norm_natCast]
    change ‖C‖ * _ * _ * _ * _ * _ ≤ _
    calc
      _ = (‖C‖ * (N.choose p.1 : ℝ) *
          (‖(ascPochhammer ℂ p.1).eval β‖ * ‖(ascPochhammer ℂ p.2).eval β'‖)) *
            (‖u‖ ^ p.1 * ‖v‖ ^ p.2) := by ring
      _ ≤ (‖C‖ * (N.choose p.1 : ℝ) *
          ((ascPochhammer ℝ p.1).eval (B : ℝ) *
            (ascPochhammer ℝ p.2).eval (B : ℝ))) * (max ‖u‖ ‖v‖) ^ N := by
        have hm := norm_ascPochhammer_eval_le_ascPochhammer β p.1 hβ
        have hn' := norm_ascPochhammer_eval_le_ascPochhammer β' p.2 hβ'
        have hp := mul_le_mul hm hn' (norm_nonneg _) ((norm_nonneg _).trans hm)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hn
          (by positivity) (mul_nonneg (by positivity)
            (mul_nonneg ((norm_nonneg _).trans hm) ((norm_nonneg _).trans hn')))
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ antidiagonal N, ‖C‖ * ((N.choose p.1 : ℝ) *
        ((ascPochhammer ℝ p.1).eval (B : ℝ) * (ascPochhammer ℝ p.2).eval (B : ℝ))) *
          (max ‖u‖ ‖v‖) ^ N := Finset.sum_le_sum hterm
    _ = ‖C‖ * (ascPochhammer ℝ N).eval ((B : ℝ) + B) * (max ‖u‖ ‖v‖) ^ N := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← ascPochhammer_eval_add]
    _ = _ := by
      simp only [regularizedHGFunCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, C,
        norm_div, norm_mul]
      rw [show (B : ℂ) + B = ((B + B : ℕ) : ℂ) by push_cast; rfl,
        ← Nat.cast_ascFactorial, Complex.norm_natCast,
        show (B : ℝ) + B = ((B + B : ℕ) : ℝ) by push_cast; rfl,
        ← Nat.cast_ascFactorial]
      simp only [_root_.norm_natCast]
      ring

/-- Absolute convergence of the third-order double series on the full bidisk,
including all exceptional split and denominator parameters. -/
theorem summable_norm_appellThirdOrder (a b β β' c d : ℂ) {u v : ℂ}
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2‖) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max ‖β‖ ‖β'‖)
  let r : ℝ≥0 := ⟨max ‖u‖ ‖v‖, (norm_nonneg u).trans (le_max_left _ _)⟩
  have hr : (r : ℝ≥0∞) < (regularizedHGFunSeries {a, b, ((B : ℂ) + B)} {c, d}).radius := by
    apply lt_of_lt_of_le _ (radius_regularizedHGFunSeries_ge_one (by simp))
    exact_mod_cast max_lt hu hv
  have hG := (regularizedHGFunSeries {a, b, ((B : ℂ) + B)} {c, d}).summable_norm_mul_pow hr
  simp only [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_norm] at hG
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype]
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_ hG
  intro N
  change (∑ p : ↥(antidiagonal N),
    ‖appellThirdOrderCoeff a b β β' c d p.val * u ^ p.val.1 * v ^ p.val.2‖) ≤ _
  rw [Finset.sum_coe_sort (antidiagonal N) (fun p : ℕ × ℕ =>
    ‖appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2‖)]
  exact sum_norm_appellThirdOrder_le a b β β' c d u v B N
    ((le_max_left _ _).trans hB.le) ((le_max_right _ _).trans hB.le)

/-- The third-order series has its defining sum throughout the bidisk. -/
theorem hasSum_appellThirdOrder (a b β β' c d : ℂ) {u v : ℂ}
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    HasSum (fun p : ℕ × ℕ => appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2)
      (appellThirdOrder a b β β' c d u v) :=
  (summable_norm_appellThirdOrder a b β β' c d hu hv).of_norm.hasSum

/-- Absolute convergence justifies grouping the third-order series by total degree. -/
theorem hasSum_appellThirdOrder_antidiagonal (a b β β' c d : ℂ) {u v : ℂ}
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    HasSum (fun N => ∑ p ∈ antidiagonal N,
      appellThirdOrderCoeff a b β β' c d p * u ^ p.1 * v ^ p.2)
      (appellThirdOrder a b β β' c d u v) := by
  have h := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hasSum_appellThirdOrder a b β β' c d hu hv)
  convert h.sigma (fun _ => hasSum_fintype _) using 1
  funext N
  exact (Finset.sum_coe_sort _ _).symm

/-- The third-order homogeneous block is the binomial coefficient times its continued matrix
moment, with arbitrary row and column parameters. -/
theorem appellThirdOrder_antidiagonal_eq_matrix_moment (a b c β β' x y : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, appellThirdOrderCoeff a b β β' c (β + β') p *
        ((x + y) ^ 2) ^ p.1 * ((x - y) ^ 2) ^ p.2 =
      (ascPochhammer ℂ N).eval a / (N.factorial : ℂ) *
        continuedRegMatrixDirichletAverage (appellF4EqualMatrix x y) (fun z => (1 - z) ^ N)
          (appellF2Parameters b c, pair β β') := by
  rw [appellThirdOrder_antidiagonal,
    continuedRegMatrixDirichletAverage_appellF4Equal_moment,
    regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_pair, sum_pair]
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_sub_cancel, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The squared sum and difference belong to the transformed bidisk. -/
private theorem equalF4_thirdOrder_region {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    ‖(x + y) ^ 2‖ < 1 ∧ ‖(x - y) ^ 2‖ < 1 := by
  have hr : (‖x‖ + ‖y‖) ^ 2 < 1 := by nlinarith [norm_nonneg x, norm_nonneg y]
  constructor
  · rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans_lt hr
  · rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2).trans_lt hr

/-- The third-order series is the equal-row matrix average with independent column parameters. -/
theorem appellThirdOrder_eq_continuedMatrix (a b c β β' : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    appellThirdOrder a b β β' c (β + β') ((x + y) ^ 2) ((x - y) ^ 2) =
      continuedRegMatrixDirichletAverage (appellF4EqualMatrix x y) (fun z => z ^ (-a))
        (appellF2Parameters b c, pair β β') := by
  obtain ⟨hu, hv⟩ := equalF4_thirdOrder_region hxy
  have hS := hasSum_appellThirdOrder_antidiagonal a b β β' c (β + β') hu hv
  simp only [appellThirdOrder_antidiagonal_eq_matrix_moment] at hS
  have hr : (‖x‖ + ‖y‖) ^ 2 < 1 := by nlinarith [norm_nonneg x, norm_nonneg y]
  exact hS.unique (hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (appellF2Parameters b c) (pair β β') (appellF4EqualMatrix x y) a
    (by positivity) hr (norm_appellF4EqualMatrix_sub_one_le x y))

/-- **Carlson (1975), (2.5), division-free regularized form.** The third-order series
represents equal-denominator F₄, with its explicit duplication ratio, at every parameter. -/
theorem appellThirdOrder_eq_regularizedAppellF4 (a b c : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    appellThirdOrder a b (c - 1 / 2) (c - 1 / 2) c (2 * c - 1)
        ((x + y) ^ 2) ((x - y) ^ 2) =
      quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [show 2 * c - 1 = (c - 1 / 2) + (c - 1 / 2) by ring,
    appellThirdOrder_eq_continuedMatrix a b c (c - 1 / 2) (c - 1 / 2) hxy,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_equal a b c hxy]

/-- **Carlson (1975), (2.5), absolutely convergent double series.**
This regularized identity includes every exceptional denominator and split parameter. -/
theorem hasSum_appellThirdOrder_regularizedAppellF4 (a b c : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      appellThirdOrderCoeff a b (c - 1 / 2) (c - 1 / 2) c (2 * c - 1) p *
        ((x + y) ^ 2) ^ p.1 * ((x - y) ^ 2) ^ p.2)
      (quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2)) := by
  rw [← appellThirdOrder_eq_regularizedAppellF4 a b c hxy]
  obtain ⟨hu, hv⟩ := equalF4_thirdOrder_region hxy
  exact hasSum_appellThirdOrder a b (c - 1 / 2) (c - 1 / 2) c (2 * c - 1) hu hv

/-- **Carlson (1975), (2.5), ordinary form.** Away from the two displayed denominator
pole sets, F₄ is an absolutely convergent third-order double Pochhammer series.
The regularized theorem supplies the division-free interpretation at exceptional values. -/
theorem hasSum_appellF4_thirdOrder (a b c : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hd : ∀ k : ℕ, 2 * c - 1 ≠ -(k : ℂ))
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ (p.1 + p.2)).eval b *
        (ascPochhammer ℂ p.1).eval (c - 1 / 2) *
        (ascPochhammer ℂ p.2).eval (c - 1 / 2) /
        ((ascPochhammer ℂ (p.1 + p.2)).eval c *
          (ascPochhammer ℂ (p.1 + p.2)).eval (2 * c - 1) *
          (p.1.factorial : ℂ) * p.2.factorial)) *
        ((x + y) ^ 2) ^ p.1 * ((x - y) ^ 2) ^ p.2)
      (appellF4 a b c c (x ^ 2) (y ^ 2)) := by
  have hβ : ∀ k : ℕ, c - 1 / 2 ≠ -(k : ℂ) := by
    intro k hk
    apply hd (2 * k)
    push_cast
    linear_combination 2 * hk
  have hdup := Gamma_mul_quadraticGammaRatio_of_ne hβ
  rw [show (c - 1 / 2) + (c - 1 / 2) = 2 * c - 1 by ring,
    show c - 1 / 2 + 1 / 2 = c by ring] at hdup
  have hS := (hasSum_appellThirdOrder_regularizedAppellF4 a b c hxy).mul_left
    (Gamma c * Gamma (2 * c - 1))
  have hval : Gamma c * Gamma (2 * c - 1) *
      (quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2)) =
        appellF4 a b c c (x ^ 2) (y ^ 2) := by
    rw [mul_assoc (Gamma c), ← mul_assoc (Gamma (2 * c - 1)), hdup, appellF4]
    ring
  rw [hval] at hS
  convert hS using 1
  funext p
  rcases p with ⟨m, n⟩
  rw [appellThirdOrderCoeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc,
    ← Gamma_add_nat_div_Gamma_eq (2 * c - 1) hd]
  have hG (s : ℂ) (hs : ∀ k : ℕ, s ≠ -(k : ℂ)) : Gamma (s + (m + n : ℕ)) ≠ 0 :=
    Gamma_ne_zero (fun k hk => hs (k + (m + n)) (by
      push_cast at hk ⊢; linear_combination hk))
  have hA := hG c hc
  have hB := hG (2 * c - 1) hd
  have hC := Gamma_ne_zero hc
  have hD := Gamma_ne_zero hd
  clear hG hS hdup hval
  generalize Gamma (c + (m + n : ℕ)) = A at *
  generalize Gamma (2 * c - 1 + (m + n : ℕ)) = B at *
  generalize Gamma c = C at *
  generalize Gamma (2 * c - 1) = D at *
  field_simp

end Carlson.TwoVariable
