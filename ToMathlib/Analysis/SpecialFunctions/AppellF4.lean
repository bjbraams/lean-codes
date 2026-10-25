/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF2F3
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Appell's fourth double hypergeometric series

The Gamma-regularized series converges absolutely for arbitrary complex parameters
on `sqrt ‖x‖ + sqrt ‖y‖ < 1`. Scalar Gauss-series bounds control the parameter
factors; the square of the finite binomial sum gives the full argument region.
The ordinary Pochhammer series is recovered away from denominator poles.
-/

open Complex Polynomial Set Filter Finset
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- The coefficient of Appell's fourth series, regularized by both denominator Gamma factors. -/
def regularizedAppellF4Coeff (a b c d : ℂ) (p : ℕ × ℕ) : ℂ :=
  regularizedHGFunCoeff {a, b} {1} (p.1 + p.2) * ((p.1 + p.2).choose p.1 : ℂ) ^ 2 *
    regularizedHGFunCoeff {1, 1} {c} p.1 * regularizedHGFunCoeff {1, 1} {d} p.2

/-- The Gamma-regularized fourth Appell function as a double series. -/
def regularizedAppellF4 (a b c d x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, regularizedAppellF4Coeff a b c d p * x ^ p.1 * y ^ p.2

/-- The ordinary normalization of Appell `F₄`; its series interpretation excludes
denominator poles. -/
def appellF4 (a b c d x y : ℂ) : ℂ :=
  (Gamma c * Gamma d) * regularizedAppellF4 a b c d x y

/-- Explicit Pochhammer coefficients of regularized `F₄`, including exceptional denominators. -/
theorem regularizedAppellF4Coeff_eq (a b c d : ℂ) (m n : ℕ) :
    regularizedAppellF4Coeff a b c d (m, n) =
      (ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ (m + n)).eval b /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + m) * Gamma (d + n)) := by
  simp only [regularizedAppellF4Coeff, regularizedHGFunCoeff, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    ascPochhammer_eval_one, add_comm (1 : ℂ), Gamma_nat_eq_factorial]
  rw [Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, pow_two, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero, Nat.cast_ne_zero.mpr m.factorial_ne_zero,
    Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Scalar Gauss-type coefficients are geometrically bounded at each radius below one. -/
theorem exists_bound_regularizedHGFunCoeff_mul_pow {A C : Multiset ℂ} (hcard : A.card = C.card + 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖regularizedHGFunCoeff A C n * (r : ℂ) ^ n‖ ≤ B := by
  have hs : Summable (fun n => regularizedHGFunCoeff A C n * (r : ℂ) ^ n) := by
    apply (hasSum_regularizedHGFun_of_mem_eball ?_).summable
    rw [Metric.mem_eball, edist_zero_right]
    apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one hcard)
    rw [← ofReal_norm, norm_real, Real.norm_eq_abs, abs_of_nonneg hr, ENNReal.ofReal_lt_one]
    exact hr1
  obtain ⟨B, hB⟩ := exists_norm_le_of_cauchySeq hs.hasSum.tendsto_sum_nat.cauchySeq
  exact ⟨B, (norm_nonneg _).trans (hB 0), hB⟩

/-- Squared binomial coefficients have the square of the usual binomial-sum majorant. -/
private theorem sum_binomial_sq_le (N : ℕ) (x y : ℂ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : ℝ) ^ 2 * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 ≤
      ((Real.sqrt ‖x‖ + Real.sqrt ‖y‖) ^ 2) ^ N := by
  have he (p : ℕ × ℕ) :
      (N.choose p.1 : ℝ) ^ 2 * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 =
        ((N.choose p.1 : ℝ) * (Real.sqrt ‖x‖) ^ p.1 * (Real.sqrt ‖y‖) ^ p.2) ^ 2 := by
    simp only [mul_pow]
    rw [pow_right_comm (Real.sqrt ‖x‖) p.1 2, pow_right_comm (Real.sqrt ‖y‖) p.2 2,
      Real.sq_sqrt (norm_nonneg x), Real.sq_sqrt (norm_nonneg y)]
  simp_rw [he]
  apply (sum_sq_le_sq_sum_of_nonneg (fun p _ => by positivity)).trans_eq
  have hsum : ∑ p ∈ antidiagonal N,
      (N.choose p.1 : ℝ) * (Real.sqrt ‖x‖) ^ p.1 * (Real.sqrt ‖y‖) ^ p.2 =
        (Real.sqrt ‖x‖ + Real.sqrt ‖y‖) ^ N := by
    simpa only [nsmul_eq_mul, mul_assoc] using
      ((Commute.all (Real.sqrt ‖x‖) (Real.sqrt ‖y‖)).add_pow' N).symm
  rw [hsum, pow_right_comm]

/-- Bounded parameter factors and squared binomial coefficients give an absolutely
summable double series on the square-root region. -/
private theorem summable_bounded_binomial_sq (A B D : ℕ → ℂ) {C E F : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hA : ∀ n, ‖A n‖ ≤ C) (hB : ∀ n, ‖B n‖ ≤ E) (hD : ∀ n, ‖D n‖ ≤ F)
    (x y : ℂ) (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖A (p.1 + p.2) * ((p.1 + p.2).choose p.1 : ℂ) ^ 2 * B p.1 * D p.2 *
        x ^ p.1 * y ^ p.2‖) := by
  let q := (Real.sqrt ‖x‖ + Real.sqrt ‖y‖) ^ 2
  have hq : q < 1 := by dsimp [q]; nlinarith [Real.sqrt_nonneg ‖x‖, Real.sqrt_nonneg ‖y‖]
  have hM := (summable_geometric_of_lt_one (sq_nonneg _) hq).mul_left (C * E * F)
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  change Summable (fun N : ℕ => ∑' p : ↥(antidiagonal N),
    ‖A (p.val.1 + p.val.2) * ((p.val.1 + p.val.2).choose p.val.1 : ℂ) ^ 2 *
      B p.val.1 * D p.val.2 * x ^ p.val.1 * y ^ p.val.2‖)
  simp only [tsum_fintype]
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_ hM
  intro N
  rw [Finset.sum_coe_sort (antidiagonal N) (fun p : ℕ × ℕ =>
    ‖A (p.1 + p.2) * ((p.1 + p.2).choose p.1 : ℂ) ^ 2 * B p.1 * D p.2 *
      x ^ p.1 * y ^ p.2‖)]
  calc
    _ ≤ ∑ p ∈ antidiagonal N, (C * E * F) *
        ((N.choose p.1 : ℝ) ^ 2 * ‖x‖ ^ p.1 * ‖y‖ ^ p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hdeg := Finset.mem_antidiagonal.mp hp
      simp only [norm_mul, norm_pow, norm_natCast, hdeg]
      calc
        _ ≤ C * (N.choose p.1 : ℝ) ^ 2 * E * F * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 := by
          gcongr
          · exact hA _
          · exact hB _
          · exact hD _
        _ = _ := by ring
    _ ≤ (C * E * F) * q ^ N := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_binomial_sq_le N x y) (by positivity)

/-- Absolute convergence of regularized `F₄` throughout the full square-root region,
for every complex numerator and denominator parameter. -/
theorem summable_norm_regularizedAppellF4 (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖regularizedAppellF4Coeff a b c d p * x ^ p.1 * y ^ p.2‖) := by
  obtain ⟨r, hr, hr1⟩ := exists_between hxy
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  obtain ⟨C, hC, hA⟩ :=
    exists_bound_regularizedHGFunCoeff_mul_pow (A := {a, b}) (C := {1}) (by simp) hr0.le hr1
  obtain ⟨E, hE, hB⟩ :=
    exists_bound_regularizedHGFunCoeff_mul_pow (A := {1, 1}) (C := {c}) (by simp) hr0.le hr1
  obtain ⟨F, hF, hD⟩ :=
    exists_bound_regularizedHGFunCoeff_mul_pow (A := {1, 1}) (C := {d}) (by simp) hr0.le hr1
  let A := fun n => regularizedHGFunCoeff {a, b} {1} n * (r : ℂ) ^ n
  let B := fun n => regularizedHGFunCoeff {1, 1} {c} n * (r : ℂ) ^ n
  let D := fun n => regularizedHGFunCoeff {1, 1} {d} n * (r : ℂ) ^ n
  have hscaled : Real.sqrt ‖x / (r : ℂ) ^ 2‖ + Real.sqrt ‖y / (r : ℂ) ^ 2‖ < 1 := by
    simp only [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      Real.sqrt_div (norm_nonneg _), Real.sqrt_sq_eq_abs]
    rw [← add_div]
    exact (div_lt_one hr0).mpr hr
  have hs := summable_bounded_binomial_sq A B D hC hE hF hA hB hD
    (x / (r : ℂ) ^ 2) (y / (r : ℂ) ^ 2) hscaled
  apply hs.congr
  intro p
  congr 1
  dsimp [A, B, D, regularizedAppellF4Coeff]
  rw [pow_add, div_pow, div_pow, pow_right_comm (r : ℂ) 2 p.1,
    pow_right_comm (r : ℂ) 2 p.2]
  field_simp

/-- The absolutely convergent fourth Appell series has its defining sum. -/
theorem hasSum_regularizedAppellF4 (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => regularizedAppellF4Coeff a b c d p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF4 a b c d x y) :=
  (summable_norm_regularizedAppellF4 a b c d hxy).of_norm.hasSum

/-- Grouping regularized `F₄` by total degree is justified by absolute convergence. -/
theorem hasSum_regularizedAppellF4_antidiagonal (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun N => ∑ p ∈ antidiagonal N,
      regularizedAppellF4Coeff a b c d p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF4 a b c d x y) := by
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_regularizedAppellF4 a b c d hxy)
  convert h.sigma (fun _ => hasSum_fintype _) using 1
  funext N
  exact (Finset.sum_coe_sort _ _).symm

/-- The ordinary `F₄` Pochhammer series, away from the two denominator pole sets. -/
theorem hasSum_appellF4 (a b c d : ℂ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, d ≠ -(k : ℂ)) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ (p.1 + p.2)).eval b /
        ((ascPochhammer ℂ p.1).eval c * (ascPochhammer ℂ p.2).eval d *
          (p.1.factorial : ℂ) * p.2.factorial)) * x ^ p.1 * y ^ p.2)
      (appellF4 a b c d x y) := by
  rw [appellF4]
  convert (hasSum_regularizedAppellF4 a b c d hxy).mul_left (Gamma c * Gamma d) using 1
  funext p
  rw [regularizedAppellF4Coeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc,
    ← Gamma_add_nat_div_Gamma_eq d hd]
  have hG (s : ℂ) (hs : ∀ k : ℕ, s ≠ -(k : ℂ)) (n : ℕ) : Gamma (s + n) ≠ 0 :=
    Gamma_ne_zero (fun k hk => hs (k + n) (by push_cast at hk ⊢; linear_combination hk))
  field_simp [Gamma_ne_zero hc, Gamma_ne_zero hd, hG c hc p.1, hG d hd p.2]

end Complex
