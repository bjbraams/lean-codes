/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF1
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Appell's second and third double hypergeometric series

Gamma regularization includes every complex denominator parameter. Absolute
convergence holds throughout the open diamond for `F₂` and the unit bidisk for `F₃`.
The proofs use scalar Gauss-series bounds and summation by total degree, retaining
arbitrary complex numerator and denominator parameters.
-/

open Polynomial Filter Finset
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- The coefficient of Appell's second series, regularized by `Γ(c) Γ(c')`. -/
def regularizedAppellF2Coeff (a b b' c c' : ℂ) (p : ℕ × ℕ) : ℂ :=
  regularizedHGFunCoeff {a} 0 (p.1 + p.2) * ((p.1 + p.2).choose p.1 : ℂ) *
    regularizedHGFunCoeff {b, 1} {c} p.1 * regularizedHGFunCoeff {b', 1} {c'} p.2

/-- The coefficient of Appell's third series, regularized by `Γ(c)`. -/
def regularizedAppellF3Coeff (a a' b b' c : ℂ) (p : ℕ × ℕ) : ℂ :=
  regularizedHGFunCoeff {1, 1} {c} (p.1 + p.2) *
    regularizedHGFunCoeff {a, b} {1} p.1 * regularizedHGFunCoeff {a', b'} {1} p.2 /
      ((p.1 + p.2).choose p.1 : ℂ)

/-- The Gamma-regularized Appell `F₂`, as a double series. -/
def regularizedAppellF2 (a b b' c c' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, regularizedAppellF2Coeff a b b' c c' p * x ^ p.1 * y ^ p.2

/-- The Gamma-regularized Appell `F₃`, as a double series. -/
def regularizedAppellF3 (a a' b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2

/-- Appell `F₂` with ordinary normalization, away from denominator poles. -/
def appellF2 (a b b' c c' x y : ℂ) : ℂ :=
  (Gamma c * Gamma c') * regularizedAppellF2 a b b' c c' x y

/-- Appell `F₃` with ordinary normalization, away from denominator poles. -/
def appellF3 (a a' b b' c x y : ℂ) : ℂ :=
  Gamma c * regularizedAppellF3 a a' b b' c x y

/-- Explicit Pochhammer coefficients of the regularized second Appell series. -/
theorem regularizedAppellF2Coeff_eq (a b b' c c' : ℂ) (m n : ℕ) :
    regularizedAppellF2Coeff a b b' c c' (m, n) =
      (ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ m).eval b *
        (ascPochhammer ℂ n).eval b' /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + m) * Gamma (c' + n)) := by
  simp only [regularizedAppellF2Coeff, regularizedHGFunCoeff, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.map_zero, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.prod_zero, ascPochhammer_eval_one, mul_one]
  rw [Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero, Nat.cast_ne_zero.mpr m.factorial_ne_zero,
    Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Explicit Pochhammer coefficients of the regularized third Appell series. -/
theorem regularizedAppellF3Coeff_eq (a a' b b' c : ℂ) (m n : ℕ) :
    regularizedAppellF3Coeff a a' b b' c (m, n) =
      (ascPochhammer ℂ m).eval a * (ascPochhammer ℂ n).eval a' *
        (ascPochhammer ℂ m).eval b * (ascPochhammer ℂ n).eval b' /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + (m + n : ℕ))) := by
  simp only [regularizedAppellF3Coeff, regularizedHGFunCoeff, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    ascPochhammer_eval_one, add_comm (1 : ℂ), Gamma_nat_eq_factorial]
  rw [Nat.cast_add_choose ℂ]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero, Nat.cast_ne_zero.mpr m.factorial_ne_zero,
    Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Scalar hypergeometric series with at most Gauss growth converge in the unit disk. -/
private theorem summable_HG_unit {A C : Multiset ℂ} (hcard : A.card = C.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => regularizedHGFunCoeff A C n * z ^ n) := by
  apply (hasSum_regularizedHGFun_of_mem_eball ?_).summable
  rw [Metric.mem_eball, edist_zero_right]
  apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one hcard)
  rw [← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

/-- Nonnegative summation over antidiagonals detects absolute summability of a double series. -/
private theorem summable_norm_of_antidiagonal {f : ℕ × ℕ → ℂ} {M : ℕ → ℝ}
    (hM : Summable M) (hbound : ∀ N, ∑ p ∈ antidiagonal N, ‖f p‖ ≤ M N) :
    Summable (fun p => ‖f p‖) := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  change Summable (fun N : ℕ => ∑' p : ↥(antidiagonal N), ‖f p.val‖)
  simp only [tsum_fintype]
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_ hM
  intro N
  exact (Finset.sum_coe_sort _ _).le.trans (hbound N)

/-- Binomial-weighted products of two bounded scalar sequences have the scalar
summability bound corresponding to the sum of the two argument norms. -/
private theorem summable_binomial_double (A B D : ℕ → ℂ) {C E : ℝ}
    (hC : 0 ≤ C) (_hE : 0 ≤ E) (hB : ∀ n, ‖B n‖ ≤ C) (hD : ∀ n, ‖D n‖ ≤ E)
    (X Y : ℂ) (hA : Summable (fun N => ‖A N‖ * (‖X‖ + ‖Y‖) ^ N)) :
    Summable (fun p : ℕ × ℕ =>
      ‖A (p.1 + p.2) * ((p.1 + p.2).choose p.1 : ℂ) * B p.1 * D p.2 *
        X ^ p.1 * Y ^ p.2‖) := by
  apply summable_norm_of_antidiagonal (hA.mul_left (C * E))
  intro N
  calc
    _ ≤ ∑ p ∈ antidiagonal N, (C * E) * ‖A N‖ *
        ((N.choose p.1 : ℝ) * (‖X‖ ^ p.1 * ‖Y‖ ^ p.2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hdeg := Finset.mem_antidiagonal.mp hp
      simp only [norm_mul, norm_pow, norm_natCast, hdeg]
      calc
        _ ≤ ‖A N‖ * (N.choose p.1 : ℝ) * C * E * ‖X‖ ^ p.1 * ‖Y‖ ^ p.2 := by
          gcongr
          · exact hB _
          · exact hD _
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum, (Commute.all ‖X‖ ‖Y‖).add_pow']
      simp only [nsmul_eq_mul]
      ring

/-- Absolute convergence of the regularized `F₂` for every complex parameter,
throughout the open diamond `‖x‖ + ‖y‖ < 1`. -/
theorem summable_norm_regularizedAppellF2 (a b b' c c' : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖regularizedAppellF2Coeff a b b' c c' p * x ^ p.1 * y ^ p.2‖) := by
  obtain ⟨r, hr, hr1⟩ := exists_between hxy
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let B := fun n => regularizedHGFunCoeff {b, 1} {c} n * (r : ℂ) ^ n
  let D := fun n => regularizedHGFunCoeff {b', 1} {c'} n * (r : ℂ) ^ n
  have hBs : Summable B := summable_HG_unit (by simp) (by simpa [abs_of_pos hr0] using hr1)
  have hDs : Summable D := summable_HG_unit (by simp) (by simpa [abs_of_pos hr0] using hr1)
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq hBs.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨E, hE⟩ := exists_norm_le_of_cauchySeq hDs.hasSum.tendsto_sum_nat.cauchySeq
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0)
  have hq : ‖x / (r : ℂ)‖ + ‖y / (r : ℂ)‖ < 1 := by
    simp only [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rw [← add_div]
    exact (div_lt_one hr0).mpr hr
  have hAs := (summable_HG_unit (A := {a}) (C := 0) (by simp)
    (z := ((‖x / (r : ℂ)‖ + ‖y / (r : ℂ)‖ : ℝ) : ℂ)) (by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hq)).norm
  have hA : Summable (fun N => ‖regularizedHGFunCoeff {a} 0 N‖ *
      (‖x / (r : ℂ)‖ + ‖y / (r : ℂ)‖) ^ N) := by
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hAs
  have hs := summable_binomial_double (fun N => regularizedHGFunCoeff {a} 0 N)
    B D hC0 hE0 hC hE (x / (r : ℂ)) (y / (r : ℂ)) hA
  apply hs.congr
  intro p
  congr 1
  dsimp [B, D, regularizedAppellF2Coeff]
  rw [div_pow, div_pow]
  field_simp

/-- Absolute convergence of regularized `F₃` for every complex parameter on the unit bidisk. -/
theorem summable_norm_regularizedAppellF3 (a a' b b' c : ℂ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2‖) := by
  obtain ⟨r, hr, hr1⟩ := exists_between (max_lt hx hy)
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let A := fun n => regularizedHGFunCoeff {1, 1} {c} n * (r : ℂ) ^ n
  let B := fun n => regularizedHGFunCoeff {a, b} {1} n * (x / (r : ℂ)) ^ n
  let D := fun n => regularizedHGFunCoeff {a', b'} {1} n * (y / (r : ℂ)) ^ n
  have hAs : Summable A := summable_HG_unit (by simp) (by simpa [abs_of_pos hr0] using hr1)
  have hBs : Summable B := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_left _ _).trans_lt hr))
  have hDs : Summable D := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_right _ _).trans_lt hr))
  obtain ⟨M, hM⟩ := exists_norm_le_of_cauchySeq hAs.hasSum.tendsto_sum_nat.cauchySeq
  have hBD := (hBs.norm.mul_of_nonneg hDs.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)).mul_left M
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := fun p : ℕ × ℕ =>
    M * (‖B p.1‖ * ‖D p.2‖)) ?_ hBD
  intro p
  have he : regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2 =
      A (p.1 + p.2) * B p.1 * D p.2 / ((p.1 + p.2).choose p.1 : ℂ) := by
    dsimp [A, B, D, regularizedAppellF3Coeff]
    rw [pow_add, div_pow, div_pow]
    field_simp
  rw [he, norm_div, norm_mul, norm_mul, norm_natCast]
  have hc : (1 : ℝ) ≤ ((p.1 + p.2).choose p.1 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
  calc
    _ ≤ ‖A (p.1 + p.2)‖ * ‖B p.1‖ * ‖D p.2‖ := div_le_self (by positivity) hc
    _ = ‖A (p.1 + p.2)‖ * (‖B p.1‖ * ‖D p.2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hM _) (by positivity)

/-- The absolutely convergent regularized second Appell series has its defining sum. -/
theorem hasSum_regularizedAppellF2 (a b b' c c' : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => regularizedAppellF2Coeff a b b' c c' p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF2 a b b' c c' x y) :=
  (summable_norm_regularizedAppellF2 a b b' c c' hxy).of_norm.hasSum

/-- The absolutely convergent regularized third Appell series has its defining sum. -/
theorem hasSum_regularizedAppellF3 (a a' b b' c : ℂ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF3 a a' b b' c x y) :=
  (summable_norm_regularizedAppellF3 a a' b b' c hx hy).of_norm.hasSum

/-- Grouping the absolutely convergent second Appell series by total degree. -/
theorem hasSum_regularizedAppellF2_antidiagonal (a b b' c c' : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun N => ∑ p ∈ antidiagonal N,
      regularizedAppellF2Coeff a b b' c c' p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF2 a b b' c c' x y) := by
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_regularizedAppellF2 a b b' c c' hxy)
  convert h.sigma (fun _ => hasSum_fintype _) using 1
  funext N
  exact (Finset.sum_coe_sort _ _).symm

/-- Grouping the absolutely convergent third Appell series by total degree. -/
theorem hasSum_regularizedAppellF3_antidiagonal (a a' b b' c : ℂ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun N => ∑ p ∈ antidiagonal N,
      regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF3 a a' b b' c x y) := by
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_regularizedAppellF3 a a' b b' c hx hy)
  convert h.sigma (fun _ => hasSum_fintype _) using 1
  funext N
  exact (Finset.sum_coe_sort _ _).symm

/-- The ordinary second Appell series at denominator parameters away from the poles. -/
theorem hasSum_appellF2 (a b b' c c' : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hc' : ∀ k : ℕ, c' ≠ -(k : ℂ))
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ p.1).eval b *
        (ascPochhammer ℂ p.2).eval b' /
        ((ascPochhammer ℂ p.1).eval c * (ascPochhammer ℂ p.2).eval c' *
          (p.1.factorial : ℂ) * p.2.factorial)) * x ^ p.1 * y ^ p.2)
      (appellF2 a b b' c c' x y) := by
  rw [appellF2]
  convert (hasSum_regularizedAppellF2 a b b' c c' hxy).mul_left (Gamma c * Gamma c') using 1
  funext p
  rw [regularizedAppellF2Coeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc,
    ← Gamma_add_nat_div_Gamma_eq c' hc']
  have hG (s : ℂ) (hs : ∀ k : ℕ, s ≠ -(k : ℂ)) (n : ℕ) : Gamma (s + n) ≠ 0 :=
    Gamma_ne_zero (fun k hk => hs (k + n) (by push_cast at hk ⊢; linear_combination hk))
  field_simp [Gamma_ne_zero hc, Gamma_ne_zero hc', hG c hc p.1, hG c' hc' p.2]

/-- The ordinary third Appell series at denominator parameters away from the poles. -/
theorem hasSum_appellF3 (a a' b b' c : ℂ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ p.1).eval a * (ascPochhammer ℂ p.2).eval a' *
        (ascPochhammer ℂ p.1).eval b * (ascPochhammer ℂ p.2).eval b' /
        ((ascPochhammer ℂ (p.1 + p.2)).eval c *
          (p.1.factorial : ℂ) * p.2.factorial)) * x ^ p.1 * y ^ p.2)
      (appellF3 a a' b b' c x y) := by
  rw [appellF3]
  convert (hasSum_regularizedAppellF3 a a' b b' c hx hy).mul_left (Gamma c) using 1
  funext p
  rw [regularizedAppellF3Coeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc]
  have hG : Gamma (c + (p.1 + p.2 : ℕ)) ≠ 0 := Gamma_ne_zero (fun k hk => by
    apply hc (k + (p.1 + p.2))
    push_cast at hk ⊢
    linear_combination hk)
  field_simp [Gamma_ne_zero hc, hG]

end Complex
