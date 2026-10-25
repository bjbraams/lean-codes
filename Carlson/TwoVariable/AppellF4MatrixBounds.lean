/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Coefficients
public import Pochhammer.Estimates
public import ToMathlib.Analysis.InfiniteSum.BinomialSubstitution

/-!
# Absolute bounds for the unrestricted F₄ matrix expansion

Scalar regularized hypergeometric bounds control all exceptional parameters.
The overlapping column factors have a single rising-factorial majorant.
-/

open Complex Polynomial Finset Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- One term in the expanded unrestricted matrix kernel series, before regrouping. -/
def appellF4MatrixSeriesTerm (a b c d x y : ℂ) (v : (ℕ × ℕ) × ℕ) : ℂ :=
  regularizedHGFunCoeff {a} ∅ (v.1.1 + v.1.2) *
    ((v.1.1 + v.1.2).choose v.1.1 : ℂ) *
    regularizedHGFunCoeff {b, 1} {c} v.1.1 * (v.1.1.choose v.2 : ℂ) *
    ((ascPochhammer ℂ v.2).eval (c + d - a - 1) *
      (ascPochhammer ℂ v.1.2).eval (b + v.2) / Gamma (d + (v.2 + v.1.2 : ℕ))) *
    x ^ v.1.1 * (-y) ^ v.2 * y ^ v.1.2

/-- Explicit factorial form of a term of the matrix expansion. -/
theorem appellF4MatrixSeriesTerm_eq (a b c d x y : ℂ) (m n k : ℕ) :
    appellF4MatrixSeriesTerm a b c d x y ((m, n), k) =
      ((ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ m).eval b *
        (m.choose k : ℂ) * (-1 : ℂ) ^ k *
        (ascPochhammer ℂ k).eval (c + d - a - 1) *
        (ascPochhammer ℂ n).eval (b + k) /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + m) * Gamma (d + (k + n : ℕ)))) *
        x ^ m * y ^ (k + n) := by
  simp only [appellF4MatrixSeriesTerm, regularizedHGFunCoeff, Multiset.map_singleton,
    Multiset.prod_singleton, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.prod_cons, ascPochhammer_eval_one]
  rw [Nat.cast_add_choose ℂ, neg_pow, pow_add]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero,
    Nat.cast_ne_zero.mpr m.factorial_ne_zero]

/-- The overlapping column factors are bounded by a single regularized Gauss coefficient. -/
private theorem column_norm_le (A b d : ℂ) (B k n : ℕ)
    (hA : ‖A‖ ≤ (B : ℝ)) (hb : ‖b‖ ≤ (B : ℝ)) :
    ‖(ascPochhammer ℂ k).eval A * (ascPochhammer ℂ n).eval (b + k) /
        Gamma (d + (k + n : ℕ))‖ ≤ ‖regularizedHGFunCoeff {(B : ℂ), 1} {d} (k + n)‖ := by
  have hbk : ‖b + k‖ ≤ (B : ℝ) + k := by
    exact (norm_add_le b (k : ℂ)).trans (by simpa using add_le_add_right hb (k : ℝ))
  have h1 := norm_ascPochhammer_eval_le_ascPochhammer A k hA
  have h2 := norm_ascPochhammer_eval_le_ascPochhammer (b + k) n hbk
  have hm : ‖(ascPochhammer ℂ k).eval A * (ascPochhammer ℂ n).eval (b + k)‖ ≤
      (ascPochhammer ℝ (k + n)).eval (B : ℝ) := by
    rw [norm_mul, ascPochhammer_add_eval]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have he : regularizedHGFunCoeff {(B : ℂ), 1} {d} (k + n) =
      (ascPochhammer ℂ (k + n)).eval (B : ℂ) / Gamma (d + (k + n : ℕ)) := by
    simp [regularizedHGFunCoeff, ascPochhammer_eval_one, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc, Nat.cast_ne_zero.mpr (k + n).factorial_ne_zero]
  have hnorm : ‖(ascPochhammer ℂ (k + n)).eval (B : ℂ)‖ =
      (ascPochhammer ℝ (k + n)).eval (B : ℝ) := by
    rw [← Nat.cast_ascFactorial, Complex.norm_natCast, ← Nat.cast_ascFactorial]
  rw [he, norm_div, norm_div, hnorm]
  exact div_le_div_of_nonneg_right hm (norm_nonneg _)

/-- A strict matrix majorant admits a common geometric radius for the three scalar bounds. -/
private theorem exists_matrix_majorant_radius {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXY : X + Y + X * Y < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ X / r ^ 2 * (1 + Y / r) + Y / r ^ 2 < 1 := by
  have ht : ∀ᶠ r : ℝ in 𝓝 1, X + Y + X * Y < r ^ 3 :=
    (continuousAt_id.pow 3).eventually (Ioi_mem_nhds (by simpa using hXY))
  obtain ⟨l, hl, hls⟩ := exists_Ioc_subset_of_mem_nhds' ht (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r, hlr, hr1⟩ := exists_between hl.2
  have hr0 : 0 < r := hl.1.trans_lt hlr
  have hr3 := hls ⟨hlr, hr1.le⟩
  change X + Y + X * Y < r ^ 3 at hr3
  refine ⟨r, hr0, hr1, ?_⟩
  have he : X / r ^ 2 * (1 + Y / r) + Y / r ^ 2 = (r * (X + Y) + X * Y) / r ^ 3 := by
    field_simp
    ring
  rw [he]
  apply (div_lt_one (pow_pos hr0 3)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hr1.le (add_nonneg hX hY)]

/-- Scalar coefficient bounds give a binomial majorant for each expanded matrix term. -/
private theorem matrixTerm_norm_le (a b c d x y : ℂ) (B : ℕ) {r C E F : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA : ‖c + d - a - 1‖ ≤ (B : ℝ)) (hb : ‖b‖ ≤ (B : ℝ))
    (h1 : ∀ j, ‖regularizedHGFunCoeff {a} ∅ j‖ ≤ C / r ^ j)
    (h2 : ∀ j, ‖regularizedHGFunCoeff {b, 1} {c} j‖ ≤ E / r ^ j)
    (h3 : ∀ j, ‖regularizedHGFunCoeff {(B : ℂ), 1} {d} j‖ ≤ F / r ^ j)
    (m n k : ℕ) :
    ‖appellF4MatrixSeriesTerm a b c d x y ((m, n), k)‖ ≤
      (C * E * F) * (((m + n).choose m : ℝ) * (m.choose k : ℝ) *
        (‖x‖ / r ^ 2) ^ m * (‖y‖ / r ^ 2) ^ n * (‖y‖ / r) ^ k) := by
  simp only [appellF4MatrixSeriesTerm, norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
  calc
    _ ≤ (C / r ^ (m + n)) * ((m + n).choose m : ℝ) * (E / r ^ m) *
        (m.choose k : ℝ) * (F / r ^ (k + n)) * ‖x‖ ^ m * ‖y‖ ^ k * ‖y‖ ^ n := by
      gcongr
      · exact h1 _
      · exact h2 _
      · exact (column_norm_le (c + d - a - 1) b d B k n hA hb).trans (h3 _)
    _ = _ := by
      simp only [div_pow, pow_add, pow_two]
      field_simp
      ring

/-- Absolute convergence of the expanded matrix kernel, including all exceptional
parameters, on the positive three-term kernel majorant region. -/
theorem summable_norm_appellF4MatrixSeriesTerm (a b c d : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ < 1) :
    Summable (fun v : (ℕ × ℕ) × ℕ => ‖appellF4MatrixSeriesTerm a b c d x y v‖) := by
  obtain ⟨r, hr, hr1, hreg⟩ := exists_matrix_majorant_radius (norm_nonneg x) (norm_nonneg y) hxy
  obtain ⟨B, hB⟩ := exists_nat_gt (max ‖c + d - a - 1‖ ‖b‖)
  obtain ⟨C, hC, h1⟩ := exists_bound_regularizedHGFunCoeff_mul_pow
    (A := {a}) (C := ∅) (by simp) hr.le hr1
  obtain ⟨E, hE, h2⟩ := exists_bound_regularizedHGFunCoeff_mul_pow
    (A := {b, 1}) (C := {c}) (by simp) hr.le hr1
  obtain ⟨F, hF, h3⟩ := exists_bound_regularizedHGFunCoeff_mul_pow
    (A := {(B : ℂ), 1}) (C := {d}) (by simp) hr.le hr1
  have hbound {A D : Multiset ℂ} {K : ℝ}
      (h : ∀ j, ‖regularizedHGFunCoeff A D j * (r : ℂ) ^ j‖ ≤ K) (j : ℕ) :
      ‖regularizedHGFunCoeff A D j‖ ≤ K / r ^ j := by
    apply (le_div_iff₀ (pow_pos hr j)).mpr
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr] using h j
  have hmajor := (summable_choose_choose_mul_pow
    (div_nonneg (norm_nonneg x) (sq_nonneg r))
    (div_nonneg (norm_nonneg y) (sq_nonneg r))
    (div_nonneg (norm_nonneg y) hr.le) hreg).mul_left (C * E * F)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  rintro ⟨⟨m, n⟩, k⟩
  exact matrixTerm_norm_le a b c d x y B hr hC hE
    ((le_max_left _ _).trans hB.le) ((le_max_right _ _).trans hB.le)
    (hbound h1) (hbound h2) (hbound h3) m n k

end Carlson.TwoVariable
