/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Logarithmic means and their relative error

Carlson (1977), §2.6, compares logarithmic, geometric and arithmetic means and
estimates the relative error of the arithmetic mean. The complex estimates use
the principal logarithm of a quotient, rather than a difference of principal
logarithms. The series proof adapts Mathlib's real logarithm expansion; the
branch combination uses Jeremy Tan's complex arctangent logarithm identity.
-/

open Filter Set
open scoped Topology

public noncomputable section

namespace Complex

/-- The odd logarithm series, combined as a principal logarithm on the unit disk. -/
private theorem hasSum_log_quotient {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (1 / (2 * n + 1 : ℂ)) * z ^ (2 * n + 1))
      (log ((1 + z) / (1 - z))) := by
  let term := fun n : ℕ => -( (-z) ^ (n + 1) / ((n : ℂ) + 1)) + z ^ (n + 1) / (n + 1)
  have he : term ∘ (2 * ·) = fun n : ℕ =>
      2 * (1 / (2 * n + 1 : ℂ)) * z ^ (2 * n + 1) := by
    funext n
    dsimp [term, Function.comp_def]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) z]
    push_cast
    ring
  have hs : HasSum term (log (1 + z) - log (1 - z)) := by
    convert (hasSum_taylorSeries_neg_log' (z := -z) (by simpa using hz)).neg.add
      (hasSum_taylorSeries_neg_log' hz) using 1
    simp [sub_eq_add_neg]
  have hodd : HasSum (fun n : ℕ => 2 * (1 / (2 * n + 1 : ℂ)) * z ^ (2 * n + 1))
      (log (1 + z) - log (1 - z)) := by
    rw [← he, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
    · exact hs
    · intro m hm
      rw [range_two_mul, Set.mem_ofPred_eq, ← Nat.even_add_one] at hm
      dsimp [term]
      rw [Even.neg_pow hm, neg_add_cancel]
  have hlog := hasSum_arctan_aux (z := -I * z) (by simpa using hz)
  have hi : -I * z * I = z := by
    calc
      -I * z * I = -(I * I) * z := by ring
      _ = z := by rw [I_mul_I]; ring
  rw [hi, ← sub_eq_add_neg] at hlog
  rwa [hlog] at hodd

/-- The relative arithmetic/logarithmic-mean error has an even power series. -/
theorem hasSum_logarithmicMeanError {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => z ^ (2 * n + 2) / (2 * n + 3 : ℂ))
      (log ((1 + z) / (1 - z)) / (2 * z) - 1) := by
  have hs : HasSum (fun n : ℕ => z ^ (2 * n) / (2 * n + 1 : ℂ))
      (log ((1 + z) / (1 - z)) / (2 * z)) := by
    convert (hasSum_log_quotient hz).div_const (2 * z) using 1
    funext n
    rw [pow_succ]
    field_simp
  have ht := (hasSum_nat_add_iff 1
    (f := fun n : ℕ => z ^ (2 * n) / (2 * n + 1 : ℂ))
    (g := log ((1 + z) / (1 - z)) / (2 * z) - 1)).mpr (by simpa using hs)
  convert ht using 1
  funext n
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  push_cast
  congr 1
  ring

/-- **Carlson 2.6-3 in disk coordinates.** A sharp geometric majorant bounds the
relative error, strictly when the two inputs differ. -/
theorem norm_logarithmicMeanError_lt {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    ‖log ((1 + z) / (1 - z)) / (2 * z) - 1‖ <
      ‖z‖ ^ 2 / (3 * (1 - ‖z‖ ^ 2)) := by
  let r := ‖z‖
  have hr : 0 < r := norm_pos_iff.mpr hz0
  have hr2 : r ^ 2 < 1 := by dsimp [r]; nlinarith [norm_nonneg z]
  let f := fun n : ℕ => ‖z ^ (2 * n + 2) / (2 * n + 3 : ℂ)‖
  let g := fun n : ℕ => r ^ 2 / 3 * (r ^ 2) ^ n
  have hg : HasSum g (r ^ 2 / 3 * (1 - r ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg r) hr2).mul_left _
  have he (n : ℕ) : g n = r ^ (2 * n + 2) / 3 := by
    dsimp [g]
    rw [pow_add, pow_mul]
    ring
  have hf (n : ℕ) : f n = r ^ (2 * n + 2) / (2 * n + 3 : ℝ) := by
    simp only [f, norm_div, norm_pow, r]
    norm_cast
  have hle (n : ℕ) : f n ≤ g n := by
    rw [hf, he]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hlt : f 1 < g 1 := by
    rw [hf, he]
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
    exact div_lt_div_of_pos_left (pow_pos hr _) (by norm_num) (by norm_num)
  have hfs : Summable f := hg.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  have hsum := hfs.tsum_lt_tsum hle hlt hg.summable
  have hnorm := (hasSum_logarithmicMeanError hz hz0).norm_le_of_bounded hfs.hasSum
    (fun _ => le_rfl)
  rw [hg.tsum_eq] at hsum
  apply hnorm.trans_lt
  convert hsum using 1
  dsimp [r]
  field_simp

/-- **Carlson Theorem 2.6-3.** The error bound in the original complex variables.
The logarithm is the principal value of the quotient, with no separate-log branch assumption. -/
theorem norm_arithmetic_logarithmicMean_ratio_sub_one_lt {x y : ℂ}
    (hxy0 : 0 < ‖x - y‖) (hxy : ‖x - y‖ < ‖x + y‖) :
    ‖(x + y) / 2 * log (x / y) / (x - y) - 1‖ <
      ‖x - y‖ ^ 2 / (3 * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2)) := by
  have hs : x + y ≠ 0 := norm_pos_iff.mp (hxy0.trans hxy)
  have hd : x - y ≠ 0 := norm_pos_iff.mp hxy0
  have hy : y ≠ 0 := by
    intro hy
    simp only [hy, sub_zero, add_zero] at hxy
    exact lt_irrefl _ hxy
  let z := (x - y) / (x + y)
  have hz0 : z ≠ 0 := div_ne_zero hd hs
  have hz : ‖z‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hs)).mpr hxy
  have heq : (1 + z) / (1 - z) = x / y := by
    dsimp [z]
    field_simp [hy]
    ring
  have he : log ((1 + z) / (1 - z)) / (2 * z) - 1 =
      (x + y) / 2 * log (x / y) / (x - y) - 1 := by
    rw [heq]
    dsimp [z]
    field_simp
  have h := norm_logarithmicMeanError_lt hz hz0
  rw [he] at h
  convert h using 1
  dsimp [z]
  rw [norm_div]
  field_simp

end Complex

namespace Real

/-- The real relative-error series on the punctured unit interval. -/
theorem hasSum_logarithmicMeanError {z : ℝ} (hz : |z| < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => z ^ (2 * n + 2) / (2 * n + 3 : ℝ))
      (log ((1 + z) / (1 - z)) / (2 * z) - 1) := by
  have hp : 0 < (1 + z) / (1 - z) := div_pos (by linarith [abs_lt.mp hz])
    (by linarith [abs_lt.mp hz])
  have hlog : (log ((1 + z) / (1 - z)) : ℂ) =
      Complex.log ((1 + (z : ℂ)) / (1 - (z : ℂ))) := by
    rw [Complex.ofReal_log hp.le]
    congr 1
    push_cast
    rfl
  have h := Complex.hasSum_logarithmicMeanError (z := (z : ℂ))
    (by simpa using hz) (Complex.ofReal_ne_zero.mpr hz0)
  rw [← hlog] at h
  exact_mod_cast h

/-- The strict real lower bound for the relative mean error on the punctured unit interval. -/
theorem sq_div_three_lt_logarithmicMeanError {z : ℝ} (hz : |z| < 1) (hz0 : z ≠ 0) :
    z ^ 2 / 3 < log ((1 + z) / (1 - z)) / (2 * z) - 1 := by
  have hs := hasSum_logarithmicMeanError hz hz0
  have h := hs.summable.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (by
      rw [show 2 * n + 2 = (n + 1) * 2 by omega, pow_mul]
      exact sq_nonneg _) (by positivity))
  rw [hs.tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  have hp : 0 < z ^ 4 := by nlinarith [sq_pos_of_ne_zero hz0, sq_nonneg (z ^ 2 - 1)]
  linarith

/-- The real upper bound inherited from the sharp complex estimate. -/
theorem logarithmicMeanError_lt_sq_div {z : ℝ} (hz : |z| < 1) (hz0 : z ≠ 0) :
    log ((1 + z) / (1 - z)) / (2 * z) - 1 < z ^ 2 / (3 * (1 - z ^ 2)) := by
  have hp : 0 < (1 + z) / (1 - z) := div_pos (by linarith [abs_lt.mp hz])
    (by linarith [abs_lt.mp hz])
  have hlog : (log ((1 + z) / (1 - z)) : ℂ) =
      Complex.log ((1 + (z : ℂ)) / (1 - (z : ℂ))) := by
    rw [Complex.ofReal_log hp.le]
    congr 1
    push_cast
    rfl
  have h := Complex.norm_logarithmicMeanError_lt (z := (z : ℂ))
    (by simpa using hz) (Complex.ofReal_ne_zero.mpr hz0)
  rw [← hlog] at h
  have he : (log ((1 + z) / (1 - z)) : ℂ) / (2 * (z : ℂ)) - 1 =
      ((log ((1 + z) / (1 - z)) / (2 * z) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  have hr : ‖(z : ℂ)‖ ^ 2 = z ^ 2 := by simp [sq_abs]
  rw [hr] at h
  exact (le_abs_self _).trans_lt h

/-- **Carlson Theorem 2.6-2.** Sharp two-sided bounds on the arithmetic/logarithmic
mean ratio for distinct positive arguments. -/
theorem arithmetic_logarithmicMean_ratio_bounds {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    1 + (x - y) ^ 2 / (3 * (x + y) ^ 2) <
        (x + y) / 2 * (log x - log y) / (x - y) ∧
      (x + y) / 2 * (log x - log y) / (x - y) <
        1 + (x - y) ^ 2 / (12 * x * y) := by
  have hs : 0 < x + y := add_pos hx hy
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  let z := (x - y) / (x + y)
  have hz : |z| < 1 := by
    rw [abs_div, abs_of_pos hs]
    exact (div_lt_one hs).mpr (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hz0 : z ≠ 0 := div_ne_zero hd hs.ne'
  have hlow := sq_div_three_lt_logarithmicMeanError hz hz0
  have hupp := logarithmicMeanError_lt_sq_div hz hz0
  have hsq : 0 < 1 - z ^ 2 := by nlinarith [abs_lt.mp hz, sq_abs z]
  have heq : (1 + z) / (1 - z) = x / y := by
    dsimp [z]
    field_simp [hy.ne']
    ring
  have he : log ((1 + z) / (1 - z)) / (2 * z) - 1 =
      (x + y) / 2 * (log x - log y) / (x - y) - 1 := by
    rw [heq, log_div hx.ne' hy.ne']
    dsimp [z]
    field_simp
  have hl : z ^ 2 / 3 = (x - y) ^ 2 / (3 * (x + y) ^ 2) := by
    dsimp [z]
    field_simp [hs.ne']
  have hu : z ^ 2 / (3 * (1 - z ^ 2)) = (x - y) ^ 2 / (12 * x * y) := by
    apply (div_eq_div_iff (by positivity : 3 * (1 - z ^ 2) ≠ 0)
      (by positivity : 12 * x * y ≠ 0)).mpr
    dsimp [z]
    field_simp [hs.ne']
    ring
  rw [he, hl] at hlow
  rw [he, hu] at hupp
  constructor <;> linarith

/-- For ordered positive arguments, the logarithmic mean is below the arithmetic mean. -/
private theorem logMean_lt_arithmetic_of_lt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    (x - y) / (log x - log y) < (x + y) / 2 := by
  have hx : 0 < x := hy.trans hxy
  have hd : 0 < log x - log y := sub_pos.mpr (log_lt_log hy hxy)
  have h := lt_log_one_add_of_pos (x := (x - y) / y) (div_pos (sub_pos.mpr hxy) hy)
  have harg : 1 + (x - y) / y = x / y := by field_simp; ring
  have hrat : 2 * ((x - y) / y) / ((x - y) / y + 2) = 2 * (x - y) / (x + y) := by
    field_simp
    ring
  rw [harg, hrat, log_div hx.ne' hy.ne'] at h
  have hh := (div_lt_iff₀ (add_pos hx hy)).mp h
  apply (div_lt_iff₀ hd).mpr
  nlinarith

/-- For ordered positive arguments, the logarithmic mean exceeds the geometric mean. -/
private theorem geometric_lt_logMean_of_lt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    sqrt (x * y) < (x - y) / (log x - log y) := by
  have hx : 0 < x := hy.trans hxy
  have hu : 0 < sqrt x := sqrt_pos.mpr hx
  have hv : 0 < sqrt y := sqrt_pos.mpr hy
  have hq : 1 < sqrt x / sqrt y := (one_lt_div hv).mpr (sqrt_lt_sqrt hy.le hxy)
  have h := self_lt_sinh_iff.mpr (log_pos hq)
  rw [sinh_log (div_pos hu hv), log_div hu.ne' hv.ne', log_sqrt hx.le, log_sqrt hy.le] at h
  have hm := mul_lt_mul_of_pos_right h (show 0 < 2 * sqrt x * sqrt y by positivity)
  have he : ((sqrt x / sqrt y - (sqrt x / sqrt y)⁻¹) / 2) *
      (2 * sqrt x * sqrt y) = x - y := by
    field_simp
    nlinarith [sq_sqrt hx.le, sq_sqrt hy.le]
  rw [he] at hm
  rw [sqrt_mul hx.le]
  apply (lt_div_iff₀ (sub_pos.mpr (log_lt_log hy hxy))).mpr
  nlinarith

/-- **Carlson Theorem 2.6-1.** The logarithmic mean of two distinct positive
arguments lies strictly between their geometric and arithmetic means. -/
theorem geometric_lt_logarithmicMean_lt_arithmetic {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    sqrt (x * y) < (x - y) / (log x - log y) ∧
      (x - y) / (log x - log y) < (x + y) / 2 := by
  rcases lt_or_gt_of_ne hne with hxy | hxy
  · have hl := geometric_lt_logMean_of_lt hx hxy
    have hu := logMean_lt_arithmetic_of_lt hx hxy
    have he : (y - x) / (log y - log x) = (x - y) / (log x - log y) := by
      apply (div_eq_div_iff (sub_ne_zero.mpr (log_lt_log hx hxy).ne')
        (sub_ne_zero.mpr (log_lt_log hx hxy).ne)).mpr
      ring
    rw [he, mul_comm y x] at hl
    rw [he, add_comm y x] at hu
    exact ⟨hl, hu⟩
  · exact ⟨geometric_lt_logMean_of_lt hy hxy, logMean_lt_arithmetic_of_lt hy hxy⟩

end Real
