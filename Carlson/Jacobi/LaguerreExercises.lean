/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Laguerre
public import Carlson.Jacobi.RPolynomialExercises
public import Carlson.TwoVariable.RPolynomial.EqualParameter
import Pochhammer.Vandermonde

/-!
# Laguerre polynomials in the standard normalization (Exercises 7.9-1 – 7.9-8)

The standard generalized Laguerre polynomial `L_n^β` is Carlson's monic Laguerre polynomial
divided by `(-1)ⁿ n!`. Its generating functions are obtained by regrouping absolutely convergent
double series along antidiagonals.

## Main results

* `Carlson.TwoVariable.laguerre`, `monicLaguerre_eq`: the standard normalization.
* `Carlson.TwoVariable.hasSum_laguerre_generating`: Exercise 7.9-2.
* `Carlson.TwoVariable.hasSum_laguerre_exp`: Exercise 7.9-1.
* `Carlson.TwoVariable.hasSum_laguerre_exp_zeroFOne`: Exercise 7.9-5.
* `Carlson.TwoVariable.laguerre_add`: Exercise 7.9-6.
* `Carlson.TwoVariable.derivative_laguerre`: Exercise 7.9-8.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.9.
-/

open Complex Polynomial Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Regrouping a double series along antidiagonals, from fiberwise sums and summable fiber
norms. -/
theorem hasSum_antidiagonal_of_fiberwise {f : ℕ × ℕ → ℂ} {g : ℕ → ℂ} {F : ℂ}
    (hfib : ∀ m, HasSum (fun k => f (m, k)) (g m)) (hg : HasSum g F)
    (hnf : ∀ m, Summable fun k => ‖f (m, k)‖) (hnorm : Summable fun m => ∑' k, ‖f (m, k)‖) :
    HasSum (fun n => ∑ p ∈ antidiagonal n, f p) F := by
  have hsum : Summable f :=
    Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).mpr ⟨hnf, hnorm⟩)
  have hf : HasSum f F := by
    have h := hsum.hasSum
    rwa [← hg.unique (h.prod_fiberwise hfib)] at h
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr hf
  exact he.sigma (g := fun n => ∑ p ∈ antidiagonal n, f p) fun n => by
    have := hasSum_fintype (fun c : antidiagonal n => f c.1)
    rwa [← Finset.sum_coe_sort (antidiagonal n) f]

/-- The real binomial series `∑ (B)ₖ sᵏ/k! = (1 - s)^{-B}` for `0 ≤ B`, `0 ≤ s < 1`. -/
theorem hasSum_real_ascPochhammer_div_factorial_mul_pow {B s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℝ k).eval B / k.factorial * s ^ k) ((1 - s) ^ (-B)) := by
  have h := (hasSum_ascPochhammer_div_factorial_mul_pow (B : ℂ) (u := (s : ℂ))
    (by rw [Complex.norm_real, Real.norm_of_nonneg hs0]; exact hs1)).1
  have hval : (1 : ℂ) / (1 - (s : ℂ)) ^ (B : ℂ) = (((1 - s) ^ (-B) : ℝ) : ℂ) := by
    rw [Real.rpow_neg (by linarith), ofReal_inv, ofReal_cpow (by linarith), one_div]; push_cast; rfl
  rw [hval] at h
  refine (Complex.hasSum_ofReal).mp (h.congr_fun fun k => ?_)
  push_cast
  congr 2
  rw [← ascPochhammer_map (algebraMap ℝ ℂ), eval_map]
  exact (Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) B).symm

/-- The generalized Laguerre polynomial in the standard normalization,
`L_n^β(x) = ∑ₘ (-1)ᵐ (β + m + 1)_{n-m} xᵐ/((n - m)! m!)`. -/
def laguerre (β : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ m ∈ range (n + 1), C ((-1) ^ m * (ascPochhammer ℂ (n - m)).eval (β + m + 1) /
    ((n - m).factorial * m.factorial)) * X ^ m

/-- Evaluation of the standard Laguerre polynomial. -/
theorem eval_laguerre (β x : ℂ) (n : ℕ) :
    (laguerre β n).eval x = ∑ m ∈ range (n + 1), (-1) ^ m *
      (ascPochhammer ℂ (n - m)).eval (β + m + 1) / ((n - m).factorial * m.factorial) * x ^ m := by
  simp [laguerre, eval_finsetSum]

/-- Carlson's monic Laguerre polynomial is `(-1)ⁿ n!` times the standard one. -/
theorem monicLaguerre_eq (β : ℂ) (n : ℕ) :
    monicLaguerre β n = C ((-1 : ℂ) ^ n * n.factorial) * laguerre β n := by
  rw [monicLaguerre, laguerre, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [← mul_assoc, ← C_mul]
  congr 2
  have hneg : (ascPochhammer ℂ (n - m)).eval (-β - n) =
      (-1) ^ (n - m) * (ascPochhammer ℂ (n - m)).eval (β + m + 1) := by
    rw [show -β - (n : ℂ) = -(β + n) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_ascPochhammer]
    congr 2; push_cast [Nat.cast_sub hmn]; ring
  rw [hneg, Nat.cast_choose ℂ hmn]
  have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have hsign : ((-1 : ℂ) ^ (n - m)) = (-1) ^ n * (-1) ^ m := by
    conv_rhs => rw [← Nat.sub_add_cancel hmn]
    rw [pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
  rw [hsign]
  field_simp

/-- The `₁F₁` coefficients are absolutely summable against any geometric sequence. -/
theorem summable_norm_oneFOne_coeff (a : ℂ) {b : ℂ} (hb : ∀ m : ℕ, (ascPochhammer ℂ m).eval b ≠ 0)
    (q : ℝ) :
    Summable fun m : ℕ => ‖(ascPochhammer ℂ m).eval a / ((ascPochhammer ℂ m).eval b *
      m.factorial)‖ * q ^ m := by
  set A : ℝ := ‖a‖ + 1
  set g : ℕ → ℝ := fun m => (ascPochhammer ℝ m).eval A / (‖(ascPochhammer ℂ m).eval b‖ *
    m.factorial) * |q| ^ m
  have hbound : ∀ m : ℕ, ‖‖(ascPochhammer ℂ m).eval a / ((ascPochhammer ℂ m).eval b *
      m.factorial)‖ * q ^ m‖ ≤ g m := fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_pow, norm_div, norm_mul, Complex.norm_natCast]
    simp only [g]
    gcongr
    exact norm_ascPochhammer_eval_le_ascPochhammer a m (by simp [A])
  refine Summable.of_norm_bounded ?_ hbound
  by_cases hq : q = 0
  · refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    simp [g, hq, zero_pow hm]
  have hA : 0 < A := by positivity
  have hg0 : ∀ m, g m ≠ 0 := fun m => by
    simp only [g]
    refine mul_ne_zero (div_ne_zero ?_ ?_) (pow_ne_zero _ (abs_ne_zero.mpr hq))
    · exact (ascPochhammer_pos m A hA).ne'
    · exact mul_ne_zero (norm_ne_zero_iff.mpr (hb m)) (by exact_mod_cast m.factorial_ne_zero)
  have hstep : ∀ m : ℕ, g (m + 1) = g m * ((A + m) * |q| / (‖b + m‖ * (m + 1))) := fun m => by
    have hB : ‖b + m‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h0; apply hb (m + 1)
      rw [ascPochhammer_succ_eval, h0, mul_zero]
    have hP : ‖(ascPochhammer ℂ m).eval b‖ ≠ 0 := norm_ne_zero_iff.mpr (hb m)
    have hF : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    simp only [g, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, norm_mul]
    push_cast
    field_simp
    ring
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall hg0) ?_
  have hden : Tendsto (fun m : ℕ => ‖b + m‖ * ((m : ℝ) + 1) / (A + m)) atTop atTop := by
    have hlin : Tendsto (fun m : ℕ => ((m : ℝ) - ‖b‖ - A) / 2) atTop atTop := by
      refine Tendsto.atTop_div_const (by norm_num) ?_
      exact tendsto_atTop_add_const_right _ _
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    refine tendsto_atTop_mono' _ ((eventually_ge_atTop ⌈A⌉₊).mono fun m hm => ?_) hlin
    have hmA : A ≤ m := (Nat.ceil_le).mp hm
    have h1 : (m : ℝ) - ‖b‖ ≤ ‖b + m‖ := by
      have := norm_sub_norm_le ((m : ℂ)) (-b)
      rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast, add_comm] at this; linarith
    have hpos : 0 < A + m := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [le_div_iff₀ hpos]
    have h2 : 0 ≤ ‖b + m‖ := norm_nonneg _
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hlim := (tendsto_const_nhds (x := |q|)).div_atTop hden
  refine hlim.congr fun m => ?_
  rw [Real.norm_of_nonneg, Real.norm_of_nonneg, hstep, mul_div_cancel_left₀ _ (hg0 m)]
  · have : 0 < A + m := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    field_simp
  · simp only [g]; have := ascPochhammer_pos m A hA; positivity
  · simp only [g]; have := ascPochhammer_pos (m + 1) A hA; positivity

/-- **Exercise 7.9-2**: if `1 + β` is not a nonpositive integer and `|t| < 1`,
`(1 - t)^{-1-α} ₁F₁(1 + α; 1 + β; tx/(t - 1)) = ∑ₙ (1 + α)ₙ/(1 + β)ₙ tⁿ L_n^β(x)`. -/
theorem hasSum_laguerre_generating (α : ℂ) {β : ℂ}
    (hβ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + β) ≠ 0) {t : ℂ} (ht : ‖t‖ < 1) (x : ℂ) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (1 + α) / (ascPochhammer ℂ n).eval (1 + β) *
        t ^ n * (laguerre β n).eval x)
      ((1 - t) ^ (-(1 + α)) * ∑' m : ℕ, (ascPochhammer ℂ m).eval (1 + α) /
        ((ascPochhammer ℂ m).eval (1 + β) * m.factorial) * (t * x / (t - 1)) ^ m) := by
  set c : ℕ → ℂ := fun m => (ascPochhammer ℂ m).eval (1 + α) /
    ((ascPochhammer ℂ m).eval (1 + β) * m.factorial)
  set z : ℂ := t * x / (t - 1)
  have ht1 : 1 - t ≠ 0 := fun h => by
    have : t = 1 := by linear_combination -h
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have ht1' : t - 1 ≠ 0 := fun h => ht1 (by linear_combination -h)
  set f : ℕ × ℕ → ℂ := fun p => c p.1 * (-x * t) ^ p.1 *
    ((ascPochhammer ℂ p.2).eval (1 + α + p.1) / (p.2.factorial : ℂ) * t ^ p.2)
  set g : ℕ → ℂ := fun m => (1 - t) ^ (-(1 + α)) * (c m * z ^ m)
  have hfib : ∀ m, HasSum (fun k => f (m, k)) (g m) := fun m => by
    have h := ((hasSum_ascPochhammer_div_factorial_mul_pow (1 + α + m) ht).1).mul_left
      (c m * (-x * t) ^ m)
    convert h using 1
    simp only [g, z]
    rw [cpow_add _ _ ht1, cpow_natCast, cpow_neg, div_pow]
    field_simp
    rw [show t - 1 = -(1 - t) by ring, neg_pow, neg_pow (t * x), mul_pow]
    have h11 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(c m * (1 - t) ^ m * t ^ m * x ^ m / (1 - t) ^ (1 + α))) * h11
  have hg : HasSum g ((1 - t) ^ (-(1 + α)) * ∑' m, c m * z ^ m) := by
    have hs : Summable fun m => c m * z ^ m := by
      refine Summable.of_norm ?_
      have := summable_norm_oneFOne_coeff (1 + α) hβ ‖z‖
      refine this.congr fun m => ?_
      simp only [c, norm_mul, norm_pow]
    exact hs.hasSum.mul_left _
  have hnf : ∀ m, Summable fun k => ‖f (m, k)‖ := fun m => by
    have h := ((hasSum_ascPochhammer_div_factorial_mul_pow (1 + α + m) ht).2).mul_left
      (‖c m * (-x * t) ^ m‖)
    refine h.congr fun k => ?_
    simp only [f, norm_mul]
  set A : ℝ := ‖1 + α‖
  set sr : ℝ := ‖t‖
  have hs0 : 0 ≤ sr := norm_nonneg t
  have hfibb : ∀ m, ∑' k, ‖f (m, k)‖ ≤ ‖c m‖ * ‖x * t‖ ^ m * (1 - sr) ^ (-(A + m)) := fun m => by
    have hreal := hasSum_real_ascPochhammer_div_factorial_mul_pow (B := A + m) hs0 ht
    have hle : ∀ k, ‖f (m, k)‖ ≤ ‖c m‖ * ‖x * t‖ ^ m *
        ((ascPochhammer ℝ k).eval (A + m) / k.factorial * sr ^ k) := fun k => by
      simp only [f, norm_mul, norm_pow, norm_div, Complex.norm_natCast, norm_neg]
      gcongr
      exact norm_ascPochhammer_eval_le_ascPochhammer _ _ (by
        calc ‖1 + α + m‖ ≤ ‖1 + α‖ + ‖(m : ℂ)‖ := norm_add_le _ _
          _ = A + m := by rw [Complex.norm_natCast])
    calc ∑' k, ‖f (m, k)‖ ≤ ∑' k, ‖c m‖ * ‖x * t‖ ^ m *
          ((ascPochhammer ℝ k).eval (A + m) / k.factorial * sr ^ k) :=
          (hnf m).tsum_le_tsum hle (hreal.summable.mul_left _)
      _ = _ := by rw [tsum_mul_left, hreal.tsum_eq]
  have hnorm : Summable fun m => ∑' k, ‖f (m, k)‖ := by
    have hsr : 0 < 1 - sr := by linarith
    have hmaj := (summable_norm_oneFOne_coeff (1 + α) hβ (‖x * t‖ / (1 - sr))).mul_left
      ((1 - sr) ^ (-A))
    refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => norm_nonneg _)
      (fun m => (hfibb m).trans (le_of_eq ?_)) hmaj
    rw [Real.rpow_neg hsr.le, Real.rpow_neg hsr.le, Real.rpow_add hsr, Real.rpow_natCast,
      div_pow]
    simp only [c]
    field_simp
  have h := hasSum_antidiagonal_of_fiberwise hfib hg hnf hnorm
  refine h.congr_fun fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m k => f (m, k)) n, eval_laguerre,
    mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hα := ascPochhammer_eval_eq_mul_of_le (1 + α) hmn
  have hβn := ascPochhammer_eval_eq_mul_of_le (1 + β) hmn
  have hβm := hβ m
  have hβk : (ascPochhammer ℂ (n - m)).eval (1 + β + m) ≠ 0 := fun h0 => hβ n (by
    rw [hβn, h0, mul_zero])
  have hf1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hf2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have htn : t ^ n = t ^ m * t ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  simp only [f, c]
  rw [hα, hβn, htn, show β + (m : ℂ) + 1 = 1 + β + m by ring, mul_pow, neg_pow x]
  field_simp

/-- **Exercise 7.9-1**: the generating function of the Laguerre polynomials,
`(1 - t)^{-1-β} exp(tx/(t - 1)) = ∑ₙ tⁿ L_n^β(x)` for `|t| < 1`. -/
theorem hasSum_laguerre_exp {β : ℂ} (hβ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + β) ≠ 0)
    {t : ℂ} (ht : ‖t‖ < 1) (x : ℂ) :
    HasSum (fun n : ℕ => t ^ n * (laguerre β n).eval x)
      ((1 - t) ^ (-(1 + β)) * exp (t * x / (t - 1))) := by
  have h := hasSum_laguerre_generating β hβ ht x
  have hexp : ∑' m : ℕ, (ascPochhammer ℂ m).eval (1 + β) /
      ((ascPochhammer ℂ m).eval (1 + β) * m.factorial) * (t * x / (t - 1)) ^ m =
      exp (t * x / (t - 1)) := by
    rw [exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    refine tsum_congr fun m => ?_
    have := hβ m
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    field_simp
  rw [hexp] at h
  refine h.congr_fun fun n => ?_
  rw [div_self (hβ n), one_mul]

/-- **Exercise 7.9-5**: `e^t ₀F₁(1 + β; -tx) = ∑ₙ tⁿ/(1 + β)ₙ L_n^β(x)` when `1 + β` is not a
nonpositive integer. -/
theorem hasSum_laguerre_exp_zeroFOne {β : ℂ}
    (hβ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + β) ≠ 0) (t x : ℂ) :
    HasSum (fun n : ℕ => t ^ n / (ascPochhammer ℂ n).eval (1 + β) * (laguerre β n).eval x)
      (exp t * ∑' m : ℕ, (-t * x) ^ m / ((ascPochhammer ℂ m).eval (1 + β) * m.factorial)) := by
  have hA : Summable fun k : ℕ => ‖t ^ k / (k.factorial : ℂ)‖ := by
    have := Real.summable_pow_div_factorial ‖t‖
    refine this.congr fun k => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
  have hB := summable_norm_pow_div_ascPochhammer_factorial hβ (-t * x)
  have h := hasSum_sum_range_mul_of_summable_norm hA hB
  have hexp : ∑' k : ℕ, t ^ k / (k.factorial : ℂ) = exp t := by
    rw [exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [hexp] at h
  refine h.congr_fun fun n => ?_
  rw [eval_laguerre, mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn]
  have hβn := ascPochhammer_eval_eq_mul_of_le (1 + β) (Nat.sub_le n m)
  rw [Nat.sub_sub_self hmn] at hβn
  have hβm := hβ (n - m)
  have hβk : (ascPochhammer ℂ m).eval (1 + β + ((n - m : ℕ) : ℂ)) ≠ 0 := fun h0 => hβ n (by
    rw [hβn, h0, mul_zero])
  have hf1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hf2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have htn : t ^ n = t ^ m * t ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hβn, htn, show β + ((n - m : ℕ) : ℂ) + 1 = 1 + β + ((n - m : ℕ) : ℂ) by ring, mul_pow,
    neg_pow t]
  field_simp

/-- **Exercise 7.9-6**: `L_n^{α+β}(x) = ∑ₘ (α)ₘ/m! L_{n-m}^β(x)`. -/
theorem laguerre_add (α β : ℂ) (n : ℕ) :
    laguerre (α + β) n = ∑ m ∈ range (n + 1),
      C ((ascPochhammer ℂ m).eval α / m.factorial) * laguerre β (n - m) := by
  apply Polynomial.funext
  intro x
  simp only [eval_finsetSum, eval_mul, eval_C, eval_laguerre, mul_sum]
  -- expand the Pochhammer symbol on the left by Chu–Vandermonde
  have hL : ∀ j ∈ range (n + 1), (-1 : ℂ) ^ j *
      (ascPochhammer ℂ (n - j)).eval (α + β + j + 1) / ((n - j).factorial * j.factorial) *
        x ^ j = ∑ m ∈ range (n - j + 1), (ascPochhammer ℂ m).eval α / m.factorial *
          ((-1) ^ j * (ascPochhammer ℂ (n - j - m)).eval (β + j + 1) /
            ((n - j - m).factorial * j.factorial) * x ^ j) := fun j hj => by
    rw [show α + β + (j : ℂ) + 1 = α + (β + j + 1) by ring, ascPochhammer_eval_add_sum_range,
      mul_sum, sum_div, sum_mul]
    refine sum_congr rfl fun m hm => ?_
    have hm' : m ≤ n - j := Nat.lt_succ_iff.mp (mem_range.mp hm)
    rw [Nat.cast_choose ℂ hm']
    have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have h2 : ((n - j - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - j - m).factorial_ne_zero
    have h3 : ((n - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
    have h4 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
  rw [sum_congr rfl hL]
  rw [Finset.sum_comm' (t' := range (n + 1)) (s' := fun m => range (n - m + 1))]
  · refine sum_congr rfl fun m hm => sum_congr rfl fun j hj => ?_
    rw [show n - j - m = n - m - j by omega]
  · intro j m
    simp only [mem_range]
    omega

/-- **Exercise 7.9-8**: `(d/dx) L_n^β(x) = -L_{n-1}^{β+1}(x)`. -/
theorem derivative_laguerre (β : ℂ) (n : ℕ) :
    derivative (laguerre β (n + 1)) = -laguerre (β + 1) n := by
  rw [laguerre, laguerre, derivative_sum, sum_range_succ', ← sum_neg_distrib]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow,
    Nat.cast_zero, map_zero, mul_zero, add_zero]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Nat.add_sub_cancel, ← mul_assoc, ← C_mul, ← neg_mul, ← C_neg,
    show n + 1 - (j + 1) = n - j by omega]
  congr 2
  rw [show β + ((j + 1 : ℕ) : ℂ) + 1 = β + 1 + j + 1 by push_cast; ring, Nat.factorial_succ]
  have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h2 : ((n - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  push_cast
  field_simp
  ring

end Carlson.TwoVariable
