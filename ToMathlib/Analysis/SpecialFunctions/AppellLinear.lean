/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF1
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The third-order series in Carlson's linear Appell transformation

Carlson (1976), *The need for a new classification of double hypergeometric series*,
equation (4). The transformed series converges absolutely in `‖X‖ + ‖Y‖ < 1`.
The two split parameters are positive real numbers, as in the article; the other
parameters may be arbitrary complex numbers when the denominator is Gamma-regularized.
The majorant is a Gauss series, using Mathlib's convergence-radius theorem.
-/

open Polynomial Filter
open scoped Topology

@[expose] public noncomputable section
namespace Complex

/-- The regularized third-order coefficient in Carlson's linear transformation.
The binomial factor converts the total-degree factorial into `m! n!`. -/
def regularizedAppellLinearCoeff (a b b' c : ℂ) (p : ℕ × ℕ) : ℂ :=
  regularizedHGFunCoeff {a, b + b'} {c} (p.1 + p.2) *
    ((p.1 + p.2).choose p.1 : ℂ) *
      ((ascPochhammer ℂ p.1).eval b / (ascPochhammer ℂ p.1).eval (b + b'))

/-- The explicit Pochhammer form of Carlson's regularized third-order coefficient. -/
theorem regularizedAppellLinearCoeff_eq (a b b' c : ℂ) (m n : ℕ) :
    regularizedAppellLinearCoeff a b b' c (m, n) =
      (ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ (m + n)).eval (b + b') *
        (ascPochhammer ℂ m).eval b /
        (Gamma (c + (m + n : ℕ)) * (ascPochhammer ℂ m).eval (b + b') *
          (m.factorial : ℂ) * n.factorial) := by
  simp only [regularizedAppellLinearCoeff, regularizedHGFunCoeff, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  rw [Nat.cast_choose ℂ (Nat.le_add_right m n), Nat.add_sub_cancel_left]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (m + n).factorial_ne_zero]

/-- The third-order double series obtained by a linear change of Appell's variables. -/
def regularizedAppellLinear (a b b' c X Y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2

/-- The ordinary normalization of Carlson's transformed double series. -/
def appellLinear (a b b' c X Y : ℂ) : ℂ :=
  Gamma c * regularizedAppellLinear a b b' c X Y

/-- Positive real split parameters give a Pochhammer ratio in the unit interval. -/
private theorem norm_pochhammer_split_le_one {b b' : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval (b : ℂ) /
      (ascPochhammer ℂ n).eval ((b : ℂ) + b')‖ ≤ 1 := by
  have hmono : (ascPochhammer ℝ n).eval b ≤ (ascPochhammer ℝ n).eval (b + b') := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      exact mul_le_mul ih (by linarith) (by positivity)
        (ascPochhammer_pos n (b + b') (by positivity)).le
  have he (x : ℝ) : (ascPochhammer ℂ n).eval (x : ℂ) =
      (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
    rw [ascPochhammer_eval₂ Complex.ofRealHom]
    exact eval₂_at_apply Complex.ofRealHom x
  rw [← ofReal_add, he, he, ← ofReal_div, norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (ascPochhammer_pos n b hb)
      (ascPochhammer_pos n (b + b') (by positivity)))]
  exact (div_le_one (ascPochhammer_pos n (b + b') (by positivity))).mpr hmono

/-- The total-degree majorant for the transformed series is a Gauss coefficient
multiplied by `(‖X‖ + ‖Y‖)^N`. -/
private theorem sum_norm_appellLinear_le (a c : ℂ) {b b' : ℝ}
    (hb : 0 < b) (hb' : 0 < b') (X Y : ℂ) (N : ℕ) :
    ∑ p ∈ Finset.antidiagonal N,
      ‖regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2‖ ≤
      ‖regularizedHGFunCoeff {a, (b : ℂ) + b'} {c} N‖ * (‖X‖ + ‖Y‖) ^ N := by
  calc
    _ ≤ ∑ p ∈ Finset.antidiagonal N,
        ‖regularizedHGFunCoeff {a, (b : ℂ) + b'} {c} N‖ *
          ((N.choose p.1 : ℝ) * (‖X‖ ^ p.1 * ‖Y‖ ^ p.2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hdeg := Finset.mem_antidiagonal.mp hp
      simp only [regularizedAppellLinearCoeff, norm_mul, norm_pow, hdeg,
        norm_natCast]
      have h := norm_pochhammer_split_le_one hb hb' p.1
      calc
        _ ≤ ‖regularizedHGFunCoeff {a, (b : ℂ) + b'} {c} N‖ *
            (N.choose p.1 : ℝ) * 1 * ‖X‖ ^ p.1 * ‖Y‖ ^ p.2 := by gcongr
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum, (Commute.all ‖X‖ ‖Y‖).add_pow']
      simp only [nsmul_eq_mul]

/-- Absolute convergence of Carlson's third-order series in the open diamond.
Only the split parameters need be positive; `a` and the regularized `c` are arbitrary. -/
theorem summable_norm_regularizedAppellLinear (a c : ℂ) {b b' : ℝ}
    (hb : 0 < b) (hb' : 0 < b') {X Y : ℂ} (hXY : ‖X‖ + ‖Y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2‖) := by
  have hG : Summable (fun N : ℕ =>
      ‖regularizedHGFunCoeff {a, (b : ℂ) + b'} {c} N‖ * (‖X‖ + ‖Y‖) ^ N) := by
    have hs := (hasSum_regularizedHGFun_of_mem_eball (a := {a, (b : ℂ) + b'})
      (b := {c}) (z := ((‖X‖ + ‖Y‖ : ℝ) : ℂ)) (by
        rw [Metric.mem_eball, edist_zero_right]
        apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one (by simp))
        rw [← ofReal_norm, ENNReal.ofReal_lt_one]
        rw [norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (norm_nonneg X) (norm_nonneg Y))]
        exact hXY)).summable
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg X) (norm_nonneg Y))] using hs.norm
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  change Summable (fun N : ℕ => ∑' p : ↥(Finset.antidiagonal N),
    ‖regularizedAppellLinearCoeff a b b' c p.val * X ^ p.val.1 * Y ^ p.val.2‖)
  simp only [tsum_fintype]
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_ hG
  intro N
  calc
    _ = ∑ p ∈ Finset.antidiagonal N,
        ‖regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2‖ :=
      Finset.sum_coe_sort _ _
    _ ≤ _ := sum_norm_appellLinear_le a c hb hb' X Y N

/-- The absolutely convergent transformed double series has its defining sum. -/
theorem hasSum_regularizedAppellLinear (a c : ℂ) {b b' : ℝ}
    (hb : 0 < b) (hb' : 0 < b') {X Y : ℂ} (hXY : ‖X‖ + ‖Y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => regularizedAppellLinearCoeff a b b' c p * X ^ p.1 * Y ^ p.2)
      (regularizedAppellLinear a b b' c X Y) :=
  (summable_norm_regularizedAppellLinear a c hb hb' hXY).of_norm.hasSum

/-- The ordinary third-order double series, away from the denominator poles. -/
theorem hasSum_appellLinear (a c : ℂ) {b b' : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {X Y : ℂ} (hXY : ‖X‖ + ‖Y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ (p.1 + p.2)).eval a *
        (ascPochhammer ℂ (p.1 + p.2)).eval ((b : ℂ) + b') *
        (ascPochhammer ℂ p.1).eval (b : ℂ) /
        ((ascPochhammer ℂ (p.1 + p.2)).eval c *
          (ascPochhammer ℂ p.1).eval ((b : ℂ) + b') *
          (p.1.factorial : ℂ) * p.2.factorial)) * X ^ p.1 * Y ^ p.2)
      (appellLinear a b b' c X Y) := by
  rw [appellLinear]
  convert (hasSum_regularizedAppellLinear a c hb hb' hXY).mul_left (Gamma c) using 1
  funext p
  rw [regularizedAppellLinearCoeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc]
  have hcn : Gamma (c + (p.1 + p.2 : ℕ)) ≠ 0 := Gamma_ne_zero (fun k hk => by
    apply hc (k + (p.1 + p.2))
    push_cast at hk ⊢
    linear_combination hk)
  field_simp [Gamma_ne_zero hc, hcn]

end Complex
