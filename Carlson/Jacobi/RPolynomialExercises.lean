/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EndpointBridge
public import Carlson.Jacobi.SecondKind
public import Carlson.Jacobi.FiniteExpansion
public import Carlson.RPolynomial.DifferentialForm
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Carlson.RPolynomial.TaylorContinuation
public import Carlson.TwoVariable.Quadratic.Polynomial
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# R-polynomial exercises of Chapter 7

Identities for the Jacobi R-polynomials `Rₙ(-α - n, -β - n; x, y)` and the Jacobi functions of
the second kind, stated for the Pochhammer numerators where that removes exceptional parameters.

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_jacobi_eq_sum`: Exercise 7.1-1.
* `Carlson.TwoVariable.hasSum_bateman`: Bateman's generating relation, Exercise 7.1-2.
* `Carlson.TwoVariable.jacobiOn_eq_sum_monomial`, `hasSum_jacobiSecondKind_laurent`: the
  coefficients of `pₙ` and the expansion of `qₙ` at infinity, Exercise 7.1-5.
* `Carlson.TwoVariable.hasSum_zeroFOne_mul_zeroFOne`: Exercise 7.1-9.
* `Carlson.TwoVariable.affine_pow_eq_sum_jacobiOn`: Exercise 7.2-2.
* `Carlson.TwoVariable.iteratedDeriv_add_cpow_mul_add_cpow`: Exercise 7.8-5.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 7.
-/

open Polynomial Complex Finset Dirichlet Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- `(-a - n)ₘ (1 + a)_{n-m} = (-1)ᵐ (1 + a)ₙ` for `m ≤ n`. -/
theorem ascPochhammer_neg_sub_mul (a : ℂ) {m n : ℕ} (hm : m ≤ n) :
    (ascPochhammer ℂ m).eval (-a - n) * (ascPochhammer ℂ (n - m)).eval (1 + a) =
      (-1) ^ m * (ascPochhammer ℂ n).eval (1 + a) := by
  have h1 := ascPochhammer_eval_eq_mul_of_le (1 + a) (Nat.sub_le n m)
  rw [Nat.sub_sub_self hm] at h1
  have h2 : (ascPochhammer ℂ m).eval (-a - n) =
      (-1) ^ m * (ascPochhammer ℂ m).eval (1 + a + ((n - m : ℕ) : ℂ)) := by
    rw [show -a - (n : ℂ) = -(a + n) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_ascPochhammer]
    congr 2; push_cast [Nat.cast_sub hm]; ring
  rw [h1, h2]; ring

/-- **Exercise 7.1-1**, numerator form:
`Nₙ(-α - n, -β - n; x, y) =
(-1)ⁿ (1 + α)ₙ (1 + β)ₙ ∑ₘ (n choose m) xᵐ y^(n-m)/((1 + α)_(n-m) (1 + β)ₘ)`
when `(1 + α)ₙ` and `(1 + β)ₙ` do not vanish. -/
theorem carlsonRPolynomialNumerator₂_jacobi_eq_sum (n : ℕ) {α β : ℂ}
    (hα : (ascPochhammer ℂ n).eval (1 + α) ≠ 0) (hβ : (ascPochhammer ℂ n).eval (1 + β) ≠ 0)
    (x y : ℂ) :
    carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) x y =
      (-1) ^ n * (ascPochhammer ℂ n).eval (1 + α) * (ascPochhammer ℂ n).eval (1 + β) *
        ∑ m ∈ range (n + 1), (n.choose m : ℂ) * x ^ m * y ^ (n - m) /
          ((ascPochhammer ℂ (n - m)).eval (1 + α) * (ascPochhammer ℂ m).eval (1 + β)) := by
  rw [carlsonRPolynomialNumerator₂_eq_sum_range, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hA := ascPochhammer_neg_sub_mul α hmn
  have hB := ascPochhammer_neg_sub_mul β (Nat.sub_le n m)
  rw [Nat.sub_sub_self hmn] at hB
  have hA0 : (ascPochhammer ℂ (n - m)).eval (1 + α) ≠ 0 := fun h0 => hα (by
    rw [ascPochhammer_eval_eq_mul_of_le (1 + α) (Nat.sub_le n m), h0, zero_mul])
  have hB0 : (ascPochhammer ℂ m).eval (1 + β) ≠ 0 := fun h0 => hβ (by
    rw [ascPochhammer_eval_eq_mul_of_le (1 + β) hmn, h0, zero_mul])
  have hsign : ((-1 : ℂ) ^ m) * (-1) ^ (n - m) = (-1) ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [mul_div_assoc', eq_div_iff (mul_ne_zero hA0 hB0)]
  linear_combination (n.choose m : ℂ) * x ^ m * y ^ (n - m) *
    ((ascPochhammer ℂ (n - m)).eval (-β - n) * (ascPochhammer ℂ m).eval (1 + β) * hA +
      (-1) ^ m * (ascPochhammer ℂ n).eval (1 + α) * hB +
      (ascPochhammer ℂ n).eval (1 + α) * (ascPochhammer ℂ n).eval (1 + β) * hsign)

/-- **Exercise 7.1-5, first part**: the coefficients of the monic Jacobi polynomial,
`pₙ(x) = ∑ₖ (n choose k) R_{n-k}(-α - n, -β - n; -r, -s) xᵏ`, with
`R_{n-k} = N_{n-k}/(-α - β - 2n)_{n-k}`. -/
theorem jacobiOn_eq_sum_monomial (α β r s : ℂ) (n : ℕ)
    (h : (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0) :
    jacobiOn α β r s n = ∑ k ∈ range (n + 1),
      C ((n.choose k : ℂ) * carlsonRPolynomialNumerator₂ (n - k) (-α - n) (-β - n) (-r) (-s) /
        (ascPochhammer ℂ (n - k)).eval (-α - β - 2 * n)) * X ^ k := by
  set c : ℂ := -α - β - 2 * n
  have hc : (ascPochhammer ℂ n).eval c ≠ 0 := by
    have : (ascPochhammer ℂ n).eval c =
        (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval (α + β + n + 1) := by
      rw [show c = -(α + β + n + 1 + n - 1) by simp only [c]; ring,
        ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
      congr 2; ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
  apply Polynomial.funext
  intro x
  rw [eval_jacobiOn_eq_numerator α β r s x n h]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  have hadd := carlsonRPolynomialNumerator₂_add_const n (-α - n) (-β - n) (-r) (-s) x
  rw [show -r + x = x - r by ring, show -s + x = x - s by ring] at hadd
  rw [hadd, sum_div, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self hkn, Nat.choose_symm hkn]
  have hsplit := ascPochhammer_eval_eq_mul_of_le c (Nat.sub_le n k)
  rw [show n - (n - k) = k by omega] at hsplit
  have hck : (ascPochhammer ℂ (n - k)).eval c ≠ 0 := fun h0 => hc (by rw [hsplit, h0, zero_mul])
  have hck' : (ascPochhammer ℂ k).eval (c + ((n - k : ℕ) : ℂ)) ≠ 0 := fun h0 =>
    hc (by rw [hsplit, h0, mul_zero])
  rw [show -α - (n : ℂ) + (-β - n) + ((n - k : ℕ) : ℂ) = c + ((n - k : ℕ) : ℂ) by
    simp only [c]; ring, hsplit]
  field_simp

/-- Iterated derivatives of `w ↦ (y - w)^{-(n+1)}` at `0`:
`(n + 1)ₘ y^{-(n+1+m)}`. -/
theorem iteratedDeriv_sub_zpow_zero (n m : ℕ) (y : ℂ) :
    iteratedDeriv m (fun w : ℂ => (y - w) ^ (-((n : ℤ) + 1))) 0 =
      (ascPochhammer ℂ m).eval ((n : ℂ) + 1) * y ^ (-((n : ℤ) + 1) - m) := by
  have hc := iteratedDeriv_comp_const_sub (n := m) (f := fun x : ℂ => x ^ (-((n : ℤ) + 1)))
    (s := y)
  rw [congrFun hc 0, sub_zero, iteratedDeriv_eq_iterate, iter_deriv_zpow, smul_eq_mul]
  have hprod : (-1 : ℂ) ^ m * ∏ i ∈ range m, (((-((n : ℤ) + 1) : ℤ) : ℂ) - i) =
      (ascPochhammer ℂ m).eval ((n : ℂ) + 1) := by
    clear hc
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, pow_succ, ascPochhammer_succ_eval, ← ih]; push_cast; ring
  rw [← mul_assoc, hprod]

/-- **Exercise 7.1-5, second part**: the expansion of the Jacobi function of the second kind at
infinity, `qₙ(y) = ∑ₘ (n + m choose m) R_m(1 + α + n, 1 + β + n; r, s) y^{-n-1-m}` for
`|y| > |r|, |s|`. Here `R_m` is written as `Γ(c) R_m/Γ(c)` with `c = 2 + α + β + 2n`, which holds
for all parameters. -/
theorem hasSum_jacobiSecondKind_laurent (α β r s : ℂ) (n : ℕ) {y : ℂ} (hr : ‖r‖ < ‖y‖)
    (hs : ‖s‖ < ‖y‖) :
    HasSum (fun m : ℕ => ((n + m).choose m : ℂ) * y ^ (-((n : ℤ) + 1) - m) *
        (Gamma (α + n + 1 + (β + n + 1)) *
          regCarlsonRPolynomial m (pair (α + n + 1) (β + n + 1)) (pair r s)))
      (jacobiSecondKind α β r s n y) := by
  have hy : 0 < ‖y‖ := (norm_nonneg r).trans_lt hr
  have hz : ‖fun i => pair r s i - 0‖ < ‖y‖ := by
    refine (pi_norm_lt_iff hy).mpr fun i => ?_
    fin_cases i <;> simpa [pair]
  have hhull : convexHull ℝ (Set.range (pair r s)) ⊆ Metric.ball 0 ‖y‖ := by
    refine convexHull_min ?_ (convex_ball 0 ‖y‖)
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simpa [pair]
  have hdom : (y, pair r s) ∈ carlsonResolventDomain := fun u hu h0 => by
    have hmem := hhull (carlsonAffineForm_mem_convexHull (pair r s) hu)
    rw [sub_eq_zero] at h0
    rw [← h0, Metric.mem_ball, dist_zero_right] at hmem
    exact lt_irrefl _ hmem
  have hG := isRegCarlsonContinuation_continuedRegCarlsonResolvent n hdom
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => (y - w) ^ (-((n : ℤ) + 1))) (Metric.ball 0 ‖y‖) := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) Metric.isOpen_ball
    have hw' : y - w ≠ 0 := fun h0 => by
      rw [sub_eq_zero] at h0; rw [← h0, Metric.mem_ball, dist_zero_right] at hw
      exact lt_irrefl _ hw
    exact ((differentiableAt_const _).sub differentiableAt_id).zpow (Or.inl hw')
      |>.differentiableWithinAt
  have hcast : (fun w : ℂ => (y - w) ^ (-((n : ℤ) + 1))) = fun w => (y - w) ^ (-(n + 1 : ℤ)) := by
    funext w; ring_nf
  rw [← hcast] at hG
  have h := hG.hasSum_taylor hf hz (pair (α + n + 1) (β + n + 1))
  simp only [sub_zero] at h
  unfold jacobiSecondKind
  refine (h.mul_left (Gamma (α + n + 1 + (β + n + 1)))).congr_fun fun m => ?_
  rw [iteratedDeriv_sub_zpow_zero]
  have hch : (ascPochhammer ℂ m).eval ((n : ℂ) + 1) =
      (m.factorial : ℂ) * ((n + m).choose m : ℂ) := by
    have := ascPochhammer_eval_cast (S := ℂ) m (n + 1)
    rw [ascPochhammer_nat_eq_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose] at this
    push_cast at this; rw [← this]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpair : (fun i => pair r s i) = pair r s := rfl
  rw [hch, hpair]
  field_simp

/-- `(1 - a - n)ₙ = (-1)ⁿ (a)ₙ`. -/
theorem ascPochhammer_one_sub_sub (a : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (1 - a - n) = (-1) ^ n * (ascPochhammer ℂ n).eval a := by
  rw [show 1 - a - (n : ℂ) = -(a + n - 1) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_ascPochhammer]
  congr 2; ring

/-- The `₀F₁` series `∑ zᵐ/((a)ₘ m!)` is absolutely summable when no `(a)ₘ` vanishes. -/
theorem summable_norm_pow_div_ascPochhammer_factorial {a : ℂ}
    (ha : ∀ m : ℕ, (ascPochhammer ℂ m).eval a ≠ 0) (z : ℂ) :
    Summable fun m : ℕ => ‖z ^ m / ((ascPochhammer ℂ m).eval a * m.factorial)‖ := by
  by_cases hz : z = 0
  · refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    simp [hz, zero_pow hm]
  set g : ℕ → ℝ := fun m => ‖z ^ m / ((ascPochhammer ℂ m).eval a * m.factorial)‖
  have hg0 : ∀ m, g m ≠ 0 := fun m => by
    simp only [g, norm_ne_zero_iff]
    exact div_ne_zero (pow_ne_zero _ hz) (mul_ne_zero (ha m) (by exact_mod_cast
      m.factorial_ne_zero))
  have hstep : ∀ m : ℕ, g (m + 1) = g m * (‖z‖ / (‖a + m‖ * (m + 1))) := fun m => by
    have hA : ‖(ascPochhammer ℂ m).eval a‖ ≠ 0 := norm_ne_zero_iff.mpr (ha m)
    have hB : ‖a + m‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h0; apply ha (m + 1)
      rw [ascPochhammer_succ_eval, h0, mul_zero]
    have hF : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    simp only [g, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, norm_div, norm_mul,
      norm_pow, Complex.norm_natCast]
    push_cast
    field_simp
    ring
  refine Summable.of_norm (summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall hg0) ?_ |>.norm)
  have hden : Tendsto (fun m : ℕ => ‖a + m‖ * ((m : ℝ) + 1)) atTop atTop := by
    have hlin : Tendsto (fun m : ℕ => (m : ℝ) - ‖a‖) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' _ (Eventually.of_forall fun m => ?_) hlin
    have h1 : (m : ℝ) - ‖a‖ ≤ ‖a + m‖ := by
      have := norm_sub_norm_le ((m : ℂ)) (-a)
      rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast, add_comm] at this; linarith
    have h2 : 0 ≤ ‖a + m‖ := norm_nonneg _
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hlim := (tendsto_const_nhds (x := ‖z‖)).div_atTop hden
  refine hlim.congr fun m => ?_
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
  change ‖z‖ / (‖a + m‖ * (m + 1)) = g (m + 1) / g m
  rw [hstep, mul_div_cancel_left₀ _ (hg0 m)]

/-- **Exercise 7.1-2** (Bateman's generating relation), numerator form: if `1 + α, 1 + β` are not
nonpositive integers, then
`₀F₁(1 + β; tx) ₀F₁(1 + α; ty) = ∑ₙ (-t)ⁿ Nₙ(-α - n, -β - n; x, y)/((1 + α)ₙ (1 + β)ₙ n!)`.
Since `(1 + α + β + n)ₙ Rₙ = (-1)ⁿ Nₙ`, this is Carlson's
`∑ tⁿ (1 + α + β + n)ₙ Rₙ(-α - n, -β - n; x, y)/((1 + α)ₙ (1 + β)ₙ n!)`. -/
theorem hasSum_bateman {α β : ℂ} (hα : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + α) ≠ 0)
    (hβ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + β) ≠ 0) (t x y : ℂ) :
    HasSum (fun n : ℕ => (-t) ^ n * carlsonRPolynomialNumerator₂ n (-α - n) (-β - n) x y /
        ((ascPochhammer ℂ n).eval (1 + α) * (ascPochhammer ℂ n).eval (1 + β) * n.factorial))
      ((∑' m : ℕ, (t * x) ^ m / ((ascPochhammer ℂ m).eval (1 + β) * m.factorial)) *
        ∑' m : ℕ, (t * y) ^ m / ((ascPochhammer ℂ m).eval (1 + α) * m.factorial)) := by
  have h := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_pow_div_ascPochhammer_factorial hβ (t * x))
    (summable_norm_pow_div_ascPochhammer_factorial hα (t * y))
  refine h.congr_fun fun n => ?_
  rw [carlsonRPolynomialNumerator₂_jacobi_eq_sum n (hα n) (hβ n), mul_sum, mul_sum, sum_div]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have h1 := hα (n - m)
  have h2 := hβ m
  have h3 := hα n
  have h4 := hβ n
  have hf1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hf2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have hchoose : (n.choose m : ℂ) = n.factorial / (m.factorial * (n - m).factorial) := by
    rw [Nat.cast_choose ℂ hmn]
  have h11 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have htn : t ^ n = t ^ m * t ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hchoose, neg_pow t n, htn]
  field_simp
  rw [mul_pow, mul_pow, show ((-1 : ℂ) ^ n) ^ 2 = 1 by rw [sq, h11]]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 7.1-9**: if `δ` and `2δ - 1` are not nonpositive integers, then
`₀F₁(δ; x²) ₀F₁(δ; y²) = ∑ₙ Rₙ(δ - ½, δ - ½; (x + y)², (x - y)²)/((δ)ₙ n!)`, with
`Rₙ = Nₙ/(2δ - 1)ₙ`. -/
theorem hasSum_zeroFOne_mul_zeroFOne {δ : ℂ} (hδ : ∀ m : ℕ, (ascPochhammer ℂ m).eval δ ≠ 0)
    (h2δ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (2 * δ - 1) ≠ 0) (x y : ℂ) :
    HasSum (fun n : ℕ => carlsonRPolynomialNumerator₂ n (δ - 1 / 2) (δ - 1 / 2) ((x + y) ^ 2)
        ((x - y) ^ 2) / ((ascPochhammer ℂ n).eval (2 * δ - 1) *
          (ascPochhammer ℂ n).eval δ * n.factorial))
      ((∑' m : ℕ, (x ^ 2) ^ m / ((ascPochhammer ℂ m).eval δ * m.factorial)) *
        ∑' m : ℕ, (y ^ 2) ^ m / ((ascPochhammer ℂ m).eval δ * m.factorial)) := by
  have hδ' : ∀ m : ℕ, (ascPochhammer ℂ m).eval (1 + (δ - 1)) ≠ 0 := fun m => by
    rw [show 1 + (δ - 1) = δ by ring]; exact hδ m
  have h := hasSum_bateman hδ' hδ' 1 (x ^ 2) (y ^ 2)
  simp only [show 1 + (δ - 1) = δ by ring, one_mul] at h
  refine h.congr_fun fun n => ?_
  have hq := carlsonRPolynomialNumerator₂_secondQuadratic n (1 - δ - n) x y
  rw [show 1 - 2 * (1 - δ - (n : ℂ)) - 2 * n = 2 * δ - 1 by ring,
    show (1 : ℂ) / 2 - (1 - δ - n) - n = δ - 1 / 2 by ring, ascPochhammer_one_sub_sub] at hq
  rw [show -(δ - 1) - (n : ℂ) = 1 - δ - n by ring]
  have h1 := h2δ n
  have h2 := hδ n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h11 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hN : carlsonRPolynomialNumerator₂ n (1 - δ - n) (1 - δ - n) (x ^ 2) (y ^ 2) =
      (-1) ^ n * (ascPochhammer ℂ n).eval δ * carlsonRPolynomialNumerator₂ n (δ - 1 / 2)
        (δ - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) / (ascPochhammer ℂ n).eval (2 * δ - 1) := by
    rw [eq_div_iff h1, ← hq]; ring
  rw [hN, neg_pow, one_pow]
  generalize carlsonRPolynomialNumerator₂ n (δ - 1 / 2) (δ - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) = N
  generalize (ascPochhammer ℂ n).eval (2 * δ - 1) = P at h1 ⊢
  generalize (ascPochhammer ℂ n).eval δ = D at h2 ⊢
  generalize ((-1 : ℂ) ^ n) = σ at h11 ⊢
  field_simp
  linear_combination (-N) * h11

/-- The Jacobi coefficient of `(A + Bx)ⁿ`:
`(n choose m) Bᵐ R_{n-m}(1 + α + m, 1 + β + m; A + Br, A + Bs)`, with `R = Γ(c) R/Γ(c)`. -/
theorem carlsonJacobiCoefficient_affine_pow (α β r s A B : ℂ) (n m : ℕ) :
    carlsonJacobiCoefficient α β r s m ((C B * X + C A) ^ n) =
      (n.choose m : ℂ) * B ^ m * (Gamma (α + m + 1 + (β + m + 1)) *
        regCarlsonRPolynomial (n - m) (pair (α + m + 1) (β + m + 1))
          (pair (A + B * r) (A + B * s))) := by
  rw [carlsonJacobiCoefficient_apply]
  have hp : (C B * X + C A) ^ n = (X ^ n).comp (C B * X + C A) := by simp
  rw [hp, iterate_derivative_comp_affine, iterate_derivative_X_pow_eq_C_mul, mul_comp, C_comp,
    pow_comp, X_comp]
  simp only [carlsonPolynomialAverage, LinearMap.smul_apply, smul_eq_mul]
  have hX : (C B * X + C A) ^ (n - m) = (X ^ (n - m)).comp (C B * X + C A) := by simp
  rw [← mul_assoc, ← C_mul, ← smul_eq_C_mul, map_smul, hX, regCarlsonPolynomialAverage_comp_affine,
    ← monomial_one_right_eq_X_pow, regCarlsonPolynomialAverage_monomial, smul_eq_mul, one_mul]
  have hz : (fun i => B * pair r s i + A) = pair (A + B * r) (A + B * s) := by
    funext i; fin_cases i <;> simp [pair] <;> ring
  rw [hz, sum_pair]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- **Exercise 7.2-2**: for admissible parameters,
`(A + Bx)ⁿ = ∑ₘ (n choose m) Bᵐ R_{n-m}(1 + α + m, 1 + β + m; A + Br, A + Bs) pₘ(x)`. -/
theorem affine_pow_eq_sum_jacobiOn (α β r s A B : ℂ) (hc : IsGammaRegular (α + β + 2)) (n : ℕ) :
    (C B * X + C A) ^ n = ∑ m ∈ range (n + 1),
      C ((n.choose m : ℂ) * B ^ m * (Gamma (α + m + 1 + (β + m + 1)) *
        regCarlsonRPolynomial (n - m) (pair (α + m + 1) (β + m + 1))
          (pair (A + B * r) (A + B * s)))) * jacobiOn α β r s m := by
  set p : ℂ[X] := (C B * X + C A) ^ n
  have hdeg : p.natDegree ≤ n := by
    refine natDegree_pow_le.trans ?_
    have : (C B * X + C A).natDegree ≤ 1 := natDegree_linear_le
    calc n * (C B * X + C A).natDegree ≤ n * 1 := Nat.mul_le_mul_left n this
      _ = n := mul_one n
  have h := sum_carlsonJacobiCoefficient α β r s hc p
  have hsub : range (p.natDegree + 1) ⊆ range (n + 1) := range_subset_range.mpr (by omega)
  rw [sum_subset hsub fun m hm hnot => ?_] at h
  · conv_lhs => rw [← h]
    refine sum_congr rfl fun m _ => ?_
    rw [carlsonJacobiCoefficient_affine_pow, smul_eq_C_mul]
  · have hm' : p.natDegree < m := by simp at hm hnot; omega
    rw [carlsonJacobiCoefficient_apply, iterate_derivative_eq_zero hm', map_zero, zero_div,
      zero_smul]

/-- **Exercise 7.8-5**: for `x, y` in the slit plane,
`(∂/∂x + ∂/∂y)ⁿ x^{-β'} y^{-β} = (-1)ⁿ x^{-β'} y^{-β} (xy)^{-n} Nₙ(β, β'; x, y)`, i.e.
`(β + β')ₙ Rₙ(β, β'; x, y) = (-1)ⁿ x^{β'+n} y^{β+n} (∂/∂x + ∂/∂y)ⁿ x^{-β'} y^{-β}`. The operator is
written as `d/dt` along the diagonal. -/
theorem iteratedDeriv_add_cpow_mul_add_cpow (n : ℕ) (β β' : ℂ) {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) :
    iteratedDeriv n (fun t => (x + t) ^ (-β') * (y + t) ^ (-β)) 0 =
      (-1) ^ n * x ^ (-β') * y ^ (-β) * carlsonRPolynomialNumerator₂ n β β' x y / (x * y) ^ n := by
  have hz : ∀ i, pair x y i ∈ slitPlane := fun i => by fin_cases i <;> assumption
  have h := iteratedDeriv_prod_add_cpow n (pair β' β) (pair x y) hz
  simp only [Fin.prod_univ_two, pair_zero, pair_one] at h
  rw [h]
  have hx0 := slitPlane_ne_zero hx
  have hy0 := slitPlane_ne_zero hy
  have hsm := carlsonRPolynomialNumerator₂_smul n β' β (x * y) x⁻¹ y⁻¹
  rw [show x * y * x⁻¹ = y by field_simp, show x * y * y⁻¹ = x by field_simp,
    carlsonRPolynomialNumerator₂_swap] at hsm
  have hxy : (x * y) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero hx0 hy0)
  have hpair : (fun i => (pair x y i)⁻¹) = pair x⁻¹ y⁻¹ := by
    funext i; fin_cases i <;> rfl
  rw [hpair, carlsonRPolynomialNumerator_pair, eq_div_iff hxy]
  rw [hsm]; ring

end Carlson.TwoVariable
