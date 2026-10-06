/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.GegenbauerProduct
public import Carlson.TwoVariable.BilateralContinuation
public import Carlson.PolynomialAverage
public import Carlson.TwoVariable.RPolynomial.EqualParameter

/-!
# Ossicini's and Gegenbauer's product formulas at complex angles

`Carlson.Jacobi.GegenbauerProduct` proves Corollary 6.11-3 and Theorem 6.11-4 for real angles and
`re ν > 0`. Here they are proved in the generality of the book. Ossicini's formula follows from
Meixner's formula for all parameters (`hasSum_meixner_continued`); the product formula is
extended from real to complex angles by the identity theorem, one angle at a time.

## Main results

* `Carlson.TwoVariable.hasSum_ossicini_complex`: Corollary 6.11-3 for `2ν` not a nonpositive
  integer, complex `θ, φ, t` and `‖t‖ < exp(-|Im θ| - |Im φ|)`.
* `Carlson.TwoVariable.gegenbauer_product_formula_complex`: Theorem 6.11-4 for `re ν > 0` and
  complex `θ, φ`.
* `Carlson.TwoVariable.norm_eval_gegenbauer_cos_le`: the bound of Exercise 6.7-2.
* `Carlson.TwoVariable.eval_gegenbauer_eq_sum`: the coefficient formula, Exercise 6.9-4.
* `Carlson.TwoVariable.eval_gegenbauer_even_zero`, `eval_gegenbauer_odd_zero`: Exercise 6.9-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.11.
-/

open Dirichlet
open Complex Set Filter Polynomial
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- `‖t e^{±iθ} e^{±iφ}‖ < 1` under Carlson's hypothesis `‖t‖ < exp(-|Im θ| - |Im φ|)`. -/
theorem norm_mul_exp_mul_exp_lt {t θ φ : ℂ} (ht : ‖t‖ < Real.exp (-|θ.im| - |φ.im|))
    (s₁ s₂ : ℂ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    ‖t * exp (s₁ * θ * I) * exp (s₂ * φ * I)‖ < 1 := by
  rw [norm_mul, norm_mul, norm_exp, norm_exp]
  have hθ : (s₁ * θ * I).re ≤ |θ.im| := by
    rcases hs₁ with rfl | rfl <;> simp [neg_le_abs, le_abs_self]
  have hφ : (s₂ * φ * I).re ≤ |φ.im| := by
    rcases hs₂ with rfl | rfl <;> simp [neg_le_abs, le_abs_self]
  calc ‖t‖ * Real.exp (s₁ * θ * I).re * Real.exp (s₂ * φ * I).re
      ≤ ‖t‖ * Real.exp |θ.im| * Real.exp |φ.im| := by gcongr
    _ < Real.exp (-|θ.im| - |φ.im|) * Real.exp |θ.im| * Real.exp |φ.im| := by
        gcongr
    _ = 1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp

/-- The regularized Ossicini series for all parameters `ν`, complex angles, and
`‖t‖ < exp(-|Im θ| - |Im φ|)`. -/
theorem hasSum_regOssicini_complex (ν θ φ : ℂ) {t : ℂ}
    (ht : ‖t‖ < Real.exp (-|θ.im| - |φ.im|)) :
    HasSum (fun n : ℕ => t ^ n * n.factorial * (gegenbauer ν n).eval (cos θ) *
        (gegenbauer ν n).eval (cos φ) * (Gamma (2 * ν + n))⁻¹)
      (regCarlsonR (-ν) (pair ν ν)
        (pair (1 - 2 * t * cos (θ + φ) + t ^ 2) (1 - 2 * t * cos (θ - φ) + t ^ 2))) := by
  set a := exp (θ * I)
  set b := exp (φ * I)
  have ha0 : a ≠ 0 := exp_ne_zero _
  have hb0 : b ≠ 0 := exp_ne_zero _
  have hinv (z : ℂ) : (exp (z * I))⁻¹ = exp ((-1) * z * I) := by
    rw [← exp_neg]; ring_nf
  have hn (s₁ s₂ : ℂ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) :=
    norm_mul_exp_mul_exp_lt ht s₁ s₂ h₁ h₂
  have e1 : a = exp (1 * θ * I) := by simp [a]
  have e2 : b = exp (1 * φ * I) := by simp [b]
  have h := hasSum_meixner_continued ν ν (2 * ν) (t * a) (t * a⁻¹) b b⁻¹
    (by rw [e1, e2]; exact hn 1 1 (.inl rfl) (.inl rfl))
    (by rw [e1, hinv]; exact hn 1 (-1) (.inl rfl) (.inr rfl))
    (by rw [hinv, e2]; exact hn (-1) 1 (.inr rfl) (.inl rfl))
    (by rw [hinv, hinv]; exact hn (-1) (-1) (.inr rfl) (.inr rfl))
  rw [show 2 * ν - ν = ν by ring, show ν - ν = 0 by ring, show ν + ν - 2 * ν = 0 by ring,
    cpow_zero, cpow_zero, one_mul, one_mul] at h
  have hA : (1 - t * a * b) * (1 - t * a⁻¹ * b⁻¹) = 1 - 2 * t * cos (θ + φ) + t ^ 2 := by
    have := one_sub_mul_exp_mul t (θ + φ)
    rw [add_mul, exp_add, mul_inv] at this
    rw [← this]; ring
  have hB : (1 - t * a * b⁻¹) * (1 - t * a⁻¹ * b) = 1 - 2 * t * cos (θ - φ) + t ^ 2 := by
    have := one_sub_mul_exp_mul t (θ - φ)
    rw [show (θ - φ) * I = θ * I + -(φ * I) by ring, exp_add, exp_neg, mul_inv,
      inv_inv] at this
    rw [← this]; ring
  rw [hA, hB] at h
  refine h.congr_fun fun n => ?_
  have hθ := factorial_mul_eval_gegenbauer ν a ha0 n
  have hφ := factorial_mul_eval_gegenbauer ν b hb0 n
  rw [exp_add_inv_div_two] at hθ hφ
  rw [carlsonRPolynomialNumerator₂_smul, ← hθ, regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
    ← hφ, show ν + ν + (n : ℂ) = 2 * ν + n by ring]
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- **Ossicini's formula** (Corollary 6.11-3) in Carlson's generality: if `2ν` is not a
nonpositive integer, `θ, φ, t ∈ ℂ` and `‖t‖ < exp(-|Im θ| - |Im φ|)`, then
`R_{-ν}(ν, ν; 1 - 2t cos(θ+φ) + t², 1 - 2t cos(θ-φ) + t²)
  = ∑ tⁿ C_n^ν(cos θ) C_n^ν(cos φ) / C_n^ν(1)`. -/
theorem hasSum_ossicini_complex {ν : ℂ} (hν : ∀ k : ℕ, 2 * ν ≠ -k) (θ φ : ℂ) {t : ℂ}
    (ht : ‖t‖ < Real.exp (-|θ.im| - |φ.im|)) :
    HasSum (fun n : ℕ => t ^ n * (gegenbauer ν n).eval (cos θ) *
        (gegenbauer ν n).eval (cos φ) / (gegenbauer ν n).eval 1)
      (carlsonR (-ν) (pair ν ν)
        (pair (1 - 2 * t * cos (θ + φ) + t ^ 2) (1 - 2 * t * cos (θ - φ) + t ^ 2))) := by
  have h := (hasSum_regOssicini_complex ν θ φ ht).mul_left (Gamma (2 * ν))
  rw [carlsonR, sum_pair, ← two_mul]
  refine h.congr_fun fun n => ?_
  have hreg : IsGammaRegular (2 * ν) := hν
  have hP : (ascPochhammer ℂ n).eval (2 * ν) ≠ 0 := hreg.ascPochhammer_ne_zero n
  rw [eval_gegenbauer_one, Complex.Gamma_add_nat_eq_ascPochhammer_mul hreg]
  have hΓ : Gamma (2 * ν) ≠ 0 := Gamma_ne_zero hν
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- A property of all real numbers holds frequently near `0` in the punctured complex plane. -/
theorem frequently_ofReal_nhdsNE {P : ℂ → Prop} (h : ∀ x : ℝ, P x) :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ), P z := by
  have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have := (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [ofReal_zero] at this
    · exact Eventually.of_forall fun n => by
        simp only [mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]; positivity
  exact ht.frequently (Frequently.of_forall fun n => h _)

/-- The right side of Gegenbauer's product formula is entire in the nodes. -/
theorem analyticAt_carlsonDirichletAverage_gegenbauer {ν : ℂ} (hν : 0 < ν.re) (n : ℕ)
    {θ₀ : ℂ} {z : ℂ → Fin 2 → ℂ} (hz : ∀ i, AnalyticAt ℂ (fun θ => z θ i) θ₀) :
    AnalyticAt ℂ (fun θ => carlsonDirichletAverage (pair ν ν) (z θ)
      (fun x => (gegenbauer ν n).eval x)) θ₀ := by
  have hb : pair ν ν ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> simpa [pair] using hν
  have heq : (fun θ => carlsonDirichletAverage (pair ν ν) (z θ) (fun x => (gegenbauer ν n).eval x))
      = fun θ => Gamma (∑ i, pair ν ν i) *
        regCarlsonPolynomialAverage (pair ν ν) (z θ) (gegenbauer ν n) := by
    funext θ
    rw [carlsonDirichletAverage, regCarlsonPolynomialAverage_eq_native _ _ hb]
  rw [heq]
  refine analyticAt_const.mul ?_
  simp only [regCarlsonPolynomialAverage_apply]
  exact Finset.analyticAt_fun_sum _ fun m _ => analyticAt_const.mul
    (analyticAt_regCarlsonRPolynomial_comp (fun _ => analyticAt_const) hz m)

/-- **Gegenbauer's product formula** (Theorem 6.11-4) in Carlson's generality: for `re ν > 0`
and complex `θ, φ`,
`C_n^ν(cos θ) C_n^ν(cos φ) = C_n^ν(1) ∫₀¹ C_n^ν(u cos(θ+φ) + (1-u) cos(θ-φ)) dμ_{(ν,ν)}(u)`. -/
theorem gegenbauer_product_formula_complex {ν : ℂ} (hν : 0 < ν.re) (θ φ : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval (cos θ) * (gegenbauer ν n).eval (cos φ) =
      (gegenbauer ν n).eval 1 * carlsonDirichletAverage (pair ν ν)
        (pair (cos (θ + φ)) (cos (θ - φ))) (fun x => (gegenbauer ν n).eval x) := by
  set P := gegenbauer ν n
  have hP : ∀ w : ℂ, AnalyticAt ℂ (fun θ : ℂ => P.eval (cos θ)) w := fun w =>
    ((Polynomial.differentiable P).comp differentiable_cos).analyticAt w
  have hG (φ : ℂ) : AnalyticOnNhd ℂ (fun θ => P.eval 1 * carlsonDirichletAverage (pair ν ν)
      (pair (cos (θ + φ)) (cos (θ - φ))) (fun x => P.eval x)) univ := fun w _ =>
    analyticAt_const.mul (analyticAt_carlsonDirichletAverage_gegenbauer hν n (fun i => by
      fin_cases i
      · exact (differentiable_cos.comp (differentiable_id.add_const φ)).analyticAt w
      · exact (differentiable_cos.comp (differentiable_id.sub_const φ)).analyticAt w))
  have hG' (θ : ℂ) : AnalyticOnNhd ℂ (fun φ => P.eval 1 * carlsonDirichletAverage (pair ν ν)
      (pair (cos (θ + φ)) (cos (θ - φ))) (fun x => P.eval x)) univ := fun w _ =>
    analyticAt_const.mul (analyticAt_carlsonDirichletAverage_gegenbauer hν n (fun i => by
      fin_cases i
      · exact (differentiable_cos.comp (differentiable_id.const_add θ)).analyticAt w
      · exact (differentiable_cos.comp (differentiable_id.const_sub θ)).analyticAt w))
  -- real `φ`, complex `θ`
  have step1 : ∀ (φ : ℝ) (θ : ℂ), P.eval (cos θ) * P.eval (cos φ) =
      P.eval 1 * carlsonDirichletAverage (pair ν ν) (pair (cos (θ + φ)) (cos (θ - φ)))
        (fun x => P.eval x) := by
    intro φ
    have hF : AnalyticOnNhd ℂ (fun θ : ℂ => P.eval (cos θ) * P.eval (cos (φ : ℂ))) univ :=
      fun w _ => (hP w).mul analyticAt_const
    have := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hF (hG φ) isPreconnected_univ
      (mem_univ 0) (frequently_ofReal_nhdsNE fun x => gegenbauer_product_formula hν x φ n)
    exact fun θ => this (mem_univ θ)
  have hF : AnalyticOnNhd ℂ (fun φ : ℂ => P.eval (cos θ) * P.eval (cos φ)) univ :=
    fun w _ => analyticAt_const.mul (hP w)
  have := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hF (hG' θ) isPreconnected_univ
    (mem_univ 0) (frequently_ofReal_nhdsNE fun x => step1 x θ)
  exact this (mem_univ φ)

/-- **Exercise 6.7-2**: `‖C_n^ν(cos θ)‖ ≤ (2‖ν‖)ₙ e^(n |Im θ|)/n!` for all complex `ν` and `θ`;
for `ν = 1/2` this is `‖Pₙ(cos θ)‖ ≤ e^(n |Im θ|)`. -/
theorem norm_eval_gegenbauer_cos_le (ν θ : ℂ) (n : ℕ) :
    ‖(gegenbauer ν n).eval (cos θ)‖ ≤
      (ascPochhammer ℝ n).eval (2 * ‖ν‖) / n.factorial * Real.exp (n * |θ.im|) := by
  set w := exp (θ * I)
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hw : ‖w‖ ≤ Real.exp |θ.im| := by
    rw [norm_exp]; gcongr; simp [neg_le_abs]
  have hwi : ‖w⁻¹‖ ≤ Real.exp |θ.im| := by
    rw [← exp_neg, norm_exp]; gcongr; simp [le_abs_self]
  have h := norm_carlsonRPolynomialNumerator_le_pochhammer n (pair ν ν) (pair w w⁻¹)
    (B := fun _ => ‖ν‖) (fun i => by fin_cases i <;> simp [pair]) (Real.exp_pos _).le
    (fun i => by
      fin_cases i
      · simpa [pair] using hw
      · simpa [pair] using hwi)
  rw [carlsonRPolynomialNumerator_pair, ← factorial_mul_eval_gegenbauer ν w hw0 n,
    exp_add_inv_div_two, norm_mul, Complex.norm_natCast, Fin.sum_univ_two, ← two_mul,
    ← Real.exp_nat_mul] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast n.factorial_pos)]
  linarith

/-- Every complex number is `(w + w⁻¹)/2` for some nonzero `w`. -/
theorem exists_add_inv_div_two (z : ℂ) : ∃ w : ℂ, w ≠ 0 ∧ (w + w⁻¹) / 2 = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 1) two_pos
  have hprod : (z + s) * (z - s) = 1 := by linear_combination -hs
  have hw : z + s ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  refine ⟨z + s, hw, ?_⟩
  rw [show (z + s)⁻¹ = z - s from (eq_inv_of_mul_eq_one_right hprod).symm]
  ring

/-- **Exercise 6.9-4** (the coefficients of Gegenbauer's polynomial): for all `ν` and `z`,
`C_n^ν(z) = ∑_m (ν)_(n-m)/(m! (n-2m)!) (-1)ᵐ (2z)^(n-2m)`, the sum over `2m ≤ n` (the factor
`(n-m choose m)/(n-m)!` vanishes for `2m > n`). -/
theorem eval_gegenbauer_eq_sum (ν z : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval z = ∑ m ∈ Finset.range (n + 1),
      (ascPochhammer ℂ (n - m)).eval ν / ((n - m).factorial : ℂ) * ((n - m).choose m : ℂ) *
        (-1) ^ m * (2 * z) ^ (n - 2 * m) := by
  obtain ⟨w, hw0, hwz⟩ := exists_add_inv_div_two z
  have h := factorial_mul_eval_gegenbauer ν w hw0 n
  have hs := carlsonRPolynomialNumerator₂_self_eq_sum n ν w w⁻¹
  rw [hwz] at h
  rw [← h, mul_div_cancel_left₀ _ (by exact_mod_cast n.factorial_ne_zero : (n.factorial : ℂ) ≠ 0),
    mul_inv_cancel₀ hw0, show w + w⁻¹ = 2 * z by rw [← hwz]; ring] at hs
  rw [hs]

/-- **Exercise 6.9-1**: `C_{2n}^ν(0) = (-1)ⁿ (ν)ₙ/n!`; in particular `P_{2n}(0) = (-1)ⁿ (½)ₙ/n!`. -/
theorem eval_gegenbauer_even_zero (ν : ℂ) (n : ℕ) :
    (gegenbauer ν (2 * n)).eval 0 = (-1) ^ n * (ascPochhammer ℂ n).eval ν / (n.factorial : ℂ) := by
  rw [eval_gegenbauer_eq_sum, Finset.sum_eq_single n]
  · rw [show 2 * n - n = n by omega, Nat.choose_self, Nat.sub_self, pow_zero]; push_cast; ring
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h | h
    · rw [mul_zero, zero_pow (by omega)]; simp
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Exercise 6.9-1**: `C_{2n+1}^ν(0) = 0`. -/
theorem eval_gegenbauer_odd_zero (ν : ℂ) (n : ℕ) : (gegenbauer ν (2 * n + 1)).eval 0 = 0 := by
  rw [eval_gegenbauer_eq_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases le_or_gt m n with h | h
  · rw [mul_zero, zero_pow (by omega)]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

end Carlson.TwoVariable
