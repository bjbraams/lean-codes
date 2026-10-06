/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.TwoVariable.RPolynomial

/-!
# Two-node R-polynomials with equal parameters (Exercise 6.9-3)

With equal parameters the generating relation is `((1 - tx)(1 - ty))^(-β) = (1 - u)^(-β)` with
`u = t(x + y) - t²xy`. Expanding in powers of `u` and regrouping the absolutely convergent double
series by powers of `t` gives Carlson's explicit expansion of `Rₙ(β, β; x, y)`; with
`x = w`, `y = w⁻¹` this is the coefficient formula for Gegenbauer polynomials (Exercise 6.9-4, in
`Carlson.Jacobi.GegenbauerProductComplex`).

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_self_eq_sum`: Exercise 6.9-3.
* `Carlson.TwoVariable.hasSum_regroup_binomial`: regrouping a power series in a binomial.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Regrouping a power series in a binomial `A + B` by total degree, where `B` counts twice:
if `∑ aₖ (A + B)ᵏ = F` with `∑ ‖aₖ‖ (‖A‖ + ‖B‖)ᵏ < ∞`, then
`∑ₙ ∑_q a_(n-q) (n-q choose q) B^q A^(n-2q) = F`. -/
theorem hasSum_regroup_binomial {a : ℕ → ℂ} {A B F : ℂ}
    (hU : HasSum (fun k => a k * (A + B) ^ k) F)
    (hnorm : Summable fun k => ‖a k‖ * (‖A‖ + ‖B‖) ^ k) :
    HasSum (fun n => ∑ q ∈ range (n + 1),
      a (n - q) * ((n - q).choose q : ℂ) * B ^ q * A ^ (n - q - q)) F := by
  set f : ℕ × ℕ → ℂ := fun p => a p.1 * (p.1.choose p.2 : ℂ) * B ^ p.2 * A ^ (p.1 - p.2)
  have hzero : ∀ k q, q ∉ range (k + 1) → f (k, q) = 0 := fun k q hq => by
    have : k < q := by simpa using hq
    simp [f, Nat.choose_eq_zero_of_lt this]
  have hfib : ∀ k, HasSum (fun q => f (k, q)) (a k * (A + B) ^ k) := fun k => by
    have h := (summable_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (f := fun q : ℕ => f (k, q)) (hzero k)).hasSum
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (f := fun q : ℕ => f (k, q))
      (hzero k)] at h
    convert h using 1
    rw [add_comm A B, add_pow, mul_sum]
    exact sum_congr rfl fun q _ => by simp only [f]; ring
  have hnf : ∀ k, Summable fun q => ‖f (k, q)‖ := fun k =>
    summable_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := range (k + 1))
      fun q hq => by
      have : k < q := by simpa using hq
      simp [f, Nat.choose_eq_zero_of_lt this]
  have hfibn : ∀ k, ∑' q, ‖f (k, q)‖ = ‖a k‖ * (‖A‖ + ‖B‖) ^ k := fun k => by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := range (k + 1)) fun q hq => by
      have : k < q := by simpa using hq
      simp [f, Nat.choose_eq_zero_of_lt this], add_comm ‖A‖, add_pow, mul_sum]
    exact sum_congr rfl fun q _ => by
      simp only [f, norm_mul, norm_pow, Complex.norm_natCast]; ring
  have hsum : Summable f := by
    refine Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).mpr ⟨hnf, ?_⟩)
    simpa only [hfibn] using hnorm
  have hf : HasSum f F := by
    have h := hsum.hasSum
    rwa [← hU.unique (h.prod_fiberwise hfib)] at h
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr hf
  have hg := he.sigma (g := fun n => ∑ p ∈ antidiagonal n, f p) fun n => by
    have := hasSum_fintype (fun c : antidiagonal n => f c.1)
    rwa [← Finset.sum_coe_sort (antidiagonal n) f]
  refine hg.congr_fun fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k q => f (k, q)) n, ← sum_range_reflect]
  refine sum_congr rfl fun q hq => ?_
  have hqn : q ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hq)
  simp only [f, show n + 1 - 1 - q = n - q by omega, Nat.sub_sub_self hqn]

/-- The single-node binomial series `∑ (β)ₖ/k! uᵏ = (1 - u)^(-β)`, with absolute convergence. -/
theorem hasSum_ascPochhammer_div_factorial_mul_pow (β : ℂ) {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun k => (ascPochhammer ℂ k).eval β / (k.factorial : ℂ) * u ^ k) (1 / (1 - u) ^ β) ∧
      Summable fun k => ‖(ascPochhammer ℂ k).eval β / (k.factorial : ℂ) * u ^ k‖ := by
  classical
  have h := hasSum_carlsonGeneratingCoeff (univ : Finset Unit) (fun _ => β) (fun _ => 1) u
    (fun _ _ => by simpa using hu)
  have hc : ∀ k, carlsonGeneratingCoeff (univ : Finset Unit) (fun _ => β) (fun _ => 1) k =
      (ascPochhammer ℂ k).eval β := fun k => by
    rw [← carlsonRPolynomialNumerator_eq_sum_piAntidiag, carlsonRPolynomialNumerator_const]
    simp
  simp only [hc] at h
  simpa using h

/-- **Exercise 6.9-3**, in numerator form: for equal parameters,
`Nₙ(β, β; x, y)/n! = ∑_q (β)_(n-q)/(q! (n-2q)!) (-xy)^q (x + y)^(n-2q)`, the sum running over
`2q ≤ n` (the factor `(n-q choose q)/(n-q)!` below vanishes for `2q > n`). -/
theorem carlsonRPolynomialNumerator₂_self_eq_sum (n : ℕ) (β x y : ℂ) :
    carlsonRPolynomialNumerator₂ n β β x y / (n.factorial : ℂ) =
      ∑ q ∈ range (n + 1), (ascPochhammer ℂ (n - q)).eval β / ((n - q).factorial : ℂ) *
        ((n - q).choose q : ℂ) * (-(x * y)) ^ q * (x + y) ^ (n - 2 * q) := by
  set δ : ℝ := 1 / (2 * (1 + ‖x‖ + ‖y‖))
  have hδ : 0 < δ := by positivity
  have hδx : δ * ‖x‖ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg y]
  have hδy : δ * ‖y‖ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg x]
  have hδxy : δ * (‖x‖ + ‖y‖) < 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) two_pos]; nlinarith
  have hsmall : ∀ t : ℂ, ‖t‖ < δ → ‖t‖ * (‖x‖ + ‖y‖) < 1 / 2 ∧ ‖t‖ * ‖x‖ ≤ 1 / 2 ∧
      ‖t‖ * ‖y‖ ≤ 1 / 2 := fun t ht =>
    ⟨(mul_le_mul_of_nonneg_right ht.le (by positivity)).trans_lt hδxy,
      (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)).trans hδx,
      (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)).trans hδy⟩
  refine congrFun (coeff_eq_of_hasSum_pow hδ (F := carlsonRGeneratingKernel (pair β β) (pair x y))
    (a := fun n => carlsonRPolynomialNumerator₂ n β β x y / (n.factorial : ℂ))
    (b := fun n => ∑ q ∈ range (n + 1), (ascPochhammer ℂ (n - q)).eval β /
      ((n - q).factorial : ℂ) * ((n - q).choose q : ℂ) * (-(x * y)) ^ q * (x + y) ^ (n - 2 * q))
    (fun t ht => ?_) (fun t ht => ?_)) n
  · obtain ⟨-, hx, hy⟩ := hsmall t ht
    have h := hasSum_carlsonRPolynomialNumerator_div_factorial (pair β β) (pair x y) t
      (fun i => by fin_cases i <;> simp [pair] <;> linarith)
    simpa only [carlsonRPolynomialNumerator_pair] using h
  · obtain ⟨hxy, hx, hy⟩ := hsmall t ht
    set A := t * (x + y)
    set B := -(t ^ 2 * (x * y))
    have hAB : ‖A‖ + ‖B‖ < 1 := by
      simp only [A, B, norm_mul, norm_neg, norm_pow]
      have h1 : ‖t‖ * ‖x + y‖ ≤ ‖t‖ * (‖x‖ + ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg _)
      have h2 : ‖t‖ ^ 2 * (‖x‖ * ‖y‖) = (‖t‖ * ‖x‖) * (‖t‖ * ‖y‖) := by ring
      have h3 : (‖t‖ * ‖x‖) * (‖t‖ * ‖y‖) ≤ 1 / 2 * (1 / 2) :=
        mul_le_mul hx hy (by positivity) (by norm_num)
      linarith
    have hu : ‖A + B‖ < 1 := (norm_add_le _ _).trans_lt hAB
    obtain ⟨hU, -⟩ := hasSum_ascPochhammer_div_factorial_mul_pow β hu
    have hρ : ‖((‖A‖ + ‖B‖ : ℝ) : ℂ)‖ < 1 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hAB
    have hnorm := (hasSum_ascPochhammer_div_factorial_mul_pow β hρ).2
    have hreg := hasSum_regroup_binomial hU (by
      refine hnorm.congr fun k => ?_
      rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
    have hK : carlsonRGeneratingKernel (pair β β) (pair x y) t = 1 / (1 - (A + B)) ^ β := by
      have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 - w).re := fun w hw => by
        have := (abs_re_le_norm w).trans_lt hw
        simp only [sub_re, one_re]; linarith [le_abs_self w.re]
      have h1 := hre (t * x) (by rw [norm_mul]; linarith)
      have h2 := hre (t * y) (by rw [norm_mul]; linarith)
      simp only [carlsonRGeneratingKernel, Fin.prod_univ_two, pair_zero, pair_one]
      rw [show 1 - (A + B) = (1 - t * x) * (1 - t * y) by simp only [A, B]; ring,
        mul_cpow_of_re_pos h1 h2]
      field_simp
    rw [hK]
    refine hreg.congr_fun fun m => ?_
    rw [sum_mul]
    refine sum_congr rfl fun q hq => ?_
    rcases le_or_gt (2 * q) m with hqm | hqm
    · have ht : t ^ m = t ^ (2 * q) * t ^ (m - 2 * q) := by
        rw [← pow_add, Nat.add_sub_cancel' hqm]
      rw [show m - q - q = m - 2 * q by omega, ht]
      simp only [A, B]
      rw [show t ^ (2 * q) = (t ^ 2) ^ q from pow_mul t 2 q]
      rw [neg_pow (t ^ 2 * (x * y)), mul_pow (t ^ 2) (x * y), mul_pow x y,
        mul_pow t (x + y)]
      ring
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp

end Carlson.TwoVariable
