/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.FourierCosine
public import Carlson.Jacobi.AsymptoticZeros
public import Carlson.Jacobi.ChebyshevSecondKind

/-!
# The two polynomial saddles in the Chebyshev case

Carlson's equation (7.4-1) is an exact sum of two geometric terms. It remains
valid when these terms cancel. This provides a first case of the polynomial
saddle expansion without taking a quotient by a possibly vanishing sum.
On `W`, one saddle strictly dominates and the relative error equals
`‖(x-y)/(x+y)‖^(2n)`, which decays uniformly on compact sets.
The exact two-term formula requires `n > 0`; the degree-zero polynomial is one.
The general-parameter polynomial expansion of Theorem 7.4-2 is not asserted here.

## Main results

* `carlsonRPolynomial_chebyshev`: the exact two-saddle formula (7.4-1).
* `isEquivalent_carlsonRPolynomial_chebyshev_two_saddles`: the difference-based equivalent.
* `norm_carlsonRPolynomial_chebyshev_div_sub_one`: exact dominant-term relative error.
* `tendstoUniformlyOn_carlsonRPolynomial_chebyshev_div`: compact-uniform limit on `W`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.4, equation (1) and the Chebyshev case of Theorem 7.4-2.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter
open scoped Topology ComplexConjugate

/-- The monic Chebyshev specialization in the multiplicative circle coordinate. -/
theorem eval_monicJacobi_neg_half_laurent (n : ℕ) (hn : n ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (monicJacobi (-1 / 2 : ℂ) (-1 / 2) n).eval ((w + w⁻¹) / 2) =
      (w ^ n + (w⁻¹) ^ n) / 2 ^ n := by
  have h := eval_monicJacobi_neg_half_cos n hn (log w * I)
  rw [cos_mul_I, show (n : ℂ) * (log w * I) = ((n : ℂ) * log w) * I by ring,
    cos_mul_I, cosh, cosh, exp_neg, exp_neg, exp_nat_mul, exp_log hw] at h
  rw [h, ← inv_pow]
  have hn' : n = (n - 1) + 1 := by omega
  conv_rhs => arg 2; rw [hn', pow_succ]
  field_simp

/-- At equal nodes the Chebyshev Carlson polynomial reduces to the corresponding
monomial; its Pochhammer denominator is nonsingular. -/
private theorem carlsonRPolynomial_chebyshev_equal_nodes (n : ℕ) (v : ℂ) :
    carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) v v /
      (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) = v ^ n := by
  rw [← carlsonRPolynomialNumerator_pair]
  have hp : pair v v = fun _ => v := by funext i; fin_cases i <;> rfl
  rw [hp, carlsonRPolynomialNumerator_const, sum_pair,
    show (1 / 2 - n : ℂ) + (1 / 2 - n) = 1 - 2 * n by ring]
  exact mul_div_cancel_left₀ _ (chebyshev_midpoint_pochhammer_ne_zero n)

/-- For distinct square nodes, the Chebyshev Carlson polynomial is exactly the
sum of the two saddle contributions. -/
theorem carlsonRPolynomial_chebyshev_of_sq_ne (n : ℕ) (hn : n ≠ 0) {x y : ℂ}
    (hxy : x ^ 2 ≠ y ^ 2) :
    carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) =
        ((x + y) / 2) ^ (2 * n) + ((x - y) / 2) ^ (2 * n) := by
  have hm : x - y ≠ 0 := by intro h; exact hxy (congrArg (fun z : ℂ => z ^ 2) (sub_eq_zero.mp h))
  have hp : x + y ≠ 0 := by
    intro h
    have he : x = -y := eq_neg_of_add_eq_zero_left h
    rw [he, neg_sq] at hxy
    exact hxy rfl
  let d := (x ^ 2 - y ^ 2) / 2
  let w := (x + y) / (x - y)
  have hw : w ≠ 0 := div_ne_zero hp hm
  have hplus : d * ((w + w⁻¹) / 2 + 1) = x ^ 2 := by
    dsimp [d, w]; field_simp; ring
  have hminus : d * ((w + w⁻¹) / 2 - 1) = y ^ 2 := by
    dsimp [d, w]; field_simp; ring
  have he : carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) =
        d ^ n * (monicJacobi (-1 / 2 : ℂ) (-1 / 2) n).eval ((w + w⁻¹) / 2) := by
    rw [eval_monicJacobi_eq_numerator]
    norm_num
    rw [← mul_div_assoc, ← carlsonRPolynomialNumerator₂_mul, hplus, hminus]
  rw [he, eval_monicJacobi_neg_half_laurent n hn hw]
  have hA : d * w / 2 = ((x + y) / 2) ^ 2 := by dsimp [d, w]; field_simp; ring
  have hB : d * w⁻¹ / 2 = ((x - y) / 2) ^ 2 := by dsimp [d, w]; field_simp; ring
  calc
    _ = (d * w / 2) ^ n + (d * w⁻¹ / 2) ^ n := by simp only [div_pow, mul_pow]; ring
    _ = _ := by rw [hA, hB, ← pow_mul, ← pow_mul]

/-- **Carlson's equation (7.4-1)**: the polynomial Chebyshev case is an exact sum
of two saddle terms for every complex argument pair and every positive degree.
No division by the sum is involved, so cancellation points are included. -/
theorem carlsonRPolynomial_chebyshev (n : ℕ) (hn : n ≠ 0) (x y : ℂ) :
    carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) =
        ((x + y) / 2) ^ (2 * n) + ((x - y) / 2) ^ (2 * n) := by
  by_cases hxy : x ^ 2 = y ^ 2
  · rw [hxy, carlsonRPolynomial_chebyshev_equal_nodes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with he | he
    · subst x
      simp only [sub_self, zero_div, zero_pow (by omega : 2 * n ≠ 0), add_zero]
      rw [show (y + y) / 2 = y by ring, pow_mul]
    · subst x
      simp only [neg_add_cancel, zero_div, zero_pow (by omega : 2 * n ≠ 0), zero_add]
      rw [show (-y - y) / 2 = -y by ring, pow_mul, neg_sq]
  · exact carlsonRPolynomial_chebyshev_of_sq_ne n hn hxy

/-- The exact Chebyshev formula gives a two-saddle asymptotic equivalent in
Mathlib's difference-based sense, including points where the sum is zero. -/
theorem isEquivalent_carlsonRPolynomial_chebyshev_two_saddles (x y : ℂ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (x ^ 2) (y ^ 2) /
        (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)))
      (fun n => ((x + y) / 2) ^ (2 * n) + ((x - y) / 2) ^ (2 * n)) := by
  apply Filter.EventuallyEq.isEquivalent
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact carlsonRPolynomial_chebyshev n hn.ne' x y

/-- On Carlson's `W`, the second polynomial saddle is strictly smaller in modulus. -/
theorem norm_sub_div_add_lt_one {x y : ℂ} (h : 0 < (x * conj y).re) :
    ‖(x - y) / (x + y)‖ < 1 := by
  have h1 := Complex.sq_norm (x - y)
  have h2 := Complex.sq_norm (x + y)
  have hh : 0 < x.re * y.re + x.im * y.im := by simpa [mul_re] using h
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im] at h1 h2
  have hn : ‖x - y‖ < ‖x + y‖ := by nlinarith [norm_nonneg (x - y), norm_nonneg (x + y)]
  rw [norm_div, div_lt_one ((norm_nonneg _).trans_lt hn)]
  exact hn

/-- The sum of the two square roots is nonzero on Carlson's `W`. -/
theorem add_ne_zero_of_mem_chebyshevDomain {x y : ℂ} (h : 0 < (x * conj y).re) : x + y ≠ 0 := by
  intro he
  have hx : x = -y := eq_neg_of_add_eq_zero_left he
  simp only [hx, neg_mul, mul_conj, neg_re, ofReal_re] at h
  linarith [normSq_nonneg y]

/-- The Chebyshev relative error after retaining the dominant saddle is exactly
the modulus ratio of the two saddle terms. -/
theorem norm_carlsonRPolynomial_chebyshev_div_sub_one (n : ℕ) (hn : n ≠ 0)
    {x y : ℂ} (h : 0 < (x * conj y).re) :
    ‖(carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ))) / ((x + y) / 2) ^ (2 * n) - 1‖ =
        ‖(x - y) / (x + y)‖ ^ (2 * n) := by
  have hp : (x + y) / 2 ≠ 0 := div_ne_zero (add_ne_zero_of_mem_chebyshevDomain h) (by norm_num)
  rw [carlsonRPolynomial_chebyshev n hn x y, add_div, div_self (pow_ne_zero _ hp),
    add_sub_cancel_left, ← div_pow, div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0), norm_pow]

/-- In the Chebyshev case the dominant polynomial saddle gives a joint relative
limit uniformly on every compact subset of `W`, including coincident arguments.
On any compact set its error is bounded by a common geometric sequence. -/
theorem tendstoUniformlyOn_carlsonRPolynomial_chebyshev_div {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKW : K ⊆ chebyshevDomain) :
    TendstoUniformlyOn (fun n : ℕ => fun p =>
      (carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) (p.1 ^ 2) (p.2 ^ 2) /
        (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ))) / ((p.1 + p.2) / 2) ^ (2 * n))
      (fun _ => 1) atTop K := by
  let f : (ℂ × ℂ) → ℂ := fun p => (p.1 - p.2) / (p.1 + p.2)
  have hf : ContinuousOn f K := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact add_ne_zero_of_mem_chebyshevDomain (hKW hp)
  obtain ⟨η, hη, hηf⟩ := hK.exists_forall_le' (continuousOn_const.sub hf.norm)
    (fun p hp => sub_pos.mpr (norm_sub_div_add_lt_one (hKW hp)))
  simp only [Pi.sub_apply] at hηf
  let ρ := max 0 (1 - η)
  have hρ0 : 0 ≤ ρ := le_max_left _ _
  have hρ : ρ < 1 := max_lt (by norm_num) (by linarith)
  have hb (p : ℂ × ℂ) (hp : p ∈ K) : ‖f p‖ ≤ ρ :=
    (by linarith [hηf p hp] : ‖f p‖ ≤ 1 - η).trans (le_max_right _ _)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlim.eventually (gt_mem_nhds hε)] with n hn hεn
  intro p hp
  rw [dist_comm, dist_eq_norm, norm_carlsonRPolynomial_chebyshev_div_sub_one n hn.ne' (hKW hp)]
  exact ((pow_le_pow_left₀ (norm_nonneg _) (hb p hp) _).trans
    (pow_le_pow_of_le_one hρ0 hρ.le (by omega : n ≤ 2 * n))).trans_lt hεn

end Carlson.TwoVariable
