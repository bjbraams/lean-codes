/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.PolygonSpecial
public import Carlson.RPolynomial.SharpEstimates
public import Carlson.RPolynomial.GeneratingIdentities
import Pochhammer.BinomialSeries

/-!
# R-functions near the diagonal (Exercise 6.2-14)

The Taylor series 6.3-1 of `R_t(cw; x)` about `x = (1, …, 1)` has explicit terms of degree at
most two (6.2-13), and its tail is `O(ρ³)` when every `|xᵢ - 1| ≤ ρ`, by a uniform majorant and
the homogeneity of the R-polynomials. Substituting `xᵢ = uᵢ^s`, expanded by the binomial series,
and using `∑ wᵢ (uᵢ - 1) = 0` gives Carlson's expansion with remainder `O(|1 - u|³)`.

## Main results

* `Carlson.exists_norm_carlsonR_sub_quadratic_le`: the second-order expansion of `R_t(cw; x)`.
* `Carlson.exists_carlsonR_cpow_near_diagonal`: Exercise 6.2-14 in the variables `uᵢ = zᵢ/z̄`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.2.
-/

open Complex Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

/-- A scaled tail bound: if `‖f n‖ ≤ λⁿ M n` with `0 ≤ λ ≤ 1` and `M` summable and nonnegative,
then `‖∑_{n ≥ N} f n‖ ≤ λ^N ∑ M`. -/
theorem norm_tsum_nat_add_le {f : ℕ → ℂ} {M : ℕ → ℝ} (hM : Summable M) (hM0 : ∀ n, 0 ≤ M n)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hf : ∀ n, ‖f n‖ ≤ l ^ n * M n) (N : ℕ) :
    ‖∑' n, f (n + N)‖ ≤ l ^ N * ∑' n, M n := by
  have hMN : Summable fun n => M (n + N) := (summable_nat_add_iff N).mpr hM
  have hb : ∀ n, ‖f (n + N)‖ ≤ l ^ N * M (n + N) := fun n => by
    refine (hf (n + N)).trans ?_
    rw [pow_add]
    have h1 := pow_le_one₀ hl0 hl1 (n := n)
    have h2 : 0 ≤ l ^ N * M (n + N) := mul_nonneg (pow_nonneg hl0 N) (hM0 (n + N))
    calc l ^ n * l ^ N * M (n + N) = l ^ n * (l ^ N * M (n + N)) := by ring
      _ ≤ 1 * (l ^ N * M (n + N)) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  have hs : Summable fun n => ‖f (n + N)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hMN.mul_left _)
  calc ‖∑' n, f (n + N)‖ ≤ ∑' n, ‖f (n + N)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, l ^ N * M (n + N) := hs.tsum_le_tsum hb (hMN.mul_left _)
    _ = l ^ N * ∑' n, M (n + N) := tsum_mul_left
    _ ≤ l ^ N * ∑' n, M n := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl0 N)
        rw [← hM.sum_add_tsum_nat_add N]
        exact le_add_of_nonneg_left (sum_nonneg fun n _ => hM0 n)

/-- The cubic remainder of the binomial series: there is `K` with
`‖(1 + h)^s - 1 - s h - s(s - 1)h²/2‖ ≤ K ‖h‖³` for `‖h‖ ≤ 1/2`. -/
theorem exists_norm_one_add_cpow_sub_le (s : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℂ, ‖h‖ ≤ 1 / 2 →
      ‖(1 + h) ^ s - 1 - s * h - s * (s - 1) / 2 * h ^ 2‖ ≤ K * ‖h‖ ^ 3 := by
  set c : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval (-s) / (n.factorial : ℂ)
  have hsumm := summable_norm_ascPochhammer_mul_pow_div_factorial (-s) (1 / 2 : ℂ)
    (by norm_num)
  set M : ℕ → ℝ := fun n => ‖c n * (1 / 2 : ℂ) ^ n‖
  refine ⟨8 * ∑' n, M n, by positivity, fun h hh => ?_⟩
  have hh1 : ‖-h‖ < 1 := by rw [norm_neg]; linarith
  have hser := hasSum_ascPochhammer_mul_pow_div_factorial (-s) (-h) hh1
  have hval : 1 / (1 - -h) ^ (-s) = (1 + h) ^ s := by
    rw [sub_neg_eq_add, cpow_neg, one_div, inv_inv]
  rw [hval] at hser
  have hsplit := hser.summable.sum_add_tsum_nat_add 3
  rw [hser.tsum_eq] at hsplit
  simp only [sum_range_succ, sum_range_zero, ascPochhammer_zero, Polynomial.eval_one,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one, zero_add] at hsplit
  have h1 : (ascPochhammer ℂ 1).eval (-s) / ((1 : ℕ).factorial : ℂ) * (-h) ^ 1 = s * h := by
    simp
  have h2 : (ascPochhammer ℂ 2).eval (-s) / ((2 : ℕ).factorial : ℂ) * (-h) ^ 2 =
      s * (s - 1) / 2 * h ^ 2 := by
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one]
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    push_cast
    ring
  rw [h1, h2] at hsplit
  have htail : (1 + h) ^ s - 1 - s * h - s * (s - 1) / 2 * h ^ 2 =
      ∑' n, (ascPochhammer ℂ (n + 3)).eval (-s) / ((n + 3).factorial : ℂ) * (-h) ^ (n + 3) := by
    rw [← hsplit]; ring
  rw [htail]
  have hb : ∀ n, ‖(ascPochhammer ℂ n).eval (-s) / (n.factorial : ℂ) * (-h) ^ n‖ ≤
      (2 * ‖h‖) ^ n * M n := fun n => by
    simp only [M, c, norm_mul, norm_pow, norm_neg, norm_div, one_div, norm_inv, Complex.norm_ofNat]
    rw [mul_pow, inv_pow]
    have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    exact le_refl _
  have := norm_tsum_nat_add_le hsumm (fun n => norm_nonneg _) (by positivity)
    (by linarith) hb 3
  calc _ ≤ (2 * ‖h‖) ^ 3 * ∑' n, M n := this
    _ = 8 * (∑' n, M n) * ‖h‖ ^ 3 := by ring

variable {ι : Type*} [Fintype ι]

/-- The Taylor coefficients of `u ↦ u^t` at `1`, divided by `n!`, grow at most like `(3/2)ⁿ`. -/
theorem exists_norm_iteratedDeriv_cpow_div_le (t : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖iteratedDeriv n (fun u : ℂ => u ^ t) 1 / (n.factorial : ℂ)‖ ≤ C * (3 / 2) ^ n := by
  have hsumm := summable_norm_ascPochhammer_mul_pow_div_factorial (-t) (2 / 3 : ℂ)
    (by norm_num)
  refine ⟨∑' n, ‖(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) * (2 / 3 : ℂ) ^ n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun n => ?_⟩
  have hle := hsumm.le_tsum n (fun m _ => norm_nonneg _)
  rw [iteratedDeriv_cpow_const_of_mem_slitPlane _ _ one_mem_slitPlane, one_cpow, mul_one]
  have hdesc : ‖(descPochhammer ℂ n).eval t‖ = ‖(ascPochhammer ℂ n).eval (-t)‖ := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
  have hle' : ‖(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ)‖ * (2 / 3) ^ n ≤
      ∑' n, ‖(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) * (2 / 3 : ℂ) ^ n‖ := by
    convert hle using 1
    rw [norm_mul, norm_pow]; norm_num
  rw [norm_div, hdesc, ← norm_div]
  have h23 : (0 : ℝ) < (2 / 3) ^ n := by positivity
  calc ‖(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ)‖
      = ‖(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ)‖ * (2 / 3) ^ n * (3 / 2) ^ n := by
        rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ _ := by gcongr

/-- **The second-order expansion of `R_t(cw; x)` at the diagonal**: for `re c > 0` and
`∑ wᵢ = 1` there is `K` such that, whenever `‖xᵢ - 1‖ ≤ ρ ≤ 1/4` for all `i`, with `yᵢ = xᵢ - 1`,
`‖R_t(cw; x) - 1 - t ∑ wᵢ yᵢ - t(t - 1)/(2(c + 1)) (∑ wᵢ yᵢ² + c (∑ wᵢ yᵢ)²)‖ ≤ K ρ³`. -/
theorem exists_norm_carlsonR_sub_quadratic_le (t c : ℂ) (hc : 0 < c.re) (w : ι → ℂ)
    (hw : ∑ i, w i = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, ρ ≤ 1 / 4 → ∀ x : ι → ℂ, (∀ i, ‖x i - 1‖ ≤ ρ) →
      ‖carlsonR t (fun i => c * w i) x - 1 - t * ∑ i, w i * (x i - 1) -
        t * (t - 1) / (2 * (c + 1)) * (∑ i, w i * (x i - 1) ^ 2 +
          c * (∑ i, w i * (x i - 1)) ^ 2)‖ ≤ K * ρ ^ 3 := by
  set b : ι → ℂ := fun i => c * w i
  have hbsum : ∑ i, b i = c := by simp only [b]; rw [← mul_sum, hw, mul_one]
  set f : ℂ → ℂ := fun u => u ^ t
  set a : ℕ → ℂ := fun n => iteratedDeriv n f 1 / (n.factorial : ℂ)
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedDeriv_cpow_div_le t
  obtain ⟨Mj, hMs, hMb⟩ := exists_summable_norm_carlsonTaylor_bounded_variables
    (isCompact_singleton (x := b)) hC0 (q := 3 / 2) (r := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) hC
  have hM0 : ∀ n, 0 ≤ Mj n := fun n =>
    (norm_nonneg _).trans (hMb n b rfl (fun _ => 0) (fun _ => by norm_num))
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  have hc1 : c + 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have hne : Nonempty ι := by
    by_contra h; rw [not_nonempty_iff] at h; simp at hw
  refine ⟨8 * ‖Gamma c‖ * ∑' n, Mj n, mul_nonneg (by positivity) (tsum_nonneg hM0),
    fun ρ hρ x hx => ?_⟩
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hx (Classical.arbitrary ι))
  -- the Taylor series about `1`
  have hball : Metric.ball (1 : ℂ) 1 ⊆ slitPlane := fun u hu => Or.inl (by
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have := (abs_re_le_norm (u - 1)).trans_lt hu
    simp only [sub_re, one_re] at this
    linarith [abs_lt.mp this])
  have hxball : Set.range x ⊆ Metric.ball 1 1 := by
    rintro _ ⟨i, rfl⟩; rw [Metric.mem_ball, dist_eq_norm]; linarith [hx i]
  have hG := isRegCarlsonRContinuation_regCarlsonR_of_convexHull t
    ((convexHull_min hxball (convex_ball 1 1)).trans hball)
  have hf : AnalyticOnNhd ℂ f (Metric.ball 1 1) := fun u hu =>
    analyticAt_id.cpow analyticAt_const (hball hu)
  have hz : ‖fun i => x i - 1‖ < 1 :=
    (pi_norm_lt_iff one_pos).mpr fun i => by linarith [hx i]
  have hs := hG.hasSum_taylor hf hz b
  set T : ℕ → ℂ := fun n => iteratedDeriv n f 1 / (n.factorial : ℂ) *
    regCarlsonRPolynomial n b (fun i => x i - 1)
  have hsplit := hs.summable.sum_add_tsum_nat_add 3
  rw [hs.tsum_eq] at hsplit
  have hsplit' : regCarlsonR t b x = T 0 + T 1 + T 2 + ∑' n, T (n + 3) := by
    rw [← hsplit]; simp [T, sum_range_succ]
  have hd : ∀ n, iteratedDeriv n f 1 = (descPochhammer ℂ n).eval t := fun n => by
    rw [iteratedDeriv_cpow_const_of_mem_slitPlane _ _ one_mem_slitPlane, one_cpow, mul_one]
  have hΓ1 : Gamma (c + 1) = c * Gamma c := Gamma_add_one c hc0
  have hΓ2 : Gamma (c + 2) = (c + 1) * (c * Gamma c) := by
    rw [show c + 2 = (c + 1) + 1 by ring, Gamma_add_one _ hc1, hΓ1]
  have e0 : T 0 = (Gamma c)⁻¹ := by
    simp only [T, hd, descPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul, regCarlsonRPolynomial_zero, hbsum]
  have hsum1 : ∑ i, c * w i * (x i - 1) = c * ∑ i, w i * (x i - 1) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have hsum2 : ∑ i, c * w i * (x i - 1) ^ 2 = c * ∑ i, w i * (x i - 1) ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have hd2 : (descPochhammer ℂ 2).eval t = t * (t - 1) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, descPochhammer_succ_eval, descPochhammer_one,
      Polynomial.eval_X]; push_cast; ring
  have e1 : T 1 = t * (∑ i, w i * (x i - 1)) * (Gamma c)⁻¹ := by
    simp only [T, hd, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hbsum,
      carlsonRPolynomialNumerator_one, descPochhammer_one, Polynomial.eval_X, Nat.factorial_one,
      Nat.cast_one, div_one, b]
    rw [hΓ1, hsum1]
    field_simp
  have e2 : T 2 = t * (t - 1) / 2 * (c * ∑ i, w i * (x i - 1) ^ 2 +
      c ^ 2 * (∑ i, w i * (x i - 1)) ^ 2) / (c * (c + 1) * Gamma c) := by
    simp only [T, hd, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hbsum,
      carlsonRPolynomialNumerator_two, b]
    rw [show ((2 : ℕ) : ℂ) = 2 by norm_num, hΓ2, hsum1, hsum2, hd2]
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    push_cast
    field_simp
  -- the remainder is `Γ(c)` times the tail
  have hrem : carlsonR t b x - 1 - t * ∑ i, w i * (x i - 1) -
      t * (t - 1) / (2 * (c + 1)) * (∑ i, w i * (x i - 1) ^ 2 +
        c * (∑ i, w i * (x i - 1)) ^ 2) = Gamma c * ∑' n, T (n + 3) := by
    unfold carlsonR
    rw [hbsum, hsplit', e0, e1, e2]
    field_simp
    ring
  rw [hrem, norm_mul]
  -- the tail bound
  set y' : ι → ℂ := fun i => if ρ = 0 then 0 else (x i - 1) / (2 * ρ)
  have hy' : ∀ i, x i - 1 = (2 * ρ : ℂ) * y' i := fun i => by
    by_cases h0 : ρ = 0
    · have := hx i; rw [h0] at this
      simp [y', h0, norm_le_zero_iff.mp this]
    · have : (ρ : ℂ) ≠ 0 := by exact_mod_cast h0
      simp only [y', h0, ite_false]; field_simp
  have hy'b : ∀ i, ‖y' i‖ ≤ 1 / 2 := fun i => by
    by_cases h0 : ρ = 0
    · simp [y', h0]
    · simp only [y', h0, ite_false, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hρ0]
      rw [div_le_iff₀ (by positivity)]
      linarith [hx i]
  have hTb : ∀ n, ‖T n‖ ≤ (2 * ρ) ^ n * Mj n := fun n => by
    have hfun : (fun i => x i - 1) = fun i => (2 * ρ : ℂ) * y' i := funext hy'
    have hR : regCarlsonRPolynomial n b (fun i => x i - 1) =
        (2 * ρ : ℂ) ^ n * regCarlsonRPolynomial n b y' := by
      rw [hfun, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
        carlsonRPolynomialNumerator_smul, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
      ring
    have hM := hMb n b rfl y' hy'b
    have h2ρ : ‖(2 * ρ : ℂ)‖ = 2 * ρ := by
      rw [show (2 * ρ : ℂ) = ((2 * ρ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    simp only [T]
    rw [hR, mul_left_comm, norm_mul, norm_pow, h2ρ]
    exact mul_le_mul_of_nonneg_left hM (by positivity)
  have htail := norm_tsum_nat_add_le hMs hM0 (by positivity) (by linarith) hTb 3
  calc ‖Gamma c‖ * ‖∑' n, T (n + 3)‖ ≤ ‖Gamma c‖ * ((2 * ρ) ^ 3 * ∑' n, Mj n) := by gcongr
    _ = 8 * ‖Gamma c‖ * (∑' n, Mj n) * ρ ^ 3 := by ring

/-- **Exercise 6.2-14, asymptotic part**, in normalized variables `uᵢ = zᵢ/z̄`: if `re c > 0`,
`∑ wᵢ = 1` and `∑ wᵢ uᵢ = 1`, then as `u → (1, …, 1)`,
`R_t(cw; u^s) = 1 + ½ st (s(c + t)/(c + 1) - 1) ∑ wᵢ (1 - uᵢ)² + O(|1 - u|³)`, uniformly: there
are `C` and `δ > 0` such that the remainder is at most `C η³` whenever every `|uᵢ - 1| ≤ η ≤ δ`. -/
theorem exists_carlsonR_cpow_near_diagonal (t s c : ℂ) (hc : 0 < c.re) (w : ι → ℂ)
    (hw : ∑ i, w i = 1) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ u : ι → ℂ, ∑ i, w i * u i = 1 → ∀ η : ℝ, (∀ i, ‖u i - 1‖ ≤ η) →
      η ≤ δ → ‖carlsonR t (fun i => c * w i) (fun i => u i ^ s) - 1 -
        s * t / 2 * (s * (c + t) / (c + 1) - 1) * ∑ i, w i * (1 - u i) ^ 2‖ ≤ C * η ^ 3 := by
  obtain ⟨K1, hK1, hbin⟩ := exists_norm_one_add_cpow_sub_le s
  obtain ⟨K2, hK2, htay⟩ := exists_norm_carlsonR_sub_quadratic_le t c hc w hw
  have hc1 : c + 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  set W := ∑ i, ‖w i‖
  set σ := ‖s * (s - 1) / 2‖
  set A1 := ‖s‖ + σ + K1 + 1
  have hA1 : 0 < A1 := by positivity
  set D1 := σ + K1
  set C : ℝ := K2 * A1 ^ 3 + ‖t‖ * (W * K1) + ‖t * (t - 1) / (2 * (c + 1))‖ * (W * (D1 * (A1 +
    ‖s‖))) + ‖t * (t - 1) * c / (2 * (c + 1))‖ * (W * D1) ^ 2
  refine ⟨C, min (1 / 2) (1 / (4 * A1)), lt_min (by norm_num) (by positivity),
    fun u hu η hη hηδ => ?_⟩
  have hW0 : 0 ≤ W := sum_nonneg fun i _ => norm_nonneg _
  have hη0 : 0 ≤ η := by
    by_contra h0
    push Not at h0
    have hne : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hw
    exact absurd ((norm_nonneg _).trans (hη (Classical.arbitrary ι))) (not_le.mpr h0)
  have hη2 : η ≤ 1 / 2 := hηδ.trans (min_le_left _ _)
  have hη1 : η ≤ 1 := by linarith
  have hηA : A1 * η ≤ 1 / 4 := by
    have := hηδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hWsum : ∀ (v : ι → ℂ) (B : ℝ), (∀ i, ‖v i‖ ≤ B) → ‖∑ i, w i * v i‖ ≤ W * B :=
    fun v B hv => by
      refine (norm_sum_le _ _).trans ?_
      rw [sum_mul]
      exact sum_le_sum fun i _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
  -- the binomial expansion of the nodes
  set h : ι → ℂ := fun i => u i - 1
  set y : ι → ℂ := fun i => u i ^ s - 1
  set e : ι → ℂ := fun i => y i - s * h i - s * (s - 1) / 2 * h i ^ 2
  have hh : ∀ i, ‖h i‖ ≤ η := hη
  have he : ∀ i, ‖e i‖ ≤ K1 * η ^ 3 := fun i => by
    have := hbin (h i) ((hh i).trans hη2)
    simp only [e, y, h, add_sub_cancel] at this ⊢
    refine this.trans (by gcongr; exact hh i)
  have hhη2 : ∀ i, ‖h i‖ ^ 2 ≤ η ^ 2 := fun i => by gcongr; exact hh i
  have hη3 : η ^ 3 ≤ η ^ 2 := by nlinarith [sq_nonneg η]
  have hη32 : η ^ 2 ≤ η := by nlinarith
  have hysh : ∀ i, ‖y i - s * h i‖ ≤ D1 * η ^ 2 := fun i => by
    have : y i - s * h i = s * (s - 1) / 2 * h i ^ 2 + e i := by simp only [e]; ring
    rw [this]
    calc _ ≤ σ * ‖h i‖ ^ 2 + K1 * η ^ 3 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (he i)); rw [norm_mul, norm_pow]
      _ ≤ σ * η ^ 2 + K1 * η ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hhη2 i) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hη3 hK1)
      _ = D1 * η ^ 2 := by ring
  have hy : ∀ i, ‖y i‖ ≤ A1 * η := fun i => by
    have : y i = s * h i + (y i - s * h i) := by ring
    rw [this]
    calc _ ≤ ‖s‖ * η + D1 * η ^ 2 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (hysh i)); rw [norm_mul]; gcongr; exact hh i
      _ ≤ ‖s‖ * η + D1 * η := by gcongr
      _ ≤ A1 * η := by simp only [A1, D1]; nlinarith
  -- the expansion of `R_t` at the diagonal
  have hT := htay (A1 * η) hηA (fun i => u i ^ s) (fun i => hy i)
  -- moments
  have hwh : ∑ i, w i * h i = 0 := by
    simp only [h, mul_sub, sum_sub_distrib, mul_one, hu, hw, sub_self]
  set Sy := ∑ i, w i * y i
  set Sy2 := ∑ i, w i * y i ^ 2
  set Sh2 := ∑ i, w i * h i ^ 2
  have hSy : ‖Sy - s * (s - 1) / 2 * Sh2‖ ≤ W * (K1 * η ^ 3) := by
    have : Sy - s * (s - 1) / 2 * Sh2 = ∑ i, w i * e i + s * ∑ i, w i * h i := by
      simp only [Sy, Sh2, e, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, hwh, mul_zero, add_zero]
    exact hWsum e _ he
  have hSy2 : ‖Sy2 - s ^ 2 * Sh2‖ ≤ W * (D1 * (A1 + ‖s‖) * η ^ 3) := by
    have : Sy2 - s ^ 2 * Sh2 = ∑ i, w i * ((y i - s * h i) * (y i + s * h i)) := by
      simp only [Sy2, Sh2, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this]
    refine hWsum _ _ fun i => ?_
    rw [norm_mul]
    have h2 : ‖y i + s * h i‖ ≤ (A1 + ‖s‖) * η := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have := hy i; have := hh i; nlinarith [norm_nonneg s]
    calc _ ≤ (D1 * η ^ 2) * ((A1 + ‖s‖) * η) := mul_le_mul (hysh i) h2 (norm_nonneg _)
          (by positivity)
      _ = D1 * (A1 + ‖s‖) * η ^ 3 := by ring
  have hSyn : ‖Sy‖ ≤ W * D1 * η ^ 2 := by
    have : Sy = ∑ i, w i * (y i - s * h i) + s * ∑ i, w i * h i := by
      simp only [Sy, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, hwh, mul_zero, add_zero]
    have := hWsum _ _ hysh
    linarith
  -- algebra
  have hQ : s * t / 2 * (s * (c + t) / (c + 1) - 1) * ∑ i, w i * (1 - u i) ^ 2 =
      (t * (s * (s - 1) / 2) + t * (t - 1) / (2 * (c + 1)) * s ^ 2) * Sh2 := by
    have : ∑ i, w i * (1 - u i) ^ 2 = Sh2 := sum_congr rfl fun i _ => by simp only [h]; ring
    rw [this]; field_simp; ring
  have hsplit : carlsonR t (fun i => c * w i) (fun i => u i ^ s) - 1 -
      s * t / 2 * (s * (c + t) / (c + 1) - 1) * ∑ i, w i * (1 - u i) ^ 2 =
      (carlsonR t (fun i => c * w i) (fun i => u i ^ s) - 1 - t * Sy -
        t * (t - 1) / (2 * (c + 1)) * (Sy2 + c * Sy ^ 2)) +
      t * (Sy - s * (s - 1) / 2 * Sh2) + t * (t - 1) / (2 * (c + 1)) * (Sy2 - s ^ 2 * Sh2) +
      t * (t - 1) * c / (2 * (c + 1)) * Sy ^ 2 := by
    rw [hQ]; field_simp; ring
  have hT' : ‖carlsonR t (fun i => c * w i) (fun i => u i ^ s) - 1 - t * Sy -
      t * (t - 1) / (2 * (c + 1)) * (Sy2 + c * Sy ^ 2)‖ ≤ K2 * (A1 * η) ^ 3 := by
    convert hT using 4
  rw [hsplit]
  have hSy2n : ‖Sy ^ 2‖ ≤ (W * D1) ^ 2 * η ^ 3 := by
    rw [norm_pow]
    calc ‖Sy‖ ^ 2 ≤ (W * D1 * η ^ 2) ^ 2 := by gcongr
      _ = (W * D1) ^ 2 * η ^ 4 := by ring
      _ ≤ (W * D1) ^ 2 * η ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη0 hη1 (by norm_num)) (by positivity)
  calc _ ≤ K2 * (A1 * η) ^ 3 + ‖t‖ * (W * (K1 * η ^ 3)) +
        ‖t * (t - 1) / (2 * (c + 1))‖ * (W * (D1 * (A1 + ‖s‖) * η ^ 3)) +
        ‖t * (t - 1) * c / (2 * (c + 1))‖ * ((W * D1) ^ 2 * η ^ 3) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add hT' ?_)) ?_)) ?_)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hSy (norm_nonneg _)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hSy2 (norm_nonneg _)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hSy2n (norm_nonneg _)
    _ = C * η ^ 3 := by simp only [C]; ring

end Carlson
