/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.SharpEstimates
public import Pochhammer.BinomialSeries
public import Pochhammer.Estimates

/-!
# Exponential growth of R-polynomials

Carlson's Theorem 6.6-2 describes the growth of `Rₙ(b, z) = Nₙ(b, z)/(c)ₙ`, `c = ∑ bᵢ`, as
`n → ∞`: `limsup ‖Rₙ(b, z)‖^{1/n} = max ‖zᵢ‖`. The upper bound holds whenever `c` is not a
nonpositive integer; it follows from the multinomial expansion and subexponential bounds on
`(B)ₙ/n!` from above and on `‖(c)ₙ‖/n!` from below.

The lower bound is proved by contradiction through the generating relation (6.6-1): if
`‖Rₙ‖ < (r - ε)ⁿ` eventually, where `r = ‖z_j‖` is maximal, then the generating function
`∏ (1 - t zᵢ)^{-bᵢ}` would extend analytically across `t = 1/z_j`, which is impossible
because `(1 - s)^{-b_j}` is not analytic at `s = 1` unless `b_j` is a nonpositive integer.

As printed, Carlson's theorem only requires `zᵢ ≠ 0` and no parameter conditions beyond `c`;
the lower bound then fails when nodes coincide, because the parameters at a repeated node can
cancel. `carlsonRPolynomial_coincident_counterexample` gives an explicit instance; here the
lower bound is proved for pairwise distinct nodes, the parameter at the maximal node not a
nonpositive integer. The form for arbitrary nodes, after aggregating equal nodes, is
`Carlson.frequently_le_norm_carlsonRPolynomial_aggregate` (`Carlson.Aggregation`).

## Main results

* `Carlson.eventually_norm_carlsonRPolynomial_le`: the upper half of Theorem 6.6-2.
* `Carlson.frequently_le_norm_carlsonRPolynomial`: the lower half, for distinct nodes.
* `Carlson.carlsonRPolynomial_coincident_counterexample`: coincident nodes can cancel.
* `Carlson.coeff_eq_of_hasSum_pow`: uniqueness of power-series coefficients on a disk.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.6.
-/

open Complex Filter Finset
open scoped Topology
@[expose] public noncomputable section

namespace Carlson

/-- Rising factorials divided by factorials grow subexponentially:
`(B)ₙ/n! ≤ C qⁿ` for every `q > 1`. -/
theorem exists_ascPochhammer_div_factorial_le (B : ℝ) {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, ∀ n : ℕ, |(ascPochhammer ℝ n).eval B| / n.factorial ≤ C * q ^ n := by
  have hq0 : 0 < q := by linarith
  have hs : ‖(q⁻¹ : ℂ)‖ < 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hq0.le]; exact inv_lt_one_of_one_lt₀ hq
  have h := (hasSum_ascPochhammer_mul_pow_div_factorial (B : ℂ) (q⁻¹ : ℂ) hs).summable
  have ht := h.tendsto_atTop_zero.norm
  rw [← Nat.cofinite_eq_atTop] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range_of_cofinite
  refine ⟨C, fun n => ?_⟩
  have hn := hC ⟨n, rfl⟩
  have hmap : (ascPochhammer ℂ n).eval (B : ℂ) = (((ascPochhammer ℝ n).eval B : ℝ) : ℂ) := by
    rw [← ascPochhammer_map Complex.ofRealHom, Polynomial.eval_map,
      show (B : ℂ) = Complex.ofRealHom B from rfl, Polynomial.eval₂_at_apply]; rfl
  simp only [hmap, norm_mul, norm_div, norm_pow, norm_inv, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs, abs_of_pos hq0] at hn
  have hqn : 0 < q ^ n := pow_pos hq0 n
  rw [inv_pow] at hn
  calc |(ascPochhammer ℝ n).eval B| / n.factorial
      = |(ascPochhammer ℝ n).eval B| / n.factorial * (q ^ n)⁻¹ * q ^ n := by field_simp
    _ ≤ C * q ^ n := mul_le_mul_of_nonneg_right hn hqn.le


/-- Away from the nonpositive integers, rising factorials divided by factorials decay at most
subexponentially: `C q⁻ⁿ ≤ ‖(c)ₙ‖/n!` for every `q > 1`. -/
theorem exists_le_norm_ascPochhammer_div_factorial {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) {q : ℝ}
    (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C * (q⁻¹) ^ n ≤ ‖(ascPochhammer ℂ n).eval c‖ / n.factorial := by
  have hq0 : 0 < q := by linarith
  set a : ℕ → ℝ := fun n => ‖(ascPochhammer ℂ n).eval c‖ / n.factorial
  have hne : ∀ n, (ascPochhammer ℂ n).eval c ≠ 0 := by
    intro n h
    obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h
    exact hc k (by rw [hk]; ring)
  have hapos : ∀ n, 0 < a n := fun n =>
    div_pos (norm_pos_iff.mpr (hne n)) (by exact_mod_cast n.factorial_pos)
  have hstep : ∀ n, a (n + 1) = a n * (‖c + n‖ / (n + 1)) := by
    intro n
    simp only [a, ascPochhammer_succ_eval, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  -- the ratio tends to one
  have hratio : Tendsto (fun n : ℕ => ‖c + n‖ / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have hlo : ∀ n : ℕ, ((n : ℝ) - ‖c‖) / (n + 1) ≤ ‖c + n‖ / (n + 1) := fun n => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := norm_sub_norm_le (n : ℂ) (-c)
      simp only [norm_neg, Complex.norm_natCast, sub_neg_eq_add] at this
      rw [add_comm] at this
      linarith
    have hhi : ∀ n : ℕ, ‖c + n‖ / (n + 1) ≤ ((n : ℝ) + ‖c‖) / (n + 1) := fun n => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := norm_add_le c (n : ℂ)
      simp only [Complex.norm_natCast] at this
      linarith
    have hl : Tendsto (fun n : ℕ => ((n : ℝ) - ‖c‖) / (n + 1)) atTop (𝓝 1) := by
      have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).sub
        ((tendsto_const_div_atTop_nhds_zero_nat ‖c‖).comp (tendsto_add_atTop_nat 1))
      simp only [sub_zero] at h
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]; push_cast; field_simp
    have hh : Tendsto (fun n : ℕ => ((n : ℝ) + ‖c‖) / (n + 1)) atTop (𝓝 1) := by
      have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).add
        ((tendsto_const_div_atTop_nhds_zero_nat ‖c‖).comp (tendsto_add_atTop_nat 1))
      simp only [add_zero] at h
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]; push_cast; field_simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hh hlo hhi
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hratio.eventually (lt_mem_nhds (inv_lt_one_of_one_lt₀ hq)))
  -- the minimum over the initial segment
  set C := (Finset.range (N + 1)).inf' (by simp) fun m => a m * q ^ m
  have hCpos : 0 < C := by
    rw [Finset.lt_inf'_iff]
    intro m _
    exact mul_pos (hapos m) (pow_pos hq0 m)
  refine ⟨C, hCpos, fun n => ?_⟩
  have hCle : ∀ m ≤ N, C ≤ a m * q ^ m := fun m hm =>
    Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have hinvq : (q⁻¹) ^ n * q ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
  -- beyond `N` the sequence decreases at most by `q⁻¹` per step
  have hgrow : ∀ k, a N * (q⁻¹) ^ k ≤ a (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hstep, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hN (N + k) (by omega)).le (by positivity) (hapos _).le
  rcases le_total n N with h | h
  · have := hCle n h
    calc C * (q⁻¹) ^ n ≤ a n * q ^ n * (q⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = a n := by rw [mul_assoc, mul_comm (q ^ n), hinvq, mul_one]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 := hCle N le_rfl
    have h2 := hgrow k
    calc C * (q⁻¹) ^ (N + k) ≤ a N * q ^ N * (q⁻¹) ^ (N + k) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = a N * (q⁻¹) ^ k := by
          rw [pow_add, show a N * q ^ N * ((q⁻¹) ^ N * (q⁻¹) ^ k) =
            a N * (q ^ N * (q⁻¹) ^ N) * (q⁻¹) ^ k by ring, mul_comm (q ^ N), ← mul_pow,
            inv_mul_cancel₀ hq0.ne', one_pow, mul_one]
      _ ≤ a (N + k) := h2


/-- Iterated derivatives of `(1 - s)^A` on the principal branch:
`Dᵏ (1 - s)^A = (-1)ᵏ A (A-1) ⋯ (A-k+1) (1 - s)^{A-k}`. -/
theorem iteratedDeriv_one_sub_cpow (A : ℂ) (k : ℕ) {s : ℂ} (hs : 1 - s ∈ slitPlane) :
    iteratedDeriv k (fun w => (1 - w) ^ A) s =
      (-1) ^ k * (descPochhammer ℂ k).eval A * (1 - s) ^ (A - k) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have hU : {w : ℂ | 1 - w ∈ slitPlane} ∈ 𝓝 s :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_slitPlane.mem_nhds hs)
    have he : iteratedDeriv k (fun w => (1 - w) ^ A) =ᶠ[𝓝 s]
        fun w => (-1) ^ k * (descPochhammer ℂ k).eval A * (1 - w) ^ (A - k) := by
      filter_upwards [hU] with w hw using ih hw
    have hd := (((hasDerivAt_id s).const_sub 1).cpow_const (c := A - k) hs).const_mul
      ((-1) ^ k * (descPochhammer ℂ k).eval A)
    simp only [id] at hd
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

/-- **Theorem 6.6-2, upper half**: if `c = ∑ bᵢ` is not a nonpositive integer and `‖zᵢ‖ ≤ r`,
then `‖Rₙ(b, z)‖ ≤ (r + ε)ⁿ` for all large `n`, where `Rₙ(b, z) = Nₙ(b, z)/(c)ₙ`. -/
theorem eventually_norm_carlsonRPolynomial_le {ι : Type*} [Fintype ι] (b z : ι → ℂ)
    (hc : ∀ m : ℕ, ∑ i, b i ≠ -m) {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖carlsonRPolynomialNumerator n b z /
      (ascPochhammer ℂ n).eval (∑ i, b i)‖ ≤ (r + ε) ^ n := by
  set B : ℝ := ∑ i, ‖b i‖
  set q : ℝ := Real.sqrt (1 + ε / (2 * (r + 1)))
  have hq2 : q ^ 2 = 1 + ε / (2 * (r + 1)) := Real.sq_sqrt (by positivity)
  have hq : 1 < q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith [show 0 < ε / (2 * (r + 1)) by positivity])
  have hq0 : 0 < q := by linarith
  obtain ⟨C₁, hC₁⟩ := exists_ascPochhammer_div_factorial_le B hq
  obtain ⟨C₂, hC₂, hC₂'⟩ := exists_le_norm_ascPochhammer_div_factorial hc hq
  have hbound : ∀ n : ℕ, ‖carlsonRPolynomialNumerator n b z /
      (ascPochhammer ℂ n).eval (∑ i, b i)‖ ≤ C₁ / C₂ * (q ^ 2 * r) ^ n := by
    intro n
    have hN := norm_carlsonRPolynomialNumerator_le_sum_norm n b z hr hz
    have hl := hC₂' n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hP : 0 < ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ := by
      have := mul_pos hC₂ (pow_pos (inv_pos.mpr hq0) n)
      have := this.trans_le hl
      exact (div_pos_iff_of_pos_right hfac).mp this
    have h1 := hC₁ n
    have hB0 : (ascPochhammer ℝ n).eval B ≤ |(ascPochhammer ℝ n).eval B| := le_abs_self _
    rw [norm_div]
    rw [div_le_iff₀ hP]
    have hinv : (q⁻¹) ^ n * q ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
    calc ‖carlsonRPolynomialNumerator n b z‖ ≤ (ascPochhammer ℝ n).eval B * r ^ n := hN
      _ ≤ C₁ * q ^ n * n.factorial * r ^ n := by
          have := (div_le_iff₀ hfac).mp h1
          nlinarith [pow_nonneg hr n]
      _ = C₁ / C₂ * (q ^ 2 * r) ^ n * (C₂ * (q⁻¹) ^ n * n.factorial) := by
          rw [mul_pow, ← pow_mul, mul_comm 2 n, pow_mul, inv_pow]
          have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq0.ne'
          field_simp
      _ ≤ C₁ / C₂ * (q ^ 2 * r) ^ n * ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ := by
          have hK : 0 ≤ C₁ / C₂ * (q ^ 2 * r) ^ n := by
            have : 0 ≤ C₁ := by
              have := hC₁ 0
              simp at this
              linarith
            positivity
          have := (le_div_iff₀ hfac).mp hl
          exact mul_le_mul_of_nonneg_left this hK
  -- absorb the constant
  have hs : q ^ 2 * r ≤ r + ε / 2 := by
    rw [hq2]
    have : ε / (2 * (r + 1)) * r ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hlim : Tendsto (fun n : ℕ => C₁ / C₂ * ((r + ε / 2) / (r + ε)) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (r + ε / 2) / (r + ε)) (by positivity)
      ((div_lt_one (by linarith)).mpr (by linarith))
    simpa using this.const_mul (C₁ / C₂)
  filter_upwards [hlim.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  refine (hbound n).trans ?_
  have hpos : 0 < r + ε := by linarith
  have h1 : (q ^ 2 * r) ^ n ≤ (r + ε / 2) ^ n :=
    pow_le_pow_left₀ (by positivity) hs n
  have h2 : C₁ / C₂ * (r + ε / 2) ^ n ≤ (r + ε) ^ n := by
    have := mul_le_mul_of_nonneg_right hn (pow_nonneg hpos.le n)
    rw [div_pow, one_mul] at this
    calc C₁ / C₂ * (r + ε / 2) ^ n = C₁ / C₂ * ((r + ε / 2) ^ n / (r + ε) ^ n) * (r + ε) ^ n := by
          field_simp
      _ ≤ (r + ε) ^ n := this
  have hC : 0 ≤ C₁ / C₂ := by
    have : 0 ≤ C₁ := by
      have := hC₁ 0
      simp at this
      linarith
    positivity
  calc C₁ / C₂ * (q ^ 2 * r) ^ n ≤ C₁ / C₂ * (r + ε / 2) ^ n := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ (r + ε) ^ n := h2


/-- The binomial function `(1 - s)^{-b}` has a genuine singularity at `s = 1` unless `b` is a
nonpositive integer: it has no analytic extension across `1` from the unit disk. -/
theorem not_exists_analyticAt_eq_one_sub_cpow {b : ℂ} (hb : ∀ m : ℕ, b ≠ -m) {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 1) (heq : ∀ s : ℂ, ‖s‖ < 1 → h s = (1 - s) ^ (-b)) : False := by
  set N : ℕ := ⌈|b.re|⌉₊ + 1
  have hN : 0 < b.re + N := by
    have := Nat.le_ceil |b.re|
    have := neg_abs_le b.re
    simp only [N, Nat.cast_add, Nat.cast_one]; linarith
  -- the coefficient `(b)_N` does not vanish
  set P := (-1 : ℂ) ^ N * (descPochhammer ℂ N).eval (-b)
  have hP : P ≠ 0 := by
    have h1 := ascPochhammer_eval_neg_eq_descPochhammer ℂ (-b) N
    rw [neg_neg] at h1
    have h2 : (ascPochhammer ℂ N).eval b ≠ 0 := by
      intro h0
      obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h0
      exact hb k (by rw [hk]; ring)
    simpa [P, h1] using h2
  -- the derivatives of `h` near `1` are those of `(1 - s)^{-b}`
  have hderiv : ∀ η : ℝ, 0 < η → η < 1 →
      iteratedDeriv N h (1 - η) = P * ((η : ℂ) ^ (-b - N)) := by
    intro η hη hη1
    have hs : ‖(1 - η : ℂ)‖ < 1 := by
      rw [show (1 - η : ℂ) = ((1 - η : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
    have hev : h =ᶠ[𝓝 (1 - η : ℂ)] fun s => (1 - s) ^ (-b) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hs] with s hs'
      exact heq s hs'
    rw [hev.iteratedDeriv_eq, iteratedDeriv_one_sub_cpow (-b) N (by
      rw [show (1 : ℂ) - (1 - η) = (η : ℂ) by ring]; exact ofReal_mem_slitPlane.mpr hη)]
    rw [show (1 : ℂ) - (1 - η) = (η : ℂ) by ring]
  -- the derivatives of `h` stay bounded near `1`
  have hcont : ContinuousAt (iteratedDeriv N h) 1 := by
    have := (hh.iterated_deriv N).continuousAt
    rwa [← iteratedDeriv_eq_iterate] at this
  have hbd : ∀ᶠ η : ℝ in 𝓝[>] 0, ‖iteratedDeriv N h (1 - η)‖ ≤ ‖iteratedDeriv N h 1‖ + 1 := by
    have hc : Tendsto (fun η : ℝ => iteratedDeriv N h (1 - η)) (𝓝 0) (𝓝 (iteratedDeriv N h 1)) := by
      have : Tendsto (fun η : ℝ => (1 - η : ℂ)) (𝓝 0) (𝓝 1) := by
        have hc : Continuous fun η : ℝ => (1 : ℂ) - η := by fun_prop
        have := hc.tendsto 0
        simpa using this
      exact hcont.tendsto.comp this
    have := hc.norm.eventually (ge_mem_nhds (show ‖iteratedDeriv N h 1‖ <
      ‖iteratedDeriv N h 1‖ + 1 by linarith))
    exact nhdsWithin_le_nhds this
  -- while those of `(1 - s)^{-b}` blow up
  have hblow : Tendsto (fun η : ℝ => ‖P‖ * η ^ (-(b.re + N))) (𝓝[>] 0) atTop := by
    exact (tendsto_rpow_neg_nhdsGT_zero (by linarith)).const_mul_atTop (norm_pos_iff.mpr hP)
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη using hη.2
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := (hbd.and (hsmall.and ((hblow.eventually_gt_atTop
    (‖iteratedDeriv N h 1‖ + 1)).and self_mem_nhdsWithin))).exists
  rw [hderiv η hη4 hη2, norm_mul, norm_cpow_eq_rpow_re_of_pos hη4] at hη1
  have : (-b - (N : ℂ)).re = -(b.re + N) := by simp; ring
  rw [this] at hη1
  linarith


/-- A point of the closed unit disk other than `1` has `re (1 - w) > 0`. -/
theorem re_one_sub_pos_of_norm_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) : 0 < (1 - w).re := by
  simp only [sub_re, one_re]
  have hre := re_le_norm w
  by_contra h
  push Not at h
  have hre1 : w.re = 1 := by linarith
  have him : w.im = 0 := by
    have hn := Complex.sq_norm w
    rw [Complex.normSq_apply] at hn
    have : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    nlinarith [sq_nonneg w.im]
  exact hw1 (Complex.ext hre1 him)

/-- **Theorem 6.6-2, lower half**, with the hypothesis corrected to pairwise distinct nodes: if
`c = ∑ bᵢ` is not a nonpositive integer and the nodes are distinct, then for a node `z_j` of
maximal modulus `r` whose parameter `b_j` is not a nonpositive integer and every `0 < ε < r`,
`‖Rₙ(b, z)‖ ≥ (r - ε)ⁿ` for infinitely many `n`. Only the parameter at `z_j` matters. -/
theorem frequently_le_norm_carlsonRPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b z : ι → ℂ) (hc : ∀ m : ℕ, ∑ i, b i ≠ -m)
    (hz : Function.Injective z) {j : ι} (hj : ∀ i, ‖z i‖ ≤ ‖z j‖)
    (hb : ∀ m : ℕ, b j ≠ -m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < ‖z j‖) :
    ∃ᶠ n in atTop, (‖z j‖ - ε) ^ n ≤ ‖carlsonRPolynomialNumerator n b z /
      (ascPochhammer ℂ n).eval (∑ i, b i)‖ := by
  set r := ‖z j‖
  have hr : 0 < r := by linarith
  have hzj : z j ≠ 0 := norm_pos_iff.mp hr
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_le] at hcon
  -- coefficient bounds for the generating series
  set a : ℕ → ℂ := fun n => carlsonRPolynomialNumerator n b z / n.factorial
  set ρ : ℝ := r - ε / 2
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  set q : ℝ := ρ / (r - ε)
  have hq : 1 < q := (one_lt_div (by linarith)).mpr (by simp only [ρ]; linarith)
  obtain ⟨C, hC⟩ := exists_ascPochhammer_div_factorial_le ‖∑ i, b i‖ hq
  have ha : ∀ᶠ n in atTop, ‖a n‖ * (ρ⁻¹) ^ n ≤ C := by
    filter_upwards [hcon] with n hn
    have hP := norm_ascPochhammer_eval_le_ascPochhammer (∑ i, b i) n le_rfl
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hPne : (ascPochhammer ℂ n).eval (∑ i, b i) ≠ 0 := by
      intro h0
      obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h0
      exact hc k (by rw [hk]; ring)
    have hsplit : ‖a n‖ = ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ / n.factorial *
        ‖carlsonRPolynomialNumerator n b z / (ascPochhammer ℂ n).eval (∑ i, b i)‖ := by
      simp only [a, norm_div, Complex.norm_natCast]
      field_simp [norm_ne_zero_iff.mpr hPne]
    have h1 := hC n
    have hle : ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ / n.factorial ≤ C * q ^ n :=
      calc ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ / n.factorial
          ≤ (ascPochhammer ℝ n).eval ‖∑ i, b i‖ / n.factorial :=
            div_le_div_of_nonneg_right hP hfac.le
        _ ≤ |(ascPochhammer ℝ n).eval ‖∑ i, b i‖| / n.factorial :=
            div_le_div_of_nonneg_right (le_abs_self _) hfac.le
        _ ≤ C * q ^ n := h1
    have hqr : q * (r - ε) = ρ := by
      simp only [q]; rw [div_mul_cancel₀ _ (by linarith : r - ε ≠ 0)]
    rw [hsplit]
    calc ‖(ascPochhammer ℂ n).eval (∑ i, b i)‖ / n.factorial *
          ‖carlsonRPolynomialNumerator n b z / (ascPochhammer ℂ n).eval (∑ i, b i)‖ * (ρ⁻¹) ^ n
        ≤ C * q ^ n * (r - ε) ^ n * (ρ⁻¹) ^ n := by
          have h0 : 0 ≤ C * q ^ n :=
            (div_nonneg (norm_nonneg _) hfac.le).trans hle
          exact mul_le_mul_of_nonneg_right (mul_le_mul hle hn.le (norm_nonneg _) h0)
            (pow_nonneg (inv_nonneg.mpr hρ.le) n)
      _ = C := by
          rw [mul_assoc C, ← mul_pow, hqr, mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow,
            mul_one]
  -- the generating series has radius at least `ρ⁻¹ > r⁻¹`
  set p := FormalMultilinearSeries.ofScalars ℂ a
  set R : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  have hR : (R : ℝ) = ρ⁻¹ := rfl
  have hRpos : (0 : ℝ) < R := by rw [hR]; exact inv_pos.mpr hρ
  have hrad : (R : ENNReal) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_isBigO _ ?_
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [ha] with n hn
    rw [FormalMultilinearSeries.ofScalars_norm, hR, Real.norm_of_nonneg (by positivity), norm_one,
      mul_one]
    exact hn
  have hradpos : 0 < p.radius := lt_of_lt_of_le (by
    rw [ENNReal.coe_pos, ← NNReal.coe_pos]; exact hRpos) hrad
  have hG := p.hasFPowerSeriesOnBall hradpos
  set G := p.sum
  have hGsum : ∀ t : ℂ, ‖t‖ < ρ⁻¹ → HasSum (fun n => a n * t ^ n) (G t) := by
    intro t ht
    have hmem : t ∈ Metric.eball (0 : ℂ) p.radius := by
      refine lt_of_lt_of_le ?_ hrad
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff hRpos, hR]
      exact ht
    have := hG.hasSum hmem
    simpa [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this
  -- on the disk of radius `r⁻¹` the series is Carlson's generating kernel
  have hGker : ∀ t : ℂ, ‖t‖ < r⁻¹ → G t = carlsonRGeneratingKernel b z t := by
    intro t ht
    have hρr : r⁻¹ < ρ⁻¹ := inv_strictAnti₀ hρ (by simp only [ρ]; linarith)
    have h1 := hGsum t (ht.trans hρr)
    have h2 := hasSum_carlsonRPolynomialNumerator_div_factorial b z t (fun i => by
      rw [norm_mul]
      calc ‖t‖ * ‖z i‖ ≤ ‖t‖ * r := mul_le_mul_of_nonneg_left (hj i) (norm_nonneg _)
        _ < r⁻¹ * r := mul_lt_mul_of_pos_right ht hr
        _ = 1 := inv_mul_cancel₀ hr.ne')
    exact h1.unique h2
  -- the extension of `(1 - s)^{-b_j}` across `s = 1`
  have hw : ∀ i ∈ Finset.univ.erase j, ∀ s : ℂ, ‖s‖ ≤ 1 → s * (z i / z j) ≠ 1 →
      0 < (1 - s * (z i / z j)).re := by
    intro i _ s hs hne
    refine re_one_sub_pos_of_norm_le_one ?_ hne
    rw [norm_mul, norm_div]
    calc ‖s‖ * (‖z i‖ / ‖z j‖) ≤ 1 * 1 := by
          apply mul_le_mul hs ((div_le_one hr).mpr (hj i)) (by positivity) zero_le_one
      _ = 1 := by ring
  set h : ℂ → ℂ := fun s => G (s / z j) *
    ∏ i ∈ Finset.univ.erase j, (1 - s * (z i / z j)) ^ (b i)
  have hh : AnalyticAt ℂ h 1 := by
    have hGa : AnalyticAt ℂ G (1 / z j) := by
      refine hG.analyticAt_of_mem ?_
      refine lt_of_lt_of_le ?_ hrad
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff hRpos, hR, norm_div, norm_one, one_div]
      exact inv_strictAnti₀ hρ (show ρ < r by simp only [ρ]; linarith)
    refine (hGa.comp_of_eq (analyticAt_id.div_const) (by simp)).mul ?_
    refine Finset.analyticAt_fun_prod _ fun i hi => ?_
    have hne : (1 : ℂ) * (z i / z j) ≠ 1 := by
      rw [one_mul]
      intro h1
      have := (div_eq_one_iff_eq hzj).mp h1
      exact (Finset.mem_erase.mp hi).1 (hz this)
    exact ((analyticAt_const.sub (analyticAt_id.mul analyticAt_const))).cpow analyticAt_const
      (Or.inl (hw i hi 1 (by simp) hne))
  have heq : ∀ s : ℂ, ‖s‖ < 1 → h s = (1 - s) ^ (-b j) := by
    intro s hs
    have hsz : ‖s / z j‖ < r⁻¹ := by
      rw [norm_div]; exact (div_lt_iff₀ hr).mpr (by rw [inv_mul_cancel₀ hr.ne']; exact hs)
    simp only [h]
    rw [hGker _ hsz, carlsonRGeneratingKernel, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      mul_assoc, ← Finset.prod_mul_distrib]
    have hone : ∀ i ∈ Finset.univ.erase j,
        1 / (1 - s / z j * z i) ^ (b i) * (1 - s * (z i / z j)) ^ (b i) = 1 := by
      intro i hi
      have hne0 : (1 - s * (z i / z j)) ≠ 0 := by
        have hlt : ‖s * (z i / z j)‖ < 1 := by
          rw [norm_mul, norm_div]
          calc ‖s‖ * (‖z i‖ / ‖z j‖) ≤ ‖s‖ * 1 :=
                mul_le_mul_of_nonneg_left ((div_le_one hr).mpr (hj i)) (norm_nonneg _)
            _ < 1 := by rw [mul_one]; exact hs
        intro h0
        have : s * (z i / z j) = 1 := by linear_combination -h0
        rw [this, norm_one] at hlt
        exact lt_irrefl _ hlt
      rw [show 1 - s / z j * z i = 1 - s * (z i / z j) by ring, one_div,
        inv_mul_cancel₀ ((cpow_ne_zero_iff).mpr (Or.inl hne0))]
    rw [Finset.prod_congr rfl hone, Finset.prod_const_one, mul_one,
      show s / z j * z j = s by field_simp, one_div, ← cpow_neg]
  exact not_exists_analyticAt_eq_one_sub_cpow hb hh heq

/-- Coefficients of a power series are determined by its sums on a disk. -/
theorem coeff_eq_of_hasSum_pow {a b : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ) {F : ℂ → ℂ}
    (ha : ∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => a n * t ^ n) (F t))
    (hb : ∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => b n * t ^ n) (F t)) : a = b := by
  have hps : ∀ c : ℕ → ℂ, (∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => c n * t ^ n) (F t)) →
      HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    intro c hc
    set r : NNReal := ⟨δ / 2, by positivity⟩
    have hr : ((r : ℝ)) = δ / 2 := rfl
    have hrad : (r : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
      refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
      have hrδ : ‖(((r : ℝ)) : ℂ)‖ < δ := by
        rw [Complex.norm_real, hr, Real.norm_of_nonneg (by positivity)]; linarith
      have h := (hc _ hrδ).summable.tendsto_atTop_zero.norm
      simp only [norm_zero] at h
      refine h.congr fun n => ?_
      rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg r.coe_nonneg]
    have hr0 : (0 : ENNReal) < r := by
      rw [ENNReal.coe_pos, ← NNReal.coe_pos, hr]; positivity
    refine ⟨r, ⟨hrad, hr0, fun {y} hy => ?_⟩⟩
    have hy' : ‖y‖ < δ := by
      have := Metric.mem_eball.mp hy
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff (by rw [hr]; positivity)] at this
      have : ‖y‖ < δ / 2 := by rw [← hr]; exact this
      linarith
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hc y hy'
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ (E := ℂ)
    ((hps a ha).eq_formalMultilinearSeries (hps b hb))

/-- **The counterexample to Theorem 6.6-2 as printed**: with coincident nodes the parameters of
the singular factor can cancel. For `b = (1/2, -1/2, 1)` and `z = (2, 2, 1)` all parameter
conditions hold, but `Rₙ(b, z) = 1` for every `n`, so `limsup |Rₙ|^{1/n} = 1 < 2 = max |zᵢ|`. -/
theorem carlsonRPolynomial_coincident_counterexample (n : ℕ) :
    carlsonRPolynomialNumerator n ![(1 / 2 : ℂ), -1 / 2, 1] ![(2 : ℂ), 2, 1] /
      (ascPochhammer ℂ n).eval (∑ i, ![(1 / 2 : ℂ), -1 / 2, 1] i) = 1 := by
  have hsum : ∑ i, ![(1 / 2 : ℂ), -1 / 2, 1] i = 1 := by
    simp only [Fin.sum_univ_three]; norm_num
  rw [hsum, ascPochhammer_eval_one]
  have hcoeff := coeff_eq_of_hasSum_pow (δ := 1 / 2) (by norm_num)
    (a := fun n => carlsonRPolynomialNumerator n ![(1 / 2 : ℂ), -1 / 2, 1] ![(2 : ℂ), 2, 1] /
      n.factorial) (b := fun _ => 1) (F := fun t => 1 / (1 - t)) (fun t ht => by
      have h := hasSum_carlsonRPolynomialNumerator_div_factorial ![(1 / 2 : ℂ), -1 / 2, 1]
        ![(2 : ℂ), 2, 1] t (fun i => by
          fin_cases i <;> simp <;> linarith [norm_nonneg t])
      convert h using 1
      simp only [carlsonRGeneratingKernel, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, cpow_one]
      rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
      have h2 : (1 - t * 2) ^ (1 / 2 : ℂ) ≠ 0 := by
        refine (cpow_ne_zero_iff).mpr (Or.inl fun h0 => ?_)
        have : ‖t * 2‖ = 1 := by rw [show t * 2 = 1 by linear_combination -h0]; simp
        rw [norm_mul] at this; norm_num at this; linarith
      field_simp)
    (fun t ht => by
      have := hasSum_geometric_of_norm_lt_one (show ‖t‖ < 1 by linarith)
      simpa [one_div] using this)
  have := congrFun hcoeff n
  rw [this]

end Carlson
