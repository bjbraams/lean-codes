/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.R.EulerTransform
public import Carlson.R.Homogeneity
public import Carlson.TwoVariable.ParameterSymmetry

/-!
# `₃F₂` at unit argument as an average of `₂F₁` (Carlson's Exercises 8.3-10 to 8.3-12)

The generalized hypergeometric series `₃F₂(a, b, c; d, e; x)` is introduced through its
coefficients `(a)ₙ (b)ₙ (c)ₙ/((d)ₙ (e)ₙ n!)`. With `s = d + e - a - b - c`, the coefficients are
`O(n^{-1-re s})`, so for `re s > 0` the series converges absolutely and uniformly on the closed
unit disk. Exchanging the sum with the beta integral gives the Dirichlet-average representation
`B(c, e - c) ₃F₂(a, b, c; d, e; x) = ∫₀¹ u^{c-1} (1 - u)^{e-c-1} ₂F₁(a, b; d; ux) du`.
At `x = 1`, Euler's transformation of `₂F₁` (derived here from the Euler transformation of the
R-function) gives Exercise 8.3-11, and two applications of it give Exercise 8.3-12.

## Main definitions

* `Carlson.TwoVariable.threeFTwoCoeff`, `Carlson.TwoVariable.threeFTwo`: the `₃F₂` series.

## Main results

* `Carlson.TwoVariable.regularizedGaussHGFun_euler`,
  `Carlson.TwoVariable.ordinaryHypergeometric_euler`: Euler's transformation
  `₂F₁(α, β; γ; x) = (1 - x)^{γ-α-β} ₂F₁(γ - α, γ - β; γ; x)` for real `|x| < 1`.
* `Carlson.TwoVariable.summable_threeFTwo`, `Carlson.TwoVariable.continuousOn_threeFTwo`,
  `Carlson.TwoVariable.betaIntegral_mul_threeFTwo`: Exercise 8.3-10.
* `Carlson.TwoVariable.betaIntegral_mul_threeFTwo_one`: Exercise 8.3-11.
* `Carlson.TwoVariable.Gamma_div_mul_threeFTwo_one`: Exercise 8.3-12.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Complex Filter Set MeasureTheory
open scoped Topology Nat

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **Euler's transformation** of the regularized Gauss function, for real `|x| < 1`:
`₂F₁(α, β; γ; x)/Γ(γ) = (1 - x)^{γ-α-β} ₂F₁(γ - α, γ - β; γ; x)/Γ(γ)`. -/
theorem regularizedGaussHGFun_euler (α β γ : ℂ) {x : ℝ} (hx : |x| < 1) :
    regularizedGaussHGFun α β γ x =
      ((1 - x : ℝ) : ℂ) ^ (γ - α - β) * regularizedGaussHGFun (γ - α) (γ - β) γ x := by
  have hx' : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs]
  have h1x : 0 < 1 - x := by linarith [le_abs_self x]
  have hw : (((1 - x : ℝ) : ℂ)) ∈ slitPlane := ofReal_mem_slitPlane.mpr h1x
  have hw' : (((1 - x : ℝ) : ℂ))⁻¹ ∈ slitPlane := by
    rw [← ofReal_inv]; exact ofReal_mem_slitPlane.mpr (inv_pos.mpr h1x)
  have hz : pair (1 : ℂ) ((1 - x : ℝ) : ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [pair]
    · exact hw
  rw [← regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun α β γ hx',
    ← regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun (γ - α) (γ - β) γ hx',
    show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    regCarlsonR_euler _ _ hz, sum_pair, show γ - (γ - β) = β by ring]
  have hinv : (fun i => (pair (1 : ℂ) ((1 - x : ℝ) : ℂ) i)⁻¹) =
      pair 1 (((1 - x : ℝ) : ℂ))⁻¹ := by
    funext i; fin_cases i <;> simp [pair]
  rw [hinv, regCarlsonR_pair_swap _ β (γ - β) hw' (by simp)]
  have hsc : pair (((1 - x : ℝ) : ℂ))⁻¹ 1 =
      fun i => (((1 - x)⁻¹ : ℝ) : ℂ) * pair (1 : ℂ) ((1 - x : ℝ) : ℂ) i := by
    have h0 : (1 : ℂ) - x ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    funext i; fin_cases i <;> simp [pair]; field_simp
  rw [hsc, regCarlsonR_smul_of_pos _ _ (inv_pos.mpr h1x) hz]
  have hpow : ((((1 - x)⁻¹ : ℝ) : ℂ)) ^ (-(γ - β + β) - -α) = ((1 - x : ℝ) : ℂ) ^ (γ - α) := by
    rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg h1x.le]; exact Real.pi_ne_zero.symm),
      ← cpow_neg]
    congr 1; ring
  have h0 : (((1 - x : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr h1x.ne'
  rw [hpow, Fin.prod_univ_two]
  simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_cpow,
    one_mul]
  rw [show -(γ - β + β) - -α = -(γ - α) by ring, ← mul_assoc, ← cpow_add _ _ h0]
  congr 2
  ring

/-- **Euler's transformation** of `₂F₁` for real `|x| < 1` and `γ` not a pole of `Γ`:
`₂F₁(α, β; γ; x) = (1 - x)^{γ-α-β} ₂F₁(γ - α, γ - β; γ; x)`. -/
theorem ordinaryHypergeometric_euler (α β : ℂ) {γ : ℂ} (hγ : ∀ k : ℕ, γ ≠ -k) {x : ℝ}
    (hx : |x| < 1) :
    ordinaryHypergeometric α β γ (x : ℂ) =
      ((1 - x : ℝ) : ℂ) ^ (γ - α - β) * ordinaryHypergeometric (γ - α) (γ - β) γ (x : ℂ) := by
  have hG : Gamma γ ≠ 0 := Gamma_ne_zero hγ
  have h1 := ordinaryHypergeometric_div_Gamma_eq (a := α) (b := β) (z := (x : ℂ)) hγ
  have h2 := ordinaryHypergeometric_div_Gamma_eq (a := γ - α) (b := γ - β) (z := (x : ℂ)) hγ
  rw [regularizedGaussHGFun_euler α β γ hx, ← h2] at h1
  field_simp at h1
  linear_combination h1

/-- The coefficients `(a)ₙ (b)ₙ (c)ₙ/((d)ₙ (e)ₙ n!)` of the generalized hypergeometric series
`₃F₂(a, b, c; d, e; x)`. -/
def threeFTwoCoeff (a b c d e : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * (ascPochhammer ℂ n).eval c /
    ((ascPochhammer ℂ n).eval d * (ascPochhammer ℂ n).eval e * n !)

/-- The generalized hypergeometric function `₃F₂(a, b, c; d, e; x)`, as the sum of its series
(the junk value is the `tsum` convention when the series diverges). -/
def threeFTwo (a b c d e x : ℂ) : ℂ :=
  ∑' n, threeFTwoCoeff a b c d e n * x ^ n

/-- The `₃F₂` coefficients are symmetric in the numerator parameters. -/
theorem threeFTwoCoeff_comm_left (a b c d e : ℂ) (n : ℕ) :
    threeFTwoCoeff b a c d e n = threeFTwoCoeff a b c d e n := by
  simp only [threeFTwoCoeff]; ring

/-- The `₃F₂` coefficients are symmetric in the numerator parameters. -/
theorem threeFTwoCoeff_comm_right (a b c d e : ℂ) (n : ℕ) :
    threeFTwoCoeff a c b d e n = threeFTwoCoeff a b c d e n := by
  simp only [threeFTwoCoeff]; ring

/-- The `₃F₂` coefficients are symmetric in the denominator parameters. -/
theorem threeFTwoCoeff_comm_denom (a b c d e : ℂ) (n : ℕ) :
    threeFTwoCoeff a b c e d n = threeFTwoCoeff a b c d e n := by
  simp only [threeFTwoCoeff]; ring

/-- A Pochhammer symbol at a point that is not a pole of `Γ` is nonzero. -/
private theorem ascPochhammer_eval_ne_zero {d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (n : ℕ) :
    (ascPochhammer ℂ n).eval d ≠ 0 := by
  rw [ascPochhammer_eval_eq_prod_range']
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => hd j ?_
  linear_combination h

open Asymptotics in
/-- For `d, e` not poles of `Γ` and `re (d + e - a - b - c) > 0`, the `₃F₂` coefficients are
absolutely summable: they are `O(n^{-1-re s})`. -/
theorem summable_norm_threeFTwoCoeff {a b c d e : ℂ} (hd : ∀ k : ℕ, d ≠ -k)
    (he : ∀ k : ℕ, e ≠ -k) (hs : 0 < (d + e - a - b - c).re) :
    Summable (fun n => ‖threeFTwoCoeff a b c d e n‖) := by
  set ε := (d + e - a - b - c).re
  set A : ℂ → ℕ → ℂ := fun s m => (ascPochhammer ℂ (m + 1)).eval s / ((m : ℂ) ^ s * m.factorial)
  have hinvA : ∀ {s : ℂ}, (∀ k : ℕ, s ≠ -k) → Tendsto (fun m => (A s m)⁻¹) atTop (𝓝 (Gamma s)) :=
    fun {s} hs' => by
      have := (tendsto_ascPochhammer_div s).inv₀ (inv_ne_zero (Gamma_ne_zero hs'))
      rw [inv_inv] at this
      exact this
  set g : ℕ → ℝ := fun m => ((m : ℝ) ^ (1 + ε))⁻¹
  have hg : Summable g := Real.summable_nat_rpow_inv.mpr (by linarith)
  have hh : (fun m : ℕ => (m : ℂ) ^ (a + b + c - d - e) / ((m : ℂ) + 1)) =O[atTop] g := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [norm_div, norm_natCast_cpow_of_pos (by omega), Real.norm_of_nonneg
      (by positivity : (0 : ℝ) ≤ g m)]
    have hre : (a + b + c - d - e).re = -ε := by simp only [ε, sub_re, add_re]; ring
    rw [hre]
    have h1 : ‖(m : ℂ) + 1‖ = m + 1 := by
      rw [show (m : ℂ) + 1 = ((m + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h1, Real.rpow_neg hm0.le]
    have hg' : g m = ((m : ℝ) ^ ε)⁻¹ * (m : ℝ)⁻¹ := by
      simp only [g]; rw [Real.rpow_add hm0, Real.rpow_one, mul_inv, mul_comm]
    rw [hg', one_mul, div_le_iff₀ (by positivity)]
    have hmε : 0 < (m : ℝ) ^ ε := Real.rpow_pos_of_pos hm0 ε
    have : (m : ℝ)⁻¹ * (m + 1) ≥ 1 := by
      rw [inv_mul_eq_div, ge_iff_le, one_le_div hm0]; linarith
    calc ((m : ℝ) ^ ε)⁻¹ = ((m : ℝ) ^ ε)⁻¹ * 1 := by ring
      _ ≤ ((m : ℝ) ^ ε)⁻¹ * ((m : ℝ)⁻¹ * (m + 1)) := by gcongr
      _ = _ := by ring
  have hbig : (fun m => A a m * A b m * A c m * (A d m)⁻¹ * (A e m)⁻¹ *
      ((m : ℂ) ^ (a + b + c - d - e) / ((m : ℂ) + 1))) =O[atTop] g := by
    have := (((((tendsto_ascPochhammer_div a).isBigO_one ℝ).mul
      ((tendsto_ascPochhammer_div b).isBigO_one ℝ)).mul
      ((tendsto_ascPochhammer_div c).isBigO_one ℝ)).mul ((hinvA hd).isBigO_one ℝ)).mul
      ((hinvA he).isBigO_one ℝ) |>.mul hh
    simpa using this
  have heq : ∀ᶠ m in atTop, threeFTwoCoeff a b c d e (m + 1) = A a m * A b m * A c m *
      (A d m)⁻¹ * (A e m)⁻¹ * ((m : ℂ) ^ (a + b + c - d - e) / ((m : ℂ) + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hPd := ascPochhammer_eval_ne_zero hd (m + 1)
    have hPe := ascPochhammer_eval_ne_zero he (m + 1)
    have hcpow : (m : ℂ) ^ (a + b + c - d - e) =
        (m : ℂ) ^ a * (m : ℂ) ^ b * (m : ℂ) ^ c / ((m : ℂ) ^ d * (m : ℂ) ^ e) := by
      rw [cpow_sub _ _ hm0, cpow_sub _ _ hm0, cpow_add _ _ hm0, cpow_add _ _ hm0]
      field_simp
    have hne : ∀ s : ℂ, (m : ℂ) ^ s ≠ 0 := fun s => cpow_ne_zero_iff.mpr (Or.inl hm0)
    have h4 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have h5 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
    simp only [threeFTwoCoeff, A]
    rw [hcpow, Nat.factorial_succ]
    have := hne a; have := hne b; have := hne c; have := hne d; have := hne e
    push_cast
    field_simp
  have hn : (fun m => ‖threeFTwoCoeff a b c d e (m + 1)‖) =O[atTop] g :=
    (hbig.congr' (heq.mono fun _ h => h.symm) EventuallyEq.rfl).norm_left
  exact (summable_nat_add_iff 1).mp (summable_of_isBigO_nat hg hn)

/-- A point with positive real part is not a pole of `Γ`. -/
private theorem ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : z ≠ -k := fun h => by
  rw [h] at hz; simp at hz; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- The beta integral with the first argument shifted by `n`:
`B(c + n, v) = B(c, v) (c)ₙ/(c + v)ₙ`. -/
private theorem betaIntegral_add_nat {c v : ℂ} (hc : 0 < c.re) (hv : 0 < v.re) (n : ℕ) :
    betaIntegral (c + n) v =
      betaIntegral c v * ((ascPochhammer ℂ n).eval c / (ascPochhammer ℂ n).eval (c + v)) := by
  have hcn : 0 < (c + n).re := by simp; positivity
  have hcv : 0 < (c + v).re := by simp; linarith
  have h1 := Gamma_mul_Gamma_eq_betaIntegral hcn hv
  have h2 := Gamma_mul_Gamma_eq_betaIntegral hc hv
  have g1 := Gamma_add_nat_div_Gamma_eq (n := n) c (ne_neg_nat_of_re_pos hc)
  have g2 := Gamma_add_nat_div_Gamma_eq (n := n) (c + v) (ne_neg_nat_of_re_pos hcv)
  have hG1 : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have hG2 : Gamma (c + v) ≠ 0 := Gamma_ne_zero_of_re_pos hcv
  have hG3 : Gamma (c + n + v) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
  have hP : (ascPochhammer ℂ n).eval (c + v) ≠ 0 :=
    ascPochhammer_eval_ne_zero (ne_neg_nat_of_re_pos hcv) n
  rw [← g1, ← g2, show c + v + n = c + n + v by ring]
  have hB1 : betaIntegral (c + n) v = Gamma (c + n) * Gamma v / Gamma (c + n + v) := by
    rw [h1]; field_simp
  have hB2 : betaIntegral c v = Gamma c * Gamma v / Gamma (c + v) := by
    rw [h2]; field_simp
  rw [hB1, hB2]
  field_simp

/-- The beta integral over the open interval. -/
private theorem integral_Ioo_eq_betaIntegral (u v : ℂ) :
    ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) = betaIntegral u v := by
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- **Exercise 8.3-10** (integral representation): for `d` not a pole of `Γ`,
`re c, re (e - c) > 0`, `re (d + e - a - b - c) > 0` and `|x| ≤ 1`,
`B(c, e - c) ₃F₂(a, b, c; d, e; x) = ∫₀¹ u^{c-1} (1 - u)^{e-c-1} ₂F₁(a, b; d; ux) du`, that is,
`₃F₂` is the Dirichlet average of `₂F₁(a, b; d; ux)` with weights `(c, e - c)`. -/
theorem betaIntegral_mul_threeFTwo {a b c d e x : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (hc : 0 < c.re)
    (hec : 0 < (e - c).re) (hs : 0 < (d + e - a - b - c).re) (hx : ‖x‖ ≤ 1) :
    betaIntegral c (e - c) * threeFTwo a b c d e x =
      ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (c - 1) * (1 - (u : ℂ)) ^ (e - c - 1) *
        ordinaryHypergeometric a b d ((u : ℂ) * x) := by
  set gc : ℕ → ℂ := fun n => (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a *
    (ascPochhammer ℂ n).eval b * ((ascPochhammer ℂ n).eval d)⁻¹
  set G : ℕ → ℝ → ℂ := fun n u => (u : ℂ) ^ (c + n - 1) * (1 - (u : ℂ)) ^ (e - c - 1)
  set F : ℕ → ℝ → ℂ := fun n u => gc n * x ^ n * G n u
  have hG : ∀ n, IntegrableOn (G n) (Ioo 0 1) := fun n =>
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent (u := c + n) (by simp; positivity) hec))
  have hF : ∀ n, Integrable (F n) (volume.restrict (Ioo (0 : ℝ) 1)) := fun n =>
    (hG n).const_mul _
  -- the integrand as a series
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, (u : ℂ) ^ (c - 1) * (1 - (u : ℂ)) ^ (e - c - 1) *
      ordinaryHypergeometric a b d ((u : ℂ) * x) = ∑' n, F n u := fun u hu => by
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    rw [ordinaryHypergeometric_eq_tsum, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [F, G, gc, smul_eq_mul]
    rw [show c + n - 1 = (c - 1) + n by ring, cpow_add _ _ hu0, cpow_natCast, mul_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    ← integral_tsum_of_summable_integral_norm hF ?_]
  · -- the termwise integrals
    have hterm : ∀ n, ∫ u in Ioo (0 : ℝ) 1, F n u =
        betaIntegral c (e - c) * (threeFTwoCoeff a b c d e n * x ^ n) := fun n => by
      simp only [F]
      rw [integral_const_mul]
      have hB : ∫ u in Ioo (0 : ℝ) 1, G n u = betaIntegral (c + n) (e - c) := by
        simp only [G]
        rw [← integral_Ioo_eq_betaIntegral, show c + n - 1 = c + n - 1 by rfl]
      rw [hB, betaIntegral_add_nat hc hec, show c + (e - c) = e by ring]
      have hPe : (ascPochhammer ℂ n).eval e ≠ 0 :=
        ascPochhammer_eval_ne_zero (ne_neg_nat_of_re_pos (by
          have := add_pos hc hec; simpa using this)) n
      have hPd := ascPochhammer_eval_ne_zero hd n
      have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      simp only [gc, threeFTwoCoeff]
      field_simp
    simp_rw [hterm]
    rw [tsum_mul_left]
    rfl
  · -- summability of the norms
    set c' : ℂ := (c.re : ℂ)
    set v' : ℂ := ((e - c).re : ℂ)
    have hc' : 0 < c'.re := by simpa [c'] using hc
    have hv' : 0 < v'.re := by simpa [v'] using hec
    set H : ℕ → ℝ → ℂ := fun n u => (u : ℂ) ^ (c' + n - 1) * (1 - (u : ℂ)) ^ (v' - 1)
    have hGH : ∀ n, ∀ u ∈ Ioo (0 : ℝ) 1, ‖G n u‖ = ‖H n u‖ := fun n u hu => by
      have h1 : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
      have hu1 : 0 < 1 - u := by linarith [hu.2]
      simp only [G, H, norm_mul, h1, norm_cpow_eq_rpow_re_of_pos hu.1,
        norm_cpow_eq_rpow_re_of_pos hu1]
      simp [c', v']
    have hHnorm : ∀ n, ∫ u in Ioo (0 : ℝ) 1, ‖H n u‖ = ‖betaIntegral (c' + n) v'‖ := fun n => by
      have hHr : ∀ u ∈ Ioo (0 : ℝ) 1, H n u = ((‖H n u‖ : ℝ) : ℂ) := fun u hu => by
        have h1 : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
        have hu1 : 0 < 1 - u := by linarith [hu.2]
        simp only [H, h1, show c' + n - 1 = ((c.re + n - 1 : ℝ) : ℂ) by simp [c'],
          show v' - 1 = (((e - c).re - 1 : ℝ) : ℂ) by simp [v'],
          ← ofReal_cpow hu.1.le, ← ofReal_cpow hu1.le, ← ofReal_mul, norm_real,
          Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
            (Real.rpow_nonneg hu1.le _))]
      rw [← integral_Ioo_eq_betaIntegral, setIntegral_congr_fun measurableSet_Ioo
        (fun u hu => (hHr u hu : H n u = _)), integral_complex_ofReal, norm_real,
        Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo fun _ _ => norm_nonneg _)]
    have hval : ∀ n, ∫ u in Ioo (0 : ℝ) 1, ‖F n u‖ =
        ‖gc n‖ * ‖x‖ ^ n * (‖betaIntegral c' v'‖ *
          ‖(ascPochhammer ℂ n).eval c' / (ascPochhammer ℂ n).eval (c' + v')‖) := fun n => by
      have hFn : ∀ u, ‖F n u‖ = ‖gc n‖ * ‖x‖ ^ n * ‖G n u‖ := fun u => by
        rw [show F n u = gc n * x ^ n * G n u from rfl, norm_mul, norm_mul, norm_pow]
      rw [show (∫ u in Ioo (0 : ℝ) 1, ‖F n u‖) =
          ∫ u in Ioo (0 : ℝ) 1, ‖gc n‖ * ‖x‖ ^ n * ‖G n u‖ by congr 1; funext u; exact hFn u]
      rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioo (hGH n), hHnorm,
        betaIntegral_add_nat hc' hv', norm_mul (betaIntegral c' v')]
    have he' : ∀ k : ℕ, c' + v' ≠ -k := ne_neg_nat_of_re_pos (by simp; linarith)
    have hs' : 0 < (d + (c' + v') - a - b - c').re := by
      have : (d + (c' + v') - a - b - c').re = (d + e - a - b - c).re := by simp [c', v']
      rw [this]; exact hs
    have hsum := (summable_norm_threeFTwoCoeff hd he' hs').mul_left ‖betaIntegral c' v'‖
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) hsum
    rw [hval n]
    have hcoef : threeFTwoCoeff a b c' d (c' + v') n =
        gc n * ((ascPochhammer ℂ n).eval c' / (ascPochhammer ℂ n).eval (c' + v')) := by
      simp only [threeFTwoCoeff, gc]; ring
    rw [hcoef, norm_mul (gc n)]
    have hxn : ‖x‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
    have h1 := norm_nonneg (gc n)
    have h2 := norm_nonneg (betaIntegral c' v')
    have h3 := norm_nonneg ((ascPochhammer ℂ n).eval c' / (ascPochhammer ℂ n).eval (c' + v'))
    have h4 := mul_nonneg (mul_nonneg h1 h2) h3
    nlinarith [mul_le_mul_of_nonneg_left hxn h4]

/-- **Exercise 8.3-10** (convergence): for `d, e` not poles of `Γ` and
`re (d + e - a - b - c) > 0`, the `₃F₂` series converges absolutely on the closed unit disk. -/
theorem summable_threeFTwo {a b c d e x : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (he : ∀ k : ℕ, e ≠ -k)
    (hs : 0 < (d + e - a - b - c).re) (hx : ‖x‖ ≤ 1) :
    Summable (fun n => threeFTwoCoeff a b c d e n * x ^ n) :=
  Summable.of_norm_bounded (summable_norm_threeFTwoCoeff hd he hs) fun n => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)

/-- **Exercise 8.3-10** (continuity): for `d, e` not poles of `Γ` and
`re (d + e - a - b - c) > 0`, the sum of the `₃F₂` series is continuous on the closed unit
disk. -/
theorem continuousOn_threeFTwo {a b c d e : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (he : ∀ k : ℕ, e ≠ -k)
    (hs : 0 < (d + e - a - b - c).re) :
    ContinuousOn (threeFTwo a b c d e) (Metric.closedBall 0 1) :=
  continuousOn_tsum (fun n => (continuous_const.mul (continuous_pow n)).continuousOn)
    (summable_norm_threeFTwoCoeff hd he hs) fun n x hx => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (by simpa using hx))

/-- The beta integral in terms of `Γ`. -/
private theorem betaIntegral_eq_Gamma {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Gamma u * Gamma v / Gamma (u + v) := by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv,
    mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by simp; linarith))]

/-- **Exercise 8.3-11**: for `d` not a pole of `Γ` and `re c, re (e - c), re (d - a - b) > 0`,
with `s = d + e - a - b - c`,
`B(c, e - c) ₃F₂(a, b, c; d, e; 1) = B(c, s) ₃F₂(d - a, d - b, c; d, s + c; 1)`. -/
theorem betaIntegral_mul_threeFTwo_one {a b c d e : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (hc : 0 < c.re)
    (hec : 0 < (e - c).re) (hdab : 0 < (d - a - b).re) :
    betaIntegral c (e - c) * threeFTwo a b c d e 1 =
      betaIntegral c (d + e - a - b - c) *
        threeFTwo (d - a) (d - b) c d ((d + e - a - b - c) + c) 1 := by
  set s := d + e - a - b - c
  have hs : 0 < s.re := by
    have : s.re = (e - c).re + (d - a - b).re := by simp [s]; ring
    rw [this]; linarith
  have h1 := betaIntegral_mul_threeFTwo (a := a) (b := b) (x := 1) hd hc hec hs (by simp)
  have h2 := betaIntegral_mul_threeFTwo (a := d - a) (b := d - b) (c := c) (e := s + c) (x := 1)
    hd hc (by simpa using hs) (by
      have : (d + (s + c) - (d - a) - (d - b) - c).re = (e - c).re := by simp [s]; ring
      rw [this]; exact hec) (by simp)
  rw [show s + c - c = s by ring] at h2
  rw [h1, h2]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu1 : |u| < 1 := by rw [abs_of_pos hu.1]; exact hu.2
  have h1u : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  have h0 : ((1 - u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [hu.2])
  rw [mul_one, ordinaryHypergeometric_euler a b hd hu1, h1u]
  rw [show s - 1 = (e - c - 1) + (d - a - b) by simp only [s]; ring, cpow_add _ _ h0]
  ring

/-- **Exercise 8.3-12**: for `re a, re c, re (d - a), re (e - c), re (d - a - b),
re (e - a - c) > 0`, with `s = d + e - a - b - c`,
`Γ(a)/(Γ(d) Γ(e)) ₃F₂(a, b, c; d, e; 1) =
Γ(s)/(Γ(s + b) Γ(s + c)) ₃F₂(s, d - a, e - a; s + b, s + c; 1)`. -/
theorem Gamma_div_mul_threeFTwo_one {a b c d e : ℂ} (ha : 0 < a.re) (hc : 0 < c.re)
    (hda : 0 < (d - a).re) (hec : 0 < (e - c).re) (hdab : 0 < (d - a - b).re)
    (heac : 0 < (e - a - c).re) :
    Gamma a / (Gamma d * Gamma e) * threeFTwo a b c d e 1 =
      Gamma (d + e - a - b - c) / (Gamma (d + e - a - b - c + b) *
        Gamma (d + e - a - b - c + c)) *
        threeFTwo (d + e - a - b - c) (d - a) (e - a) (d + e - a - b - c + b)
          (d + e - a - b - c + c) 1 := by
  set s := d + e - a - b - c
  have hs : 0 < s.re := by
    have : s.re = (e - c).re + (d - a - b).re := by simp [s]; ring
    rw [this]; linarith
  have hd : 0 < d.re := by have := add_pos ha hda; simpa using this
  have he : 0 < e.re := by have := add_pos hc hec; simpa using this
  have hsc : 0 < (s + c).re := by simp; linarith
  have hsb : 0 < (s + b).re := by
    have : (s + b).re = (e - c).re + (d - a).re := by simp [s]; ring
    rw [this]; linarith
  -- first application of 8.3-11
  have h1 := betaIntegral_mul_threeFTwo_one (a := a) (b := b) (c := c) (d := d) (e := e)
    (ne_neg_nat_of_re_pos hd) hc hec hdab
  -- permute the parameters
  have hperm1 : threeFTwo (d - a) (d - b) c d (s + c) 1 =
      threeFTwo c (d - b) (d - a) (s + c) d 1 := by
    unfold threeFTwo
    refine tsum_congr fun n => ?_
    rw [threeFTwoCoeff_comm_denom, ← threeFTwoCoeff_comm_left, threeFTwoCoeff_comm_right,
      threeFTwoCoeff_comm_left]
  -- second application of 8.3-11
  have h2 := betaIntegral_mul_threeFTwo_one (a := c) (b := d - b) (c := d - a) (d := s + c)
    (e := d) (ne_neg_nat_of_re_pos hsc) hda (by simpa using ha) (by
      have : (s + c - c - (d - b)).re = (e - a - c).re := by simp [s]; ring
      rw [this]; exact heac)
  have hs2 : s + c + d - c - (d - b) - (d - a) = e - c := by simp only [s]; ring
  rw [hs2, show d - (d - a) = a by ring, show s + c - c = s by ring,
    show s + c - (d - b) = e - a by simp only [s]; ring,
    show e - c + (d - a) = s + b by simp only [s]; ring] at h2
  have hperm2 : threeFTwo s (e - a) (d - a) (s + c) (s + b) 1 =
      threeFTwo s (d - a) (e - a) (s + b) (s + c) 1 := by
    unfold threeFTwo
    refine tsum_congr fun n => ?_
    rw [threeFTwoCoeff_comm_denom, threeFTwoCoeff_comm_right]
  rw [hperm1] at h1
  rw [hperm2] at h2
  set F0 := threeFTwo a b c d e 1
  set F1 := threeFTwo c (d - b) (d - a) (s + c) d 1
  set F2 := threeFTwo s (d - a) (e - a) (s + b) (s + c) 1
  rw [betaIntegral_eq_Gamma hc hec, betaIntegral_eq_Gamma hc hs,
    show c + (e - c) = e by ring, show c + s = s + c by ring] at h1
  rw [betaIntegral_eq_Gamma hda ha, betaIntegral_eq_Gamma hda hec,
    show d - a + a = d by ring, show d - a + (e - c) = s + b by simp only [s]; ring] at h2
  have g1 := Gamma_ne_zero_of_re_pos hc
  have g2 := Gamma_ne_zero_of_re_pos hec
  have g3 := Gamma_ne_zero_of_re_pos he
  have g4 := Gamma_ne_zero_of_re_pos hs
  have g5 := Gamma_ne_zero_of_re_pos hsc
  have g6 := Gamma_ne_zero_of_re_pos hda
  have g7 := Gamma_ne_zero_of_re_pos ha
  have g8 := Gamma_ne_zero_of_re_pos hd
  have g9 := Gamma_ne_zero_of_re_pos hsb
  have hF0 : F0 = Gamma s * Gamma e / (Gamma (s + c) * Gamma (e - c)) * F1 := by
    field_simp at h1 ⊢
    linear_combination h1
  have hF1 : F1 = Gamma (e - c) * Gamma d / (Gamma (s + b) * Gamma a) * F2 := by
    field_simp at h2 ⊢
    linear_combination h2
  rw [hF0, hF1]
  field_simp

end Carlson.TwoVariable
