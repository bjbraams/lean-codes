/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SmallVariableContinuation
public import Carlson.RPolynomial.TaylorContinuation
public import Carlson.TwoVariable.RPolynomial
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.AbelLimit

/-!
# Gauss's hypergeometric function and Gauss's theorem

Carlson's (8.3-7) (equivalently (5.9-11)) identifies Gauss's function with a two-variable
R-function: `₂F₁(α, β; γ; x) = R_{-α}(γ - β, β; 1, 1 - x)`. With Mathlib's regularized Gauss
function this holds for all complex `α, β, γ` and `‖x‖ < 1`; it follows from the R-polynomial
Taylor expansion of the R-function about equal nodes.

Letting the second node tend to `0` (Theorem 8.3-2) gives Corollary 8.3-3,
`₂F₁(α, β; γ; x)/Γ(γ) → Γ(γ - α - β)/(Γ(γ - α) Γ(γ - β))` as `x → 1` when `re (γ - α - β) > 0`.
The coefficients of the series are `O(n^{-1-re(γ-α-β)})`, by Euler's limit formula for `Γ`, so the
series converges at `x = 1`, and Abel's theorem gives Gauss's theorem (Corollary 8.3-4).

## Main definitions

* `Carlson.gaussCoeff`: the coefficients `(α)ₙ (β)ₙ/(n! Γ(γ + n))`.

## Main results

* `Carlson.regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun`: (8.3-7).
* `Carlson.tendsto_regularizedGaussHGFun_one`: Corollary 8.3-3.
* `Carlson.tendsto_ascPochhammer_div`: `(s)_{m+1}/(m^s m!) → 1/Γ(s)` for every complex `s`.
* `Carlson.summable_gaussCoeff`, `Carlson.hasSum_gaussCoeff`, `Carlson.ordinaryHypergeometric_one`:
  Gauss's theorem, Corollary 8.3-4.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Complex Filter Set Dirichlet
open scoped Topology
@[expose] public noncomputable section

namespace Carlson

/-- Iterated derivatives of a principal power on the slit plane. -/
private theorem iteratedDeriv_cpow_const' (A : ℂ) (i : ℕ) {x : ℂ} (hx : x ∈ slitPlane) :
    iteratedDeriv i (fun w : ℂ => w ^ A) x = (descPochhammer ℂ i).eval A * x ^ (A - i) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    have he : iteratedDeriv i (fun w : ℂ => w ^ A) =ᶠ[𝓝 x]
        fun w => (descPochhammer ℂ i).eval A * w ^ (A - i) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hx] with w hw using ih hw
    have hd := ((hasDerivAt_id x).cpow_const (c := A - i) hx).const_mul
      ((descPochhammer ℂ i).eval A)
    simp only [id] at hd
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

open TwoVariable in
/-- **Carlson's (8.3-7)** (equivalently (5.9-11)) with Mathlib's regularized Gauss function:
`₂F₁(α, β; γ; x)/Γ(γ) = R_{-α}(γ - β, β; 1, 1 - x)/Γ(γ)` for `‖x‖ < 1` and all complex
`α, β, γ`. -/
theorem regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun (α β γ : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    regCarlsonR (-α) (pair (γ - β) β) (pair 1 (1 - x)) = regularizedGaussHGFun α β γ x := by
  have hre : 0 < (1 - x).re := by
    simp only [sub_re, one_re]; linarith [abs_le.mp ((abs_re_le_norm x).trans hx.le) |>.2,
      (abs_re_le_norm x).trans_lt hx, le_abs_self x.re]
  have hz : pair (1 : ℂ) (1 - x) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · simp [carlsonRightHalfPlane, pair]
    · simpa [carlsonRightHalfPlane, pair] using hre
  have hG : IsRegCarlsonContinuation (fun w : ℂ => w ^ (-α)) (pair 1 (1 - x))
      (regCarlsonR (-α) · (pair 1 (1 - x))) := isRegCarlsonRContinuation_regCarlsonR (-α) hz
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-α)) (Metric.ball 1 1) := by
    intro w hw
    have hw' : 0 < w.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have := (abs_re_le_norm (w - 1)).trans_lt hw
      simp only [sub_re, one_re] at this; linarith [neg_abs_le (w.re - 1)]
    exact analyticAt_id.cpow analyticAt_const (Or.inl hw')
  have hsub : (fun i => pair (1 : ℂ) (1 - x) i - 1) = pair 0 (-x) := by
    funext i; fin_cases i <;> simp [pair]
  have hz' : ‖fun i => pair (1 : ℂ) (1 - x) i - 1‖ < 1 := by
    rw [hsub, pi_norm_lt_iff one_pos]
    intro i; fin_cases i
    · simp [pair]
    · simpa [pair] using hx
  have H := hG.hasSum_taylor hf hz' (pair (γ - β) β)
  have hmem : x ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries α β γ).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one α β γ)
    rw [← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hx
  have H2 := (regularizedGaussHGFunSeries α β γ).hasSum hmem
  refine H.unique (H2.congr_fun fun n => ?_)
  have hid : iteratedDeriv n (fun w : ℂ => w ^ (-α)) 1 = (descPochhammer ℂ n).eval (-α) := by
    have h := iteratedDeriv_cpow_const' (-α) n (x := 1) (by simp)
    simpa using h
  have hdesc : (descPochhammer ℂ n).eval (-α) = (-1) ^ n * (ascPochhammer ℂ n).eval α := by
    have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) (-α) n
    rw [neg_neg] at h
    rw [h, ← mul_assoc, ← mul_pow]; norm_num
  have hpoly : regCarlsonRPolynomial n (pair (γ - β) β) (pair 0 (-x)) =
      (ascPochhammer ℂ n).eval β * (-x) ^ n * (Gamma (γ + n))⁻¹ := by
    change regRPolynomial n (γ - β) β 0 (-x) = _
    rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma, ← carlsonRPolynomialNumerator₂_swap,
      carlsonRPolynomialNumerator₂_zero_right, show γ - β + β + n = γ + n by ring]
  rw [hsub, hid, hdesc, hpoly, regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  simp only [regularizedHGFunCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [neg_pow x n, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  linear_combination (ascPochhammer ℂ n).eval α * (ascPochhammer ℂ n).eval β * x ^ n *
    (n.factorial : ℂ)⁻¹ * (Gamma (γ + n))⁻¹ * hs

open TwoVariable in
/-- **Carlson's Corollary 8.3-3** with Mathlib's regularized Gauss function: if
`re (γ - α - β) > 0` then `₂F₁(α, β; γ; x)/Γ(γ) → Γ(γ - α - β)/(Γ(γ - α) Γ(γ - β))` as `x → 1`
in the unit disk. -/
theorem tendsto_regularizedGaussHGFun_one (α β γ : ℂ) (h : 0 < (γ - α - β).re) :
    Tendsto (regularizedGaussHGFun α β γ) (𝓝[Metric.ball 0 1] 1)
      (𝓝 (Gamma (γ - α - β) * ((Gamma (γ - α))⁻¹ * (Gamma (γ - β))⁻¹))) := by
  have hw : ∀ x : Metric.ball (0 : ℂ) 1, 0 < (1 - (x : ℂ)).re := fun x => by
    have hx := x.2
    rw [Metric.mem_ball, dist_zero_right] at hx
    simp only [sub_re, one_re]
    linarith [(abs_re_le_norm (x : ℂ)).trans_lt hx, le_abs_self (x : ℂ).re]
  have hlim : Tendsto (fun x : Metric.ball (0 : ℂ) 1 => 1 - (x : ℂ))
      (comap Subtype.val (𝓝 1)) (𝓝 0) := by
    have : Tendsto (fun v : ℂ => 1 - v) (𝓝 1) (𝓝 0) := by
      have h0 : Tendsto (fun v : ℂ => 1 - v) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      simpa using h0
    exact this.comp tendsto_comap
  have H := tendsto_regCarlsonR_update_zero_const (1 : Fin 2) (a := α) (a' := γ - α)
    (b := pair (γ - β) β) (w₀ := 1) (by simp [pair]) (by simpa [pair] using h) one_pos
    ⟨0, by decide⟩ hw hlim
  rw [one_cpow, one_mul, show α + (γ - α) - pair (γ - β) β 1 = γ - β by simp [pair],
    show γ - α - pair (γ - β) β 1 = γ - α - β by simp [pair]] at H
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  refine H.congr fun x => ?_
  have hx := x.2
  rw [Metric.mem_ball, dist_zero_right] at hx
  simp only [Function.comp_apply]
  convert regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun α β γ hx using 2
  funext i; fin_cases i <;> simp [pair]

/-- The ascending Pochhammer symbol as a product. -/
theorem ascPochhammer_eval_eq_prod_range' (s : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval s = ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, Finset.prod_range_succ]
    simp

/-- `(s)_{m+1}/(m^s m!)` is the reciprocal of Euler's sequence for `Γ(s)`. -/
theorem ascPochhammer_div_eq_inv_GammaSeq (s : ℂ) {m : ℕ} :
    (ascPochhammer ℂ (m + 1)).eval s / ((m : ℂ) ^ s * m.factorial) = (GammaSeq s m)⁻¹ := by
  rw [GammaSeq, inv_div, ascPochhammer_eval_eq_prod_range']

/-- `(s)_{m+1}/(m^s m!) → 1/Γ(s)` for every complex `s`, including the poles of `Γ`. -/
theorem tendsto_ascPochhammer_div (s : ℂ) :
    Tendsto (fun m : ℕ => (ascPochhammer ℂ (m + 1)).eval s / ((m : ℂ) ^ s * m.factorial))
      atTop (𝓝 (Gamma s)⁻¹) := by
  simp_rw [ascPochhammer_div_eq_inv_GammaSeq]
  by_cases hs : ∀ k : ℕ, s ≠ -k
  · exact (GammaSeq_tendsto_Gamma s).inv₀ (Gamma_ne_zero hs)
  · simp only [not_forall, not_not] at hs
    obtain ⟨k, rfl⟩ := hs
    rw [Gamma_neg_nat_eq_zero, inv_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    have hP : ∏ j ∈ Finset.range (m + 1), (-(k : ℂ) + j) = 0 :=
      Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr (by omega)) (by ring)
    rw [GammaSeq, hP, div_zero, inv_zero]


/-- The coefficients `(α)ₙ (β)ₙ/(n! Γ(γ + n))` of the regularized Gauss series. -/
def gaussCoeff (α β γ : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval α * (ascPochhammer ℂ n).eval β / (n.factorial * Gamma (γ + n))

open Asymptotics in
/-- For `re (γ - α - β) > 0` and `γ` not a pole of `Γ`, the Gauss coefficients are absolutely
summable: they are `O(n^{-1-re(γ-α-β)})`. -/
theorem summable_gaussCoeff {α β γ : ℂ} (hγ : ∀ k : ℕ, γ ≠ -k) (h : 0 < (γ - α - β).re) :
    Summable (gaussCoeff α β γ) := by
  set ε := (γ - α - β).re
  set A : ℂ → ℕ → ℂ := fun s m => (ascPochhammer ℂ (m + 1)).eval s / ((m : ℂ) ^ s * m.factorial)
  have hG : Gamma γ ≠ 0 := Gamma_ne_zero hγ
  have hAγ : Tendsto (fun m => (A γ m)⁻¹) atTop (𝓝 (Gamma γ)) := by
    have := (tendsto_ascPochhammer_div γ).inv₀ (inv_ne_zero hG)
    rw [inv_inv] at this
    exact this
  set g : ℕ → ℝ := fun m => ((m : ℝ) ^ (1 + ε))⁻¹
  have hg : Summable g := Real.summable_nat_rpow_inv.mpr (by linarith)
  have hh : (fun m : ℕ => (m : ℂ) ^ (α + β - γ) / ((m + 1) * Gamma γ)) =O[atTop] g := by
    refine IsBigO.of_bound ‖(Gamma γ)⁻¹‖ ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [norm_div, norm_mul, norm_natCast_cpow_of_pos (by omega), Real.norm_of_nonneg
      (by positivity : (0 : ℝ) ≤ g m)]
    have hre : (α + β - γ).re = -ε := by simp only [ε, sub_re, add_re]; ring
    rw [hre]
    have h1 : ‖(m : ℂ) + 1‖ = m + 1 := by
      rw [show (m : ℂ) + 1 = ((m + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h1, norm_inv]
    have hpow : (m : ℝ) ^ (-ε) = ((m : ℝ) ^ ε)⁻¹ := Real.rpow_neg hm0.le ε
    have hg' : g m = ((m : ℝ) ^ ε)⁻¹ * (m : ℝ)⁻¹ := by
      simp only [g]; rw [Real.rpow_add hm0, Real.rpow_one, mul_inv]; ring
    rw [hpow, hg']
    have hGn : 0 < ‖Gamma γ‖ := norm_pos_iff.mpr hG
    have hmε : 0 < (m : ℝ) ^ ε := Real.rpow_pos_of_pos hm0 ε
    rw [div_le_iff₀ (by positivity)]
    have : (m : ℝ)⁻¹ * (m + 1) ≥ 1 := by
      rw [inv_mul_eq_div, ge_iff_le, one_le_div hm0]; linarith
    calc ((m : ℝ) ^ ε)⁻¹ = ‖Gamma γ‖⁻¹ * (((m : ℝ) ^ ε)⁻¹ * 1) * ‖Gamma γ‖ := by field_simp
      _ ≤ ‖Gamma γ‖⁻¹ * (((m : ℝ) ^ ε)⁻¹ * ((m : ℝ)⁻¹ * (m + 1))) * ‖Gamma γ‖ := by gcongr
      _ = _ := by ring
  have hbig : (fun m => A α m * A β m * (A γ m)⁻¹ *
      ((m : ℂ) ^ (α + β - γ) / ((m + 1) * Gamma γ))) =O[atTop] g := by
    have := (((tendsto_ascPochhammer_div α).isBigO_one ℝ).mul
      ((tendsto_ascPochhammer_div β).isBigO_one ℝ)).mul (hAγ.isBigO_one ℝ) |>.mul hh
    simpa using this
  have heq : ∀ᶠ m in atTop, gaussCoeff α β γ (m + 1) = A α m * A β m * (A γ m)⁻¹ *
      ((m : ℂ) ^ (α + β - γ) / ((m + 1) * Gamma γ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hΓ := Gamma_add_nat_div_Gamma_eq (n := m + 1) γ hγ
    have hP : (ascPochhammer ℂ (m + 1)).eval γ ≠ 0 := by
      rw [← hΓ]; exact div_ne_zero (Gamma_ne_zero fun k hk => hγ (k + (m + 1)) (by
        push_cast at hk ⊢; linear_combination hk)) hG
    have hΓ' : Gamma (γ + ((m + 1 : ℕ) : ℂ)) = (ascPochhammer ℂ (m + 1)).eval γ * Gamma γ := by
      rw [← hΓ]; field_simp
    have hcpow : (m : ℂ) ^ (α + β - γ) = (m : ℂ) ^ α * (m : ℂ) ^ β / (m : ℂ) ^ γ := by
      rw [cpow_sub _ _ hm0, cpow_add _ _ hm0]
    simp only [gaussCoeff, A]
    rw [hΓ', hcpow, Nat.factorial_succ]
    have h1 : (m : ℂ) ^ α ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
    have h2 : (m : ℂ) ^ β ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
    have h3 : (m : ℂ) ^ γ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
    have h4 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have h5 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
    push_cast
    field_simp
  have := summable_of_isBigO_nat hg ((hbig.congr' (heq.mono fun _ h => h.symm) EventuallyEq.rfl))
  exact (summable_nat_add_iff 1).mp this

/-- Inside the unit disk the regularized Gauss function is the sum of its series. -/
theorem hasSum_gaussCoeff_mul_pow (α β γ : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n => gaussCoeff α β γ n * x ^ n) (regularizedGaussHGFun α β γ x) := by
  have hmem : x ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries α β γ).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one α β γ)
    rw [← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hx
  refine ((regularizedGaussHGFunSeries α β γ).hasSum hmem).congr_fun fun n => ?_
  rw [regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  simp only [regularizedHGFunCoeff, gaussCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]

/-- **Gauss's theorem** (Carlson's Corollary 8.3-4), regularized: if `re (γ - α - β) > 0` and `γ`
is not a pole of `Γ`, then `∑ (α)ₙ (β)ₙ/(n! Γ(γ + n)) = Γ(γ - α - β)/(Γ(γ - α) Γ(γ - β))`. -/
theorem hasSum_gaussCoeff {α β γ : ℂ} (hγ : ∀ k : ℕ, γ ≠ -k) (h : 0 < (γ - α - β).re) :
    HasSum (gaussCoeff α β γ) (Gamma (γ - α - β) * ((Gamma (γ - α))⁻¹ * (Gamma (γ - β))⁻¹)) := by
  have hS := summable_gaussCoeff hγ h
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hS.hasSum.tendsto_sum_nat
  rw [tendsto_map'_iff] at habel
  have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] 1) (𝓝[Metric.ball 0 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp)
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_of_nonneg hx.1.le]
      exact hx.2
  have hcor := (tendsto_regularizedGaussHGFun_one α β γ h).comp hmap
  have heq : (fun x : ℝ => ∑' n, gaussCoeff α β γ n * (x : ℂ) ^ n) =ᶠ[𝓝[<] 1]
      (regularizedGaussHGFun α β γ ∘ fun x : ℝ => (x : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx' : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
    exact (hasSum_gaussCoeff_mul_pow α β γ hx').tsum_eq
  have := tendsto_nhds_unique (habel.congr' heq) hcor
  rw [← this]
  exact hS.hasSum

/-- **Gauss's theorem** (Carlson's Corollary 8.3-4) in Carlson's form, with Mathlib's `₂F₁`:
`₂F₁(α, β; γ; 1) = Γ(γ) Γ(γ - α - β)/(Γ(γ - α) Γ(γ - β))` when `re (γ - α - β) > 0` and `γ` is not
a pole of `Γ`. -/
theorem ordinaryHypergeometric_one {α β γ : ℂ} (hγ : ∀ k : ℕ, γ ≠ -k)
    (h : 0 < (γ - α - β).re) :
    ordinaryHypergeometric α β γ (1 : ℂ) =
      Gamma γ * Gamma (γ - α - β) / (Gamma (γ - α) * Gamma (γ - β)) := by
  have H := (hasSum_gaussCoeff hγ h).mul_left (Gamma γ)
  have hterm : ∀ n, Gamma γ * gaussCoeff α β γ n =
      (ordinaryHypergeometricSeries ℂ α β γ n) (fun _ => (1 : ℂ)) := by
    intro n
    have h2 := Gamma_inv_mul_ordinaryHypergeometricSeries_eq (a := α) (b := β) hγ (n := n)
    rw [coeff_regularizedGaussHGFunSeries] at h2
    rw [ordinaryHypergeometricSeries, FormalMultilinearSeries.ofScalars_apply_eq, one_pow,
      smul_eq_mul, mul_one]
    rw [ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars] at h2
    have hG : Gamma γ ≠ 0 := Gamma_ne_zero hγ
    rw [gaussCoeff, ← h2, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  rw [ordinaryHypergeometric, FormalMultilinearSeries.sum]
  simp_rw [← hterm]
  rw [H.tsum_eq, div_eq_mul_inv, mul_inv]
  ring

end Carlson
