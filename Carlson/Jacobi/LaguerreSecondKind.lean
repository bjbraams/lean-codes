/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.TwoF0Connection
public import Carlson.R.SlitIntegral

/-!
# Laguerre functions of the second kind and Theorem 7.9-5

**Theorem 7.9-5.** For real `x → ∞`, `|S(β, β'; x, -x)/Γ(β + β')| → ∞` unless `-β ∈ ℕ`. This
is read off from the connection formula (5.12-18) at `y = -x`: the term
`e^x (2x)^{-β'} ₂F₀(1 - β, β'; 1/(2x))/Γ(β)` grows exponentially because `₂F₀ → 1` by the
asymptotic expansion (5.12-17) on the sector, while the other term decays like `e^{-x}`. The
converse also holds: if `β = -m` with `m ∈ ℕ`, the growing term vanishes and `S/Γ(β + β') → 0`.

**The Laguerre function of the second kind** (Carlson (7.9-4) and Definition 7.9-2):
`q̃ₙ(x) = x^{-n-1} ₂F₀(1 + n, 1 + β + n; 1/x)` for `x ∉ [0, ∞)` is the limit
`lim_{s → ∞} R_{-n-1}(1 + s + n, 1 + β + n; x, x - s)` when `re (1 + β + n) > 0`. After the
substitution `u = s/(t + s)` in the Euler integral (7.4-12) the integrand converges to
`(x - t)^{-n-1} e^{-t} t^{β+n}`, dominated uniformly for large `s` because `(1 + t/s)^s` increases
with `s` (concavity of the logarithm). The same computation with the kernel `1` gives the Beta
normalization, so no Gamma asymptotics are needed.

## Main definitions

* `Carlson.monicLaguerreSecondKind`: Carlson's `q̃ₙ` of Definition 7.9-2.

## Main results

* `Carlson.tendsto_norm_regCarlsonS_pair_neg_atTop`: Theorem 7.9-5.
* `Carlson.tendsto_regCarlsonS_pair_neg_of_neg_nat`: its converse.
* `Carlson.integral_laguerreSecondKind`: `Γ(1+β+n) q̃ₙ(x) = ∫₀^∞ (x - t)^{-n-1} e^{-t} t^{β+n} dt`.
* `Carlson.tendsto_laguerreSecondKind`, `Carlson.tendsto_carlsonR_laguerreSecondKind`: the limit
  (7.9-4).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.9.
-/

open Complex MeasureTheory Filter Set Dirichlet
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson

/-- `₂F₀(a, b; x) → 1` as `x → 0` along a ray `ph(-x) = c` with `|c| ≤ π`. -/
theorem tendsto_carlson2F0Sector_log (a b : ℂ) {c : ℝ} (hc : |c| ≤ π) :
    Tendsto (fun x : ℝ => carlson2F0Sector a b (-(Real.log (2 * x) : ℂ) + c * I)) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_norm_carlson2F0Sector_sub_sum_le a b 1 (δ := π / 2) (by positivity)
  have hnorm : ∀ x : ℝ, 0 < x → ‖exp (-(Real.log (2 * x) : ℂ) + c * I)‖ = (2 * x)⁻¹ := by
    intro x hx
    rw [norm_exp]
    simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ => C * (2 * x)⁻¹)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have h := hC (-(Real.log (2 * x) : ℂ) + c * I) (by
      simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add]
      linarith [Real.pi_pos]) (by rw [hnorm x hx0]; exact inv_le_one_of_one_le₀ (by linarith))
    simpa [twoF0Term, hnorm x hx0] using h
  · simpa using (tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by
      norm_num))).const_mul C

/-- Formula (5.12-18) at `y = -x` for real `x > 0`: `S(β, β'; x, -x)/Γ(β + β')` splits into a
growing and a decaying term. -/
theorem regCarlsonS_pair_neg_eq (β β' : ℂ) {x : ℝ} (hx : 0 < x) :
    regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair x (-x)) =
      exp x * exp (-(β' * Real.log (2 * x))) * (Gamma β)⁻¹ *
          carlson2F0Sector (1 - β) β' (-(Real.log (2 * x) : ℂ) + π * I) +
        exp (-x) * exp (-(β * (Real.log (2 * x) - π * I))) * (Gamma β')⁻¹ *
          carlson2F0Sector (1 - β') β (-(Real.log (2 * x) : ℂ) + (0 : ℝ) * I) := by
  have h := regCarlsonS_pair_eq_twoF0 (ε := 1) (Or.inl rfl) β β' (x := (x : ℂ)) (y := -(x : ℂ))
    (ξ := (Real.log (2 * x) : ℂ)) (by
      rw [← ofReal_exp, Real.exp_log (by positivity)]; push_cast; ring)
    (by simp; positivity) (by simp [abs_of_pos Real.pi_pos]; linarith [Real.pi_pos])
  rw [h]
  simp only [one_mul, ofReal_zero, zero_mul, add_zero]

/-- The norm of the coefficient of the decaying term in (5.12-18) at `y = -x`. -/
theorem norm_exp_neg_mul_exp_mul_inv_Gamma (β β' : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖exp (-(x : ℂ)) * exp (-(β * (Real.log (2 * x) - π * I))) * (Gamma β')⁻¹‖ =
      ((2 : ℝ) ^ (-β.re) * Real.exp (-(π * β.im)) * ‖(Gamma β')⁻¹‖) *
        (x ^ (-β.re) * Real.exp (-1 * x)) := by
  have hre : (-(β * ((Real.log (2 * x) : ℂ) - π * I))).re =
      Real.log ((2 * x) ^ (-β.re)) + -(π * β.im) := by
    rw [Real.log_rpow (by positivity)]
    simp only [neg_re, mul_re, sub_re, ofReal_re, mul_im, I_re, I_im, ofReal_im, sub_im]
    ring
  rw [norm_mul, norm_mul, norm_exp, norm_exp, neg_re, ofReal_re, hre, Real.exp_add,
    Real.exp_log (by positivity), Real.mul_rpow (by norm_num) hx.le]
  ring_nf

/-- **Theorem 7.9-5**: for real `x → ∞`, `|S(β, β'; x, -x)/Γ(β + β')| → ∞` unless `-β ∈ ℕ`. -/
theorem tendsto_norm_regCarlsonS_pair_neg_atTop {β : ℂ} (hβ : ∀ m : ℕ, β ≠ -m) (β' : ℂ) :
    Tendsto (fun x : ℝ => ‖regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair x (-x))‖)
      atTop atTop := by
  have hF1 := tendsto_carlson2F0Sector_log (1 - β) β' (c := π) (by rw [abs_of_pos Real.pi_pos])
  have hF2 := tendsto_carlson2F0Sector_log (1 - β') β (c := 0) (by simp; positivity)
  set K1 := ‖(Gamma β)⁻¹‖ * (2 : ℝ) ^ (-β'.re)
  have hK1 : 0 < K1 := mul_pos (norm_pos_iff.mpr (inv_ne_zero (Gamma_ne_zero hβ)))
    (Real.rpow_pos_of_pos (by norm_num) _)
  set K2 := (2 : ℝ) ^ (-β.re) * Real.exp (-(π * β.im)) * ‖(Gamma β')⁻¹‖
  -- norms of the two terms
  have hn1 : ∀ x : ℝ, 0 < x → ‖exp (x : ℂ) * exp (-(β' * Real.log (2 * x))) * (Gamma β)⁻¹‖ =
      K1 * (Real.exp x / x ^ β'.re) := by
    intro x hx
    rw [norm_mul, norm_mul, norm_exp, norm_exp, ofReal_re, neg_re, re_mul_ofReal,
      show -(β'.re * Real.log (2 * x)) = Real.log ((2 * x) ^ (-β'.re)) by
        rw [Real.log_rpow (by positivity)]; ring,
      Real.exp_log (by positivity), Real.mul_rpow (by norm_num) hx.le, Real.rpow_neg hx.le]
    simp only [K1]; ring
  have hn2 : ∀ x : ℝ, 0 < x → ‖exp (-(x : ℂ)) * exp (-(β * (Real.log (2 * x) - π * I))) *
      (Gamma β')⁻¹‖ = K2 * (x ^ (-β.re) * Real.exp (-1 * x)) := fun x hx =>
    norm_exp_neg_mul_exp_mul_inv_Gamma β β' hx
  -- the decaying term tends to zero
  have hT2 : Tendsto (fun x : ℝ => ‖exp (-(x : ℂ)) * exp (-(β * (Real.log (2 * x) - π * I))) *
      (Gamma β')⁻¹ * carlson2F0Sector (1 - β') β (-(Real.log (2 * x) : ℂ) + (0 : ℝ) * I)‖)
      atTop (𝓝 0) := by
    have h0 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β.re) 1 one_pos).const_mul K2).mul
      hF2.norm
    rw [mul_zero, zero_mul] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_mul, hn2 x hx]
  -- the growing term
  have hlow : ∀ᶠ x : ℝ in atTop, K1 / 2 * (Real.exp x / x ^ β'.re) - 1 ≤
      ‖regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair x (-x))‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (hF1.norm.eventually (lt_mem_nhds (show (1 : ℝ) / 2 < ‖(1 : ℂ)‖ by norm_num))),
      hT2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx h1 h2
    rw [regCarlsonS_pair_neg_eq β β' hx]
    set A := exp (x : ℂ) * exp (-(β' * Real.log (2 * x))) * (Gamma β)⁻¹ *
      carlson2F0Sector (1 - β) β' (-(Real.log (2 * x) : ℂ) + π * I)
    set B := exp (-(x : ℂ)) * exp (-(β * (Real.log (2 * x) - π * I))) * (Gamma β')⁻¹ *
      carlson2F0Sector (1 - β') β (-(Real.log (2 * x) : ℂ) + (0 : ℝ) * I)
    have hAB : ‖A‖ - ‖B‖ ≤ ‖A + B‖ := by simpa using norm_sub_norm_le A (-B)
    have hA : ‖A‖ = K1 * (Real.exp x / x ^ β'.re) *
        ‖carlson2F0Sector (1 - β) β' (-(Real.log (2 * x) : ℂ) + π * I)‖ := by
      simp only [A]; rw [norm_mul, hn1 x hx]
    have hpos : 0 ≤ K1 * (Real.exp x / x ^ β'.re) := by positivity
    nlinarith
  refine tendsto_atTop_mono' atTop hlow ?_
  exact tendsto_atTop_add_const_right _ (-1)
    ((tendsto_exp_div_rpow_atTop β'.re).const_mul_atTop (by positivity))

/-- **Theorem 7.9-5, the exceptional case**: if `β = -m` with `m ∈ ℕ`, then
`S(β, β'; x, -x)/Γ(β + β') → 0` as `x → ∞` through real values. -/
theorem tendsto_regCarlsonS_pair_neg_of_neg_nat (m : ℕ) (β' : ℂ) :
    Tendsto (fun x : ℝ => regCarlsonS (TwoVariable.pair (-(m : ℂ)) β') (TwoVariable.pair x (-x)))
      atTop (𝓝 0) := by
  have hF2 := tendsto_carlson2F0Sector_log (1 - β') (-(m : ℂ)) (c := 0) (by simp; positivity)
  set K2 := (2 : ℝ) ^ (-(-(m : ℂ)).re) * Real.exp (-(π * (-(m : ℂ)).im)) * ‖(Gamma β')⁻¹‖
  have h0 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-(-(m : ℂ)).re) 1 one_pos).const_mul
    K2).mul hF2.norm
  rw [mul_zero, zero_mul] at h0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h0.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [regCarlsonS_pair_neg_eq _ β' hx, Gamma_neg_nat_eq_zero, inv_zero, mul_zero, zero_mul,
    zero_add, norm_mul, norm_exp_neg_mul_exp_mul_inv_Gamma _ _ hx]

/-! ### The Laguerre function of the second kind as a confluent limit -/

/-- `(1 + t/a)^a ≤ (1 + t/b)^b` for `0 < a ≤ b` and `t ≥ 0`, by concavity of the logarithm. -/
theorem one_add_div_rpow_self_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) :
    (1 + t / a) ^ a ≤ (1 + t / b) ^ b := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : 0 < 1 + t / a := by positivity
  have h2 : 0 < 1 + t / b := by positivity
  have hw : 0 ≤ a / b := by positivity
  have hw' : 0 ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr h1) (mem_Ioi.mpr one_pos) hw hw'
    (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
  have hsum : a / b * (1 + t / a) + (1 - a / b) * 1 = 1 + t / b := by field_simp; ring
  rw [hsum] at hc
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hc hb.le
  rw [show b * (a / b * Real.log (1 + t / a)) = a * Real.log (1 + t / a) by field_simp] at this
  linarith

/-- The polynomially decaying majorant `t^c (1 + t/S)^{-S}` is integrable on `(0, ∞)` when
`-1 < c` and `c + 1 < S`. -/
theorem integrableOn_rpow_mul_one_add_div_rpow {c S : ℝ} (hc : -1 < c) (hS : c + 1 < S) :
    IntegrableOn (fun t : ℝ => t ^ c * (1 + t / S) ^ (-S)) (Ioi 0) := by
  have hS0 : 0 < S := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ c * (1 + t / S) ^ (-S)) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht'.ne')).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (by positivity)) |>.comp
        (by fun_prop : ContinuousAt (fun t : ℝ => 1 + t / S) t))).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi := (intervalIntegral.intervalIntegrable_rpow' hc (a := 0) (b := 1)).1
    refine Integrable.mono' hi ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 + t / S) ^ (-S) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (div_nonneg ht0.le hS0.le)) (by linarith)
    have := Real.rpow_nonneg ht0.le c
    nlinarith
  · have hi := (integrableOn_Ioi_rpow_of_lt (show c - S < -1 by linarith) one_pos).const_mul
      (S ^ S)
    refine Integrable.mono' hi ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (1 + t / S) ^ (-S) ≤ (t / S) ^ (-S) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h2 : (t / S) ^ (-S) = S ^ S * t ^ (-S) := by
      rw [Real.div_rpow ht0.le hS0.le, Real.rpow_neg ht0.le, Real.rpow_neg hS0.le]; field_simp
    have h3 : t ^ c * t ^ (-S) = t ^ (c - S) := by
      rw [← Real.rpow_add ht0]; ring_nf
    calc t ^ c * (1 + t / S) ^ (-S) ≤ t ^ c * (S ^ S * t ^ (-S)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le c)
      _ = S ^ S * t ^ (c - S) := by rw [← h3]; ring

/-- The integrand of the confluence limit after the substitution `u = s/(t + s)`. -/
def laguerreKernel (b : ℂ) (κ : ℝ) (f : ℝ → ℂ) (s t : ℝ) : ℂ :=
  f (s * t / (t + s)) * (((1 + t / s) ^ (-(s + κ)) : ℝ) : ℂ) * ((1 + t / s : ℝ) : ℂ) ^ (-(b + 1)) *
    (t : ℂ) ^ (b - 1)

/-- **The confluence limit** `∫₀^∞ f(st/(t+s)) (1+t/s)^{-(s+n)} (1+t/s)^{-(b+1)} t^{b-1} dt
→ ∫₀^∞ f(t) e^{-t} t^{b-1} dt` as `s → ∞`, for `f` continuous and bounded on `[0, ∞)`. -/
theorem tendsto_integral_laguerreKernel {b : ℂ} (hb : 0 < b.re) {κ : ℝ}
    (hκ : 0 ≤ κ + b.re + 1) {f : ℝ → ℂ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ M) :
    Tendsto (fun s : ℝ => ∫ t in Ioi (0 : ℝ), laguerreKernel b κ f s t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), f t * (Real.exp (-t) : ℂ) * (t : ℂ) ^ (b - 1))) := by
  set S₀ := b.re + 1
  have hS₀ : 0 < S₀ := by simp only [S₀]; linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => M * (t ^ (b.re - 1) * (1 + t / S₀) ^ (-S₀))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s => by
      unfold laguerreKernel
      exact (by fun_prop (disch := exact hf.measurable) :
        Measurable fun t : ℝ => f (s * t / (t + s)) * (((1 + t / s) ^ (-(s + κ)) : ℝ) : ℂ) *
          ((1 + t / s : ℝ) : ℂ) ^ (-(b + 1)) * (t : ℂ) ^ (b - 1)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop S₀] with s hs
    have hs0 : 0 < s := hS₀.trans_le hs
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hq : 1 ≤ 1 + t / s := le_add_of_nonneg_right (by positivity)
    have hq0 : 0 < 1 + t / s := by positivity
    unfold laguerreKernel
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re, sub_re]
    have h1 : ‖f (s * t / (t + s))‖ ≤ M := hM _ (by positivity)
    have h2 : (1 + t / s) ^ (-(s + κ)) * (1 + t / s) ^ (-(b.re + 1)) ≤
        (1 + t / S₀) ^ (-S₀) := by
      calc (1 + t / s) ^ (-(s + κ)) * (1 + t / s) ^ (-(b.re + 1))
          = (1 + t / s) ^ (-s) * (1 + t / s) ^ (-(κ + b.re + 1)) := by
            rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
        _ ≤ (1 + t / s) ^ (-s) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq0.le _)
            exact Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
        _ = ((1 + t / s) ^ s)⁻¹ := by rw [mul_one, Real.rpow_neg hq0.le]
        _ ≤ ((1 + t / S₀) ^ S₀)⁻¹ := by
            apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
            exact one_add_div_rpow_self_le hS₀ hs ht0.le
        _ = (1 + t / S₀) ^ (-S₀) := (Real.rpow_neg (by positivity) _).symm
    have p1 := Real.rpow_nonneg (show 0 ≤ 1 + t / s by positivity) (-(s + κ))
    have p2 := Real.rpow_nonneg (show 0 ≤ 1 + t / s by positivity) (-(b.re + 1))
    have p3 := Real.rpow_nonneg ht0.le (b.re - 1)
    have p4 := Real.rpow_nonneg (show 0 ≤ 1 + t / S₀ by positivity) (-S₀)
    calc ‖f (s * t / (t + s))‖ * (1 + t / s) ^ (-(s + κ)) * (1 + t / s) ^ (-(b.re + 1)) *
          t ^ (b.re - 1) = ‖f (s * t / (t + s))‖ * ((1 + t / s) ^ (-(s + κ)) *
            (1 + t / s) ^ (-(b.re + 1))) * t ^ (b.re - 1) := by ring
      _ ≤ M * (1 + t / S₀) ^ (-S₀) * t ^ (b.re - 1) := by gcongr
      _ = M * (t ^ (b.re - 1) * (1 + t / S₀) ^ (-S₀)) := by ring
  · exact (integrableOn_rpow_mul_one_add_div_rpow (c := b.re - 1) (S := S₀) (by linarith)
      (by simp only [S₀]; linarith)).const_mul M
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hq : Tendsto (fun s : ℝ => 1 + t / s) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := t)).div_atTop tendsto_id |>.const_add 1
    have hA : Tendsto (fun s : ℝ => f (s * t / (t + s))) atTop (𝓝 (f t)) := by
      have : Tendsto (fun s : ℝ => t / (1 + t / s)) atTop (𝓝 (t / 1)) :=
        tendsto_const_nhds.div hq one_ne_zero
      rw [div_one] at this
      refine (hf.tendsto t).comp (this.congr' ?_)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      field_simp
      ring
    have hB : Tendsto (fun s : ℝ => (((1 + t / s) ^ (-(s + κ)) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-t) : ℝ) : ℂ)) := by
      apply Complex.continuous_ofReal.continuousAt.tendsto.comp
      have h1 := (Real.tendsto_one_add_div_rpow_exp t).inv₀ (Real.exp_pos t).ne'
      have h2 : Tendsto (fun s : ℝ => ((1 + t / s) ^ κ)⁻¹) atTop (𝓝 ((1 : ℝ) ^ κ)⁻¹) :=
        ((Real.continuousAt_rpow_const 1 κ (Or.inl one_ne_zero)).tendsto.comp hq).inv₀
          (by simp)
      simp only [Real.one_rpow, inv_one] at h2
      have := h1.mul h2
      rw [mul_one, ← Real.exp_neg] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hq0 : 0 < 1 + t / s := by positivity
      rw [← mul_inv, ← Real.rpow_add hq0, Real.rpow_neg hq0.le]
    have hC : Tendsto (fun s : ℝ => ((1 + t / s : ℝ) : ℂ) ^ (-(b + 1))) atTop (𝓝 1) := by
      have hc := continuousAt_cpow_const (a := (1 : ℂ)) (b := -(b + 1)) one_mem_slitPlane
      have := hc.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.comp hq)
      simp only [one_cpow] at this
      exact this
    have := ((hA.mul hB).mul hC).mul (tendsto_const_nhds (x := (t : ℂ) ^ (b - 1)))
    simpa [laguerreKernel] using this

/-- Powers of positive reals as exponentials. -/
theorem ofReal_cpow_eq_exp {q : ℝ} (hq : 0 < q) (c : ℂ) :
    ((q : ℝ) : ℂ) ^ c = exp (Real.log q * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← ofReal_log hq.le]

/-- **The substitution `u = s/(t + s)`** turning the Euler integral over `(0, 1)` into the
confluence integral over `(0, ∞)`. -/
theorem integral_Ioo_eq_integral_laguerreKernel (b : ℂ) (κ : ℝ) (f : ℝ → ℂ) {s : ℝ}
    (hs : 0 < s) :
    (s : ℂ) ^ b * ∫ u in Ioo (0 : ℝ) 1, f ((1 - u) * s) * ((u ^ (s + κ) : ℝ) : ℂ) *
        ((1 - u : ℝ) : ℂ) ^ (b - 1) =
      ∫ t in Ioi (0 : ℝ), laguerreKernel b κ f s t := by
  set φ : ℝ → ℝ := fun t => s / (t + s)
  have himage : φ '' Ioi 0 = Ioo 0 1 := by
    ext u
    simp only [φ, mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩
    · rintro ⟨h0, h1⟩
      refine ⟨s / u - s, ?_, ?_⟩
      · rw [sub_pos, lt_div_iff₀ h0]; nlinarith
      · field_simp; ring
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (-(s / (t + s) ^ 2)) (Ioi 0) t := by
    intro t ht
    have ht0 : 0 < t + s := by have : (0 : ℝ) < t := ht; linarith
    have := ((hasDerivAt_id t).add_const s).inv ht0.ne'
    have h2 := this.const_mul s
    refine (h2.congr_deriv ?_).hasDerivWithinAt.congr (fun _ _ => by simp [φ, div_eq_mul_inv])
      (by simp [φ, div_eq_mul_inv])
    simp; ring
  have hinj : InjOn φ (Ioi 0) := by
    intro t₁ h₁ t₂ h₂ h
    simp only [φ] at h
    have h1 : (0 : ℝ) < t₁ + s := by have : (0 : ℝ) < t₁ := h₁; linarith
    have h2 : (0 : ℝ) < t₂ + s := by have : (0 : ℝ) < t₂ := h₂; linarith
    field_simp at h
    nlinarith
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hts : 0 < t + s := by linarith
  have hq : 0 < 1 + t / s := by positivity
  have hu : 0 < s / (t + s) := by positivity
  have h1u : 0 < 1 - s / (t + s) := by rw [sub_pos, div_lt_one hts]; linarith
  have harg : (1 - s / (t + s)) * s = s * t / (t + s) := by field_simp; ring
  have habs : |(-(s / (t + s) ^ 2))| = s / (t + s) ^ 2 := by rw [abs_neg, abs_of_pos (by positivity)]
  simp only [φ, laguerreKernel, habs, Complex.real_smul, harg]
  -- express everything through logarithms
  have hl1 : Real.log (1 - s / (t + s)) = Real.log t - Real.log (t + s) := by
    rw [show 1 - s / (t + s) = t / (t + s) by field_simp; ring, Real.log_div ht0.ne' hts.ne']
  have hl2 : Real.log (1 + t / s) = Real.log (t + s) - Real.log s := by
    rw [show 1 + t / s = (t + s) / s by field_simp; ring, Real.log_div hts.ne' hs.ne']
  have hl3 : Real.log (s / (t + s)) = Real.log s - Real.log (t + s) := Real.log_div hs.ne' hts.ne'
  have hl4 : Real.log (s / (t + s) ^ 2) = Real.log s - 2 * Real.log (t + s) := by
    rw [Real.log_div hs.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [ofReal_cpow_eq_exp hs, ofReal_cpow_eq_exp h1u, ofReal_cpow_eq_exp hq,
    ofReal_cpow_eq_exp ht0, Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hq,
    show ((s / (t + s) ^ 2 : ℝ) : ℂ) = ((Real.exp (Real.log (s / (t + s) ^ 2)) : ℝ) : ℂ) by
      rw [Real.exp_log (by positivity)], hl1, hl2, hl3, hl4]
  push_cast
  have kL : ∀ (F a b c d : ℂ), exp a * (exp b * (F * exp c * exp d)) = F * exp (a + b + c + d) :=
    fun F a b c d => by simp only [exp_add]; ring
  have kR : ∀ (F a b c : ℂ), F * exp a * exp b * exp c = F * exp (a + b + c) :=
    fun F a b c => by simp only [exp_add]; ring
  rw [kL, kR]
  congr 2
  ring

/-- The slit plane is closed under inversion. -/
theorem inv_mem_slitPlane' {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hn : 0 < normSq w := normSq_pos.mpr hw0
  rcases mem_slitPlane_iff.mp hw with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by rw [inv_re]; exact div_pos h hn))
  · exact mem_slitPlane_iff.mpr (Or.inr (by rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr h) hn.ne'))

/-- Points off `[0, ∞)` stay a positive distance from the nonnegative reals. -/
theorem exists_pos_le_norm_sub_ofReal {x : ℂ} (hx : -x ∈ slitPlane) :
    ∃ c > 0, ∀ r : ℝ, 0 ≤ r → c ≤ ‖x - r‖ := by
  rcases mem_slitPlane_iff.mp hx with h | h
  · refine ⟨-x.re, by simpa using h, fun r hr => ?_⟩
    calc -x.re ≤ r - x.re := by linarith
      _ ≤ |r - x.re| := le_abs_self _
      _ = |(x - r).re| := by simp [abs_sub_comm]
      _ ≤ ‖x - r‖ := abs_re_le_norm _
  · refine ⟨|x.im|, abs_pos.mpr (by simpa using h), fun r _ => ?_⟩
    calc |x.im| = |(x - r).im| := by simp
      _ ≤ ‖x - r‖ := abs_im_le_norm _

/-- **Carlson's monic Laguerre function of the second kind** (Definition 7.9-2):
`q̃ₙ(x) = x^{-n-1} ₂F₀(1 + n, 1 + β + n; 1/x)` for `x ∉ [0, ∞)`, on the branch with
`ph(-1/x) ∈ (-π, π)`. -/
def monicLaguerreSecondKind (β : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  x ^ (-((n : ℤ) + 1)) * carlson2F0Sector (1 + n) (1 + β + n) (log (-x⁻¹))

/-- The Laguerre function of the second kind as an Euler integral (Carlson (7.9-4)):
`Γ(1+β+n) q̃ₙ(x) = ∫₀^∞ (x - t)^{-n-1} e^{-t} t^{β+n} dt`. -/
theorem integral_laguerreSecondKind (n : ℕ) {β : ℂ} (hβ : 0 < (1 + β + n).re) {x : ℂ}
    (hx : -x ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (x - t) ^ (-((n : ℤ) + 1)) * (Real.exp (-t) : ℂ) * (t : ℂ) ^ (β + n) =
      Gamma (1 + β + n) * monicLaguerreSecondKind β n x := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hw : -x⁻¹ ∈ slitPlane := by
    rw [show -x⁻¹ = (-x)⁻¹ by rw [inv_neg]]
    exact inv_mem_slitPlane' hx
  have hw0 : -x⁻¹ ≠ 0 := slitPlane_ne_zero hw
  set ζ := log (-x⁻¹)
  have hζ : |ζ.im| < π := by
    rw [log_im, abs_lt]
    exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (slitPlane_arg_ne_pi hw)⟩
  have hexp : exp ζ = -x⁻¹ := exp_log hw0
  rw [monicLaguerreSecondKind, carlson2F0Sector_eq_integral (by simp; positivity) hβ hζ, hexp,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hΓ : Gamma (1 + β + n) ≠ 0 := Gamma_ne_zero_of_re_pos hβ
  have hxt : x - t = x * (1 + t * -x⁻¹) := by field_simp; ring
  rw [hxt, mul_zpow, show (-(1 + (n : ℂ))) = (((-((n : ℤ) + 1)) : ℤ) : ℂ) by push_cast; ring,
    cpow_intCast]
  simp only [eulerDensity]
  rw [show (β + n : ℂ) = 1 + β + n - 1 by ring]
  field_simp
  push_cast
  ring

/-- **The Laguerre function of the second kind as a confluent limit** (Carlson (7.9-4)): for
`re (1 + β + n) > 0` and `x ∉ [0, ∞)`,
`R_{-n-1}(1 + s + n, 1 + β + n; x, x - s) → q̃ₙ(x)` as `s → ∞`. Here `R_{-n-1}` is Carlson's
average of `w^{-n-1}`, written as `Γ(c)` times the regularized Dirichlet average. -/
theorem tendsto_laguerreSecondKind (n : ℕ) {β : ℂ} (hβ : 0 < (1 + β + n).re) {x : ℂ}
    (hx : -x ∈ slitPlane) :
    Tendsto (fun s : ℝ => Gamma ((1 + s + n) + (1 + β + n)) *
        regCarlsonDirichletAverage (TwoVariable.pair (1 + s + n) (1 + β + n))
          (TwoVariable.pair x (x - s)) (fun w => w ^ (-((n : ℤ) + 1))))
      atTop (𝓝 (monicLaguerreSecondKind β n x)) := by
  set b : ℂ := 1 + β + n
  obtain ⟨c, hc, hcx⟩ := exists_pos_le_norm_sub_ofReal hx
  set f : ℝ → ℂ := fun r => (x - (max r 0 : ℝ)) ^ (-((n : ℤ) + 1))
  have hf0 : ∀ r : ℝ, x - (max r 0 : ℝ) ≠ 0 := fun r h => by
    have := hcx (max r 0) (le_max_right _ _); rw [h, norm_zero] at this; linarith
  have hf : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun r => ?_
    exact (continuousAt_zpow₀ (x - ((max r 0 : ℝ) : ℂ)) (-((n : ℤ) + 1)) (Or.inl (hf0 r))).comp
      (f := fun r : ℝ => x - ((max r 0 : ℝ) : ℂ)) (by fun_prop)
  have hfM : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ c ^ (-((n : ℤ) + 1)) := by
    intro r hr
    simp only [f, norm_zpow]
    have hk : -((n : ℤ) + 1) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [hk, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (pow_pos hc _) (pow_le_pow_left₀ hc.le (hcx _ (le_max_right _ _)) _)
  have h1 : ∀ r : ℝ, 0 ≤ r → ‖(fun _ : ℝ => (1 : ℂ)) r‖ ≤ 1 := fun _ _ => by simp
  have hκ : (0 : ℝ) ≤ (n : ℝ) + b.re + 1 := by positivity
  have hN := tendsto_integral_laguerreKernel hβ hκ hf hfM
  have hD := tendsto_integral_laguerreKernel hβ hκ continuous_const h1
  have hΓb : Gamma b = ∫ t in Ioi (0 : ℝ), (fun _ : ℝ => (1 : ℂ)) t * (Real.exp (-t) : ℂ) *
      (t : ℂ) ^ (b - 1) := by
    rw [Gamma_eq_integral hβ, GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  rw [← hΓb] at hD
  have hlim := hN.div hD (Gamma_ne_zero_of_re_pos hβ)
  have hnum : ∫ t in Ioi (0 : ℝ), f t * (Real.exp (-t) : ℂ) * (t : ℂ) ^ (b - 1) =
      Gamma b * monicLaguerreSecondKind β n x := by
    rw [← integral_laguerreSecondKind n hβ hx]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [f, max_eq_left ht0.le, b]
    congr 2; ring
  rw [hnum, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hβ)] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have ha : 0 < (1 + s + n : ℂ).re := by simp; positivity
  have hab : 0 < ((1 + s + n : ℂ) + b).re := by simp only [add_re] at ha hβ ⊢; linarith
  have hBeta := Gamma_mul_Gamma_eq_betaIntegral ha hβ
  have hs0 : (s : ℂ) ^ b ≠ 0 := (cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast hs.ne'))
  have hG : Gamma ((1 + s + n : ℂ) + b) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  rw [TwoVariable.regCarlsonDirichletAverage_pair_eq, Dirichlet.regEulerIntegral]
  have hNs := integral_Ioo_eq_integral_laguerreKernel b (n : ℝ) f hs
  have hDs := integral_Ioo_eq_integral_laguerreKernel b (n : ℝ) (fun _ => (1 : ℂ)) hs
  have hNint : ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ ((1 + s + n : ℂ) - 1) * (1 - u : ℂ) ^ (b - 1) *
      ((u : ℂ) * x + (1 - u : ℂ) * (x - s)) ^ (-((n : ℤ) + 1)) =
      ∫ u in Ioo (0 : ℝ) 1, f ((1 - u) * s) * ((u ^ (s + n) : ℝ) : ℂ) *
        ((1 - u : ℝ) : ℂ) ^ (b - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have h1 : (u : ℂ) * x + (1 - u : ℂ) * (x - s) = x - ((max ((1 - u) * s) 0 : ℝ) : ℂ) := by
      rw [max_eq_left (mul_nonneg (by linarith [hu.2]) hs.le)]; push_cast; ring
    rw [h1, show (1 + s + n : ℂ) - 1 = ((s + n : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hu.1.le]
    simp only [f]; push_cast; ring
  have hDint : betaIntegral (1 + s + n) b = ∫ u in Ioo (0 : ℝ) 1, (fun _ : ℝ => (1 : ℂ))
      ((1 - u) * s) * ((u ^ (s + n) : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ) ^ (b - 1) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [show (1 + s + n : ℂ) - 1 = ((s + n : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hu.1.le]
    push_cast; ring
  simp only [Pi.div_apply]
  rw [hNint, ← hNs, ← hDs, ← hDint]
  have hB0 : betaIntegral (1 + s + n) b ≠ 0 := by
    intro h; rw [h, mul_zero] at hBeta
    exact mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hβ) hBeta
  rw [hBeta]
  field_simp
  simp only [mul_comm s]

/-- **The Laguerre limit for Carlson's `R_{-n-1}`** (Carlson (7.9-4)): for `re (1 + β + n) > 0`
and `im x ≠ 0`, `R_{-n-1}(1 + s + n, 1 + β + n; x, x - s) → q̃ₙ(x)` as `s → ∞`. -/
theorem tendsto_carlsonR_laguerreSecondKind (n : ℕ) {β : ℂ} (hβ : 0 < (1 + β + n).re) {x : ℂ}
    (hx : x.im ≠ 0) :
    Tendsto (fun s : ℝ => carlsonR (-((n : ℂ) + 1)) (TwoVariable.pair (1 + s + n) (1 + β + n))
        (TwoVariable.pair x (x - s))) atTop (𝓝 (monicLaguerreSecondKind β n x)) := by
  have hx' : -x ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hx))
  refine (tendsto_laguerreSecondKind n hβ hx').congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hb : TwoVariable.pair (1 + s + n : ℂ) (1 + β + n) ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i
    · show 0 < (1 + s + n : ℂ).re; simp; positivity
    · exact hβ
  have hhull : convexHull ℝ (Set.range (TwoVariable.pair x (x - s))) ⊆ slitPlane := by
    have h : Set.range (TwoVariable.pair x (x - s)) = {x, x - s} := by
      ext w; simp [TwoVariable.pair, Matrix.range_cons, Matrix.range_empty, eq_comm, or_comm]
    rw [h, convexHull_pair]
    rintro w ⟨a, c, ha, hc, hac, rfl⟩
    refine mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [add_im, smul_im, sub_im, ofReal_im, sub_zero, smul_eq_mul]
    rw [← add_mul, hac, one_mul]; exact hx
  rw [carlsonR_eq_carlsonRIntegral_of_convexHull _ hb hhull, carlsonRIntegral, regCarlsonRIntegral,
    TwoVariable.sum_pair]
  congr 2
  funext w
  rw [show (-((n : ℂ) + 1)) = ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring, cpow_intCast]

end Carlson
