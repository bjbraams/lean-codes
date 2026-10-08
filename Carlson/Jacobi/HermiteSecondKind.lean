/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.LaguerreSecondKind
public import Carlson.TwoVariable.EqualParameterSlit

/-!
# The Hermite function of the second kind

Carlson's Definition 7.10-2 gives the monic Hermite function of the second kind
`q̃ₙ(x) = x^{-n-1} ₂F₀(1 + n/2, (1 + n)/2; 1/x²)` for `x ∉ ℝ`, and (7.10-3) obtains it as the
limit `lim_{s → ∞} R_{-n-1}(1 + s² + n, 1 + s² + n; x + s, x - s)`.

Carlson applies the first quadratic transformation (6.9-7) before letting `s → ∞`. Here the
transformation is proved for nodes with positive real parts, and `x ± s` are not such nodes;
they are brought there by a rotation `ω = ∓i` with `re (ω x) > 0`, which multiplies the average
of `w^{-n-1}` by `ω^{n+1}`. The transformed function is
`R_{-(n+1)/2}(s² + (n+1)/2, 1 + n/2; -x², s² - x²)`, and its limit is a shifted confluence limit
of the Laguerre type with nodes `(X, X + S)` and a non-integral exponent. The branch identity
`(X + t)^c = X^c (1 + t/X)^c` for `X` in the slit plane and `t ≥ 0` relates it to `₂F₀`.

## Main definitions

* `Carlson.monicHermiteSecondKind`: Carlson's `q̃ₙ` of Definition 7.10-2, with the `₂F₀`
  parameters in the order `((1 + n)/2, 1 + n/2)` (the function is symmetric in them).

## Main results

* `Carlson.add_ofReal_cpow`: `(X + t)^c = X^c (1 + t/X)^c`.
* `Carlson.tendsto_regCarlsonDirichletAverage_shift`: the shifted confluence limit
  `R_{-a}(S + a, b; X, X + S) → X^{-a} ₂F₀(a, b; -1/X)`.
* `Carlson.tendsto_hermiteSecondKind`, `Carlson.tendsto_carlsonR_hermiteSecondKind`: the limit
  (7.10-3).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.10.
-/

open Complex MeasureTheory Filter Set Dirichlet
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson

/-- The argument of a point `1 + t/X` has the opposite sign to that of `X`. -/
theorem arg_add_arg_one_add_mem {X : ℂ} (hX : X ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    arg X + arg (1 + t * X⁻¹) ∈ Ioc (-π) π := by
  have hX0 : X ≠ 0 := slitPlane_ne_zero hX
  have hn : 0 < normSq X := normSq_pos.mpr hX0
  have hw : (1 + (t : ℂ) * X⁻¹).im = -(t * X.im / normSq X) := by
    simp [inv_im, mul_im]; ring
  have hwr : (1 + (t : ℂ) * X⁻¹).re = 1 + t * X.re / normSq X := by
    simp [inv_re, mul_re]; ring
  rcases lt_trichotomy X.im 0 with h | h | h
  · -- `X` in the lower half-plane: `arg X ∈ (-π, 0)`, `arg (1 + t/X) ∈ [0, π)`
    have h1 : arg X < 0 := arg_neg_iff.mpr h
    have h2 : 0 ≤ arg (1 + t * X⁻¹) := arg_nonneg_iff.mpr (by
      rw [hw]; have : t * X.im / normSq X ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ht h.le) hn.le
      linarith)
    constructor
    · linarith [neg_pi_lt_arg X]
    · linarith [arg_le_pi (1 + t * X⁻¹)]
  · -- `X` a positive real
    have hre : 0 < X.re := by
      rcases mem_slitPlane_iff.mp hX with h' | h'
      · exact h'
      · exact absurd h h'
    have h1 : arg X = 0 := by
      rw [arg_eq_zero_iff]; exact ⟨hre.le, h⟩
    have h2 : arg (1 + t * X⁻¹) = 0 := by
      rw [arg_eq_zero_iff]
      refine ⟨by rw [hwr]; have := div_nonneg (mul_nonneg ht hre.le) hn.le; linarith, ?_⟩
      rw [hw, h]; simp
    rw [h1, h2]; constructor <;> linarith [Real.pi_pos]
  · have h1 : 0 ≤ arg X := arg_nonneg_iff.mpr h.le
    have h1' : arg X < π := arg_lt_pi_iff.mpr (Or.inr h.ne')
    have h2 : arg (1 + t * X⁻¹) ≤ 0 := by
      rcases (show (1 + (t : ℂ) * X⁻¹).im < 0 ∨ (1 + (t : ℂ) * X⁻¹).im = 0 by
        rw [hw]; have : 0 ≤ t * X.im / normSq X := div_nonneg (mul_nonneg ht h.le) hn.le
        rcases this.lt_or_eq with h3 | h3
        · left; linarith
        · right; rw [← h3]; simp) with h3 | h3
      · exact (arg_neg_iff.mpr h3).le
      · have : 0 ≤ (1 + (t : ℂ) * X⁻¹).re := by
          rw [hwr]
          by_contra hc; push Not at hc
          have : (1 + (t : ℂ) * X⁻¹).im = 0 := h3
          have ht0 : t = 0 := by
            rw [hw, neg_eq_zero, div_eq_zero_iff] at this
            rcases this with h4 | h4
            · rcases mul_eq_zero.mp h4 with h5 | h5
              · exact h5
              · exact absurd h5 h.ne'
            · exact absurd h4 hn.ne'
          rw [ht0] at hc; simp at hc; linarith
        exact (arg_eq_zero_iff.mpr ⟨this, h3⟩).le
    constructor
    · linarith [neg_pi_lt_arg (1 + t * X⁻¹)]
    · linarith

/-- Powers split along a positive real translation: `(X + t)^c = X^c (1 + t/X)^c` for `X` in
the slit plane and `t ≥ 0`. -/
theorem add_ofReal_cpow {X : ℂ} (hX : X ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) (c : ℂ) :
    (X + t) ^ c = X ^ c * (1 + t * X⁻¹) ^ c := by
  have hX0 : X ≠ 0 := slitPlane_ne_zero hX
  have h1 : 1 + (t : ℂ) * X⁻¹ ≠ 0 := by
    intro h
    have : X + t = 0 := by
      have := congrArg (· * X) h; simp only [zero_mul, add_mul, one_mul] at this
      rw [mul_assoc, inv_mul_cancel₀ hX0, mul_one] at this; linear_combination this
    have hre : (X + t).re = 0 := by rw [this]; simp
    have him : (X + t).im = 0 := by rw [this]; simp
    simp at hre him
    rcases mem_slitPlane_iff.mp hX with h' | h'
    · linarith
    · exact h' him
  have hprod : X + t = X * (1 + t * X⁻¹) := by field_simp
  rw [hprod, cpow_def_of_ne_zero (mul_ne_zero hX0 h1), cpow_def_of_ne_zero hX0,
    cpow_def_of_ne_zero h1, log_mul hX0 h1 (arg_add_arg_one_add_mem hX ht), ← exp_add]
  ring_nf

/-- Adding a nonnegative real keeps a point in the slit plane. -/
theorem add_ofReal_mem_slitPlane {X : ℂ} (hX : X ∈ slitPlane) {r : ℝ} (hr : 0 ≤ r) :
    X + r ∈ slitPlane := by
  rcases mem_slitPlane_iff.mp hX with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))

/-- **A shifted confluence limit**: for `a > 0`, `re b > 0` and `X` in the slit plane,
`R_{-a}(S + a, b; X, X + S) → X^{-a} ₂F₀(a, b; -1/X)` as `S → ∞`, with `R_{-a}` written as
`Γ(c)` times the regularized Dirichlet average of `w^{-a}`. -/
theorem tendsto_regCarlsonDirichletAverage_shift {a : ℝ} (ha : 0 < a) {b : ℂ} (hb : 0 < b.re)
    {X : ℂ} (hX : X ∈ slitPlane) :
    Tendsto (fun S : ℝ => Gamma (((S + a : ℝ) : ℂ) + b) *
        regCarlsonDirichletAverage (TwoVariable.pair ((S + a : ℝ) : ℂ) b)
          (TwoVariable.pair X (X + S)) (fun w => w ^ (-(a : ℂ))))
      atTop (𝓝 (X ^ (-(a : ℂ)) * carlson2F0Sector a b (log X⁻¹))) := by
  obtain ⟨c, hc, hcx⟩ := exists_pos_le_norm_sub_ofReal (x := -X) (by simpa using hX)
  have hcX : ∀ r : ℝ, 0 ≤ r → c ≤ ‖X + r‖ := fun r hr => by
    have := hcx r hr; rwa [show -X - (r : ℂ) = -(X + r) by ring, norm_neg] at this
  set f : ℝ → ℂ := fun r => (X + (max r 0 : ℝ)) ^ (-(a : ℂ))
  have hf : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun r => ?_
    exact (continuousAt_cpow_const (b := -(a : ℂ))
      (add_ofReal_mem_slitPlane hX (le_max_right r 0))).comp
      (f := fun r : ℝ => X + ((max r 0 : ℝ) : ℂ)) (by fun_prop)
  have hfM : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ c ^ (-a) := by
    intro r hr
    simp only [f]
    rw [show (-(a : ℂ)) = ((-a : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    exact Real.rpow_le_rpow_of_nonpos hc (hcX _ (le_max_right _ _)) (by linarith)
  have h1 : ∀ r : ℝ, 0 ≤ r → ‖(fun _ : ℝ => (1 : ℂ)) r‖ ≤ 1 := fun _ _ => by simp
  have hκ : (0 : ℝ) ≤ (a - 1) + b.re + 1 := by linarith
  have hN := tendsto_integral_laguerreKernel hb hκ hf hfM
  have hD := tendsto_integral_laguerreKernel hb hκ continuous_const h1
  have hΓb : Gamma b = ∫ t in Ioi (0 : ℝ), (fun _ : ℝ => (1 : ℂ)) t * (Real.exp (-t) : ℂ) *
      (t : ℂ) ^ (b - 1) := by
    rw [Gamma_eq_integral hb, GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  rw [← hΓb] at hD
  have hlim := hN.div hD (Gamma_ne_zero_of_re_pos hb)
  -- the limit
  have hXi : X⁻¹ ∈ slitPlane := inv_mem_slitPlane' hX
  have hζ : |(log X⁻¹).im| < π := by
    rw [log_im, abs_lt]
    exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (slitPlane_arg_ne_pi hXi)⟩
  have hnum : ∫ t in Ioi (0 : ℝ), f t * (Real.exp (-t) : ℂ) * (t : ℂ) ^ (b - 1) =
      Gamma b * (X ^ (-(a : ℂ)) * carlson2F0Sector a b (log X⁻¹)) := by
    rw [carlson2F0Sector_eq_integral (by simpa using ha) hb hζ, exp_log (slitPlane_ne_zero hXi),
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [f, max_eq_left ht0.le, eulerDensity]
    rw [add_ofReal_cpow hX ht0.le]
    have hΓ : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
    field_simp
    push_cast
    ring
  rw [hnum, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hb)] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
  have hA : 0 < (((S + a : ℝ) : ℂ)).re := by simp; linarith
  have hBeta := Gamma_mul_Gamma_eq_betaIntegral hA hb
  rw [TwoVariable.regCarlsonDirichletAverage_pair_eq, Dirichlet.regEulerIntegral]
  have hNs := integral_Ioo_eq_integral_laguerreKernel b (a - 1) f hS
  have hDs := integral_Ioo_eq_integral_laguerreKernel b (a - 1) (fun _ => (1 : ℂ)) hS
  have hexp : (((S + a : ℝ) : ℂ)) - 1 = ((S + (a - 1) : ℝ) : ℂ) := by push_cast; ring
  have hNint : ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (((S + a : ℝ) : ℂ) - 1) * (1 - u : ℂ) ^ (b - 1) *
      ((u : ℂ) * X + (1 - u : ℂ) * (X + S)) ^ (-(a : ℂ)) =
      ∫ u in Ioo (0 : ℝ) 1, f ((1 - u) * S) * ((u ^ (S + (a - 1)) : ℝ) : ℂ) *
        ((1 - u : ℝ) : ℂ) ^ (b - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have h1 : (u : ℂ) * X + (1 - u : ℂ) * (X + S) = X + ((max ((1 - u) * S) 0 : ℝ) : ℂ) := by
      rw [max_eq_left (mul_nonneg (by linarith [hu.2]) hS.le)]; push_cast; ring
    rw [h1, hexp, ← Complex.ofReal_cpow hu.1.le]
    simp only [f]; push_cast; ring
  have hDint : betaIntegral (((S + a : ℝ) : ℂ)) b = ∫ u in Ioo (0 : ℝ) 1, (fun _ : ℝ => (1 : ℂ))
      ((1 - u) * S) * ((u ^ (S + (a - 1)) : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ) ^ (b - 1) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [hexp, ← Complex.ofReal_cpow hu.1.le]
    push_cast; ring
  simp only [Pi.div_apply]
  rw [hNint, ← hNs, ← hDs, ← hDint]
  have hs0 : (S : ℂ) ^ b ≠ 0 := (cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast hS.ne'))
  have hB0 : betaIntegral (((S + a : ℝ) : ℂ)) b ≠ 0 := by
    intro h; rw [h, mul_zero] at hBeta
    exact mul_ne_zero (Gamma_ne_zero_of_re_pos hA) (Gamma_ne_zero_of_re_pos hb) hBeta
  have hG : Gamma (((S + a : ℝ) : ℂ) + b) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re] at hA ⊢; linarith)
  rw [hBeta]
  field_simp
  simp only [mul_comm S]

/-! ### The Hermite function of the second kind -/

/-- Homogeneity of the integer-power average: scaling both nodes by `λ` multiplies the average
of `w^m` by `λ^m`. -/
theorem regCarlsonDirichletAverage_pair_mul_zpow (p q c y₁ y₂ : ℂ) (m : ℤ) :
    regCarlsonDirichletAverage (TwoVariable.pair p q) (TwoVariable.pair (c * y₁) (c * y₂))
        (fun w => w ^ m) =
      c ^ m * regCarlsonDirichletAverage (TwoVariable.pair p q) (TwoVariable.pair y₁ y₂)
        (fun w => w ^ m) := by
  rw [TwoVariable.regCarlsonDirichletAverage_pair_eq,
      TwoVariable.regCarlsonDirichletAverage_pair_eq,
    Dirichlet.regEulerIntegral, Dirichlet.regEulerIntegral, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr 1; funext u
  rw [show (u : ℂ) * (c * y₁) + (1 - u : ℂ) * (c * y₂) = c * ((u : ℂ) * y₁ + (1 - u : ℂ) * y₂) by
    ring, mul_zpow]
  ring

/-- For `re z > 0`, `(z²)^c = z^{2c}`. -/
theorem sq_cpow_of_re_pos {z : ℂ} (hz : 0 < z.re) (c : ℂ) : (z ^ 2) ^ c = z ^ (2 * c) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have harg : |arg z| < π / 2 := by
    rw [abs_lt]
    have := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    exact abs_lt.mp this
  rw [pow_two, cpow_def_of_ne_zero (mul_ne_zero hz0 hz0), cpow_def_of_ne_zero hz0,
    log_mul hz0 hz0 (by constructor <;> linarith [(abs_lt.mp harg).1, (abs_lt.mp harg).2])]
  ring_nf

/-- **Carlson's monic Hermite function of the second kind** (Definition 7.10-2):
`q̃ₙ(x) = x^{-n-1} ₂F₀((1 + n)/2, 1 + n/2; 1/x²)` for `x ∉ ℝ`. -/
def monicHermiteSecondKind (n : ℕ) (x : ℂ) : ℂ :=
  x ^ (-((n : ℤ) + 1)) *
    carlson2F0Sector (((n + 1 : ℝ) / 2 : ℝ) : ℂ) (1 + n / 2) (log (-x ^ 2)⁻¹)

/-- **The Hermite function of the second kind as a confluent limit** (Carlson (7.10-3)): for
`x ∉ ℝ`, `R_{-n-1}(1 + s² + n, 1 + s² + n; x + s, x - s) → q̃ₙ(x)` as `s → ∞`. Here `R_{-n-1}` is
Carlson's average of `w^{-n-1}`, written as `Γ(c)` times the regularized Dirichlet average. -/
theorem tendsto_hermiteSecondKind (n : ℕ) {x : ℂ} (hx : x.im ≠ 0) :
    Tendsto (fun s : ℝ => Gamma ((1 + (s : ℂ) ^ 2 + n) + (1 + (s : ℂ) ^ 2 + n)) *
        regCarlsonDirichletAverage (TwoVariable.pair (1 + (s : ℂ) ^ 2 + n) (1 + (s : ℂ) ^ 2 + n))
          (TwoVariable.pair (x + s) (x - s)) (fun w => w ^ (-((n : ℤ) + 1))))
      atTop (𝓝 (monicHermiteSecondKind n x)) := by
  set a : ℝ := (n + 1 : ℝ) / 2
  have ha : 0 < a := by positivity
  set b : ℂ := 1 + n / 2
  have hb : 0 < b.re := by simp [b]; positivity
  -- the rotation `ω` with `ω² = -1` and `re (ω x) > 0`
  obtain ⟨ω, hω2, hωx⟩ : ∃ ω : ℂ, ω ^ 2 = -1 ∧ 0 < (ω * x).re := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨I, by simp, by simp; linarith⟩
    · exact ⟨-I, by simp, by simpa using h⟩
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω2
  set X : ℂ := -x ^ 2
  have hXω : X = (ω * x) ^ 2 := by simp only [X]; rw [mul_pow, hω2]; ring
  have hX : X ∈ slitPlane := by
    rw [hXω]; exact sq_mem_slitPlane_of_re_pos hωx
  have hlim := (tendsto_regCarlsonDirichletAverage_shift ha hb hX).comp
    (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0) : Tendsto (fun s : ℝ => s ^ 2) atTop atTop)
  have hlim' := hlim.const_mul (ω⁻¹ ^ (-((n : ℤ) + 1)))
  -- the value of the limit
  have hval : ω⁻¹ ^ (-((n : ℤ) + 1)) * (X ^ (-(a : ℂ)) * carlson2F0Sector a b (log X⁻¹)) =
      monicHermiteSecondKind n x := by
    rw [monicHermiteSecondKind, hXω, sq_cpow_of_re_pos hωx,
      show 2 * (-(a : ℂ)) = (((-((n : ℤ) + 1)) : ℤ) : ℂ) by simp only [a]; push_cast; ring,
      cpow_intCast, ← mul_assoc, ← mul_zpow, inv_mul_cancel_left₀ hω0, ← hXω]
  rw [hval] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  simp only [Function.comp_apply]
  set β : ℂ := 1 + (s : ℂ) ^ 2 + n
  have hβ : 0 < β.re := by
    simp only [β, add_re, one_re, natCast_re, ← ofReal_pow, ofReal_re]; positivity
  -- rotate the nodes into the right half-plane
  have hrot : TwoVariable.pair (x + s) (x - s) =
      TwoVariable.pair (ω⁻¹ * (ω * (x + s))) (ω⁻¹ * (ω * (x - s))) := by
    rw [inv_mul_cancel_left₀ hω0, inv_mul_cancel_left₀ hω0]
  have hωre : ω.re = 0 := by
    have h1 := congrArg re hω2
    have h2 := congrArg im hω2
    simp only [pow_two, mul_re, mul_im, neg_re, one_re, neg_im, one_im, neg_zero] at h1 h2
    by_contra hne
    have him : ω.im = 0 := by
      have : ω.re * ω.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hne
    rw [him] at h1
    nlinarith [sq_nonneg ω.re]
  have hre1 : 0 < (ω * (x + s)).re := by
    have : (ω * (x + s)).re = (ω * x).re + s * ω.re := by simp [mul_add, mul_re]; ring
    rw [this, hωre, mul_zero, add_zero]; exact hωx
  have hre2 : 0 < (ω * (x - s)).re := by
    have : (ω * (x - s)).re = (ω * x).re - s * ω.re := by simp [mul_sub, mul_re]; ring
    rw [this, hωre, mul_zero, sub_zero]; exact hωx
  rw [hrot, regCarlsonDirichletAverage_pair_mul_zpow]
  -- the integer-power average is the R-function on right-half-plane nodes
  have hbβ : TwoVariable.pair β β ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i <;> exact hβ
  have hz : TwoVariable.pair (ω * (x + s)) (ω * (x - s)) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hre1
    · exact hre2
  have hR1 : regCarlsonDirichletAverage (TwoVariable.pair β β)
      (TwoVariable.pair (ω * (x + s)) (ω * (x - s))) (fun w => w ^ (-((n : ℤ) + 1))) =
      regCarlsonR (2 * (-(a : ℂ))) (TwoVariable.pair β β)
        (TwoVariable.pair (ω * (x + s)) (ω * (x - s))) := by
    rw [regCarlsonR_eq_regCarlsonRIntegral _ hbβ hz, regCarlsonRIntegral]
    congr 1; funext w
    rw [show 2 * (-(a : ℂ)) = (((-((n : ℤ) + 1)) : ℤ) : ℂ) by simp only [a]; push_cast; ring,
      cpow_intCast]
  rw [hR1, TwoVariable.regRSlit_firstQuadratic _ β _ _ hre1 hre2]
  -- identify the transformed nodes and parameters
  have hA : TwoVariable.arithmeticMeanSq (ω * (x + s)) (ω * (x - s)) = X := by
    simp only [TwoVariable.arithmeticMeanSq, X]
    rw [show (ω * (x + s) + ω * (x - s)) / 2 = ω * x by ring, mul_pow, hω2]; ring
  have hG : TwoVariable.geometricMeanSq (ω * (x + s)) (ω * (x - s)) = X + ((s ^ 2 : ℝ) : ℂ) := by
    simp only [TwoVariable.geometricMeanSq, X]
    rw [show ω * (x + s) * (ω * (x - s)) = ω ^ 2 * (x ^ 2 - (s : ℂ) ^ 2) by ring, hω2]
    push_cast; ring
  have hp1 : β + -(a : ℂ) = (((s ^ 2 + a : ℝ)) : ℂ) := by simp only [β, a]; push_cast; ring
  have hp2 : (1 / 2 : ℂ) - -(a : ℂ) = b := by simp only [b, a]; push_cast; ring
  rw [hA, hG, hp1, hp2]
  -- the Gamma normalizations
  have hΓ := TwoVariable.Gamma_mul_quadraticGammaRatio hβ
  have hsum : β + 1 / 2 = ((s ^ 2 + a : ℝ) : ℂ) + b := by simp only [β, a, b]; push_cast; ring
  rw [hsum] at hΓ
  -- native agreement for the transformed R-function
  have hbconv : TwoVariable.pair (((s ^ 2 + a : ℝ)) : ℂ) b ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i
    · show 0 < (((s ^ 2 + a : ℝ)) : ℂ).re; rw [ofReal_re]; nlinarith [sq_nonneg s]
    · exact hb
  have hhull : convexHull ℝ (Set.range (TwoVariable.pair X (X + ((s ^ 2 : ℝ) : ℂ)))) ⊆
      slitPlane := by
    have h : Set.range (TwoVariable.pair X (X + ((s ^ 2 : ℝ) : ℂ))) =
        {X, X + ((s ^ 2 : ℝ) : ℂ)} := by
      ext w; simp [TwoVariable.pair, Matrix.range_cons, Matrix.range_empty, or_comm]
    rw [h, convexHull_pair]
    rintro w ⟨p, q, hp, hq, hpq, rfl⟩
    obtain rfl : p = 1 - q := by linarith
    rw [show (1 - q) • X + q • (X + ((s ^ 2 : ℝ) : ℂ)) = X + ((q * s ^ 2 : ℝ) : ℂ) by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring]
    exact add_ofReal_mem_slitPlane hX (by positivity)
  rw [regCarlsonR_eq_regCarlsonRIntegral_of_convexHull _ hbconv hhull, regCarlsonRIntegral]
  rw [← hΓ]
  ring

/-- **The Hermite limit for Carlson's `R_{-n-1}`** (Carlson (7.10-3)): for `x ∉ ℝ`,
`R_{-n-1}(1 + s² + n, 1 + s² + n; x + s, x - s) → q̃ₙ(x)` as `s → ∞`. -/
theorem tendsto_carlsonR_hermiteSecondKind (n : ℕ) {x : ℂ} (hx : x.im ≠ 0) :
    Tendsto (fun s : ℝ => carlsonR (-((n : ℂ) + 1))
        (TwoVariable.pair (1 + (s : ℂ) ^ 2 + n) (1 + (s : ℂ) ^ 2 + n))
        (TwoVariable.pair (x + s) (x - s))) atTop (𝓝 (monicHermiteSecondKind n x)) := by
  refine (tendsto_hermiteSecondKind n hx).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  set β : ℂ := 1 + (s : ℂ) ^ 2 + n
  have hβ : 0 < β.re := by
    simp only [β, add_re, one_re, natCast_re, ← ofReal_pow, ofReal_re]; positivity
  have hb : TwoVariable.pair β β ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i <;> exact hβ
  have hhull : convexHull ℝ (Set.range (TwoVariable.pair (x + s) (x - s))) ⊆ slitPlane := by
    have h : Set.range (TwoVariable.pair (x + s) (x - s)) = {x + s, x - s} := by
      ext w; simp [TwoVariable.pair, Matrix.range_cons, Matrix.range_empty, or_comm]
    rw [h, convexHull_pair]
    rintro w ⟨p, q, hp, hq, hpq, rfl⟩
    refine mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [add_im, smul_im, sub_im, ofReal_im, add_zero, sub_zero, smul_eq_mul]
    rw [← add_mul, hpq, one_mul]; exact hx
  rw [carlsonR_eq_carlsonRIntegral_of_convexHull _ hb hhull, carlsonRIntegral, regCarlsonRIntegral,
    TwoVariable.sum_pair]
  congr 2
  funext w
  rw [show (-((n : ℂ) + 1)) = ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring, cpow_intCast]

end Carlson
