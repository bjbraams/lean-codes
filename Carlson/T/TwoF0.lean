/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.Gamma
public import ToMathlib.Analysis.SpecialFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.DominatedIntegral

/-!
# Carlson's `₂F₀` function and its asymptotic expansion

Carlson's Section 5.12 defines `₂F₀(α, β; x)` by the double Euler integral
`∫∫ e^{s t x} dλ_α(s) dλ_β(t)` (Definition 5.12-3), where `dλ_a(s) = Γ(a)⁻¹ s^{a-1} e^{-s} ds`
is the Euler measure on `(0, ∞)`, and continues it to all parameters through the remainder
representation (5.12-10)
`₂F₀(α, β; x) = ∑_{m<n} (α)ₘ (β)ₘ xᵐ/m! + (α)ₙ (β)ₙ xⁿ/n! ∫∫ Eₙ(s t x) dλ_{α+n}(s) dλ_{β+n}(t)`,
where `Eₙ(y) = S(1, n; y, 0)` is the Taylor remainder factor of the exponential. Here the
continuation is defined by this representation with enough explicit terms, for `re x ≤ 0`; its
independence of `n` follows from the recursion `Eₙ = 1 + y Eₙ₊₁/(n+1)` and the moment identity
`s dλ_a(s) = a dλ_{a+1}(s)`.

Holomorphy of the representation in `(α, β, x)` follows from dominated differentiation under
the integral, which gives Theorem 5.12-4. The representation is symmetric in `α, β`, which
gives Theorem 5.12-2, and it bounds the error
of the partial sums of the divergent `₂F₀` series: Theorem 5.12-7 in the half-plane
`re x ≤ 0`, the asymptotic expansion (5.12-17) there, and Theorem 5.12-5 for real parameters.

## Main definitions

* `Carlson.expRemainder`: the remainder factor `Eₙ(y) = S(1, n; y, 0)`.
* `Carlson.eulerDensity`: the density of Carlson's Euler measure.
* `Carlson.twoF0Term`, `Carlson.twoF0Double`, `Carlson.twoF0Rep`: the terms of the `₂F₀`
  series, the remainder double integral, and the representation (5.12-10).
* `Carlson.carlson2F0`: the continued `₂F₀` function on `re x ≤ 0`.

## Main results

* `Carlson.carlson2F0_eq_twoF0Rep`: the representation (5.12-10) with any admissible `n`.
* `Carlson.analyticOnNhd_carlson2F0`: Theorem 5.12-4, holomorphy in `(α, β, x)` on
  `ℂ² × {re x < 0}`.
* `Carlson.carlson2F0_comm`: Theorem 5.12-2 (symmetry in the parameters).
* `Carlson.carlson2F0_eq_double`, `Carlson.carlson2F0_eq_integral`: formulas (5.12-6) and
  (5.12-7) for parameters with positive real parts.
* `Carlson.norm_carlson2F0_sub_sum_le`: the error bound (5.12-15) with `φ = 0`.
* `Carlson.exists_norm_carlson2F0_sub_sum_le`: the asymptotic expansion (5.12-17) in the
  half-plane.
* `Carlson.carlson2F0_sub_sum_eq_mul_of_real`: Theorem 5.12-5.

## Implementation notes

The function is defined for `re x ≤ 0`; outside this half-plane the definition carries no
meaning. Carlson's continuation to the sector `|ph(-x)| < 3π/2` by rotating the rays of
integration (Theorem 5.12-6), the bounds (5.12-15), (5.12-16) with `φ ≠ 0`, and the
connection formulas with the S-function (5.12-18), (5.12-20) are not formalized here.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Topology

namespace Carlson

/-- The Taylor remainder factor of the exponential, `Eₙ(y) = S(1, n; y, 0)`:
`E₀(y) = eʸ` and `Eₙ(y) = n ∫₀¹ e^{uy} (1-u)^{n-1} du`, so that
`eʸ = ∑_{m<n} yᵐ/m! + yⁿ/n! Eₙ(y)` (Carlson (5.12-8)). -/
def expRemainder : ℕ → ℂ → ℂ
  | 0, y => exp y
  | n + 1, y => (n + 1) * ∫ u in (0 : ℝ)..1, exp (u * y) * (1 - (u : ℂ)) ^ n

/-- The recursion `Eₙ(y) = 1 + y Eₙ₊₁(y) / (n + 1)`. -/
theorem expRemainder_eq_one_add (n : ℕ) (y : ℂ) :
    expRemainder n y = 1 + y * expRemainder (n + 1) y / (n + 1) := by
  rcases n with _ | n
  · -- `eʸ = 1 + y ∫₀¹ e^{uy} du`
    simp only [expRemainder, CharP.cast_eq_zero, zero_add, pow_zero, mul_one, one_mul, div_one]
    have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => exp (u * y)) (y * exp (u * y)) u :=
      fun u _ => by
        have := ((hasDerivAt_id (u : ℂ)).mul_const y).cexp.comp_ofReal
        simpa [mul_comm] using this
    have hint := integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u : ℝ => y * exp (u * y)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul] at hint
    simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, exp_zero] at hint
    linear_combination (-1 : ℂ) * hint
  · -- integration by parts
    simp only [expRemainder]
    have hu : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => exp (u * y)) (y * exp (u * y)) u :=
      fun u _ => by
        have := ((hasDerivAt_id (u : ℂ)).mul_const y).cexp.comp_ofReal
        simpa [mul_comm] using this
    have hv : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => -(1 - (u : ℂ)) ^ (n + 1) / (n + 1))
        ((1 - (u : ℂ)) ^ n) u := fun u _ => by
      have h0 : HasDerivAt (fun u : ℝ => (1 - (u : ℂ))) (-1) u := by
        simpa using ((hasDerivAt_id (u : ℂ)).const_sub 1).comp_ofReal
      have h1 := (h0.pow (n + 1)).neg.div_const ((n : ℂ) + 1)
      convert h1 using 1
      have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
    have hibp := integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun u : ℝ => y * exp (u * y)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun u : ℝ => (1 - (u : ℂ)) ^ n).intervalIntegrable 0 1)
    simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, exp_zero, sub_self, zero_pow
      (Nat.succ_ne_zero n), neg_zero, zero_div, mul_zero, sub_zero, one_pow] at hibp
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : ((n : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    rw [hibp]
    have hmul : (∫ u in (0 : ℝ)..1, y * exp (u * y) * (-(1 - (u : ℂ)) ^ (n + 1) / (n + 1))) =
        -(y / (n + 1)) * ∫ u in (0 : ℝ)..1, exp (u * y) * (1 - (u : ℂ)) ^ (n + 1) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext u; ring
    rw [hmul]
    push_cast
    field_simp
    ring

/-- For `re y ≤ 0`, `‖Eₙ(y)‖ ≤ 1`. -/
theorem norm_expRemainder_le (n : ℕ) {y : ℂ} (hy : y.re ≤ 0) : ‖expRemainder n y‖ ≤ 1 := by
  rcases n with _ | n
  · simp only [expRemainder, norm_exp]
    exact Real.exp_le_one_iff.mpr hy
  · simp only [expRemainder]
    have hb : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
        ‖exp (u * y) * (1 - (u : ℂ)) ^ n‖ ≤ (1 - u) ^ n := by
      intro u hu
      rw [norm_mul, norm_exp, norm_pow, show (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith [hu.2])]
      have : (↑u * y).re ≤ 0 := by
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hu.1.le hy
      have he := Real.exp_le_one_iff.mpr this
      have hp : 0 ≤ (1 - u) ^ n := pow_nonneg (by linarith [hu.2]) n
      nlinarith
    have hI := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall hb)
      ((by fun_prop : Continuous fun u : ℝ => (1 - u) ^ n).intervalIntegrable (μ := volume) 0 1)
    have hval : ∫ u in (0 : ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => u ^ n)]
      simp [integral_pow]
    rw [hval] at hI
    rw [norm_mul]
    have : ‖((n : ℂ) + 1)‖ = n + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
    rw [this]
    calc ((n : ℝ) + 1) * ‖∫ u in (0 : ℝ)..1, exp (u * y) * (1 - (u : ℂ)) ^ n‖
        ≤ (n + 1) * (1 / (n + 1)) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 1 := by field_simp


/-- `Eₙ` is continuous. -/
theorem continuous_expRemainder (n : ℕ) : Continuous (expRemainder n) := by
  rcases n with _ | n
  · exact continuous_exp
  · have : expRemainder (n + 1) = fun y => ((n : ℂ) + 1) *
        ∫ u in (0 : ℝ)..1, exp (u * y) * (1 - (u : ℂ)) ^ n := by
      funext y; rfl
    rw [this]
    refine continuous_const.mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 1

/-! ### Euler measures -/

/-- The density of Carlson's Euler measure `dλ_a(s) = Γ(a)⁻¹ s^{a-1} e^{-s} ds` on `(0, ∞)`. -/
def eulerDensity (a : ℂ) (s : ℝ) : ℂ :=
  (Gamma a)⁻¹ * ((s : ℂ) ^ (a - 1) * exp (-(s : ℂ)))

/-- The Euler density is integrable on `(0, ∞)` when `re a > 0`. -/
theorem integrableOn_eulerDensity {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (eulerDensity a) (Ioi 0) := by
  have h := Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi (a := a) (w := 1) ha (by simp)
  refine IntegrableOn.congr_fun (Integrable.const_mul h (Gamma a)⁻¹) (fun s _ => ?_)
    measurableSet_Ioi
  simp [eulerDensity]

/-- The Euler measure is a probability measure: `∫ dλ_a = 1`. -/
theorem integral_eulerDensity {a : ℂ} (ha : 0 < a.re) :
    ∫ s in Ioi (0 : ℝ), eulerDensity a s = 1 := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (a := a) (w := 1) ha (by simp)
  simp only [one_cpow, one_mul, mul_one] at h
  simp only [eulerDensity]
  rw [MeasureTheory.integral_const_mul, h, inv_mul_cancel₀ (Gamma_ne_zero_of_re_pos ha)]

/-- The Laplace transform of the Euler measure: `∫ e^{sw} dλ_a(s) = (1 - w)^{-a}` for
`re w < 1`. -/
theorem integral_eulerDensity_mul_exp {a : ℂ} (ha : 0 < a.re) {w : ℂ} (hw : w.re < 1) :
    ∫ s in Ioi (0 : ℝ), eulerDensity a s * exp (s * w) = (1 - w) ^ (-a) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (a := a) (w := 1 - w) ha
    (by simp; linarith)
  simp only [eulerDensity]
  have hΓ := Gamma_ne_zero_of_re_pos ha
  have : ∫ s in Ioi (0 : ℝ), (Gamma a)⁻¹ * ((s : ℂ) ^ (a - 1) * exp (-(s : ℂ))) * exp (s * w) =
      ∫ s in Ioi (0 : ℝ), (Gamma a)⁻¹ * ((s : ℂ) ^ (a - 1) * exp (-(s : ℂ) * (1 - w))) := by
    congr 1; funext s
    rw [show -(s : ℂ) * (1 - w) = -(s : ℂ) + s * w by ring, exp_add]; ring
  rw [this, MeasureTheory.integral_const_mul, h]
  field_simp

/-- Multiplying the Euler density by the variable raises its order:
`s dλ_a(s) = a dλ_{a+1}(s)`. -/
theorem mul_eulerDensity {a : ℂ} (ha : 0 < a.re) {s : ℝ} (hs : 0 < s) :
    (s : ℂ) * eulerDensity a s = a * eulerDensity (a + 1) s := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [eulerDensity]
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [Gamma_add_one a ha0, add_sub_cancel_right]
  rw [cpow_sub _ _ hs0, cpow_one]
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  field_simp

/-- The total variation of the Euler measure: `∫ ‖dλ_a‖ = Γ(re a) / ‖Γ(a)‖`. -/
theorem integral_norm_eulerDensity {a : ℂ} (ha : 0 < a.re) :
    ∫ s in Ioi (0 : ℝ), ‖eulerDensity a s‖ = Real.Gamma a.re / ‖Gamma a‖ := by
  have hfun : ∀ s ∈ Ioi (0 : ℝ), ‖eulerDensity a s‖ = ‖Gamma a‖⁻¹ * (Real.exp (-s) * s ^ (a.re - 1)) := by
    intro s hs
    simp only [eulerDensity, norm_mul, norm_inv]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
    simp only [sub_re, one_re]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, MeasureTheory.integral_const_mul,
    Real.Gamma_eq_integral ha]
  field_simp



/-! ### The remainder representation -/

/-- The product of two Euler measures on the quadrant. -/
abbrev quadrantMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

/-- The double Euler integral of the remainder factor in Carlson's representation (5.12-10):
`∫∫ Eₙ(s t x) dλ_{α+n}(s) dλ_{β+n}(t)`. -/
def twoF0Double (n : ℕ) (α β x : ℂ) : ℂ :=
  ∫ p, eulerDensity (α + n) p.1 * eulerDensity (β + n) p.2 * expRemainder n (p.1 * p.2 * x)
    ∂quadrantMeasure

/-- The `m`-th term `(α)ₘ (β)ₘ xᵐ / m!` of the divergent `₂F₀` series. -/
def twoF0Term (m : ℕ) (α β x : ℂ) : ℂ :=
  (ascPochhammer ℂ m).eval α * (ascPochhammer ℂ m).eval β * x ^ m / m.factorial

/-- Carlson's representation (5.12-10) with `n` explicit terms:
`∑_{m<n} (α)ₘ (β)ₘ xᵐ/m! + (α)ₙ (β)ₙ xⁿ/n! ∫∫ Eₙ(s t x) dλ_{α+n}(s) dλ_{β+n}(t)`. -/
def twoF0Rep (n : ℕ) (α β x : ℂ) : ℂ :=
  ∑ m ∈ Finset.range n, twoF0Term m α β x + twoF0Term n α β x * twoF0Double n α β x

/-- Almost every point of the quadrant measure has positive coordinates. -/
theorem ae_quadrantMeasure : ∀ᵐ p ∂quadrantMeasure, 0 < p.1 ∧ 0 < p.2 := by
  rw [quadrantMeasure, Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod
    measurableSet_Ioi)]
  exact Eventually.of_forall fun p hp => ⟨hp.1, hp.2⟩

/-- A continuous kernel bounded on the quadrant is integrable against two Euler measures. -/
theorem integrable_eulerDensity_mul_kernel {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {K : ℝ × ℝ → ℂ} (hK : Continuous K) {C : ℝ}
    (hC : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → ‖K p‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => eulerDensity a p.1 * eulerDensity b p.2 * K p) quadrantMeasure := by
  have h := Integrable.mul_prod (integrableOn_eulerDensity ha) (integrableOn_eulerDensity hb)
  refine h.mul_bdd (c := C) hK.aestronglyMeasurable ?_
  filter_upwards [ae_quadrantMeasure] with p hp using hC p hp.1 hp.2

/-- The remainder kernel is bounded by one on the quadrant when `re x ≤ 0`. -/
theorem norm_expRemainder_mul_le (n : ℕ) {x : ℂ} (hx : x.re ≤ 0) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : ‖expRemainder n (s * t * x)‖ ≤ 1 := by
  refine norm_expRemainder_le n ?_
  have : ((s : ℂ) * t * x).re = s * t * x.re := by simp [mul_re]
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx

/-- The double integral of the product of two Euler densities is one. -/
theorem integral_eulerDensity_mul_eulerDensity {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ p, eulerDensity a p.1 * eulerDensity b p.2 ∂quadrantMeasure = 1 := by
  rw [quadrantMeasure, integral_prod_mul, integral_eulerDensity ha, integral_eulerDensity hb,
    one_mul]

/-- The step `∫∫ Eₙ dλ_{α+n} dλ_{β+n} = 1 + (α+n)(β+n) x/(n+1) ∫∫ Eₙ₊₁ dλ_{α+n+1} dλ_{β+n+1}`. -/
theorem twoF0Double_eq_one_add (n : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    (hx : x.re ≤ 0) :
    twoF0Double n α β x =
      1 + (α + n) * (β + n) * x / (n + 1) * twoF0Double (n + 1) α β x := by
  have hα1 : 0 < (α + (n + 1 : ℕ)).re := by push_cast; simp at hα ⊢; linarith
  have hβ1 : 0 < (β + (n + 1 : ℕ)).re := by push_cast; simp at hβ ⊢; linarith
  have hcast : ∀ γ : ℂ, γ + ((n + 1 : ℕ) : ℂ) = γ + n + 1 := fun γ => by push_cast; ring
  have hI1 := integrable_eulerDensity_mul_kernel hα hβ (K := fun _ => (1 : ℂ))
    continuous_const (C := 1) (fun _ _ _ => by simp)
  have hI2 := integrable_eulerDensity_mul_kernel hα1 hβ1
    (K := fun p => expRemainder (n + 1) (p.1 * p.2 * x))
    ((continuous_expRemainder _).comp (by fun_prop)) (C := 1)
    (fun p hs ht => norm_expRemainder_mul_le _ hx hs ht)
  have hpt : ∀ᵐ p ∂quadrantMeasure,
      eulerDensity (α + n) p.1 * eulerDensity (β + n) p.2 * expRemainder n (p.1 * p.2 * x) =
        eulerDensity (α + n) p.1 * eulerDensity (β + n) p.2 * 1 +
          (α + n) * (β + n) * x / (n + 1) * (eulerDensity (α + (n + 1 : ℕ)) p.1 *
            eulerDensity (β + (n + 1 : ℕ)) p.2 * expRemainder (n + 1) (p.1 * p.2 * x)) := by
    filter_upwards [ae_quadrantMeasure] with p hp
    have h1 := mul_eulerDensity hα hp.1
    have h2 := mul_eulerDensity hβ hp.2
    rw [hcast, hcast]
    rw [expRemainder_eq_one_add n]
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [show ((n + 1 : ℕ) : ℂ) = n + 1 by push_cast; ring] at *
    linear_combination (x / (n + 1) * expRemainder (n + 1) (p.1 * p.2 * x)) *
      (((p.2 : ℂ) * eulerDensity (β + n) p.2) * h1 + ((α + n) * eulerDensity (α + ↑n + 1) p.1) * h2)
  unfold twoF0Double
  rw [integral_congr_ae hpt, integral_add hI1 (hI2.const_mul _), MeasureTheory.integral_const_mul]
  simp only [mul_one]
  rw [integral_eulerDensity_mul_eulerDensity hα hβ]


/-- The representation does not depend on the number of explicit terms. -/
theorem twoF0Rep_succ (n : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    (hx : x.re ≤ 0) : twoF0Rep (n + 1) α β x = twoF0Rep n α β x := by
  unfold twoF0Rep
  rw [twoF0Double_eq_one_add n hα hβ hx, Finset.sum_range_succ]
  have hterm : twoF0Term (n + 1) α β x =
      twoF0Term n α β x * ((α + n) * (β + n) * x / (n + 1)) := by
    unfold twoF0Term
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
    push_cast
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
  rw [hterm]
  ring

/-- The representation with `n` terms agrees with the representation with `n + k` terms. -/
theorem twoF0Rep_add (n k : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    (hx : x.re ≤ 0) : twoF0Rep (n + k) α β x = twoF0Rep n α β x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, twoF0Rep_succ (n + k) (by push_cast; simp at hα ⊢; linarith)
      (by push_cast; simp at hβ ⊢; linarith) hx, ih]

/-- The number of explicit terms used to define the continued `₂F₀`. -/
def twoF0Depth (α β : ℂ) : ℕ := ⌈|α.re| + |β.re|⌉₊ + 1

/-- The depth makes both shifted parameters lie in the right half-plane. -/
theorem re_add_twoF0Depth_pos (α β : ℂ) :
    0 < (α + twoF0Depth α β).re ∧ 0 < (β + twoF0Depth α β).re := by
  have h := Nat.le_ceil (|α.re| + |β.re|)
  have ha := neg_abs_le α.re
  have hb := neg_abs_le β.re
  have hA := abs_nonneg α.re
  have hB := abs_nonneg β.re
  simp only [twoF0Depth, add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]
  constructor <;> linarith

/-- **Carlson's `₂F₀` function** (Definition 5.12-3, continued by Theorem 5.12-4) for
`re x ≤ 0`: the representation (5.12-10) with enough explicit terms that
`re (α + n), re (β + n) > 0`. -/
def carlson2F0 (α β x : ℂ) : ℂ := twoF0Rep (twoF0Depth α β) α β x

/-- **Formula (5.12-10)**: the continued `₂F₀` has the remainder representation with any `n`
such that `re (α + n), re (β + n) > 0`. -/
theorem carlson2F0_eq_twoF0Rep {n : ℕ} {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    (hx : x.re ≤ 0) : carlson2F0 α β x = twoF0Rep n α β x := by
  unfold carlson2F0
  obtain ⟨hα', hβ'⟩ := re_add_twoF0Depth_pos α β
  rcases le_total n (twoF0Depth α β) with h | h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, twoF0Rep_add n k hα hβ hx]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, twoF0Rep_add _ k hα' hβ' hx]

/-- The double integral is symmetric in the two parameters. -/
theorem twoF0Double_comm (n : ℕ) (α β x : ℂ) : twoF0Double n α β x = twoF0Double n β α x := by
  unfold twoF0Double
  rw [← integral_prod_swap]
  congr 1; funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring_nf

/-- **Theorem 5.12-2** (symmetry): `₂F₀(α, β; x) = ₂F₀(β, α; x)` for `re x ≤ 0`. -/
theorem carlson2F0_comm (α β x : ℂ) (hx : x.re ≤ 0) : carlson2F0 α β x = carlson2F0 β α x := by
  obtain ⟨hα, hβ⟩ := re_add_twoF0Depth_pos α β
  rw [carlson2F0_eq_twoF0Rep hα hβ hx, carlson2F0_eq_twoF0Rep hβ hα hx]
  unfold twoF0Rep twoF0Term
  rw [twoF0Double_comm]
  congr 1
  · exact Finset.sum_congr rfl fun m _ => by ring
  · ring

/-- **Definition 5.12-3**, formula (6): for `re α, re β > 0` and `re x ≤ 0`,
`₂F₀(α, β; x) = ∫∫ e^{s t x} dλ_α(s) dλ_β(t)`. -/
theorem carlson2F0_eq_double {α β x : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hx : x.re ≤ 0) :
    carlson2F0 α β x =
      ∫ p, eulerDensity α p.1 * eulerDensity β p.2 * exp (p.1 * p.2 * x) ∂quadrantMeasure := by
  rw [carlson2F0_eq_twoF0Rep (n := 0) (by simpa using hα) (by simpa using hβ) hx]
  simp [twoF0Rep, twoF0Term, twoF0Double, expRemainder]

/-- **Formula (5.12-7)**: for `re α, re β > 0` and `re x ≤ 0`,
`₂F₀(α, β; x) = ∫ (1 - t x)^{-α} dλ_β(t)`. -/
theorem carlson2F0_eq_integral {α β x : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hx : x.re ≤ 0) :
    carlson2F0 α β x = ∫ t in Ioi (0 : ℝ), eulerDensity β t * (1 - t * x) ^ (-α) := by
  rw [carlson2F0_comm α β x hx, carlson2F0_eq_double hβ hα hx]
  have hI := integrable_eulerDensity_mul_kernel hβ hα
    (K := fun p : ℝ × ℝ => exp (p.1 * p.2 * x)) (by fun_prop) (C := 1)
    (fun p hs ht => by
      rw [norm_exp]; refine Real.exp_le_one_iff.mpr ?_
      have : ((p.1 : ℂ) * p.2 * x).re = p.1 * p.2 * x.re := by simp [mul_re]
      rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx)
  rw [quadrantMeasure, integral_prod _ hI]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only
  rw [show (fun s : ℝ => eulerDensity β t * eulerDensity α s * exp (t * s * x)) =
      fun s => eulerDensity β t * (eulerDensity α s * exp (s * (t * x))) by
    funext s; ring_nf, MeasureTheory.integral_const_mul,
    integral_eulerDensity_mul_exp hα (by
      have : ((t : ℂ) * x).re = t * x.re := by simp [mul_re]
      rw [this]; nlinarith [(mem_Ioi.mp ht).le])]


/-- The remainder double integral is bounded by the total variations of the two Euler
measures. -/
theorem norm_twoF0Double_le (n : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    (hx : x.re ≤ 0) :
    ‖twoF0Double n α β x‖ ≤ Real.Gamma (α + n).re / ‖Gamma (α + n)‖ *
      (Real.Gamma (β + n).re / ‖Gamma (β + n)‖) := by
  unfold twoF0Double
  have hdom : ∀ᵐ p ∂quadrantMeasure, ‖eulerDensity (α + n) p.1 * eulerDensity (β + n) p.2 *
      expRemainder n (p.1 * p.2 * x)‖ ≤ ‖eulerDensity (α + n) p.1‖ * ‖eulerDensity (β + n) p.2‖ := by
    filter_upwards [ae_quadrantMeasure] with p hp
    rw [norm_mul, norm_mul]
    have := norm_expRemainder_mul_le n hx hp.1 hp.2
    have h0 := mul_nonneg (norm_nonneg (eulerDensity (α + n) p.1))
      (norm_nonneg (eulerDensity (β + n) p.2))
    nlinarith
  refine (norm_integral_le_of_norm_le ((integrableOn_eulerDensity hα).norm.mul_prod
    (integrableOn_eulerDensity hβ).norm) hdom).trans (le_of_eq ?_)
  have h := integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioi (0 : ℝ))) (fun s => ‖eulerDensity (α + n) s‖)
    (fun t => ‖eulerDensity (β + n) t‖)
  rw [h, integral_norm_eulerDensity hα, integral_norm_eulerDensity hβ]

/-- **Theorem 5.12-7** in the half-plane `re x ≤ 0` (the case `φ = 0` of (5.12-15)): the error
of the partial sum of the `₂F₀` series is at most the first omitted term times
`Γ(re(α+n)) Γ(re(β+n)) / |Γ(α+n) Γ(β+n)|`, whenever `re (α + n), re (β + n) > 0`. -/
theorem norm_carlson2F0_sub_sum_le (n : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) (hx : x.re ≤ 0) :
    ‖carlson2F0 α β x - ∑ m ∈ Finset.range n, twoF0Term m α β x‖ ≤
      ‖twoF0Term n α β x‖ * (Real.Gamma (α + n).re / ‖Gamma (α + n)‖ *
        (Real.Gamma (β + n).re / ‖Gamma (β + n)‖)) := by
  rw [carlson2F0_eq_twoF0Rep hα hβ hx, twoF0Rep, add_sub_cancel_left, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_twoF0Double_le n hα hβ hx) (norm_nonneg _)

/-- **The asymptotic expansion (5.12-17)** in the half-plane `re x ≤ 0`: for every `n` the error
of the `n`-th partial sum of the `₂F₀` series is `O(|x|ⁿ)` as `x → 0`. -/
theorem exists_norm_carlson2F0_sub_sum_le (α β : ℂ) (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℂ, x.re ≤ 0 → ‖x‖ ≤ 1 →
      ‖carlson2F0 α β x - ∑ m ∈ Finset.range n, twoF0Term m α β x‖ ≤ C * ‖x‖ ^ n := by
  set N := n + twoF0Depth α β
  obtain ⟨hα0, hβ0⟩ := re_add_twoF0Depth_pos α β
  have hαN : 0 < (α + N).re := by simp only [N, add_re, natCast_re, Nat.cast_add] at hα0 ⊢; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβN : 0 < (β + N).re := by simp only [N, add_re, natCast_re, Nat.cast_add] at hβ0 ⊢; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set c : ℕ → ℝ := fun m => ‖(ascPochhammer ℂ m).eval α * (ascPochhammer ℂ m).eval β‖ / m.factorial
  set K := Real.Gamma (α + N).re / ‖Gamma (α + N)‖ * (Real.Gamma (β + N).re / ‖Gamma (β + N)‖)
  refine ⟨∑ m ∈ Finset.Ico n N, c m + c N * K, fun x hx hx1 => ?_⟩
  have hterm : ∀ m, ‖twoF0Term m α β x‖ = c m * ‖x‖ ^ m := fun m => by
    simp only [twoF0Term, c, norm_div, norm_mul, norm_pow, Complex.norm_natCast]; ring
  have hpow : ∀ m, n ≤ m → ‖x‖ ^ m ≤ ‖x‖ ^ n := fun m hm =>
    pow_le_pow_of_le_one (norm_nonneg _) hx1 hm
  have hc : ∀ m, 0 ≤ c m := fun m => by positivity
  have hK : 0 ≤ K := by positivity
  have hsplit : carlson2F0 α β x - ∑ m ∈ Finset.range n, twoF0Term m α β x =
      ∑ m ∈ Finset.Ico n N, twoF0Term m α β x +
        (carlson2F0 α β x - ∑ m ∈ Finset.range N, twoF0Term m α β x) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ N by simp [N])]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ m ∈ Finset.Ico n N, twoF0Term m α β x‖ ≤ (∑ m ∈ Finset.Ico n N, c m) * ‖x‖ ^ n := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [hterm]
    exact mul_le_mul_of_nonneg_left (hpow m (Finset.mem_Ico.mp hm).1) (hc m)
  have h2 := norm_carlson2F0_sub_sum_le N hαN hβN hx
  rw [hterm] at h2
  have h3 : c N * ‖x‖ ^ N * K ≤ c N * K * ‖x‖ ^ n := by
    have := mul_le_mul_of_nonneg_left (hpow N (by simp [N])) (mul_nonneg (hc N) hK)
    calc c N * ‖x‖ ^ N * K = c N * K * ‖x‖ ^ N := by ring
      _ ≤ c N * K * ‖x‖ ^ n := this
  nlinarith

/-- The remainder factor is real and in `(0, 1]` at real nonpositive arguments. -/
theorem expRemainder_ofReal_mem (n : ℕ) {y : ℝ} (hy : y ≤ 0) :
    ∃ q : ℝ, expRemainder n y = q ∧ 0 < q ∧ q ≤ 1 := by
  rcases n with _ | n
  · refine ⟨Real.exp y, by simp [expRemainder, ofReal_exp], Real.exp_pos _,
      Real.exp_le_one_iff.mpr hy⟩
  · set g : ℝ → ℝ := fun u => Real.exp (u * y) * (1 - u) ^ n
    refine ⟨(n + 1) * ∫ u in (0 : ℝ)..1, g u, ?_, ?_, ?_⟩
    · simp only [expRemainder, g]
      push_cast
      congr 1
      rw [← intervalIntegral.integral_ofReal]
      congr 1; funext u; push_cast; rfl
    · have hpos : 0 < ∫ u in (0 : ℝ)..1, g u := by
        refine intervalIntegral.intervalIntegral_pos_of_pos_on
          ((by fun_prop : Continuous g).intervalIntegrable 0 1) (fun u hu => ?_) zero_lt_one
        exact mul_pos (Real.exp_pos _) (pow_pos (by linarith [hu.2]) n)
      positivity
    · have hle : ∫ u in (0 : ℝ)..1, g u ≤ ∫ u in (0 : ℝ)..1, (1 - u) ^ n := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous g).intervalIntegrable 0 1)
          ((by fun_prop : Continuous fun u : ℝ => (1 - u) ^ n).intervalIntegrable 0 1)
          fun u hu => ?_
        have h1 : Real.exp (u * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
        have h2 : 0 ≤ (1 - u) ^ n := pow_nonneg (by linarith [hu.2]) n
        nlinarith
      have hval : ∫ u in (0 : ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
        rw [intervalIntegral.integral_comp_sub_left (fun u => u ^ n)]
        simp [integral_pow]
      rw [hval] at hle
      have : ((n : ℝ) + 1) * ∫ u in (0 : ℝ)..1, g u ≤ (n + 1) * (1 / (n + 1)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      rw [show ((n : ℝ) + 1) * (1 / (n + 1)) = 1 by field_simp] at this
      exact this


/-- For real order the Euler density is real on the positive axis. -/
theorem eulerDensity_ofReal (a : ℝ) {s : ℝ} (hs : 0 < s) :
    eulerDensity a s = ((Real.Gamma a)⁻¹ * (s ^ (a - 1) * Real.exp (-s)) : ℝ) := by
  simp only [eulerDensity]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hs.le,
    Complex.Gamma_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  push_cast; ring

/-- **Theorem 5.12-5** (real parameters): if `α + n, β + n > 0` and `x ≤ 0` are real, the error
of the `n`-th partial sum of the `₂F₀` series is the first omitted term times a factor in
`(0, 1]`; in particular it has the same sign and at most the same size. -/
theorem carlson2F0_sub_sum_eq_mul_of_real (n : ℕ) {α β x : ℝ} (hα : 0 < α + n)
    (hβ : 0 < β + n) (hx : x ≤ 0) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      carlson2F0 α β x - ∑ m ∈ Finset.range n, twoF0Term m α β x = q * twoF0Term n α β x := by
  have hα' : 0 < ((α : ℂ) + n).re := by simpa using hα
  have hβ' : 0 < ((β : ℂ) + n).re := by simpa using hβ
  have hx' : ((x : ℂ)).re ≤ 0 := by simpa using hx
  rw [carlson2F0_eq_twoF0Rep hα' hβ' hx', twoF0Rep, add_sub_cancel_left]
  -- the double integral is real and in `(0, 1]`
  set a : ℝ := α + n
  set b : ℝ := β + n
  have hac : (α : ℂ) + n = (a : ℂ) := by simp [a]
  have hbc : (β : ℂ) + n = (b : ℂ) := by simp [b]
  set dA : ℝ → ℝ := fun s => (Real.Gamma a)⁻¹ * (s ^ (a - 1) * Real.exp (-s))
  set dB : ℝ → ℝ := fun s => (Real.Gamma b)⁻¹ * (s ^ (b - 1) * Real.exp (-s))
  set g : ℝ × ℝ → ℝ := fun p => dA p.1 * dB p.2 * (expRemainder n (p.1 * p.2 * x)).re
  have hEre : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
      expRemainder n (p.1 * p.2 * x) = ((expRemainder n (p.1 * p.2 * x)).re : ℂ) ∧
        0 < (expRemainder n (p.1 * p.2 * x)).re ∧ (expRemainder n (p.1 * p.2 * x)).re ≤ 1 := by
    intro p hs ht
    obtain ⟨q, hq, hq0, hq1⟩ := expRemainder_ofReal_mem n (y := p.1 * p.2 * x)
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx)
    have : expRemainder n (p.1 * p.2 * x) = q := by rw [← hq]; push_cast; ring_nf
    rw [this]; simp [hq0, hq1]
  have hint : ∀ᵐ p ∂quadrantMeasure,
      eulerDensity (α + n) p.1 * eulerDensity (β + n) p.2 * expRemainder n (p.1 * p.2 * x) =
        (g p : ℂ) := by
    filter_upwards [ae_quadrantMeasure] with p hp
    rw [hac, hbc, eulerDensity_ofReal a hp.1,
      eulerDensity_ofReal b hp.2, (hEre p hp.1 hp.2).1]
    simp only [g, dA, dB]; push_cast; ring
  have hIc := integrable_eulerDensity_mul_kernel hα' hβ'
    (K := fun p : ℝ × ℝ => expRemainder n (p.1 * p.2 * x))
    ((continuous_expRemainder n).comp (by fun_prop)) (C := 1)
    (fun p hs ht => norm_expRemainder_mul_le n hx' hs ht)
  have hIg : Integrable g quadrantMeasure := by
    have := hIc.re
    refine this.congr ?_
    filter_upwards [hint] with p hp
    rw [hp]; exact Complex.ofReal_re (g p)
  have hD : twoF0Double n α β x = ((∫ p, g p ∂quadrantMeasure : ℝ) : ℂ) := by
    unfold twoF0Double
    rw [integral_congr_ae hint, integral_complex_ofReal]
  have hdAB : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → 0 < dA p.1 * dB p.2 := by
    intro p hs ht
    simp only [dA, dB]
    have := Real.Gamma_pos_of_pos (show 0 < a from hα)
    have := Real.Gamma_pos_of_pos (show 0 < b from hβ)
    positivity
  have hle : ∫ p, g p ∂quadrantMeasure ≤ 1 := by
    have hone : ∫ p, dA p.1 * dB p.2 ∂quadrantMeasure = 1 := by
      have h := integral_eulerDensity_mul_eulerDensity hα' hβ'
      rw [hac, hbc] at h
      have h2 : ∫ p, (eulerDensity (a : ℂ) p.1 * eulerDensity (b : ℂ) p.2) ∂quadrantMeasure =
          ((∫ p, dA p.1 * dB p.2 ∂quadrantMeasure : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae ?_
        filter_upwards [ae_quadrantMeasure] with p hp
        rw [eulerDensity_ofReal a hp.1, eulerDensity_ofReal b hp.2, ← ofReal_mul]
      rw [h2] at h
      exact_mod_cast h
    rw [← hone]
    refine integral_mono_ae hIg ?_ ?_
    · have := (Integrable.mul_prod (integrableOn_eulerDensity hα') (integrableOn_eulerDensity hβ')).re
      refine this.congr ?_
      filter_upwards [ae_quadrantMeasure] with p hp
      simp only [hac, hbc]
      rw [eulerDensity_ofReal a hp.1, eulerDensity_ofReal b hp.2, ← ofReal_mul]
      exact Complex.ofReal_re _
    · filter_upwards [ae_quadrantMeasure] with p hp
      have h1 := (hEre p hp.1 hp.2).2.2
      have h2 := hdAB p hp.1 hp.2
      simp only [g]
      nlinarith
  have hpos : 0 < ∫ p, g p ∂quadrantMeasure := by
    rw [integral_pos_iff_support_of_nonneg_ae _ hIg]
    · have hsub : Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) ⊆ Function.support g := by
        intro p hp
        exact (mul_pos (hdAB p hp.1 hp.2) (hEre p hp.1 hp.2).2.1).ne'
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioi, inter_self,
        Real.volume_Ioi]
      simp
    · filter_upwards [ae_quadrantMeasure] with p hp
      exact (mul_pos (hdAB p hp.1 hp.2) (hEre p hp.1 hp.2).2.1).le
  refine ⟨∫ p, g p ∂quadrantMeasure, hpos, hle, ?_⟩
  rw [hD]; ring

/-- `Eₙ` is entire. -/
theorem analyticOnNhd_expRemainder (n : ℕ) : AnalyticOnNhd ℂ (expRemainder n) univ := by
  rcases n with _ | n
  · exact analyticOnNhd_cexp
  · have heq : expRemainder (n + 1) = fun y => ((n : ℂ) + 1) *
        ∫ u in Icc (0 : ℝ) 1, (1 - (u : ℂ)) ^ n * exp ((u : ℂ) * y) := by
      funext y
      show ((n : ℂ) + 1) * ∫ u in (0 : ℝ)..1, exp (u * y) * (1 - (u : ℂ)) ^ n = _
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
      congr 2; funext u; ring
    rw [heq]
    have hg : IntegrableOn (fun u : ℝ => (1 - (u : ℂ)) ^ n) (Icc 0 1) :=
      (by fun_prop : Continuous fun u : ℝ => (1 - (u : ℂ)) ^ n).integrableOn_Icc
    have hH : AnalyticOnNhd ℂ (fun q : ℂ × ℂ => exp (q.2 * q.1)) univ := fun q _ =>
      (analyticAt_snd.mul analyticAt_fst).cexp
    have h := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc hg
      (γ := fun u : ℝ => (u : ℂ)) continuous_ofReal.continuousOn isOpen_univ hH
      (fun _ _ _ _ => mem_univ _)
    exact fun y hy => analyticAt_const.mul (h y hy)


/-- The reciprocal Gamma function is entire. -/
theorem analyticOnNhd_inv_Gamma : AnalyticOnNhd ℂ (fun a : ℂ => (Gamma a)⁻¹) univ :=
  differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ

/-- The complexified integrand of the remainder double integral, as a function of the
parameters `(α, β, x)` and of complex `(σ, τ)`. -/
def twoF0Integrand (n : ℕ) (v : (ℂ × ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  (Gamma (v.1.1 + n))⁻¹ * (v.2.1 ^ (v.1.1 + n - 1) * exp (-v.2.1)) *
    ((Gamma (v.1.2.1 + n))⁻¹ * (v.2.2 ^ (v.1.2.1 + n - 1) * exp (-v.2.2))) *
      expRemainder n (v.2.1 * v.2.2 * v.1.2.2)

/-- The complexified integrand is jointly analytic at positive real `(σ, τ)`. -/
theorem analyticAt_twoF0Integrand (n : ℕ) (p : ℂ × ℂ × ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    AnalyticAt ℂ (twoF0Integrand n) (p, ((s : ℂ), (t : ℂ))) := by
  have hs' : (s : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hs
  have ht' : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  set q := (p, ((s : ℂ), (t : ℂ)))
  have hα : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.1) q :=
    ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hβ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.2.1) q :=
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hx : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.2.2) q :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hσ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.2.1) q :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hτ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.2.2) q :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hG : ∀ {f : (ℂ × ℂ × ℂ) × (ℂ × ℂ) → ℂ}, AnalyticAt ℂ f q →
      AnalyticAt ℂ (fun v => (Gamma (f v + n))⁻¹) q := fun hf =>
    (analyticOnNhd_inv_Gamma _ (mem_univ _)).comp_of_eq (hf.add analyticAt_const) rfl
  have hE := (analyticOnNhd_expRemainder n _ (mem_univ _)).comp_of_eq
    ((hσ.mul hτ).mul hx) rfl
  unfold twoF0Integrand
  exact (((hG hα).mul ((hσ.cpow ((hα.add analyticAt_const).sub analyticAt_const) hs').mul
    hσ.neg.cexp)).mul ((hG hβ).mul ((hτ.cpow ((hβ.add analyticAt_const).sub analyticAt_const)
      ht').mul hτ.neg.cexp))).mul hE

/-- The one-dimensional Gamma-type majorant is integrable. -/
private theorem integrableOn_rpow_add_rpow_mul_exp {A₀ A₁ : ℝ} (h₀ : 0 < A₀) (h₁ : 0 < A₁) :
    IntegrableOn (fun s : ℝ => (s ^ (A₀ - 1) + s ^ (A₁ - 1)) * Real.exp (-s)) (Ioi 0) := by
  have i₀ := Real.GammaIntegral_convergent h₀
  have i₁ := Real.GammaIntegral_convergent h₁
  refine (i₀.add i₁).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

/-- The domain of the representation with `n` explicit terms. -/
def twoF0Domain (n : ℕ) : Set (ℂ × ℂ × ℂ) :=
  {p | 0 < (p.1 + n).re ∧ 0 < (p.2.1 + n).re ∧ p.2.2.re < 0}

/-- The domain of the representation is open. -/
theorem isOpen_twoF0Domain (n : ℕ) : IsOpen (twoF0Domain n) := by
  have c1 : Continuous fun q : ℂ × ℂ × ℂ => (q.1 + n).re :=
    Complex.continuous_re.comp (continuous_fst.add continuous_const)
  have c2 : Continuous fun q : ℂ × ℂ × ℂ => (q.2.1 + n).re :=
    Complex.continuous_re.comp ((continuous_fst.comp continuous_snd).add continuous_const)
  have c3 : Continuous fun q : ℂ × ℂ × ℂ => q.2.2.re :=
    Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
  exact (isOpen_lt continuous_const c1).inter
    ((isOpen_lt continuous_const c2).inter (isOpen_lt c3 continuous_const))

set_option maxHeartbeats 1000000 in
/-- **Holomorphy of the remainder double integral** in `(α, β, x)`. -/
theorem analyticOnNhd_twoF0Double (n : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => twoF0Double n p.1 p.2.1 p.2.2) (twoF0Domain n) := by
  set F : ℂ × ℂ × ℂ → ℝ × ℝ → ℂ := fun p a => twoF0Integrand n (p, ((a.1 : ℂ), (a.2 : ℂ)))
  have hF : ∀ p, (fun a : ℝ × ℝ => eulerDensity (p.1 + n) a.1 * eulerDensity (p.2.1 + n) a.2 *
      expRemainder n (a.1 * a.2 * p.2.2)) = F p := fun p => by
    funext a; simp [F, twoF0Integrand, eulerDensity]
  have hQ : quadrantMeasure = ((volume : Measure ℝ).prod volume).restrict
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := Measure.prod_restrict _ _
  have hmQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hfun : (fun p : ℂ × ℂ × ℂ => twoF0Double n p.1 p.2.1 p.2.2) =
      fun p => ∫ a, F p a ∂quadrantMeasure := by
    funext p
    unfold twoF0Double
    rw [hF p]
  rw [hfun]
  apply analyticOnNhd_integral_of_locally_dominated (isOpen_twoF0Domain n)
  · intro p hp
    rw [← hF]
    exact (integrable_eulerDensity_mul_kernel hp.1 hp.2.1
      (K := fun a : ℝ × ℝ => expRemainder n (a.1 * a.2 * p.2.2))
      ((continuous_expRemainder n).comp (by fun_prop)) (C := 1)
      (fun a hs ht => norm_expRemainder_mul_le n hp.2.2.le hs ht)).aestronglyMeasurable
  · intro p hp
    rw [hQ]
    refine ContinuousOn.aestronglyMeasurable ?_ hmQ
    have heq : ∀ a ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), fderiv ℂ (fun q => F q a) p =
        (fderiv ℂ (twoF0Integrand n) (p, ((a.1 : ℂ), (a.2 : ℂ)))).comp
          (ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ)) := fun a ha => by
      show fderiv ℂ (twoF0Integrand n ∘ fun e => (e, ((a.1 : ℂ), (a.2 : ℂ)))) p = _
      exact ((analyticAt_twoF0Integrand n p ha.1 ha.2).differentiableAt.hasFDerivAt.comp p
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) p ((a.1 : ℂ), (a.2 : ℂ)))).fderiv
    refine ContinuousOn.congr ?_ heq
    intro a ha
    exact (((analyticAt_twoF0Integrand n p ha.1 ha.2).fderiv.continuousAt.comp_of_eq
      (show ContinuousAt (fun v : ℝ × ℝ => (p, ((v.1 : ℂ), (v.2 : ℂ)))) a by fun_prop)
        rfl).clm_comp continuousAt_const).continuousWithinAt
  · rw [hQ]
    filter_upwards [self_mem_ae_restrict hmQ] with a ha
    intro p _
    exact (analyticAt_twoF0Integrand n p ha.1 ha.2).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  · intro p hp
    -- a closed ball on which the real parts are controlled
    set A := (p.1 + n).re
    set B := (p.2.1 + n).re
    have hA : 0 < A := hp.1
    have hB : 0 < B := hp.2.1
    have hev : ∀ᶠ q in 𝓝 p, A / 2 < (q.1 + (n : ℂ)).re ∧ (q.1 + (n : ℂ)).re < A + 1 ∧
        B / 2 < (q.2.1 + (n : ℂ)).re ∧ (q.2.1 + (n : ℂ)).re < B + 1 ∧ q.2.2.re < 0 := by
      have c1 : Continuous fun q : ℂ × ℂ × ℂ => (q.1 + (n : ℂ)).re :=
        Complex.continuous_re.comp (continuous_fst.add continuous_const)
      have c2 : Continuous fun q : ℂ × ℂ × ℂ => (q.2.1 + (n : ℂ)).re :=
        Complex.continuous_re.comp ((continuous_fst.comp continuous_snd).add continuous_const)
      have c3 : Continuous fun q : ℂ × ℂ × ℂ => q.2.2.re :=
        Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
      filter_upwards [c1.continuousAt.eventually_const_lt (show A / 2 < A by linarith),
        c1.continuousAt.eventually_lt_const (show A < A + 1 by linarith),
        c2.continuousAt.eventually_const_lt (show B / 2 < B by linarith),
        c2.continuousAt.eventually_lt_const (show B < B + 1 by linarith),
        c3.continuousAt.eventually_lt_const hp.2.2] with q a b c d e
      exact ⟨a, b, c, d, e⟩
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hev
    have hK := isCompact_closedBall p r
    have hGc : ContinuousOn (fun q : ℂ × ℂ × ℂ => ‖(Gamma (q.1 + n))⁻¹‖ * ‖(Gamma (q.2.1 + n))⁻¹‖)
        (Metric.closedBall p r) :=
      ((differentiable_one_div_Gamma.continuous.comp (continuous_fst.add continuous_const)).norm.mul
        (differentiable_one_div_Gamma.continuous.comp
          ((continuous_fst.comp continuous_snd).add continuous_const)).norm).continuousOn
    obtain ⟨M, hM⟩ := hK.bddAbove_image hGc
    set bound : ℝ × ℝ → ℝ := fun a => max M 0 *
      (((a.1 ^ (A / 2 - 1) + a.1 ^ (A + 1 - 1)) * Real.exp (-a.1)) *
        ((a.2 ^ (B / 2 - 1) + a.2 ^ (B + 1 - 1)) * Real.exp (-a.2)))
    refine ⟨Metric.closedBall p r, bound, Metric.closedBall_mem_nhds p hr, ?_, ?_⟩
    · have := (integrableOn_rpow_add_rpow_mul_exp (by linarith : 0 < A / 2)
        (by linarith : 0 < A + 1)).mul_prod (integrableOn_rpow_add_rpow_mul_exp
          (by linarith : 0 < B / 2) (by linarith : 0 < B + 1))
      exact this.const_mul _
    · filter_upwards [ae_quadrantMeasure] with a ha q hq
      obtain ⟨h1, h2, h3, h4, h5⟩ := hball hq
      have hMq := hM (mem_image_of_mem _ hq)
      simp only [F, twoF0Integrand, bound]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ha.1, Complex.norm_cpow_eq_rpow_re_of_pos ha.2,
        show -((a.1 : ℂ)) = ((-a.1 : ℝ) : ℂ) by push_cast; ring,
        show -((a.2 : ℂ)) = ((-a.2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_exp_ofReal, Complex.norm_exp_ofReal]
      have hE := norm_expRemainder_mul_le n h5.le ha.1 ha.2
      have hs := Real.rpow_le_rpow_add_rpow ha.1 (c₁ := A / 2 - 1) (c := (q.1 + (n : ℂ) - 1).re)
        (c₂ := A + 1 - 1) (by simp only [sub_re, one_re]; linarith)
        (by simp only [sub_re, one_re]; linarith)
      have ht := Real.rpow_le_rpow_add_rpow ha.2 (c₁ := B / 2 - 1) (c := (q.2.1 + (n : ℂ) - 1).re)
        (c₂ := B + 1 - 1) (by simp only [sub_re, one_re]; linarith)
        (by simp only [sub_re, one_re]; linarith)
      have e1 := Real.exp_pos (-a.1)
      have e2 := Real.exp_pos (-a.2)
      have g1 := norm_nonneg ((Gamma (q.1 + n))⁻¹)
      have g2 := norm_nonneg ((Gamma (q.2.1 + n))⁻¹)
      have p1 := Real.rpow_nonneg ha.1.le (q.1 + (n : ℂ) - 1).re
      have p2 := Real.rpow_nonneg ha.2.le (q.2.1 + (n : ℂ) - 1).re
      have hMM : ‖(Gamma (q.1 + n))⁻¹‖ * ‖(Gamma (q.2.1 + n))⁻¹‖ ≤ max M 0 :=
        hMq.trans (le_max_left _ _)
      calc ‖(Gamma (q.1 + n))⁻¹‖ * (a.1 ^ (q.1 + (n : ℂ) - 1).re * Real.exp (-a.1)) *
            (‖(Gamma (q.2.1 + n))⁻¹‖ * (a.2 ^ (q.2.1 + (n : ℂ) - 1).re * Real.exp (-a.2))) *
            ‖expRemainder n (a.1 * a.2 * q.2.2)‖
          ≤ ‖(Gamma (q.1 + n))⁻¹‖ * (a.1 ^ (q.1 + (n : ℂ) - 1).re * Real.exp (-a.1)) *
            (‖(Gamma (q.2.1 + n))⁻¹‖ * (a.2 ^ (q.2.1 + (n : ℂ) - 1).re * Real.exp (-a.2))) * 1 := by
              gcongr
        _ = (‖(Gamma (q.1 + n))⁻¹‖ * ‖(Gamma (q.2.1 + n))⁻¹‖) *
            ((a.1 ^ (q.1 + (n : ℂ) - 1).re * Real.exp (-a.1)) *
              (a.2 ^ (q.2.1 + (n : ℂ) - 1).re * Real.exp (-a.2))) := by ring
        _ ≤ max M 0 * (((a.1 ^ (A / 2 - 1) + a.1 ^ (A + 1 - 1)) * Real.exp (-a.1)) *
              ((a.2 ^ (B / 2 - 1) + a.2 ^ (B + 1 - 1)) * Real.exp (-a.2))) := by
              have q1 := Real.rpow_nonneg ha.1.le (A / 2 - 1)
              have q2 := Real.rpow_nonneg ha.1.le (A + 1 - 1)
              gcongr

/-- **Theorem 5.12-4** (holomorphy): the continued `₂F₀(α, β; x)` is holomorphic in `(α, β, x)`
on `ℂ² × {re x < 0}`. -/
theorem analyticOnNhd_carlson2F0 :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => carlson2F0 p.1 p.2.1 p.2.2) {p | p.2.2.re < 0} := by
  intro p hp
  set n := twoF0Depth p.1 p.2.1
  obtain ⟨hα, hβ⟩ := re_add_twoF0Depth_pos p.1 p.2.1
  have hpn : p ∈ twoF0Domain n := ⟨hα, hβ, hp⟩
  have heq : (fun q : ℂ × ℂ × ℂ => carlson2F0 q.1 q.2.1 q.2.2) =ᶠ[𝓝 p]
      fun q => twoF0Rep n q.1 q.2.1 q.2.2 := by
    filter_upwards [(isOpen_twoF0Domain n).mem_nhds hpn] with q hq
    exact carlson2F0_eq_twoF0Rep hq.1 hq.2.1 hq.2.2.le
  refine AnalyticAt.congr ?_ heq.symm
  have hD := analyticOnNhd_twoF0Double n p hpn
  have hterm : ∀ m, AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => twoF0Term m q.1 q.2.1 q.2.2) p := by
    intro m
    unfold twoF0Term
    have h1 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => (ascPochhammer ℂ m).eval q.1) p :=
      (Differentiable.analyticAt (Polynomial.differentiable _) _).comp_of_eq analyticAt_fst rfl
    have h2 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => (ascPochhammer ℂ m).eval q.2.1) p :=
      (Differentiable.analyticAt (Polynomial.differentiable _) _).comp_of_eq
        (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p)
        rfl
    have h3 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p :=
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p
    exact ((h1.mul h2).mul (h3.pow m)).div_const
  unfold twoF0Rep
  exact (Finset.analyticAt_fun_sum _ fun m _ => hterm m).add ((hterm n).mul hD)

end Carlson
