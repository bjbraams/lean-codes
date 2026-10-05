/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.FourierCosine
public import Carlson.Jacobi.PlaneWave
public import Carlson.Jacobi.GegenbauerAddition
public import Carlson.TwoVariable.SEqualParameter
public import ToMathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Bessel functions in Carlson's Section 7.7

Theorem 6.9-2 expresses `S(β, β; -iw, iw)` as `Γ(β + 1/2) ₀F₁(β + 1/2; -(w/2)²)`, which for
`β = 1/2 + n` is `n! (w/2)⁻ⁿ Jₙ(w)` in terms of Mathlib's `Complex.besselJ`, and for `β = 1 + n`
is a spherical Bessel function. Inserting these into the Fourier cosine expansion (Example
7.7-2) and the plane-wave expansion (Example 7.7-1) gives the classical Bessel expansions.

The expansion (8) over `ℤ` is obtained from the cosine series (7) by the reflection
`J₋ₙ = (-1)ⁿ Jₙ` and the bound `‖Jₘ(x)‖ ≤ exp (‖x‖²/4) (‖x‖/2)^{|m|} / |m|!`. The Fourier
cosine coefficients (6) follow from (5) by termwise integration: the series at an imaginary
angle shows that the coefficients decay geometrically.

## Main definitions

* `Carlson.TwoVariable.sphericalBesselJ`: the spherical Bessel function `jₙ`, entire.

## Main results

* `Carlson.TwoVariable.carlsonS_pair_self_neg_I_mul`: `S(β, β; -iw, iw)` as a `₀F₁`.
* `Carlson.TwoVariable.hasSum_exp_I_mul_mul_legendre`: Example 7.7-1, equation (3).
* `Carlson.TwoVariable.integral_fourier_cosine`: Example 7.7-2, equation (6).
* `Carlson.TwoVariable.hasSum_exp_I_mul_mul_cos`: Example 7.7-3, equation (7).
* `Carlson.TwoVariable.hasSum_exp_I_mul_mul_cos_int`,
  `Carlson.TwoVariable.hasSum_exp_I_mul_mul_sin_int`: equations (8) and (9).
* `Carlson.TwoVariable.hasSum_zpow_mul_besselJ`: equation (10), the generating function
  `exp (x (t - 1/t)/2) = ∑_{m ∈ ℤ} tᵐ Jₘ(x)`.
* `Carlson.TwoVariable.hasSum_exp_mul_cos_int`, `Carlson.TwoVariable.hasSum_zpow_mul_besselI`:
  the first forms of (9) and (10), with the modified Bessel functions `Iₘ`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.7.
-/

open Complex Set Filter Polynomial Dirichlet
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Theorem 6.9-2 at opposite nodes `∓ iw`, regularized:
`S(β, β; -iw, iw)/Γ(2β) = q(β) ₀F₁(β + 1/2; -(w/2)²)/Γ(β + 1/2)`. -/
theorem regCarlsonS_pair_self_neg_I_mul (β w : ℂ) :
    regCarlsonS (pair β β) (pair (-(I * w)) (I * w)) =
      quadraticGammaRatio β * regularizedHGFun 0 {β + 1 / 2} (-(w / 2) ^ 2) := by
  have h1 := hasSum_regCarlsonS_pair_self β (-(I * w)) (I * w)
  have h2 := (hasSum_regularizedHGFun_zero_singleton (β + 1 / 2) (-(w / 2) ^ 2)).mul_left
    (quadraticGammaRatio β)
  refine h1.unique (h2.congr_fun fun n => ?_)
  have : (-(I * w) - I * w) ^ 2 / 16 = -(w / 2) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  simp only [this, show (-(I * w) + I * w) / 2 = 0 by ring, exp_zero, mul_one]

/-- Theorem 6.9-2 at opposite nodes `∓ iw`: `S(β, β; -iw, iw) = Γ(β + 1/2) F₀₁(β + 1/2; -(w/2)²)`
with the regularized `₀F₁`. -/
theorem carlsonS_pair_self_neg_I_mul {β : ℂ} (hβ : 0 < β.re) (w : ℂ) :
    carlsonS (pair β β) (pair (-(I * w)) (I * w)) =
      Gamma (β + 1 / 2) * regularizedHGFun 0 {β + 1 / 2} (-(w / 2) ^ 2) := by
  rw [carlsonS, sum_pair, regCarlsonS_pair_self_neg_I_mul, ← mul_assoc,
    Gamma_mul_quadraticGammaRatio hβ]

/-- The derivatives of the exponential. -/
private theorem iteratedDeriv_cexp (n : ℕ) : iteratedDeriv n exp = exp := by
  simpa using iteratedDeriv_cexp_const_mul n 1

/-- Carlson's Example 7.7-3, equation (7): `exp (i x cos θ) = J₀(x) + 2 ∑ iⁿ Jₙ(x) cos nθ` for
all complex `x, θ`. -/
theorem hasSum_exp_I_mul_mul_cos (x θ : ℂ) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2) * I ^ n * besselJ n x * cos (n * θ))
      (exp (I * x * cos θ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero, zero_mul, exp_zero]
    convert hasSum_single (f := fun n : ℕ => (if n = 0 then 1 else 2) * I ^ n *
      besselJ n 0 * cos (n * θ)) 0 (fun n hn => by simp [besselJ_zero, hn]) using 1
    simp [besselJ_zero]
  have hB : I * x ≠ 0 := mul_ne_zero I_ne_zero hx
  have H := hasSum_fourier_cosine 0 (I * x) hB (h := |θ.im| + 1) (f := exp)
    (by fun_prop : Differentiable ℂ exp).differentiableOn (by linarith)
  simp only [zero_add, zero_sub, iteratedDeriv_cexp] at H
  refine H.congr_fun fun n => ?_
  have hb : pair (1 / 2 + (n : ℂ)) (1 / 2 + n) ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> simp [pair] <;> positivity
  have hre : 0 < (1 / 2 + (n : ℂ)).re := by simp; positivity
  have hS : carlsonDirichletAverage (pair (1 / 2 + (n : ℂ)) (1 / 2 + n)) (pair (-(I * x)) (I * x))
      exp = carlsonS (pair (1 / 2 + (n : ℂ)) (1 / 2 + n)) (pair (-(I * x)) (I * x)) :=
    (carlsonS_eq_integral hb).symm
  simp only [besselJ_def, cpow_natCast]
  rw [hS, carlsonS_pair_self_neg_I_mul hre,
    show 1 / 2 + (n : ℂ) + 1 / 2 = n + 1 by ring, Gamma_nat_eq_factorial]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_pow]
  field_simp
  ring

/-- A bound for the terms of the Jacobi–Anger series over `ℤ`. -/
theorem norm_I_zpow_mul_besselJ_mul_exp_le (m : ℤ) (x θ : ℂ) :
    ‖I ^ m * besselJ m x * exp (m * θ * I)‖ ≤ Real.exp (‖x‖ ^ 2 / 4) *
      ((‖x‖ / 2 * Real.exp |θ.im|) ^ m.natAbs / m.natAbs.factorial) := by
  rw [norm_mul, norm_mul, norm_zpow, norm_I, one_zpow, one_mul, norm_exp]
  have he : (m * θ * I).re ≤ m.natAbs * |θ.im| := by
    have : (m * θ * I).re = -(m * θ.im) := by simp [mul_re, mul_im]
    rw [this]
    calc -(m * θ.im) ≤ |(m : ℝ) * θ.im| := neg_le_abs _
      _ = m.natAbs * |θ.im| := by rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
  calc ‖besselJ m x‖ * Real.exp (m * θ * I).re
      ≤ Real.exp (‖x‖ ^ 2 / 4) * ((‖x‖ / 2) ^ m.natAbs / m.natAbs.factorial) *
          Real.exp (m.natAbs * |θ.im|) := by
        gcongr
        exact norm_besselJ_intCast_le m x
    _ = _ := by rw [Real.exp_nat_mul, mul_pow]; ring

/-- The Jacobi–Anger series over `ℤ` is summable. -/
theorem summable_I_zpow_mul_besselJ_mul_exp (x θ : ℂ) :
    Summable fun m : ℤ => I ^ m * besselJ m x * exp (m * θ * I) := by
  set r := ‖x‖ / 2 * Real.exp |θ.im|
  set C := Real.exp (‖x‖ ^ 2 / 4)
  have hs : Summable fun n : ℕ => C * (r ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial r).mul_left C
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_norm_bounded hs fun n => ?_
    simpa using norm_I_zpow_mul_besselJ_mul_exp_le n x θ
  · refine Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hs) fun n => ?_
    have := norm_I_zpow_mul_besselJ_mul_exp_le (-(n + 1 : ℕ)) x θ
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at this
    simpa using this

/-- Carlson's Example 7.7-3, equation (8). -/
theorem hasSum_exp_I_mul_mul_cos_int (x θ : ℂ) :
    HasSum (fun m : ℤ => I ^ m * besselJ m x * exp (m * θ * I)) (exp (I * x * cos θ)) := by
  set f : ℤ → ℂ := fun m => I ^ m * besselJ m x * exp (m * θ * I)
  have hS := summable_I_zpow_mul_besselJ_mul_exp x θ
  have h1 := hS.hasSum.nat_add_neg
  have h2 := (hasSum_exp_I_mul_mul_cos x θ).add (hasSum_ite_eq 0 (f 0))
  have heq : (fun n : ℕ => f n + f (-n)) = fun n : ℕ =>
      (if n = 0 then 1 else 2) * I ^ n * besselJ n x * cos (n * θ) +
        (if n = 0 then f 0 else 0) := by
    funext n
    simp only [f]
    rw [show ((-(n : ℤ) : ℤ) : ℂ) = -((n : ℤ) : ℂ) by push_cast; ring, besselJ_neg_int]
    push_cast
    simp only [zpow_neg, zpow_natCast]
    rw [cos]
    have hI : (I ^ n)⁻¹ * (-1) ^ n = I ^ n := by
      rw [← inv_pow, inv_I, ← mul_pow]; congr 1; ring
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [hn.ne', ↓reduceIte]
      rw [show -(n : ℂ) * θ * I = -(n * θ * I) by ring, show -((n : ℂ) * θ) * I = -(n * θ * I) by
        ring]
      linear_combination (besselJ n x * exp (-(n * θ * I))) * hI
  rw [heq] at h1
  have := h1.unique h2
  have ht : ∑' m, f m = exp (I * x * cos θ) := add_right_cancel this
  rw [← ht]; exact hS.hasSum

/-- Carlson's Example 7.7-3, equation (9). -/
theorem hasSum_exp_I_mul_mul_sin_int (x θ : ℂ) :
    HasSum (fun m : ℤ => besselJ m x * exp (m * θ * I)) (exp (I * x * sin θ)) := by
  have H := hasSum_exp_I_mul_mul_cos_int x (θ - π / 2)
  rw [cos_sub_pi_div_two] at H
  refine H.congr_fun fun m => ?_
  have he : exp (m * (θ - π / 2) * I) = exp (m * θ * I) * (I⁻¹) ^ m := by
    rw [show (m : ℂ) * (θ - π / 2) * I = m * θ * I + m * (-(π / 2 * I)) by ring, exp_add,
      exp_int_mul, exp_neg, exp_pi_div_two_mul_I]
  rw [he, show I ^ m * besselJ m x * (exp (m * θ * I) * I⁻¹ ^ m) =
    (I * I⁻¹) ^ m * besselJ m x * exp (m * θ * I) by rw [mul_zpow]; ring, mul_inv_cancel₀ I_ne_zero,
    one_zpow, one_mul]

/-- Carlson's Example 7.7-3, equation (10): the generating function of the Bessel coefficients,
`exp (x (t - 1/t) / 2) = ∑_{m ∈ ℤ} tᵐ Jₘ(x)` for `t ≠ 0`. -/
theorem hasSum_zpow_mul_besselJ (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun m : ℤ => t ^ m * besselJ m x) (exp (x / 2 * (t - t⁻¹))) := by
  set θ := -(I * log t)
  have hθ : θ * I = log t := by
    simp only [θ]; rw [show -(I * log t) * I = -(I * I) * log t by ring, I_mul_I]; ring
  have H := hasSum_exp_I_mul_mul_sin_int x θ
  have hsin : I * x * sin θ = x / 2 * (t - t⁻¹) := by
    rw [sin, show -θ * I = -(θ * I) by ring, hθ, exp_neg, exp_log ht]
    ring_nf; rw [I_sq]; ring
  rw [hsin] at H
  refine H.congr_fun fun m => ?_
  rw [mul_assoc (m : ℂ), hθ, exp_int_mul, exp_log ht, mul_comm]

/-- The spherical Bessel function `jₙ(z) = (π/(2z))^{1/2} J_{n+1/2}(z)`, in its entire form
`(√π/2) (z/2)ⁿ ₀F₁(n + 3/2; -(z/2)²) / Γ(n + 3/2)`. -/
def sphericalBesselJ (n : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt π / 2 : ℂ) * (z / 2) ^ n * regularizedHGFun 0 {(n : ℂ) + 3 / 2} (-(z / 2) ^ 2)

/-- The spherical Bessel function in terms of `J_{n+1/2}`: `(z/2)^{1/2} jₙ(z) = (√π/2) J_{n+1/2}(z)`
for `z ≠ 0`. -/
theorem cpow_half_mul_sphericalBesselJ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (z / 2) ^ (1 / 2 : ℂ) * sphericalBesselJ n z =
      (Real.sqrt π / 2 : ℂ) * besselJ (n + 1 / 2) z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  rw [sphericalBesselJ, besselJ_def]
  simp only
  rw [cpow_add _ _ hz2, cpow_natCast, show (n : ℂ) + 1 / 2 + 1 = n + 3 / 2 by ring]
  ring

/-- `Γ(n + 3/2) = (1/2)ₙ (n + 1/2) √π`. -/
private theorem Gamma_nat_add_three_halves (n : ℕ) :
    Gamma (1 + (n : ℂ) + 1 / 2) = (ascPochhammer ℂ n).eval (1 / 2) * ((n : ℂ) + 1 / 2) *
      (Real.sqrt π : ℂ) := by
  have hre : 0 < (1 / 2 : ℂ).re := by norm_num
  rw [show 1 + (n : ℂ) + 1 / 2 = (1 / 2 + n) + 1 by ring, Gamma_add_one _ (by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
    Complex.Gamma_add_nat_eq_ascPochhammer_mul (.of_re_pos hre), Complex.Gamma_one_half_eq,
    Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  push_cast; ring

/-- Carlson's Example 7.7-1, equation (3): the expansion of a plane wave in spherical Bessel
functions and Legendre polynomials, `exp (i w x) = ∑ iⁿ (2n+1) jₙ(w) Pₙ(x)` for all complex
`w, x`, with `Pₙ = C_n^{1/2}`. -/
theorem hasSum_exp_I_mul_mul_legendre (w x : ℂ) :
    HasSum (fun n : ℕ => I ^ n * (2 * n + 1) * sphericalBesselJ n w *
      (gegenbauer (1 / 2 : ℂ) n).eval x) (exp (I * w * x)) := by
  have hc : IsGammaRegular ((0 : ℂ) + 0 + 2) := by
    intro k hk; have := congrArg re hk; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have H := hasSum_exp_jacobiOn 0 0 (-1) 1 hc (I * w) x
  refine H.congr_fun fun n => ?_
  have hre : 0 < (1 + (0 : ℂ) + n).re := by simp; positivity
  have hp : pair (I * w * -1) (I * w * 1) = pair (-(I * w)) (I * w) := by
    congr 1 <;> ring
  rw [hp, carlsonS_pair_self_neg_I_mul hre, show 1 + (0 : ℂ) + n + 1 / 2 = 1 + n + 1 / 2 by ring,
    Gamma_nat_add_three_halves]
  have h1 : (ascPochhammer ℂ n).eval (1 - 1 / 2 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) n
  have h2 : (ascPochhammer ℂ n).eval (1 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) n
  have hJ := eval_jacobiOn_gegenbauer 1 x n h1 h2
  rw [show (1 : ℂ) - 1 = 0 by ring, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hJ
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h1
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hJ' : (jacobiOn 0 0 (-1) 1 n).eval x = n.factorial * (gegenbauer (1 / 2 : ℂ) n).eval x /
      (2 ^ n * (ascPochhammer ℂ n).eval (1 / 2)) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ two_ne_zero) h1)]; exact hJ
  rw [hJ', sphericalBesselJ, show 1 + (n : ℂ) + 1 / 2 = n + 3 / 2 by ring, mul_pow, div_pow]
  field_simp
/-- Carlson's Example 7.7-2, equation (6): the Fourier cosine coefficients of `f (A + B cos θ)`
are Dirichlet averages of the derivatives of `f`:
`∫₀^π f(A + B cos θ) cos nθ dθ = π Bⁿ/(n! 2ⁿ) F⁽ⁿ⁾(½+n, ½+n; A−B, A+B)`. -/
theorem integral_fourier_cosine (A B : ℂ) (hB : B ≠ 0) {h : ℝ} (hh : 0 < h) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk (A - B) (A + B) (‖B‖ * Real.exp h / 2)))
    (n : ℕ) :
    ∫ θ in (0 : ℝ)..π, f (A + B * cos θ) * cos (n * θ) =
      π * (B ^ n / (n.factorial * 2 ^ n)) *
        carlsonDirichletAverage (pair (1 / 2 + n) (1 / 2 + n)) (pair (A - B) (A + B))
          (iteratedDeriv n f) := by
  set a : ℕ → ℂ := fun k => (if k = 0 then 1 else 2) * (B ^ k / (k.factorial * 2 ^ k)) *
    carlsonDirichletAverage (pair (1 / 2 + k) (1 / 2 + k)) (pair (A - B) (A + B))
      (iteratedDeriv k f)
  have hser : ∀ θ : ℂ, |θ.im| < h → HasSum (fun k : ℕ => a k * cos (k * θ)) (f (A + B * cos θ)) :=
    fun θ hθ => hasSum_fourier_cosine A B hB hf hθ
  -- absolute summability of the coefficients, from the series at `θ = i h/2`
  set t := h / 2
  have ht : 0 < t := by positivity
  have hsi := hser (t * I) (by simp; rw [abs_of_pos ht]; simp only [t]; linarith)
  obtain ⟨M, hM⟩ := Tendsto.bddAbove_range_of_cofinite
    (by rw [Nat.cofinite_eq_atTop]; exact hsi.summable.tendsto_atTop_zero.norm)
  have hcosh : ∀ k : ℕ, ‖cos (k * (t * I))‖ = Real.cosh (k * t) := by
    intro k
    rw [show (k : ℂ) * (t * I) = ((k * t : ℝ) : ℂ) * I by push_cast; ring, cos_mul_I,
      ← ofReal_cosh, norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  have hbound : ∀ k : ℕ, ‖a k‖ ≤ 2 * M * Real.exp (-t) ^ k := by
    intro k
    have hk := hM (Set.mem_range_self k)
    simp only [norm_mul, hcosh] at hk
    have hc : Real.exp (k * t) / 2 ≤ Real.cosh (k * t) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(k * t))]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (Set.mem_range_self 0))
    have hek : Real.exp (-t) ^ k * Real.exp (k * t) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    calc ‖a k‖ = ‖a k‖ * (Real.exp (-t) ^ k * Real.exp (k * t)) := by rw [hek, mul_one]
      _ ≤ ‖a k‖ * (Real.exp (-t) ^ k * (2 * Real.cosh (k * t))) := by gcongr; linarith
      _ = 2 * (‖a k‖ * Real.cosh (k * t)) * Real.exp (-t) ^ k := by ring
      _ ≤ 2 * M * Real.exp (-t) ^ k := by gcongr
  have hsum : Summable fun k => ‖a k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      ((summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _)
  have hcos1 : ∀ (k : ℕ) (θ : ℝ), ‖cos ((k : ℂ) * θ)‖ ≤ 1 := by
    intro k θ
    rw [show (k : ℂ) * θ = ((k * θ : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos, norm_real,
      Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := π)
    (F := fun k (θ : ℝ) => a k * cos (k * θ) * cos (n * θ))
    (f := fun θ : ℝ => f (A + B * cos θ) * cos (n * θ))
    (fun k _ => ‖a k‖)
    (fun k => (by fun_prop : Continuous fun θ : ℝ => a k * cos (k * θ) * cos (n * θ))
      |>.aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_mul]
      calc ‖a k‖ * ‖cos (k * θ)‖ * ‖cos (n * θ)‖ ≤ ‖a k‖ * 1 * 1 := by
            gcongr
            · exact hcos1 k θ
            · exact hcos1 n θ
        _ = ‖a k‖ := by ring)
    (Filter.Eventually.of_forall fun _ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ =>
      (hser θ (by simp; exact hh)).mul_right (cos (n * θ)))
  have horth (k n : ℕ) :
      ∫ θ in (0 : ℝ)..π, Real.cos (k * θ) * Real.cos (n * θ) =
        if k = n then (if n = 0 then π else π / 2) else 0 := by
    have hrewrite (j k : ℕ) := Polynomial.Chebyshev.integral_measureT_eq_integral_cos
      (f := fun x => (Polynomial.Chebyshev.T ℝ j).eval x *
        (Polynomial.Chebyshev.T ℝ k).eval x)
    simp only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] at hrewrite
    rw [← hrewrite k n]
    split_ifs with hkn hn
    · subst k; subst n
      exact Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · subst k
      exact Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn
    · exact Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hkn
  have hk : ∀ k : ℕ, ∫ θ in (0 : ℝ)..π, a k * cos (k * θ) * cos (n * θ) =
      if k = n then a n * (if n = 0 then (π : ℂ) else π / 2) else 0 := by
    intro k
    have hc : ∀ θ : ℝ, a k * cos (k * θ) * cos (n * θ) =
        a k * ((Real.cos (k * θ) * Real.cos (n * θ) : ℝ) : ℂ) := by
      intro θ; push_cast; ring
    simp_rw [hc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      horth]
    split_ifs with h1 h2 <;> first | (subst h1; simp_all) | simp_all
  simp_rw [hk] at hint
  rw [hint.unique (hasSum_ite_eq n _)]
  simp only [a]
  split_ifs with hn
  · subst hn; simp; ring
  · ring

/-- Carlson's Example 7.7-3, equation (9), first form: `exp (x cos θ) = ∑_{m ∈ ℤ} Iₘ(x) e^{imθ}`. -/
theorem hasSum_exp_mul_cos_int (x θ : ℂ) :
    HasSum (fun m : ℤ => besselI m x * exp (m * θ * I)) (exp (x * cos θ)) := by
  have H := hasSum_exp_I_mul_mul_cos_int (-(I * x)) θ
  rw [show I * -(I * x) = x by ring_nf; rw [I_sq]; ring] at H
  refine H.congr_fun fun m => ?_
  rw [besselJ_int_neg, besselJ_intCast_I_mul, ← mul_assoc, ← mul_assoc, ← mul_zpow, ← mul_zpow,
    show I * -1 * I = 1 by rw [mul_neg_one, neg_mul, I_mul_I, neg_neg], one_zpow, one_mul]

/-- Carlson's Example 7.7-3, equation (10), first form: the generating function of the modified
Bessel functions, `exp (x (t + 1/t)/2) = ∑_{m ∈ ℤ} tᵐ Iₘ(x)` for `t ≠ 0`. -/
theorem hasSum_zpow_mul_besselI (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun m : ℤ => t ^ m * besselI m x) (exp (x / 2 * (t + t⁻¹))) := by
  set θ := -(I * log t)
  have hθ : θ * I = log t := by
    simp only [θ]; rw [show -(I * log t) * I = -(I * I) * log t by ring, I_mul_I]; ring
  have H := hasSum_exp_mul_cos_int x θ
  have hcos : x * cos θ = x / 2 * (t + t⁻¹) := by
    rw [cos, show -θ * I = -(θ * I) by ring, hθ, exp_neg, exp_log ht]
    ring
  rw [hcos] at H
  refine H.congr_fun fun m => ?_
  rw [mul_assoc (m : ℂ), hθ, exp_int_mul, exp_log ht, mul_comm]

end Carlson.TwoVariable
