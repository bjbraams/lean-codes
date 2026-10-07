/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Bessel
public import Carlson.Jacobi.SeriesExercises
public import Carlson.Jacobi.RPolynomialExercises
public import Carlson.RPolynomial.PowerSeries
public import Carlson.Jacobi.SegmentOrthogonality
public import Carlson.R.ContourRepresentation
public import Pochhammer.Identities
public import Carlson.Jacobi.GegenbauerExercises
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Bessel exercises (Chapter 7)

Exercises of Carlson's Chapter 7 on Bessel functions, and Example 7.7-4. The Bessel functions are
Mathlib's `Complex.besselJ`, written as `J_a(x) = (x/2)^a F̃₀₁(a + 1; -(x/2)²)` with the
regularized `₀F₁`; Carlson's prefactors `x^{-a}` appear here as `(x/2)^{-a}`, which avoids branch
conditions. The addition theorems come from the Gegenbauer series of Exercise 7.6-2 and the
Fourier cosine series of Example 7.7-2, whose coefficients are Dirichlet averages of a `₀F₁`
evaluated by Exercise 7.1-9.

## Main results

* `hasSum_exp_I_mul_besselJ_gegenbauer`: Sonine's formula, Exercise 7.7-1.
* `hasSum_regularizedHGFun_gegenbauer_addition`, `hasSum_besselJ_gegenbauer_addition`:
  Gegenbauer's addition theorem, Example 7.7-4, equations (12) and (13).
* `hasSum_sphericalBesselJ_legendre_addition`: Example 7.7-4, equation (14).
* `hasSum_besselJ_zero_addition`: Exercise 7.7-6.
* `hasSum_besselJ_gegenbauer_sin_half`: Exercise 7.7-7.
* `two_pi_mul_besselJ_eq_integral`, `two_pi_mul_besselJ_eq_integral_cos`: Bessel's integral,
  Exercise 7.7-3.
* `integral_exp_mul_legendre`: Exercise 7.8-7.
* `hasSum_besselJ_zero_mul_besselI_zero`: Exercise 7.1-10.
* `hasSum_neumann`, `hasSum_neumann_regularized`: Neumann's series, Exercise 7.7-2.
* `hasSum_regularizedHGFun_add`: Exercise 7.7-5.
* `tendsto_eval_gegenbauer_cos_div`, `tendsto_eval_gegenbauer_cos_div_besselJ`,
  `tendsto_eval_legendre_cos_div`: Bessel functions as limits of Gegenbauer polynomials,
  Exercise 6.7-13.
* `iterate_besselD_cpow_neg_mul_besselJ`, `iterate_besselD_cpow_mul_besselJ`: the
  `(x⁻¹ d/dx)ⁿ` formulas of Exercise 6.9-20.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 7.
-/

open Complex Polynomial Dirichlet
open scoped Real Topology
open Filter

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- A pair of parameters with positive real parts lies in the Dirichlet convergence region. -/
theorem pair_mem_mvBetaConvergent {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    pair a b ∈ mvBetaConvergent := by
  intro i
  fin_cases i <;> simpa [pair]

/-- `Γ(ν + n + 1) = Γ(ν) (ν)ₙ (ν + n)` at a Gamma-regular `ν`. -/
theorem Gamma_add_nat_add_one_eq {ν : ℂ} (hν : IsGammaRegular ν) (n : ℕ) :
    Gamma (ν + n + 1) = Gamma ν * (ascPochhammer ℂ n).eval ν * (ν + n) := by
  have h := Complex.Gamma_add_nat_eq_ascPochhammer_mul hν (n + 1)
  rw [ascPochhammer_succ_eval] at h
  push_cast at h
  rw [← add_assoc] at h
  rw [h]; ring

/-- **Sonine's formula** (Exercise 7.7-1), with the regularized `₀F₁` in place of
`λ^{-ν} J_{ν+n}(λ)`: for `ν` Gamma-regular with `re (ν + 1/2) > 0`,
`e^{iλx} = Γ(ν) ∑ₙ iⁿ (ν + n) (λ/2)ⁿ F̃₀₁(ν + n + 1; -(λ/2)²) Cₙ^ν(x)`. -/
theorem hasSum_exp_I_mul_gegenbauer {ν : ℂ} (hν : IsGammaRegular ν) (hre : 0 < (ν + 1 / 2).re)
    (lam x : ℂ) :
    HasSum (fun n : ℕ => Gamma ν * (ν + n) * I ^ n * (lam / 2) ^ n *
        regularizedHGFun 0 {ν + n + 1} (-(lam / 2) ^ 2) * (gegenbauer ν n).eval x)
      (exp (I * lam * x)) := by
  have h := hasSum_gegenbauer_expansion (fun m => hν.ascPochhammer_ne_zero m) hre 0 (I * lam)
    (τ := jacobiEllipseRadius (0 - I * lam) (0 + I * lam) (0 + I * lam * x) + 1) (f := exp)
    differentiable_exp.differentiableOn (by linarith)
  simp only [zero_add, zero_sub] at h
  refine h.congr_fun fun n => ?_
  have hp : 0 < (ν + 1 / 2 + n).re := by
    rw [add_re, natCast_re]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hb := pair_mem_mvBetaConvergent hp hp
  have hS : carlsonDirichletAverage (pair (ν + 1 / 2 + n) (ν + 1 / 2 + n))
      (pair (-(I * lam)) (I * lam)) (iteratedDeriv n exp) =
      Gamma (ν + n + 1) * regularizedHGFun 0 {ν + n + 1} (-(lam / 2) ^ 2) := by
    rw [carlsonDirichletAverage, regCarlsonDirichletAverage_iteratedDeriv_exp,
      ← carlsonSIntegral_eq_Gamma_mul_reg, ← carlsonS_eq_integral hb,
      carlsonS_pair_self_neg_I_mul hp]
    rw [show ν + 1 / 2 + n + 1 / 2 = ν + n + 1 by ring]
  rw [hS, Gamma_add_nat_add_one_eq hν,
    show (I * lam / 2) ^ n = I ^ n * (lam / 2) ^ n by rw [mul_div_assoc, mul_pow]]
  have := hν.ascPochhammer_ne_zero n
  field_simp

/-- `J_a(x) = (x/2)^a F̃₀₁(a + 1; -(x/2)²)` with Mathlib's regularized `₀F₁`. -/
theorem besselJ_eq (a x : ℂ) :
    besselJ a x = (x / 2) ^ a * regularizedHGFun 0 {a + 1} (-(x / 2) ^ 2) := rfl

/-- `(x/2)^{-ν} J_{ν+n}(x) = (x/2)ⁿ F̃₀₁(ν + n + 1; -(x/2)²)` for `x ≠ 0`. -/
theorem cpow_neg_mul_besselJ_add_nat (ν : ℂ) {x : ℂ} (hx : x ≠ 0) (n : ℕ) :
    (x / 2) ^ (-ν) * besselJ (ν + n) x =
      (x / 2) ^ n * regularizedHGFun 0 {ν + n + 1} (-(x / 2) ^ 2) := by
  have hx2 : x / 2 ≠ 0 := div_ne_zero hx two_ne_zero
  rw [besselJ_eq, ← mul_assoc, ← cpow_add _ _ hx2, show -ν + (ν + n) = (n : ℂ) by ring,
    cpow_natCast]

/-- **Sonine's formula** (Exercise 7.7-1): for `ν` Gamma-regular with `re (ν + 1/2) > 0` and
`λ ≠ 0`, `e^{iλx} = Γ(ν) (λ/2)^{-ν} ∑ₙ iⁿ (ν + n) J_{ν+n}(λ) Cₙ^ν(x)`. Carlson writes the
prefactor as `2^ν λ^{-ν}`. -/
theorem hasSum_exp_I_mul_besselJ_gegenbauer {ν : ℂ} (hν : IsGammaRegular ν)
    (hre : 0 < (ν + 1 / 2).re) {lam : ℂ} (hlam : lam ≠ 0) (x : ℂ) :
    HasSum (fun n : ℕ => Gamma ν * (lam / 2) ^ (-ν) *
        (I ^ n * (ν + n) * besselJ (ν + n) lam * (gegenbauer ν n).eval x))
      (exp (I * lam * x)) := by
  refine (hasSum_exp_I_mul_gegenbauer hν hre lam x).congr_fun fun n => ?_
  have h := cpow_neg_mul_besselJ_add_nat ν hlam n
  linear_combination (Gamma ν * I ^ n * (ν + n) * (gegenbauer ν n).eval x) * h

/-- Termwise Dirichlet average of the regularized `₀F₁`:
`F̃₀₁(c; ·)` averages to `∑ₘ R̃ₘ(b, z)/(m! Γ(c + m))`. -/
theorem hasSum_regCarlsonDirichletAverage_regularizedHGFun {ι : Type*} [Fintype ι]
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (c : ℂ) :
    HasSum (fun m : ℕ => regCarlsonRPolynomial m b z / (m.factorial * Gamma (c + m)))
      (regCarlsonDirichletAverage b z (regularizedHGFun 0 {c})) := by
  set R : ℝ := ∑ i, ‖z i‖
  have hR : 0 ≤ R := by positivity
  have h := hasSum_regCarlsonR_of_powerSeries hb 0
    (fun m => 1 / (m.factorial * Gamma (c + m))) z (regularizedHGFun 0 {c})
    (fun m => ‖(R : ℂ) ^ m / (m.factorial * Gamma (c + m))‖)
    (summable_norm_regularizedHGFun_zero_singleton c R) (fun m u hu => ?_) (fun u _ => ?_)
  · have hz : shiftCarlsonVariables 0 z = z := by funext i; simp [shiftCarlsonVariables]
    rw [hz] at h
    exact h.congr_fun fun m => by ring
  · rw [sub_zero, norm_mul, norm_div, norm_one, norm_div, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hR, one_div, inv_mul_eq_div]
    gcongr
    exact norm_carlsonAffineForm_le_sum_norm z hu
  · exact (hasSum_regularizedHGFun_zero_singleton c _).congr_fun fun m => by ring

/-- The Dirichlet average behind Example 7.7-4, from Exercise 7.1-9: for `re δ > 1/2`,
`F(δ - 1/2, δ - 1/2; (x + y)², (x - y)²)` of `F̃₀₁(δ; ·)` is
`Γ(δ) F̃₀₁(δ; x²) F̃₀₁(δ; y²)`. -/
theorem carlsonDirichletAverage_regularizedHGFun {δ : ℂ} (hδ : 1 / 2 < δ.re) (x y : ℂ) :
    carlsonDirichletAverage (pair (δ - 1 / 2) (δ - 1 / 2)) (pair ((x + y) ^ 2) ((x - y) ^ 2))
        (regularizedHGFun 0 {δ}) =
      Gamma δ * regularizedHGFun 0 {δ} (x ^ 2) * regularizedHGFun 0 {δ} (y ^ 2) := by
  have hp : 0 < (δ - 1 / 2).re := by
    rw [sub_re]; norm_num; linarith
  have hδ0 : IsGammaRegular δ := .of_re_pos (by linarith)
  have h2δ : IsGammaRegular (2 * δ - 1) := .of_re_pos (by
    simp only [sub_re, mul_re]; norm_num; linarith)
  have hG := Gamma_ne_zero hδ0
  have H := hasSum_zeroFOne_mul_zeroFOne (fun m => hδ0.ascPochhammer_ne_zero m)
    (fun m => h2δ.ascPochhammer_ne_zero m) x y
  have hS (w : ℂ) : (∑' m : ℕ, (w ^ 2) ^ m / ((ascPochhammer ℂ m).eval δ * m.factorial)) =
      Gamma δ * regularizedHGFun 0 {δ} (w ^ 2) := by
    refine HasSum.tsum_eq (((hasSum_regularizedHGFun_zero_singleton δ (w ^ 2)).mul_left
      (Gamma δ)).congr_fun fun m => ?_)
    rw [Complex.Gamma_add_nat_eq_ascPochhammer_mul hδ0]
    have := hδ0.ascPochhammer_ne_zero m
    have : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    field_simp
  rw [hS, hS] at H
  have hA := (hasSum_regCarlsonDirichletAverage_regularizedHGFun
    (pair_mem_mvBetaConvergent hp hp) (pair ((x + y) ^ 2) ((x - y) ^ 2)) δ).mul_left
    (Gamma (∑ i, pair (δ - 1 / 2) (δ - 1 / 2) i))
  rw [carlsonDirichletAverage]
  refine hA.unique ((H.div_const (Gamma δ)).congr_fun fun m => ?_) |>.trans ?_
  · rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, carlsonRPolynomialNumerator_pair,
      sum_pair, show δ - 1 / 2 + (δ - 1 / 2) = 2 * δ - 1 by ring,
      Complex.Gamma_add_nat_eq_ascPochhammer_mul h2δ,
      Complex.Gamma_add_nat_eq_ascPochhammer_mul hδ0]
    have := hδ0.ascPochhammer_ne_zero m
    have := h2δ.ascPochhammer_ne_zero m
    have := Gamma_ne_zero h2δ
    have : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    field_simp
  · field_simp

/-- **Gegenbauer's addition theorem** (Example 7.7-4, equation (12) after the change of notation
leading to (13)), with the regularized `₀F₁`: for `ν` Gamma-regular with `re (ν + 1/2) > 0`,
`F̃₀₁(ν + 1; -(A² + B² - 2ABx)/4) =
Γ(ν) ∑ₙ (ν + n) (AB/4)ⁿ F̃₀₁(ν + n + 1; -(A/2)²) F̃₀₁(ν + n + 1; -(B/2)²) Cₙ^ν(x)`. -/
theorem hasSum_regularizedHGFun_gegenbauer_addition {ν : ℂ} (hν : IsGammaRegular ν)
    (hre : 0 < (ν + 1 / 2).re) (A B x : ℂ) :
    HasSum (fun n : ℕ => Gamma ν * (ν + n) * (A * B / 4) ^ n *
        regularizedHGFun 0 {ν + n + 1} (-(A / 2) ^ 2) *
        regularizedHGFun 0 {ν + n + 1} (-(B / 2) ^ 2) * (gegenbauer ν n).eval x)
      (regularizedHGFun 0 {ν + 1} (-(A ^ 2 + B ^ 2 - 2 * A * B * x) / 4)) := by
  set A' : ℂ := -(A ^ 2 + B ^ 2) / 4
  set B' : ℂ := A * B / 2
  have hf : Differentiable ℂ (regularizedHGFun 0 {ν + 1}) := fun y =>
    (hasDerivAt_regularizedHGFun_zero_singleton _ y).differentiableAt
  have h := hasSum_gegenbauer_expansion (fun m => hν.ascPochhammer_ne_zero m) hre A' B'
    (τ := jacobiEllipseRadius (A' - B') (A' + B') (A' + B' * x) + 1) hf.differentiableOn
    (by linarith)
  rw [show A' + B' * x = -(A ^ 2 + B ^ 2 - 2 * A * B * x) / 4 by simp only [A', B']; ring] at h
  refine h.congr_fun fun n => ?_
  have hδ : 1 / 2 < (ν + n + 1).re := by
    simp only [add_re, natCast_re, one_re]
    have : (ν + 1 / 2).re = ν.re + 1 / 2 := by simp
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hav := carlsonDirichletAverage_regularizedHGFun hδ (I * A / 2) (I * B / 2)
  have e1 : (I * A / 2 + I * B / 2) ^ 2 = A' - B' := by
    simp only [A', B']; linear_combination ((A + B) ^ 2 / 4) * I_sq
  have e2 : (I * A / 2 - I * B / 2) ^ 2 = A' + B' := by
    simp only [A', B']; linear_combination ((A - B) ^ 2 / 4) * I_sq
  have e3 (w : ℂ) : (I * w / 2) ^ 2 = -(w / 2) ^ 2 := by linear_combination (w ^ 2 / 4) * I_sq
  rw [e1, e2, e3, e3, show ν + n + 1 - 1 / 2 = ν + 1 / 2 + n by ring] at hav
  rw [iteratedDeriv_regularizedHGFun_zero_singleton, show ν + 1 + (n : ℂ) = ν + n + 1 by ring,
    hav, Gamma_add_nat_add_one_eq hν, show B' / 2 = A * B / 4 by simp only [B']; ring]
  have := hν.ascPochhammer_ne_zero n
  field_simp

/-- **Gegenbauer's addition theorem for Bessel functions** (Example 7.7-4, equation (13)): if
`w² = A² + B² - 2ABx` with `A, B, w ≠ 0`, `ν` Gamma-regular and `re (ν + 1/2) > 0`, then
`(w/2)^{-ν} J_ν(w) = Γ(ν) ∑ₙ (ν + n) (A/2)^{-ν} J_{ν+n}(A) (B/2)^{-ν} J_{ν+n}(B) Cₙ^ν(x)`.
Carlson writes the prefactors as `w^{-ν}` and `2^ν (AB)^{-ν}`. -/
theorem hasSum_besselJ_gegenbauer_addition {ν : ℂ} (hν : IsGammaRegular ν)
    (hre : 0 < (ν + 1 / 2).re) {A B w : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hw : w ≠ 0) (x : ℂ)
    (hwx : w ^ 2 = A ^ 2 + B ^ 2 - 2 * A * B * x) :
    HasSum (fun n : ℕ => Gamma ν * ((ν + n) * ((A / 2) ^ (-ν) * besselJ (ν + n) A) *
        ((B / 2) ^ (-ν) * besselJ (ν + n) B) * (gegenbauer ν n).eval x))
      ((w / 2) ^ (-ν) * besselJ ν w) := by
  have h0 := cpow_neg_mul_besselJ_add_nat ν hw 0
  simp only [Nat.cast_zero, add_zero, pow_zero, one_mul] at h0
  rw [h0, show -(w / 2) ^ 2 = -(A ^ 2 + B ^ 2 - 2 * A * B * x) / 4 by rw [div_pow, hwx]; ring]
  refine (hasSum_regularizedHGFun_gegenbauer_addition hν hre A B x).congr_fun fun n => ?_
  rw [cpow_neg_mul_besselJ_add_nat ν hA, cpow_neg_mul_besselJ_add_nat ν hB,
    show A * B / 4 = A / 2 * (B / 2) by ring, mul_pow]
  ring

/-- `Γ(1/2) = √π` as a complex number. -/
theorem Gamma_one_half_eq_sqrt : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  push_cast; ring_nf

/-- **Spherical-wave addition theorem** (Example 7.7-4, equation (14)): if
`w² = A² + B² - 2ABx`, then `j₀(w) = ∑ₙ (2n + 1) jₙ(A) jₙ(B) Pₙ(x)`, with `Pₙ = Cₙ^{1/2}`.
For `A = kr`, `B = kr'`, `x = cos θ` and `w = k|r - r'|`, Carlson writes the left side as
`sin w / w`. -/
theorem hasSum_sphericalBesselJ_legendre_addition {A B w : ℂ} (x : ℂ)
    (hwx : w ^ 2 = A ^ 2 + B ^ 2 - 2 * A * B * x) :
    HasSum (fun n : ℕ => (2 * n + 1) * sphericalBesselJ n A * sphericalBesselJ n B *
        (gegenbauer (1 / 2 : ℂ) n).eval x)
      (sphericalBesselJ 0 w) := by
  have hν : IsGammaRegular (1 / 2 : ℂ) := .of_re_pos (by norm_num)
  have H := (hasSum_regularizedHGFun_gegenbauer_addition hν (by norm_num) A B x).mul_left
    ((Real.sqrt π : ℂ) / 2)
  rw [sphericalBesselJ, pow_zero, mul_one, Nat.cast_zero, zero_add,
    show -(w / 2) ^ 2 = -(A ^ 2 + B ^ 2 - 2 * A * B * x) / 4 by rw [div_pow, hwx]; ring,
    show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num]
  refine H.congr_fun fun n => ?_
  rw [sphericalBesselJ, sphericalBesselJ, Gamma_one_half_eq_sqrt,
    show (n : ℂ) + 3 / 2 = 1 / 2 + n + 1 by ring, show A * B / 4 = A / 2 * (B / 2) by ring,
    mul_pow]
  ring

/-- **Exercise 7.7-6** (Graf's addition theorem for `J₀`): if `w² = A² + B² - 2AB cos θ` with
`A, B ≠ 0`, then `J₀(w) = J₀(A) J₀(B) + 2 ∑_{n ≥ 1} Jₙ(A) Jₙ(B) cos nθ`. -/
theorem hasSum_besselJ_zero_addition {A B w : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (θ : ℂ)
    (hw : w ^ 2 = A ^ 2 + B ^ 2 - 2 * A * B * cos θ) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2) * besselJ n A * besselJ n B * cos (n * θ))
      (besselJ 0 w) := by
  set A' : ℂ := -(A ^ 2 + B ^ 2) / 4
  set B' : ℂ := A * B / 2
  have hB' : B' ≠ 0 := div_ne_zero (mul_ne_zero hA hB) two_ne_zero
  have hf : Differentiable ℂ (regularizedHGFun 0 {1}) := fun y =>
    (hasDerivAt_regularizedHGFun_zero_singleton _ y).differentiableAt
  have H := hasSum_fourier_cosine A' B' hB' (h := |θ.im| + 1) hf.differentiableOn
    (by linarith)
  rw [besselJ_eq, cpow_zero, one_mul, zero_add,
    show -(w / 2) ^ 2 = A' + B' * cos θ by rw [div_pow, hw]; simp only [A', B']; ring]
  refine H.congr_fun fun n => ?_
  have hδ : 1 / 2 < ((n : ℂ) + 1).re := by
    simp only [add_re, natCast_re, one_re]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hav := carlsonDirichletAverage_regularizedHGFun hδ (I * A / 2) (I * B / 2)
  have e1 : (I * A / 2 + I * B / 2) ^ 2 = A' - B' := by
    simp only [A', B']; linear_combination ((A + B) ^ 2 / 4) * I_sq
  have e2 : (I * A / 2 - I * B / 2) ^ 2 = A' + B' := by
    simp only [A', B']; linear_combination ((A - B) ^ 2 / 4) * I_sq
  have e3 (z : ℂ) : (I * z / 2) ^ 2 = -(z / 2) ^ 2 := by linear_combination (z ^ 2 / 4) * I_sq
  rw [e1, e2, e3, e3, show (n : ℂ) + 1 - 1 / 2 = 1 / 2 + n by ring,
    Complex.Gamma_nat_eq_factorial] at hav
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [iteratedDeriv_regularizedHGFun_zero_singleton, show (1 : ℂ) + n = n + 1 by ring, hav,
    besselJ_eq, besselJ_eq, cpow_natCast, cpow_natCast,
    show B' ^ n / (n.factorial * 2 ^ n) = (A / 2) ^ n * (B / 2) ^ n / n.factorial by
      simp only [B']; rw [← mul_pow, show A / 2 * (B / 2) = A * B / 2 / 2 by ring,
        div_pow (A * B / 2) 2 n, div_div, mul_comm (2 ^ n : ℂ)]]
  field_simp

/-- **Exercise 7.7-7**: for `A ≠ 0`, `sin (θ/2) ≠ 0`, `ν` Gamma-regular and `re (ν + 1/2) > 0`,
`(A sin (θ/2))^{-ν} J_ν(2A sin (θ/2)) = Γ(ν) ∑ₙ (ν + n) [(A/2)^{-ν} J_{ν+n}(A)]² Cₙ^ν(cos θ)`.
Carlson writes the prefactors as `(2A sin (θ/2))^{-ν}` and `2^ν A^{-2ν}`. -/
theorem hasSum_besselJ_gegenbauer_sin_half {ν : ℂ} (hν : IsGammaRegular ν)
    (hre : 0 < (ν + 1 / 2).re) {A θ : ℂ} (hA : A ≠ 0) (hθ : sin (θ / 2) ≠ 0) :
    HasSum (fun n : ℕ => Gamma ν * ((ν + n) * ((A / 2) ^ (-ν) * besselJ (ν + n) A) ^ 2 *
        (gegenbauer ν n).eval (cos θ)))
      ((A * sin (θ / 2)) ^ (-ν) * besselJ ν (2 * A * sin (θ / 2))) := by
  have hw : 2 * A * sin (θ / 2) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hA) hθ
  have hc : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have h2 := cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linear_combination h2 + 2 * cos_sq_add_sin_sq (θ / 2)
  have H := hasSum_besselJ_gegenbauer_addition hν hre hA hA hw (cos θ) (by rw [hc]; ring)
  rw [show 2 * A * sin (θ / 2) / 2 = A * sin (θ / 2) by ring] at H
  exact H.congr_fun fun n => by ring

/-- `∫₀^{2π} e^{ikθ} dθ = 2π δ_{k0}` for an integer `k`. -/
theorem integral_exp_int_mul_I (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (k * θ * I) = if k = 0 then 2 * (π : ℂ) else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp only [ofReal_zero, mul_zero, exp_zero] at h
    rw [show ((k : ℂ) * I * ((2 * π : ℝ) : ℂ)) = k * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I, sub_self, zero_div] at h
    rw [← h]
    congr 1; funext θ; ring_nf

/-- The Bessel coefficients are absolutely summable over the integers. -/
theorem summable_norm_besselJ_int (x : ℂ) : Summable fun m : ℤ => ‖besselJ m x‖ := by
  have h := summable_I_zpow_mul_besselJ_mul_exp x 0
  set C := Real.exp (‖x‖ ^ 2 / 4)
  have hs : Summable fun n : ℕ => C * ((‖x‖ / 2) ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial _).mul_left C
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
    simpa using norm_besselJ_intCast_le n x
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hs)
    have := norm_besselJ_intCast_le (-(n + 1 : ℕ)) x
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at this
    simpa using this

/-- **Bessel's integral** (Exercise 7.7-3, first form): for `n ∈ ℤ` and `x ∈ ℂ`,
`2π Jₙ(x) = ∫₀^{2π} exp(ix sin θ - inθ) dθ`. -/
theorem two_pi_mul_besselJ_eq_integral (n : ℤ) (x : ℂ) :
    2 * π * besselJ n x = ∫ θ in (0 : ℝ)..2 * π, exp (I * x * sin θ - n * θ * I) := by
  set F : ℤ → ℝ → ℂ := fun m θ => besselJ m x * exp (((m - n : ℤ) : ℂ) * θ * I)
  have hnorm (k : ℤ) (θ : ℝ) : ‖exp ((k : ℂ) * θ * I)‖ = 1 := by
    rw [show (k : ℂ) * θ * I = ((k * θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * π) (F := F) (f := fun θ : ℝ => exp (I * x * sin θ - n * θ * I))
    (fun m _ => ‖besselJ m x‖)
    (fun m => (by fun_prop : Continuous (F m)).aestronglyMeasurable)
    (fun m => .of_forall fun θ _ => by simp only [F, norm_mul, hnorm, mul_one]; rfl)
    (.of_forall fun _ _ => summable_norm_besselJ_int x) intervalIntegrable_const
    (.of_forall fun θ _ => by
      have h := (hasSum_exp_I_mul_mul_sin_int x θ).mul_right (exp (-(n * θ * I)))
      rw [← exp_add, ← sub_eq_add_neg] at h
      refine h.congr_fun fun m => ?_
      simp only [F]
      rw [mul_assoc (besselJ (m : ℂ) x) (exp _), ← exp_add]
      congr 2; push_cast; ring)
  have hint (m : ℤ) : ∫ θ in (0 : ℝ)..2 * π, F m θ = if m = n then 2 * π * besselJ n x else 0 := by
    simp only [F]
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
    simp only [sub_eq_zero]
    split_ifs with h
    · rw [h]; ring
    · ring
  simp only [hint] at H
  exact (H.unique (hasSum_ite_eq n _)).symm

/-- **Bessel's integral** (Exercise 7.7-3, second form): for `n ∈ ℤ` and `x ∈ ℂ`,
`2π Jₙ(x) = 2 ∫₀^π cos(x sin θ - nθ) dθ`. -/
theorem two_pi_mul_besselJ_eq_integral_cos (n : ℤ) (x : ℂ) :
    2 * π * besselJ n x = 2 * ∫ θ in (0 : ℝ)..π, cos (x * sin θ - n * θ) := by
  set g : ℝ → ℂ := fun θ => exp (I * x * sin θ - n * θ * I)
  have hc : Continuous g := by fun_prop
  rw [two_pi_mul_besselJ_eq_integral, ← intervalIntegral.integral_add_adjacent_intervals
    (b := π) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h2 : ∫ θ in π..2 * π, g θ = ∫ θ in (0 : ℝ)..π, g (2 * π - θ) := by
    rw [intervalIntegral.integral_comp_sub_left]; norm_num; ring_nf
  have hg (θ : ℝ) : g (2 * π - θ) = exp (-(x * sin θ - n * θ) * I) := by
    simp only [g]
    push_cast
    rw [sin_two_pi_sub, show I * x * -sin (θ : ℂ) - n * (2 * π - θ) * I =
      -(x * sin θ - n * θ) * I + (-n : ℤ) * (2 * π * I) by push_cast; ring, exp_add,
      exp_int_mul_two_pi_mul_I, mul_one]
  have hcos (θ : ℝ) : g θ + exp (-(x * sin θ - n * θ) * I) = 2 * cos (x * sin θ - n * θ) := by
    rw [two_cos]; simp only [g]; ring_nf
  simp only [h2, hg]
  rw [← intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => exp (-(x * sin θ - n * θ) * I)).intervalIntegrable _ _)]
  simp only [hcos, intervalIntegral.integral_const_mul]

/-- The Euler integral `∫₀¹ yᵐ (1 - y)ᵐ e^{ix(1 - 2y)} dy` as a spherical-Bessel value:
`(2m+1)!/(m!)²` times it is `Γ(m + 3/2) F̃₀₁(m + 3/2; -(x/2)²)`. -/
theorem integral_pow_mul_one_sub_pow_mul_exp (m : ℕ) (x : ℂ) :
    ((2 * m + 1).factorial : ℂ) / (m.factorial : ℂ) ^ 2 *
        ∫ y in (0 : ℝ)..1, (y : ℂ) ^ m * (1 - (y : ℂ)) ^ m * exp (I * x * (1 - 2 * y)) =
      Gamma (m + 1 + 1 / 2) * regularizedHGFun 0 {(m : ℂ) + 1 + 1 / 2} (-(x / 2) ^ 2) := by
  have hre : 0 < ((m : ℂ) + 1).re := by simp; positivity
  have hb := pair_mem_mvBetaConvergent hre hre
  rw [← carlsonS_pair_self_neg_I_mul hre, carlsonS, regCarlsonS_eq_integral hb, regCarlsonSIntegral,
    regCarlsonDirichletAverage_pair_eq, regEulerIntegral, sum_pair,
    show (m : ℂ) + 1 + (m + 1) = ((2 * m + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hint : ∫ y in Set.Ioo (0 : ℝ) 1, (y : ℂ) ^ m * (1 - (y : ℂ)) ^ m *
        exp (I * x * (1 - 2 * y)) =
      ∫ u in Set.Ioo (0 : ℝ) 1, (u : ℂ) ^ ((m : ℂ) + 1 - 1) * (1 - u : ℂ) ^ ((m : ℂ) + 1 - 1) *
        exp ((u : ℂ) * -(I * x) + (1 - u : ℂ) * (I * x)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    simp only [add_sub_cancel_right, cpow_natCast]
    congr 2; ring
  rw [hint]
  have : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

/-- **Exercise 7.8-7**: `∫₋₁¹ e^{ixy} Pₘ(y) dy = 2 iᵐ jₘ(x)` for the Legendre polynomial
`Pₘ = Cₘ^{1/2}` and the spherical Bessel function `jₘ`. -/
theorem integral_exp_mul_legendre (m : ℕ) (x : ℂ) :
    ∫ y in (-1 : ℝ)..1, exp (I * x * y) * (gegenbauer (1 / 2 : ℂ) m).eval (y : ℂ) =
      2 * I ^ m * sphericalBesselJ m x := by
  set f : ℂ → ℂ := fun y => exp (I * x * y)
  have hrep := jacobiSegmentIntegral_mul_jacobiOn (α := 0) (β := 0) (by norm_num) (by norm_num)
    (r := -1) (s := 1) (by norm_num) isOpen_univ (Set.subset_univ _) (f := f)
    (by fun_prop : Differentiable ℂ f).differentiableOn m
  set p := jacobiOn (0 : ℂ) 0 (-1) 1 m
  set K := ∫ y in (0 : ℝ)..1, (y : ℂ) ^ m * (1 - (y : ℂ)) ^ m * exp (I * x * (1 - 2 * y))
  have hL : jacobiSegmentIntegral 0 0 (-1) 1 (fun y => f y * p.eval y) =
      ∫ y in (-1 : ℝ)..1, f y * p.eval (y : ℂ) := by
    unfold jacobiSegmentIntegral
    simp only [cpow_zero, mul_one]
    have hc := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1)
      (f := fun y : ℝ => f y * p.eval (y : ℂ)) (two_ne_zero) (-1)
    norm_num at hc
    rw [show (1 : ℂ) - -1 = 2 by norm_num]
    convert congrArg (fun z => 2 * z) hc using 1
    · congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring_nf
    · field_simp
  have hR : (1 - -1 : ℂ) ^ ((0 : ℂ) + 0 + 1) * (1 - -1 : ℂ) ^ (2 * m) /
        (ascPochhammer ℂ m).eval (0 + 0 + (m : ℂ) + 1) *
        ∫ y in (0 : ℝ)..1, complexJacobiWeight (0 + m) (0 + m) y *
          iteratedDeriv m f ((-1 - 1) * y + 1) =
      2 * 4 ^ m / (ascPochhammer ℂ m).eval ((m : ℂ) + 1) * (I * x) ^ m * K := by
    rw [iteratedDeriv_cexp_const_mul, show (1 - -1 : ℂ) = 2 by norm_num,
      show (0 : ℂ) + 0 + 1 = 1 by norm_num, cpow_one, pow_mul, show (2 : ℂ) ^ 2 = 4 by norm_num,
      show (0 : ℂ) + 0 + m + 1 = m + 1 by ring, zero_add]
    have hK : (∫ y in (0 : ℝ)..1, complexJacobiWeight m m y *
        ((I * x) ^ m * exp (I * x * ((-1 - 1) * y + 1)))) = (I * x) ^ m * K := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [complexJacobiWeight, cpow_natCast]
      ring_nf
    rw [hK]; ring
  rw [hL, hR] at hrep
  set D := (ascPochhammer ℂ m).eval (1 / 2 : ℂ)
  have hD0 : D ≠ 0 := ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) m
  have hf0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hD : (2 * m).factorial = 4 ^ m * D * m.factorial := by
    have h := ascPochhammer_eval_double (1 / 2 : ℂ) m
    rw [show 2 * (1 / 2 : ℂ) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      ascPochhammer_eval_one, ascPochhammer_eval_one] at h
    exact_mod_cast h
  have hP : (ascPochhammer ℂ m).eval ((m : ℂ) + 1) = 4 ^ m * D := by
    have h := congrArg (Nat.cast : ℕ → ℂ) (Nat.factorial_mul_ascFactorial m m)
    rw [← ascPochhammer_nat_eq_ascFactorial] at h
    push_cast at h
    rw [← two_mul, hD] at h
    exact mul_left_cancel₀ hf0 (by rw [h]; ring)
  have hfac : ((2 * m + 1).factorial : ℂ) = (2 * m + 1) * (4 ^ m * D * m.factorial) := by
    rw [Nat.factorial_succ]; push_cast; rw [hD]
  have hG : Gamma ((m : ℂ) + 1 + 1 / 2) = D * (m + 1 / 2) * (Real.sqrt π : ℂ) := by
    have h := Complex.Gamma_add_nat_eq_ascPochhammer_mul
      (IsGammaRegular.of_re_pos (by norm_num : 0 < (1 / 2 : ℂ).re)) (m + 1)
    rw [ascPochhammer_succ_eval, Gamma_one_half_eq_sqrt] at h
    push_cast at h
    rw [show (m : ℂ) + 1 + 1 / 2 = 1 / 2 + (m + 1) by ring, h]
    ring
  have hE : ((2 * m + 1).factorial : ℂ) / (m.factorial : ℂ) ^ 2 * K = _ :=
    integral_pow_mul_one_sub_pow_mul_exp m x
  rw [hfac, hG] at hE
  have hK : K = D * (m + 1 / 2) * (Real.sqrt π : ℂ) *
      regularizedHGFun 0 {(m : ℂ) + 1 + 1 / 2} (-(x / 2) ^ 2) * (m.factorial : ℂ) ^ 2 /
      ((2 * m + 1) * (4 ^ m * D * m.factorial)) := by
    have h2m : (2 * (m : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < 2 * m + 1 := by positivity
      intro h; have := congrArg re h; simp at this; linarith
    have h4 : (4 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [eq_div_iff (mul_ne_zero h2m (mul_ne_zero (mul_ne_zero h4 hD0) hf0)), ← hE]
    field_simp
  have hLeg (y : ℝ) : (gegenbauer (1 / 2 : ℂ) m).eval (y : ℂ) =
      2 ^ m * D / m.factorial * p.eval (y : ℂ) := by
    have hJ := eval_jacobiOn_gegenbauer 1 (y : ℂ) m
      (by rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact hD0)
      (ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) m)
    rw [show (1 : ℂ) - 1 = 0 by ring, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hJ
    field_simp
    linear_combination -hJ
  have hI : ∫ y in (-1 : ℝ)..1, exp (I * x * y) * (gegenbauer (1 / 2 : ℂ) m).eval (y : ℂ) =
      2 ^ m * D / m.factorial * ∫ y in (-1 : ℝ)..1, f y * p.eval (y : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hLeg, f]; ring
  rw [hI, hrep, hK, hP, sphericalBesselJ, show (m : ℂ) + 3 / 2 = m + 1 + 1 / 2 by ring,
    div_pow x 2 m, show (4 : ℂ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
  have h2m : (2 * (m : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < 2 * m + 1 := by positivity
    intro h; have := congrArg re h; simp at this; linarith
  field_simp
  ring

/-- **Exercise 7.1-10**: `J₀(2t sin θ) I₀(2t cos θ) = ∑ₙ t²ⁿ/(n!)² Pₙ(cos 2θ)`, with
`Pₙ = Cₙ^{1/2}`. -/
theorem hasSum_besselJ_zero_mul_besselI_zero (t θ : ℂ) :
    HasSum (fun n : ℕ => t ^ (2 * n) / (n.factorial * n.factorial) *
        (gegenbauer (1 / 2 : ℂ) n).eval (cos (2 * θ)))
      (besselJ 0 (2 * t * sin θ) * besselI 0 (2 * t * cos θ)) := by
  have h1 (m : ℕ) : (ascPochhammer ℂ m).eval (1 : ℂ) ≠ 0 := by
    rw [ascPochhammer_eval_one]; exact_mod_cast m.factorial_ne_zero
  have H := hasSum_zeroFOne_mul_zeroFOne (δ := 1) h1
    (fun m => by rw [show (2 : ℂ) * 1 - 1 = 1 by norm_num]; exact h1 m) (I * t * sin θ) (t * cos θ)
  have hS (z : ℂ) : ∑' m : ℕ, z ^ m / ((ascPochhammer ℂ m).eval (1 : ℂ) * m.factorial) =
      regularizedHGFun 0 {1} z := by
    refine HasSum.tsum_eq ((hasSum_regularizedHGFun_zero_singleton 1 z).congr_fun fun m => ?_)
    rw [ascPochhammer_eval_one, add_comm, Complex.Gamma_nat_eq_factorial]
  rw [hS, hS] at H
  have e1 : -(2 * t * sin θ / 2) ^ 2 = (I * t * sin θ) ^ 2 := by
    linear_combination (-(t * sin θ) ^ 2) * I_sq
  rw [besselJ_eq, besselI, cpow_zero, cpow_zero, one_mul, one_mul, zero_add, e1,
    show (2 * t * cos θ / 2) ^ 2 = (t * cos θ) ^ 2 by ring]
  refine H.congr_fun fun n => ?_
  set w := exp (2 * θ * I)
  have hw : w ≠ 0 := exp_ne_zero _
  have hp : (I * t * sin θ + t * cos θ) ^ 2 = t ^ 2 * w := by
    rw [show w = exp (θ * I) * exp (θ * I) by simp only [w, ← exp_add]; ring_nf, exp_mul_I]
    ring
  have hm : (I * t * sin θ - t * cos θ) ^ 2 = t ^ 2 * w⁻¹ := by
    rw [show w⁻¹ = exp (-θ * I) * exp (-θ * I) by simp only [w, ← exp_neg, ← exp_add]; ring_nf,
      exp_mul_I, cos_neg, sin_neg]
    ring
  have hc : cos (2 * θ) = (w + w⁻¹) / 2 := cos_eq_exp_add_inv _
  rw [hp, hm, carlsonRPolynomialNumerator₂_smul, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num,
    ← factorial_mul_eval_gegenbauer _ _ hw, ← hc, show (2 : ℂ) * 1 - 1 = 1 by norm_num,
    ascPochhammer_eval_one, ← pow_mul]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- `‖(-n)ₖ (2ν + n)ₖ‖ ≤ (n (‖2ν‖ + 2n))ᵏ`. -/
theorem norm_ascPochhammer_neg_mul_le (ν : ℂ) (n k : ℕ) :
    ‖(ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval (2 * ν + n)‖ ≤
      ((n : ℝ) * (‖2 * ν‖ + 2 * n)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : n ≤ k
    · rw [(ascPochhammer_eval_eq_zero_iff _ _).mpr ⟨n, by omega, by ring⟩, zero_mul, norm_zero]
      positivity
    · push Not at hk
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, pow_succ]
      have h1 : ‖-(n : ℂ) + k‖ ≤ n := by
        rw [show -(n : ℂ) + k = ((-(n : ℝ) + k : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(Nat.cast_le (α := ℝ)).mpr hk.le]
      have h2 : ‖2 * ν + n + k‖ ≤ ‖2 * ν‖ + 2 * n := by
        calc ‖2 * ν + n + k‖ ≤ ‖2 * ν‖ + ‖(n : ℂ)‖ + ‖(k : ℂ)‖ := norm_add₃_le
          _ ≤ ‖2 * ν‖ + 2 * n := by
            rw [Complex.norm_natCast, Complex.norm_natCast]
            linarith [(Nat.cast_le (α := ℝ)).mpr hk.le]
      calc ‖(ascPochhammer ℂ k).eval (-(n : ℂ)) * (-(n : ℂ) + k) *
            ((ascPochhammer ℂ k).eval (2 * ν + n) * (2 * ν + n + k))‖
          = ‖(ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval (2 * ν + n)‖ *
              (‖-(n : ℂ) + k‖ * ‖2 * ν + n + k‖) := by
            rw [← norm_mul, ← norm_mul]; ring_nf
        _ ≤ ((n : ℝ) * (‖2 * ν‖ + 2 * n)) ^ k * (n * (‖2 * ν‖ + 2 * n)) := by
            gcongr

/-- `n sin (t/(2n)) → t/2` as `n → ∞`. -/
theorem tendsto_natCast_mul_sin_div (t : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) * sin (t / (2 * n))) atTop (𝓝 (t / 2)) := by
  by_cases ht : t = 0
  · subst ht; simp
  have hw : Tendsto (fun n : ℕ => t / (2 * n)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (tendsto_const_div_atTop_nhds_zero_nat (t / 2)).congr fun n => div_div t 2 n
    · filter_upwards [eventually_ne_atTop 0] with n hn
      simp [ht, hn]
  have hs := ((Complex.hasDerivAt_sin 0).tendsto_slope_zero.comp hw).const_mul (t / 2)
  simp only [zero_add, sin_zero, sub_zero, cos_zero, mul_one, smul_eq_mul,
    Function.comp_def] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- The factor limit `(-n + k)(2ν + n + k) sin² (t/(2n)) → -(t/2)²`. -/
theorem tendsto_factor_sin_sq (ν t : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => (-(n : ℂ) + k) * (2 * ν + n + k) * sin (t / (2 * n)) ^ 2) atTop
      (𝓝 (-(t / 2) ^ 2)) := by
  have h1 : Tendsto (fun n : ℕ => -1 + (k : ℂ) / n) atTop (𝓝 (-1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  have h2 : Tendsto (fun n : ℕ => 1 + (2 * ν + k) / n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  have h3 := (tendsto_natCast_mul_sin_div t).pow 2
  have h := (h1.mul h2).mul h3
  rw [show (-1 + 0 : ℂ) * (1 + 0) * (t / 2) ^ 2 = -(t / 2) ^ 2 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-- The termwise limit `(-n)ₖ (2ν + n)ₖ sin^{2k}(t/(2n)) → (-(t/2)²)ᵏ`. -/
theorem tendsto_ascPochhammer_mul_sin_pow (ν t : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => (ascPochhammer ℂ k).eval (-(n : ℂ)) *
      (ascPochhammer ℂ k).eval (2 * ν + n) * (sin (t / (2 * n)) ^ 2) ^ k) atTop
        (𝓝 ((-(t / 2) ^ 2) ^ k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ih.mul (tendsto_factor_sin_sq ν t k)
    rw [← pow_succ] at h
    refine h.congr fun n => ?_
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, pow_succ]; ring

/-- `‖sin w‖ ≤ 2‖w‖` for `‖w‖ ≤ 1`. -/
theorem norm_sin_le_two_mul {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖sin w‖ ≤ 2 * ‖w‖ := by
  have hb := sin_bound hw
  have h3 : ‖w ^ 3 / 6‖ ≤ ‖w‖ / 6 := by
    rw [norm_div, norm_pow, RCLike.norm_ofNat]
    have : ‖w‖ ^ 3 ≤ ‖w‖ := by
      calc ‖w‖ ^ 3 = ‖w‖ * ‖w‖ ^ 2 := by ring
        _ ≤ ‖w‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hw
        _ = ‖w‖ := mul_one _
    linarith
  have h5 : ‖w‖ ^ 5 / 100 ≤ ‖w‖ / 100 := by
    have : ‖w‖ ^ 5 ≤ ‖w‖ := by
      calc ‖w‖ ^ 5 = ‖w‖ * ‖w‖ ^ 4 := by ring
        _ ≤ ‖w‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hw
        _ = ‖w‖ := mul_one _
    linarith
  calc ‖sin w‖ ≤ ‖sin w - (w - w ^ 3 / 6)‖ + ‖w - w ^ 3 / 6‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖w‖ ^ 5 / 100 + (‖w‖ + ‖w ^ 3 / 6‖) := add_le_add hb (norm_sub_le _ _)
    _ ≤ 2 * ‖w‖ := by linarith [norm_nonneg w]

/-- The uniform bound `‖(-n)ₖ (2ν + n)ₖ sin^{2k}(t/(2n))‖ ≤ ((‖2ν‖ + 2) ‖t‖²)ᵏ` for
`n ≥ max 1 ‖t‖`. -/
theorem norm_ascPochhammer_mul_sin_pow_le (ν t : ℂ) {n : ℕ} (hn : 1 ≤ n) (ht : ‖t‖ ≤ n)
    (k : ℕ) :
    ‖(ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval (2 * ν + n) *
      (sin (t / (2 * n)) ^ 2) ^ k‖ ≤ ((‖2 * ν‖ + 2) * ‖t‖ ^ 2) ^ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ‖t / (2 * n)‖ = ‖t‖ / (2 * n) := by
    rw [norm_div, norm_mul, RCLike.norm_ofNat, Complex.norm_natCast]
  have hw1 : ‖t / (2 * n)‖ ≤ 1 := by
    rw [hw, div_le_one (by positivity)]; linarith
  have hs : ‖sin (t / (2 * n)) ^ 2‖ ≤ (‖t‖ / n) ^ 2 := by
    rw [norm_pow]
    have := norm_sin_le_two_mul hw1
    rw [hw] at this
    calc ‖sin (t / (2 * n))‖ ^ 2 ≤ (2 * (‖t‖ / (2 * n))) ^ 2 := by gcongr
      _ = (‖t‖ / n) ^ 2 := by field_simp
  rw [norm_mul, norm_pow]
  calc ‖(ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval (2 * ν + n)‖ *
        ‖sin (t / (2 * n)) ^ 2‖ ^ k
      ≤ ((n : ℝ) * (‖2 * ν‖ + 2 * n)) ^ k * ((‖t‖ / n) ^ 2) ^ k := by
        gcongr
        exact norm_ascPochhammer_neg_mul_le ν n k
    _ = ((‖2 * ν‖ / n + 2) * ‖t‖ ^ 2) ^ k := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ ((‖2 * ν‖ + 2) * ‖t‖ ^ 2) ^ k := by
        gcongr
        exact div_le_self (norm_nonneg _) (by exact_mod_cast hn)

/-- The Gauss functions `₂F₁(-n, 2ν + n; ν + 1/2; sin² (t/(2n)))` tend to
`∑ₖ (-(t/2)²)ᵏ/((ν + 1/2)ₖ k!)`. -/
theorem tendsto_hypergeometric_sin_sq {ν : ℂ}
    (hν : ∀ m : ℕ, (ascPochhammer ℂ m).eval (ν + 1 / 2) ≠ 0) (t : ℂ) :
    Tendsto (fun n : ℕ => ordinaryHypergeometric (-(n : ℂ)) (2 * ν + n) (ν + 1 / 2)
      (sin (t / (2 * n)) ^ 2)) atTop
        (𝓝 (∑' k : ℕ, (-(t / 2) ^ 2) ^ k / ((ascPochhammer ℂ k).eval (ν + 1 / 2) *
          k.factorial))) := by
  simp only [ordinaryHypergeometric_eq_tsum, smul_eq_mul]
  set K : ℂ := (((‖2 * ν‖ + 2) * ‖t‖ ^ 2 : ℝ) : ℂ)
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k => ‖K ^ k / ((ascPochhammer ℂ k).eval (ν + 1 / 2) * k.factorial)‖)
    (summable_norm_pow_div_ascPochhammer_factorial hν K) (fun k => ?_) ?_
  · have h := (tendsto_ascPochhammer_mul_sin_pow ν t k).const_mul
      (((k.factorial : ℂ))⁻¹ * ((ascPochhammer ℂ k).eval (ν + 1 / 2))⁻¹)
    convert h using 1
    · funext n; ring
    · field_simp
  · obtain ⟨N, hN⟩ := exists_nat_ge ‖t‖
    filter_upwards [eventually_ge_atTop (max 1 N)] with n hn k
    have hb := norm_ascPochhammer_mul_sin_pow_le ν t (le_of_max_le_left hn)
      (hN.trans (by exact_mod_cast le_of_max_le_right hn)) k
    have hP := hν k
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    rw [show ((k.factorial : ℂ)⁻¹ * (ascPochhammer ℂ k).eval (-(n : ℂ)) *
        (ascPochhammer ℂ k).eval (2 * ν + n) * ((ascPochhammer ℂ k).eval (ν + 1 / 2))⁻¹) *
        (sin (t / (2 * n)) ^ 2) ^ k = ((ascPochhammer ℂ k).eval (-(n : ℂ)) *
        (ascPochhammer ℂ k).eval (2 * ν + n) * (sin (t / (2 * n)) ^ 2) ^ k) /
        ((ascPochhammer ℂ k).eval (ν + 1 / 2) * k.factorial) by field_simp,
      norm_div, norm_div]
    gcongr
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact hb

/-- `∑ₖ zᵏ/((c)ₖ k!) = Γ(c) F̃₀₁(c; z)` when `c` is not a nonpositive integer. -/
theorem tsum_pow_div_ascPochhammer_factorial {c : ℂ}
    (hc : ∀ m : ℕ, (ascPochhammer ℂ m).eval c ≠ 0) (z : ℂ) :
    ∑' k : ℕ, z ^ k / ((ascPochhammer ℂ k).eval c * k.factorial) =
      Gamma c * regularizedHGFun 0 {c} z := by
  have hreg : IsGammaRegular c := fun j hj => hc (j + 1)
    (by rw [ascPochhammer_eval_eq_zero_iff]; exact ⟨j, by omega, by rw [hj]; ring⟩)
  refine HasSum.tsum_eq (((hasSum_regularizedHGFun_zero_singleton c z).mul_left
    (Gamma c)).congr_fun fun k => ?_)
  rw [Complex.Gamma_add_nat_eq_ascPochhammer_mul hreg]
  have := hc k
  have := Gamma_ne_zero hreg
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- **Exercise 6.7-13** (Gegenbauer form), with the regularized `₀F₁`: if `ν + 1/2` and `2ν`
are not nonpositive integers, then
`Cₙ^ν(cos (t/n))/Cₙ^ν(1) → Γ(ν + 1/2) F̃₀₁(ν + 1/2; -(t/2)²)`. -/
theorem tendsto_eval_gegenbauer_cos_div {ν : ℂ}
    (hν : ∀ m : ℕ, (ascPochhammer ℂ m).eval (ν + 1 / 2) ≠ 0)
    (h2ν : ∀ m : ℕ, (ascPochhammer ℂ m).eval (2 * ν) ≠ 0) (t : ℂ) :
    Tendsto (fun n : ℕ => (gegenbauer ν n).eval (cos (t / n)) / (gegenbauer ν n).eval 1) atTop
      (𝓝 (Gamma (ν + 1 / 2) * regularizedHGFun 0 {ν + 1 / 2} (-(t / 2) ^ 2))) := by
  rw [← tsum_pow_div_ascPochhammer_factorial hν]
  refine (tendsto_hypergeometric_sin_sq hν t).congr fun n => ?_
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 := h2ν n
  rw [eval_gegenbauer_eq_hypergeometric ν _ n (hν n), eval_gegenbauer_one,
    show t / n = 2 * (t / (2 * n)) by rw [mul_div_assoc', mul_div_mul_left _ _ two_ne_zero],
    cos_two_mul, show (1 - (2 * cos (t / (2 * n)) ^ 2 - 1)) / 2 = sin (t / (2 * n)) ^ 2 by
      linear_combination -sin_sq_add_cos_sq (t / (2 * n))]
  field_simp

/-- **Exercise 6.7-13** (Bessel form): for `t ≠ 0`, with `ν + 1/2` and `2ν` not nonpositive
integers, `Cₙ^ν(cos (t/n))/Cₙ^ν(1) → Γ(ν + 1/2) (t/2)^{1/2-ν} J_{ν-1/2}(t)`. -/
theorem tendsto_eval_gegenbauer_cos_div_besselJ {ν : ℂ}
    (hν : ∀ m : ℕ, (ascPochhammer ℂ m).eval (ν + 1 / 2) ≠ 0)
    (h2ν : ∀ m : ℕ, (ascPochhammer ℂ m).eval (2 * ν) ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => (gegenbauer ν n).eval (cos (t / n)) / (gegenbauer ν n).eval 1) atTop
      (𝓝 (Gamma (ν + 1 / 2) * ((t / 2) ^ (1 / 2 - ν) * besselJ (ν - 1 / 2) t))) := by
  have h := cpow_neg_mul_besselJ_add_nat (ν - 1 / 2) ht 0
  simp only [Nat.cast_zero, add_zero, pow_zero, one_mul, neg_sub] at h
  rw [h, show ν - 1 / 2 + 1 = ν + 1 / 2 by ring]
  exact tendsto_eval_gegenbauer_cos_div hν h2ν t

/-- **Exercise 6.7-13** (Legendre form): `Pₙ(cos (t/n)) → J₀(t)`, with `Pₙ = Cₙ^{1/2}`. -/
theorem tendsto_eval_legendre_cos_div (t : ℂ) :
    Tendsto (fun n : ℕ => (gegenbauer (1 / 2 : ℂ) n).eval (cos (t / n))) atTop
      (𝓝 (besselJ 0 t)) := by
  have h1 (m : ℕ) : (ascPochhammer ℂ m).eval (1 : ℂ) ≠ 0 := by
    rw [ascPochhammer_eval_one]; exact_mod_cast m.factorial_ne_zero
  have h := tendsto_eval_gegenbauer_cos_div (ν := 1 / 2)
    (fun m => by rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]; exact h1 m)
    (fun m => by rw [show 2 * (1 / 2 : ℂ) = 1 by norm_num]; exact h1 m) t
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one, one_mul] at h
  rw [besselJ_eq, cpow_zero, one_mul, zero_add]
  refine h.congr fun n => ?_
  rw [eval_legendre_one, div_one]

/-- **Exercise 7.7-2** (Neumann series), regularized: for `ν` Gamma-regular with
`re (ν + 1/2) > 0`,
`Γ(ν) ∑ₙ (ν)ₙ/n! (ν + 2n) (y/2)^{2n} F̃₀₁(ν + 2n + 1; -(y/2)²) = 1`.
It is Sonine's formula at `x = 0`. -/
theorem hasSum_neumann_regularized {ν : ℂ} (hν : IsGammaRegular ν)
    (hre : 0 < (ν + 1 / 2).re) (y : ℂ) :
    HasSum (fun n : ℕ => Gamma ν * ((ascPochhammer ℂ n).eval ν / n.factorial) *
      (ν + 2 * n) * (y / 2) ^ (2 * n) * regularizedHGFun 0 {ν + 2 * n + 1} (-(y / 2) ^ 2)) 1 := by
  have h := hasSum_exp_I_mul_gegenbauer hν hre y 0
  rw [mul_zero, exp_zero] at h
  have hodd : ∀ m ∉ Set.range (fun n : ℕ => 2 * n), Gamma ν * (ν + m) * I ^ m * (y / 2) ^ m *
      regularizedHGFun 0 {ν + m + 1} (-(y / 2) ^ 2) * (gegenbauer ν m).eval 0 = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact absurd ⟨k, by simp only; omega⟩ hm
      · exact ⟨k, hk⟩
    rw [eval_gegenbauer_odd_zero, mul_zero]
  have h2 := ((Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n)
    (fun a b hab => by simpa using hab) hodd).mpr h)
  refine h2.congr_fun fun n => ?_
  simp only [Function.comp_apply]
  rw [eval_gegenbauer_even_zero, pow_mul I 2 n, I_sq]
  push_cast
  rcases neg_one_pow_eq_or ℂ n with hs | hs <;> rw [hs] <;> ring

/-- **Exercise 7.7-2** (Neumann series of a power): for `y ≠ 0`, `ν` Gamma-regular and
`re (ν + 1/2) > 0`, `(y/2)^ν = ∑ₙ Γ(ν + n)/n! (ν + 2n) J_{ν+2n}(y)`. Carlson writes the left
side as `2^{-ν} y^ν`. -/
theorem hasSum_neumann {ν : ℂ} (hν : IsGammaRegular ν) (hre : 0 < (ν + 1 / 2).re) {y : ℂ}
    (hy : y ≠ 0) :
    HasSum (fun n : ℕ => Gamma (ν + n) / n.factorial * (ν + 2 * n) * besselJ (ν + 2 * n) y)
      ((y / 2) ^ ν) := by
  have hy2 : y / 2 ≠ 0 := div_ne_zero hy two_ne_zero
  have h := (hasSum_neumann_regularized hν hre y).mul_left ((y / 2) ^ ν)
  rw [mul_one] at h
  refine h.congr_fun fun n => ?_
  have hJ := cpow_neg_mul_besselJ_add_nat ν hy (2 * n)
  have hc : (y / 2) ^ ν * (y / 2) ^ (-ν) = 1 := by
    rw [← cpow_add _ _ hy2, add_neg_cancel, cpow_zero]
  rw [Complex.Gamma_add_nat_eq_ascPochhammer_mul hν]
  push_cast at hJ
  linear_combination (Gamma ν * (ascPochhammer ℂ n).eval ν / n.factorial * (ν + 2 * n)) *
    ((y / 2) ^ ν * hJ - besselJ (ν + 2 * n) y * hc)

/-- **Exercise 7.7-5**, regularized: for `ν` Gamma-regular with `re (ν + 1/2) > 0` and all
complex `X, Y`,
`F̃₀₁(ν + 1; X + Y) = Γ(ν) ∑ₘ (ν + 2m) (ν)ₘ/m! (-XY)ᵐ F̃₀₁(ν + 2m + 1; X) F̃₀₁(ν + 2m + 1; Y)`.
With `c = ν + 1` and Carlson's `₀F₁(c; z) = Γ(c) F̃₀₁(c; z)` this is
`₀F₁(c; x + y) = ∑ₙ (-xy)ⁿ/((c)₂ₙ (c - 1 + n)ₙ n!) ₀F₁(c + 2n; x) ₀F₁(c + 2n; y)`.
It is Gegenbauer's addition theorem at `x = 0`. -/
theorem hasSum_regularizedHGFun_add {ν : ℂ} (hν : IsGammaRegular ν) (hre : 0 < (ν + 1 / 2).re)
    (X Y : ℂ) :
    HasSum (fun m : ℕ => Gamma ν * (ν + 2 * m) * ((ascPochhammer ℂ m).eval ν / m.factorial) *
      (-(X * Y)) ^ m * regularizedHGFun 0 {ν + 2 * m + 1} X *
        regularizedHGFun 0 {ν + 2 * m + 1} Y) (regularizedHGFun 0 {ν + 1} (X + Y)) := by
  obtain ⟨A, hA⟩ := IsAlgClosed.exists_pow_nat_eq (-4 * X) (by norm_num : 0 < 2)
  obtain ⟨B, hB⟩ := IsAlgClosed.exists_pow_nat_eq (-4 * Y) (by norm_num : 0 < 2)
  have h := hasSum_regularizedHGFun_gegenbauer_addition hν hre A B 0
  rw [show -(A ^ 2 + B ^ 2 - 2 * A * B * 0) / 4 = X + Y by rw [hA, hB]; ring] at h
  have hodd : ∀ m ∉ Set.range (fun n : ℕ => 2 * n), Gamma ν * (ν + m) * (A * B / 4) ^ m *
      regularizedHGFun 0 {ν + m + 1} (-(A / 2) ^ 2) *
      regularizedHGFun 0 {ν + m + 1} (-(B / 2) ^ 2) * (gegenbauer ν m).eval 0 = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact absurd ⟨k, by simp only; omega⟩ hm
      · exact ⟨k, hk⟩
    rw [eval_gegenbauer_odd_zero, mul_zero]
  have h2 := ((Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n)
    (fun a b hab => by simpa using hab) hodd).mpr h)
  refine h2.congr_fun fun m => ?_
  simp only [Function.comp_apply]
  have hX : -(A / 2) ^ 2 = X := by rw [div_pow, hA]; ring
  have hY : -(B / 2) ^ 2 = Y := by rw [div_pow, hB]; ring
  have hAB : (A * B / 4) ^ (2 * m) = (X * Y) ^ m := by
    rw [pow_mul, show (A * B / 4) ^ 2 = A ^ 2 * B ^ 2 / 16 by ring, hA, hB]; ring_nf
  rw [eval_gegenbauer_even_zero, hX, hY, hAB, neg_pow, mul_pow]
  push_cast
  ring

/-- The operator `x⁻¹ d/dx` of Exercise 6.9-20. -/
def besselD (f : ℂ → ℂ) : ℂ → ℂ := fun x => deriv f x / x

/-- `x⁻¹ d/dx` commutes with constant factors. -/
theorem iterate_besselD_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    besselD^[n] (fun x => c * f x) = fun x => c * (besselD^[n] f) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [besselD, deriv_const_mul_field']
    ring

/-- Iterates of `x⁻¹ d/dx` only depend on the values on the slit plane. -/
theorem iterate_besselD_congr {f g : ℂ → ℂ} (hfg : ∀ x ∈ slitPlane, f x = g x) (n : ℕ) :
    ∀ x ∈ slitPlane, (besselD^[n] f) x = (besselD^[n] g) x := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [besselD]
    have he : besselD^[n] f =ᶠ[𝓝 x] besselD^[n] g :=
      (isOpen_slitPlane.eventually_mem hx).mono fun y hy => ih y hy
    rw [he.deriv_eq]

/-- `G_μ(x) = F̃₀₁(μ + 1; -(x/2)²)`, the entire function `(x/2)^{-μ} J_μ(x)`. -/
def besselG (μ : ℂ) (x : ℂ) : ℂ := regularizedHGFun 0 {μ + 1} (-(x / 2) ^ 2)

/-- `x⁻¹ d/dx G_μ = -G_{μ+1}/2` for `x ≠ 0`. -/
theorem besselD_besselG (μ : ℂ) {x : ℂ} (hx : x ≠ 0) :
    besselD (besselG μ) x = -(1 / 2) * besselG (μ + 1) x := by
  have hd : HasDerivAt (besselG μ) (regularizedHGFun 0 {μ + 1 + 1} (-(x / 2) ^ 2) * (-(x / 2)))
      x := by
    have h1 : HasDerivAt (fun y : ℂ => -(y / 2) ^ 2) (-(x / 2)) x := by
      have := (hasDerivAt_pow 2 x).const_mul (-1 / 4 : ℂ)
      convert this using 1
      · funext y; ring
      · push_cast; ring
    exact (hasDerivAt_regularizedHGFun_zero_singleton (μ + 1) _).comp x h1
  simp only [besselD, hd.deriv, besselG]
  field_simp

/-- `(x⁻¹ d/dx)ⁿ G_μ = (-1/2)ⁿ G_{μ+n}` on the slit plane. -/
theorem iterate_besselD_besselG (n : ℕ) :
    ∀ (μ : ℂ), ∀ x ∈ slitPlane,
      (besselD^[n] (besselG μ)) x = (-(1 / 2)) ^ n * besselG (μ + n) x := by
  induction n with
  | zero => intro μ x _; simp
  | succ n ih =>
    intro μ x hx
    rw [Function.iterate_succ_apply]
    have hc : ∀ y ∈ slitPlane, besselD (besselG μ) y = -(1 / 2) * besselG (μ + 1) y :=
      fun y hy => besselD_besselG μ (slitPlane_ne_zero hy)
    rw [iterate_besselD_congr hc n x hx, iterate_besselD_const_mul]
    dsimp only
    rw [ih (μ + 1) x hx]
    push_cast
    rw [show μ + 1 + n = μ + (n + 1) by ring, pow_succ]
    ring

/-- `H_μ(x) = x^{2μ} G_μ(x)`. -/
def besselH (μ : ℂ) (x : ℂ) : ℂ := x ^ (2 * μ) * besselG μ x

/-- `x⁻¹ d/dx H_μ = 2 H_{μ-1}` on the slit plane. -/
theorem besselD_besselH (μ : ℂ) {x : ℂ} (hx : x ∈ slitPlane) :
    besselD (besselH μ) x = 2 * besselH (μ - 1) x := by
  have hx0 := slitPlane_ne_zero hx
  have hG : HasDerivAt (besselG μ) (regularizedHGFun 0 {μ + 1 + 1} (-(x / 2) ^ 2) * (-(x / 2)))
      x := by
    have h1 : HasDerivAt (fun y : ℂ => -(y / 2) ^ 2) (-(x / 2)) x := by
      have := (hasDerivAt_pow 2 x).const_mul (-1 / 4 : ℂ)
      convert this using 1
      · funext y; ring
      · push_cast; ring
    exact (hasDerivAt_regularizedHGFun_zero_singleton (μ + 1) _).comp x h1
  have hP := (hasStrictDerivAt_cpow_const (c := 2 * μ) hx).hasDerivAt
  have hd := hP.mul hG
  simp only [besselD]
  rw [show besselH μ = (fun y => y ^ (2 * μ)) * besselG μ from rfl, hd.deriv]
  simp only [besselH]
  have hc := regularizedHGFun_zero_singleton_sub_one (μ + 1) (-(x / 2) ^ 2)
  rw [show μ + 1 - 1 = μ by ring] at hc
  have hp1 : x ^ (2 * μ - 1) = x ^ (2 * (μ - 1)) * x := by
    rw [show 2 * μ - 1 = 2 * (μ - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one]
  have hp2 : x ^ (2 * μ) = x ^ (2 * (μ - 1)) * x ^ 2 := by
    rw [show 2 * μ = 2 * (μ - 1) + 2 by ring, cpow_add _ _ hx0,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  simp only [besselG, show μ - 1 + 1 = μ by ring]
  rw [hp1, hp2, hc]
  field_simp

/-- `(x⁻¹ d/dx)ⁿ H_μ = 2ⁿ H_{μ-n}` on the slit plane. -/
theorem iterate_besselD_besselH (n : ℕ) :
    ∀ (μ : ℂ), ∀ x ∈ slitPlane, (besselD^[n] (besselH μ)) x = 2 ^ n * besselH (μ - n) x := by
  induction n with
  | zero => intro μ x _; simp
  | succ n ih =>
    intro μ x hx
    rw [Function.iterate_succ_apply]
    have hc : ∀ y ∈ slitPlane, besselD (besselH μ) y = 2 * besselH (μ - 1) y :=
      fun y hy => besselD_besselH μ hy
    rw [iterate_besselD_congr hc n x hx, iterate_besselD_const_mul]
    dsimp only
    rw [ih (μ - 1) x hx]
    push_cast
    rw [show μ - 1 - n = μ - (n + 1) by ring, pow_succ]
    ring

/-- `(y/2)^a = (1/2)^a yᵃ` with the real factor `1/2`. -/
theorem div_two_cpow (y a : ℂ) : (y / 2) ^ a = (((1 / 2 : ℝ)) : ℂ) ^ a * y ^ a := by
  rw [← TauCeti.ofReal_mul_cpow (by norm_num)]
  congr 1; push_cast; ring

/-- **Exercise 6.9-20**, first Bessel form: on the slit plane,
`(x⁻¹ d/dx)ⁿ [x^{-μ} J_μ(x)] = (-1)ⁿ x^{-μ-n} J_{μ+n}(x)`. -/
theorem iterate_besselD_cpow_neg_mul_besselJ (μ : ℂ) (n : ℕ) {x : ℂ} (hx : x ∈ slitPlane) :
    (besselD^[n] (fun y => y ^ (-μ) * besselJ μ y)) x =
      (-1) ^ n * x ^ (-μ - n) * besselJ (μ + n) x := by
  set h : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hh : h ≠ 0 := by simp [h]
  have hJ (ν y : ℂ) (hy : y ≠ 0) : y ^ (-ν) * besselJ ν y = h ^ ν * besselG ν y := by
    rw [besselJ_eq, div_two_cpow, besselG, ← mul_assoc, ← mul_assoc, mul_comm (y ^ (-ν)),
      mul_assoc (h ^ ν), ← cpow_add _ _ hy, neg_add_cancel, cpow_zero, mul_one]
  have hc : ∀ y ∈ slitPlane, (fun y => y ^ (-μ) * besselJ μ y) y = h ^ μ * besselG μ y :=
    fun y hy => hJ μ y (slitPlane_ne_zero hy)
  rw [iterate_besselD_congr hc n x hx, iterate_besselD_const_mul]
  dsimp only
  rw [iterate_besselD_besselG n μ x hx, show -μ - n = -(μ + n) by ring, mul_assoc,
    hJ (μ + n) x (slitPlane_ne_zero hx), cpow_add _ _ hh, cpow_natCast]
  simp only [h]
  push_cast
  rw [neg_pow, div_pow, one_pow]
  ring

/-- **Exercise 6.9-20**, second Bessel form: on the slit plane,
`(x⁻¹ d/dx)ⁿ [x^μ J_μ(x)] = x^{μ-n} J_{μ-n}(x)`. -/
theorem iterate_besselD_cpow_mul_besselJ (μ : ℂ) (n : ℕ) {x : ℂ} (hx : x ∈ slitPlane) :
    (besselD^[n] (fun y => y ^ μ * besselJ μ y)) x = x ^ (μ - n) * besselJ (μ - n) x := by
  set h : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hh : h ≠ 0 := by simp [h]
  have hJ (ν y : ℂ) (hy : y ≠ 0) : y ^ ν * besselJ ν y = h ^ ν * besselH ν y := by
    rw [besselJ_eq, div_two_cpow, besselH, besselG, show 2 * ν = ν + ν by ring,
      cpow_add _ _ hy]
    ring
  have hc : ∀ y ∈ slitPlane, (fun y => y ^ μ * besselJ μ y) y = h ^ μ * besselH μ y :=
    fun y hy => hJ μ y (slitPlane_ne_zero hy)
  rw [iterate_besselD_congr hc n x hx, iterate_besselD_const_mul]
  dsimp only
  rw [iterate_besselD_besselH n μ x hx, hJ (μ - n) x (slitPlane_ne_zero hx), sub_eq_add_neg,
    cpow_add _ _ hh, cpow_neg, cpow_natCast]
  simp only [h]
  push_cast
  rw [div_pow, one_pow, inv_div, div_one, ← sub_eq_add_neg]
  ring

end Carlson.TwoVariable
