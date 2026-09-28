/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.SEqualParameter
public import ToMathlib.Analysis.SpecialFunctions.Bessel

/-!
# The S-function and the confluent hypergeometric functions

With a zero node, the two-variable S-function is Kummer's function:
`S(a, b; x, 0) = ₁F₁(a; a + b; x)` (Carlson's (5.8-6)). With equal parameters it is an
exponential times a `₀F₁` (Theorem 6.9-2). Translating the nodes connects the two, which is
Kummer's second formula (6.9-6), and specializing the nodes to `±ix` and `±x` gives the Bessel
functions `J_μ` and `I_μ` of every complex order (6.9-18), (6.9-21).

The identities are stated with Mathlib's regularized hypergeometric function
`Complex.regularizedHGFun`, whose coefficients carry `1/Γ(c + n)` in place of `1/(c)ₙ`. The
regularized forms hold for all complex parameters; the forms in Carlson's normalization follow
where the relevant Gamma factors are finite.

## Main results

* `Carlson.TwoVariable.regCarlsonS_pair_zero_right`, `Carlson.TwoVariable.carlsonS_pair_zero_right`:
  (5.8-6).
* `Carlson.TwoVariable.regCarlsonS_pair_self`: Theorem 6.9-2 in closed form.
* `Carlson.TwoVariable.regularizedHGFun_kummer_second`,
  `Carlson.TwoVariable.Gamma_mul_regularizedHGFun_kummer_second`: Kummer's second formula (6.9-6).
* `Carlson.TwoVariable.quadraticGammaRatio_mul_besselJ`, `Carlson.TwoVariable.Gamma_mul_besselJ`:
  (6.9-18).
* `Carlson.TwoVariable.quadraticGammaRatio_mul_besselI`, `Carlson.TwoVariable.Gamma_mul_besselI`:
  (6.9-21).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§5.8, 6.9.
-/

open Complex
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Carlson's (5.8-6), regularized: `S(a, b; x, 0)/Γ(a + b) = ₁F₁(a; a + b; x)/Γ(a + b)`, for
all complex `a, b, x`. -/
theorem regCarlsonS_pair_zero_right (a b x : ℂ) :
    regCarlsonS (pair a b) (pair x 0) = regularizedHGFun {a} {a + b} x := by
  refine (hasSum_regCarlsonSSeries (pair x 0) (pair a b)).unique
    ((hasSum_regularizedHGFun (by simp) x).congr_fun fun n => ?_)
  change _ * regRPolynomial n a b x 0 = _
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma, carlsonRPolynomialNumerator₂_zero_right]
  simp [regularizedHGFunCoeff]
  ring

/-- Carlson's (5.8-6): `S(a, b; x, 0) = Γ(a + b) ₁F₁(a; a + b; x)/Γ(a + b)`. -/
theorem carlsonS_pair_zero_right (a b x : ℂ) :
    carlsonS (pair a b) (pair x 0) = Gamma (a + b) * regularizedHGFun {a} {a + b} x := by
  rw [carlsonS, sum_pair, regCarlsonS_pair_zero_right]

/-- Theorem 6.9-2 in closed form: `S(β, β; x, y)/Γ(2β) = q(β) e^{(x+y)/2} ₀F₁(β + 1/2;
(x-y)²/16)/Γ(β + 1/2)`, with Mathlib's regularized `₀F₁`. -/
theorem regCarlsonS_pair_self (β x y : ℂ) :
    regCarlsonS (pair β β) (pair x y) = quadraticGammaRatio β * exp ((x + y) / 2) *
      regularizedHGFun 0 {β + 1 / 2} ((x - y) ^ 2 / 16) := by
  refine (hasSum_regCarlsonS_pair_self β x y).unique
    (((hasSum_regularizedHGFun (by simp) _).mul_left
      (quadraticGammaRatio β * exp ((x + y) / 2))).congr_fun fun n => ?_)
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton]
  ring

/-- **Kummer's second formula** (6.9-6), regularized, for all complex `β, x`:
`₁F₁(β; 2β; 2x)/Γ(2β) = q(β) eˣ ₀F₁(β + 1/2; x²/4)/Γ(β + 1/2)`. -/
theorem regularizedHGFun_kummer_second (β x : ℂ) :
    regularizedHGFun {β} {β + β} (2 * x) =
      quadraticGammaRatio β * exp x * regularizedHGFun 0 {β + 1 / 2} (x ^ 2 / 4) := by
  rw [← regCarlsonS_pair_zero_right]
  have h := regSSeries_add_const β β x (-x) x
  change regCarlsonS (pair β β) (pair (x + x) (-x + x)) =
    exp x * regCarlsonS (pair β β) (pair x (-x)) at h
  rw [show 2 * x = x + x by ring, show (0 : ℂ) = -x + x by ring, h, regCarlsonS_pair_self,
    show (x + -x) / 2 = 0 by ring, exp_zero, show (x - -x) ^ 2 / 16 = x ^ 2 / 4 by ring]
  ring

/-- **Kummer's second formula** (6.9-6) for `re β > 0`, `₁F₁(β; 2β; 2x) = eˣ ₀F₁(β + 1/2; x²/4)`,
written with the regularized functions multiplied by `Γ(2β)` and `Γ(β + 1/2)`. -/
theorem Gamma_mul_regularizedHGFun_kummer_second {β : ℂ} (hβ : 0 < β.re) (x : ℂ) :
    Gamma (β + β) * regularizedHGFun {β} {β + β} (2 * x) =
      Gamma (β + 1 / 2) * exp x * regularizedHGFun 0 {β + 1 / 2} (x ^ 2 / 4) := by
  rw [regularizedHGFun_kummer_second, ← Gamma_mul_quadraticGammaRatio hβ]
  ring

/-- Carlson's (6.9-18), regularized, for every complex order `μ`:
`q(μ + 1/2) J_μ(x) = (x/2)^μ S(1/2 + μ, 1/2 + μ; ix, -ix)/Γ(1 + 2μ)`. -/
theorem quadraticGammaRatio_mul_besselJ (μ x : ℂ) :
    quadraticGammaRatio (1 / 2 + μ) * besselJ μ x =
      (x / 2) ^ μ * regCarlsonS (pair (1 / 2 + μ) (1 / 2 + μ)) (pair (I * x) (-(I * x))) := by
  rw [regCarlsonS_pair_self, besselJ_def]
  simp only
  rw [show (I * x + -(I * x)) / 2 = 0 by ring, exp_zero, show 1 / 2 + μ + 1 / 2 = μ + 1 by ring,
    show (I * x - -(I * x)) ^ 2 / 16 = -(x / 2) ^ 2 by ring_nf; rw [I_sq]; ring]
  ring

/-- Carlson's (6.9-18) for `re μ > -1/2`:
`Γ(1 + μ) J_μ(x) = (x/2)^μ S(1/2 + μ, 1/2 + μ; ix, -ix)`. -/
theorem Gamma_mul_besselJ {μ : ℂ} (hμ : -(1 / 2 : ℝ) < μ.re) (x : ℂ) :
    Gamma (1 + μ) * besselJ μ x =
      (x / 2) ^ μ * carlsonS (pair (1 / 2 + μ) (1 / 2 + μ)) (pair (I * x) (-(I * x))) := by
  have hβ : 0 < (1 / 2 + μ).re := by simp; linarith
  rw [carlsonS, sum_pair, ← mul_left_comm, ← quadraticGammaRatio_mul_besselJ, ← mul_assoc,
    Gamma_mul_quadraticGammaRatio hβ, show 1 / 2 + μ + 1 / 2 = 1 + μ by ring]

/-- Carlson's (6.9-21), regularized, for every complex order `μ`:
`q(μ + 1/2) I_μ(x) = (x/2)^μ S(1/2 + μ, 1/2 + μ; x, -x)/Γ(1 + 2μ)`. -/
theorem quadraticGammaRatio_mul_besselI (μ x : ℂ) :
    quadraticGammaRatio (1 / 2 + μ) * besselI μ x =
      (x / 2) ^ μ * regCarlsonS (pair (1 / 2 + μ) (1 / 2 + μ)) (pair x (-x)) := by
  rw [regCarlsonS_pair_self, besselI]
  rw [show (x + -x) / 2 = 0 by ring, exp_zero, show 1 / 2 + μ + 1 / 2 = μ + 1 by ring,
    show (x - -x) ^ 2 / 16 = (x / 2) ^ 2 by ring]
  ring

/-- Carlson's (6.9-21) for `re μ > -1/2`:
`Γ(1 + μ) I_μ(x) = (x/2)^μ S(1/2 + μ, 1/2 + μ; x, -x)`. -/
theorem Gamma_mul_besselI {μ : ℂ} (hμ : -(1 / 2 : ℝ) < μ.re) (x : ℂ) :
    Gamma (1 + μ) * besselI μ x =
      (x / 2) ^ μ * carlsonS (pair (1 / 2 + μ) (1 / 2 + μ)) (pair x (-x)) := by
  have hβ : 0 < (1 / 2 + μ).re := by simp; linarith
  rw [carlsonS, sum_pair, ← mul_left_comm, ← quadraticGammaRatio_mul_besselI, ← mul_assoc,
    Gamma_mul_quadraticGammaRatio hβ, show 1 / 2 + μ + 1 / 2 = 1 + μ by ring]

end Carlson.TwoVariable
