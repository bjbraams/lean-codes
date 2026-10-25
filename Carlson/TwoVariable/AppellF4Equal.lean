/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AppellF4
public import Carlson.TwoVariable.EqualParameterPolynomial
public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.TwoVariable.Quadratic.Polynomial
public import Pochhammer.Estimates

/-!
# Equal-denominator F₄ as a series of equal-parameter moments

Carlson (1975), equation (2.4), and Carlson (1977), Exercise 7.1-13.
The quadratic polynomial transformation identifies each homogeneous F₄ coefficient
with a Gauss coefficient times an equal-parameter moment. Analytic continuation
removes the apparent singularities of the moment normalization, including those
where `(2c-1)ₙ` vanishes. The series holds throughout `‖x‖ + ‖y‖ < 1`.
-/

open Complex Polynomial Set Filter Finset
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The quadratic numerator transformation, with Gamma normalization on a right half-plane. -/
private theorem equalF4_numerator_transform (c x y : ℂ) (N : ℕ) (hc : 1 < c.re) :
    (-1 : ℂ) ^ N *
        carlsonRPolynomialNumerator₂ N (1 - c - N) (1 - c - N) (x ^ 2) (y ^ 2) /
          Gamma (c + N) =
      regEqualRPolynomial N (c - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hGc := Gamma_ne_zero_of_re_pos (show 0 < c.re by linarith)
  have hGn : Gamma (c + N) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
  have hP := ascPochhammer_eval_ne_zero_of_re_pos
    (show 0 < (2 * c - 1).re by simp; linarith) N
  have hq := carlsonRPolynomialNumerator₂_secondQuadratic N (1 - c - N) x y
  rw [show 1 - 2 * (1 - c - N) - 2 * N = 2 * c - 1 by ring,
    show 1 / 2 - (1 - c - N) - N = c - 1 / 2 by ring,
    ascPochhammer_eval_reflect] at hq
  have hnum : carlsonRPolynomialNumerator₂ N (1 - c - N) (1 - c - N) (x ^ 2) (y ^ 2) =
      ((-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval c *
        carlsonRPolynomialNumerator₂ N (c - 1 / 2) (c - 1 / 2)
          ((x + y) ^ 2) ((x - y) ^ 2)) / (ascPochhammer ℂ N).eval (2 * c - 1) :=
    (eq_div_iff hP).mpr (by simpa only [mul_comm] using hq)
  rw [hnum, regEqualRPolynomial_eq_numerator N hβ]
  rw [show (c - 1 / 2) + (c - 1 / 2) = 2 * c - 1 by ring,
    show c - 1 / 2 + 1 / 2 = c by ring]
  rw [← Gamma_add_nat_div_Gamma_eq c (fun k hk => hGc ((Gamma_eq_zero_iff _).mpr ⟨k, hk⟩))]
  have hs : ((-1 : ℂ) ^ N) ^ 2 = 1 := by rw [← pow_mul, mul_comm N 2, pow_mul]; norm_num
  generalize Gamma (c + N) = A at *
  generalize Gamma c = B at *
  generalize (ascPochhammer ℂ N).eval (2 * c - 1) = P at *
  generalize carlsonRPolynomialNumerator₂ N (c - 1 / 2) (c - 1 / 2)
    ((x + y) ^ 2) ((x - y) ^ 2) = Q at *
  field_simp
  linear_combination Q * hs

/-- The equal-denominator coefficient identity on a right half-plane. -/
private theorem equalF4_antidiagonal_of_re (a b c x y : ℂ) (N : ℕ) (hc : 1 < c.re) :
    ∑ p ∈ antidiagonal N,
        regularizedAppellF4Coeff a b c c p * (x ^ 2) ^ p.1 * (y ^ 2) ^ p.2 =
      gaussCoeff a b c N *
        regEqualRPolynomial N (c - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  rw [regularizedAppellF4_antidiagonal_eq_numerator,
    ← equalF4_numerator_transform c x y N hc, gaussCoeff]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Homogeneous F₄ coefficients are entire in the equal denominator parameter. -/
private theorem analyticAt_equalF4_antidiagonal (a b x y c : ℂ) (N : ℕ) :
    AnalyticAt ℂ (fun s => ∑ p ∈ antidiagonal N,
      regularizedAppellF4Coeff a b s s p * (x ^ 2) ^ p.1 * (y ^ 2) ^ p.2) c := by
  have h (p : ℕ × ℕ) : AnalyticAt ℂ (fun s =>
      regularizedAppellF4Coeff a b s s p * (x ^ 2) ^ p.1 * (y ^ 2) ^ p.2) c := by
    rcases p with ⟨m, n⟩
    simp only [regularizedAppellF4Coeff_eq, div_eq_mul_inv, mul_inv_rev]
    apply AnalyticAt.mul _ analyticAt_const
    apply AnalyticAt.mul _ analyticAt_const
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.mul
    · exact (differentiable_one_div_Gamma.analyticAt _).comp
        (f := fun s : ℂ => s + n) (analyticAt_id.add analyticAt_const)
    · apply AnalyticAt.mul _ analyticAt_const
      exact (differentiable_one_div_Gamma.analyticAt _).comp
        (f := fun s : ℂ => s + m) (analyticAt_id.add analyticAt_const)
  convert (antidiagonal N).analyticAt_sum (fun p _ => h p) using 1
  ext s
  simp only [Finset.sum_apply]

/-- Gauss coefficients times entire equal moments are entire in the denominator parameter. -/
private theorem analyticAt_equalF4_moment (a b x y c : ℂ) (N : ℕ) :
    AnalyticAt ℂ (fun s => gaussCoeff a b s N *
      regEqualRPolynomial N (s - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2)) c := by
  apply AnalyticAt.mul
  · simp only [gaussCoeff, div_eq_mul_inv, mul_inv_rev]
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.mul _ analyticAt_const
    exact (differentiable_one_div_Gamma.analyticAt _).comp
      (f := fun s : ℂ => s + N) (analyticAt_id.add analyticAt_const)
  · exact analyticAt_regEqualRPolynomial_comp (analyticAt_id.sub analyticAt_const)
      analyticAt_const analyticAt_const N

/-- **Carlson (1975), (2.4), coefficient identity.** Equal-denominator F₄ coefficients
are Gauss coefficients times equal-parameter moments, including removable parameter values. -/
theorem regularizedAppellF4_antidiagonal_eq_equalRPolynomial (a b c x y : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N,
        regularizedAppellF4Coeff a b c c p * (x ^ 2) ^ p.1 * (y ^ 2) ^ p.2 =
      gaussCoeff a b c N *
        regEqualRPolynomial N (c - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2) := by
  have hf : AnalyticOnNhd ℂ (fun s => ∑ p ∈ antidiagonal N,
      regularizedAppellF4Coeff a b s s p * (x ^ 2) ^ p.1 * (y ^ 2) ^ p.2) univ :=
    fun s _ => analyticAt_equalF4_antidiagonal a b x y s N
  have hg : AnalyticOnNhd ℂ (fun s => gaussCoeff a b s N *
      regEqualRPolynomial N (s - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2)) univ :=
    fun s _ => analyticAt_equalF4_moment a b x y s N
  apply congrFun (hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ)) ?_) c
  filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
  exact equalF4_antidiagonal_of_re a b s x y N hs

/-- **Exercise 7.1-13, equal-denominator series, regularized form.**
The equal-moment Gauss series converges on the full square-root region for the squared nodes. -/
theorem hasSum_regularizedAppellF4_equalRPolynomial (a b c : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun N => gaussCoeff a b c N *
      regEqualRPolynomial N (c - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2))
      (regularizedAppellF4 a b c c (x ^ 2) (y ^ 2)) := by
  have hregion : Real.sqrt ‖x ^ 2‖ + Real.sqrt ‖y ^ 2‖ < 1 := by
    simpa only [norm_pow, Real.sqrt_sq (norm_nonneg _)] using hxy
  simpa only [regularizedAppellF4_antidiagonal_eq_equalRPolynomial] using
    hasSum_regularizedAppellF4_antidiagonal a b c c hregion

/-- **Exercise 7.1-13, equal-denominator series, ordinary form.**
`Γ(c) * regEqualRPolynomial` is the normalized moment with its removable values filled in. -/
theorem hasSum_appellF4_equalRPolynomial (a b c : ℂ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun N =>
      ((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
        ((N.factorial : ℂ) * (ascPochhammer ℂ N).eval c)) *
        (Gamma c * regEqualRPolynomial N (c - 1 / 2) ((x + y) ^ 2) ((x - y) ^ 2)))
      (appellF4 a b c c (x ^ 2) (y ^ 2)) := by
  rw [appellF4]
  convert (hasSum_regularizedAppellF4_equalRPolynomial a b c hxy).mul_left
    (Gamma c * Gamma c) using 1
  funext N
  rw [gaussCoeff, ← Gamma_add_nat_div_Gamma_eq c hc]
  have hGc := Gamma_ne_zero hc
  have hGn : Gamma (c + N) ≠ 0 :=
    Gamma_ne_zero (fun k hk => hc (k + N) (by push_cast at hk ⊢; linear_combination hk))
  generalize Gamma (c + N) = A at *
  generalize Gamma c = B at *
  field_simp

end Carlson.TwoVariable
