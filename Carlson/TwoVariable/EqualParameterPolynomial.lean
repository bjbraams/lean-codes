/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Normalization.EqualParameter
public import Carlson.TwoVariable.QuadraticContinuation
public import Carlson.TwoVariable.RPolynomial

/-!
# Equal-parameter polynomial normalization

The polynomial counterpart of `regEqualR` is `Rₙ(β,β;x,y) / Γ(β+1/2)`.
Legendre duplication and the existing removable equal-parameter normalization
make it entire in the parameter and both nodes. Unlike a quotient by `(2β)ₙ`,
this definition retains the removable values when that polynomial vanishes.
-/

open Complex Set Filter Polynomial
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The entire equal-parameter moment `Rₙ(β,β;x,y) / Γ(β+1/2)`, with removable values. -/
def regEqualRPolynomial (n : ℕ) (β x y : ℂ) : ℂ :=
  (2 : ℂ) ^ (2 * β - 1) / (Real.sqrt Real.pi : ℂ) * equalRPolynomial n β (pair x y)

/-- The equal-parameter polynomial normalization is jointly entire under analytic substitutions. -/
theorem analyticAt_regEqualRPolynomial_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {β x y : E → ℂ} {p : E} (hβ : AnalyticAt ℂ β p)
    (hx : AnalyticAt ℂ x p) (hy : AnalyticAt ℂ y p) (n : ℕ) :
    AnalyticAt ℂ (fun w => regEqualRPolynomial n (β w) (x w) (y w)) p := by
  let Q : E → Option (Fin 2) → ℂ := fun w => optionPoint (β w) (pair (x w) (y w))
  have hQ : AnalyticAt ℂ Q p := by
    apply analyticAt_pi_iff.mpr
    intro o
    cases o with
    | none => exact hβ
    | some i => fin_cases i; exact hx; exact hy
  have hE := (analyticOnNhd_equalRPolynomial (ι := Fin 2) n (Q p) (mem_univ _)).comp
    (f := Q) hQ
  have h2 : AnalyticAt ℂ (fun w => (2 : ℂ) ^ (2 * β w - 1) / (Real.sqrt Real.pi : ℂ)) p :=
    (analyticAt_const.cpow ((analyticAt_const.mul hβ).sub analyticAt_const) (by simp)).div_const
  apply AnalyticAt.mul h2
  simpa only [Q, Function.comp_def, optionPoint_none, optionPoint_some] using hE

/-- The general regularized polynomial is the duplication ratio times the equal normalization. -/
theorem regCarlsonRPolynomial_pair_self_eq (n : ℕ) (β x y : ℂ) :
    regCarlsonRPolynomial n (pair β β) (pair x y) =
      quadraticGammaRatio β * regEqualRPolynomial n β x y := by
  have hpair : pair β β = fun _ => β := by funext i; fin_cases i <;> rfl
  by_cases hβ : ∀ m : ℕ, β ≠ -(m : ℂ)
  · rw [regEqualRPolynomial, equalRPolynomial_of_ne n hβ, hpair, quadraticGammaRatio]
    have hG := Gamma_ne_zero hβ
    have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h2 : (2 : ℂ) ^ (1 - 2 * β) * (2 : ℂ) ^ (2 * β - 1) = 1 := by
      rw [← cpow_add _ _ two_ne_zero]
      ring_nf
      simp
    field_simp
    linear_combination (-regCarlsonRPolynomial n (fun _ => β) (pair x y)) * h2
  · push Not at hβ
    obtain ⟨m, rfl⟩ := hβ
    rw [hpair, regCarlsonRPolynomial_const_neg_nat, quadraticGammaRatio, Gamma_neg_nat_eq_zero]
    simp

/-- On positive-real-part parameters the entire normalization is the usual moment quotient. -/
theorem regEqualRPolynomial_eq_numerator (n : ℕ) {β : ℂ} (hβ : 0 < β.re) (x y : ℂ) :
    regEqualRPolynomial n β x y =
      carlsonRPolynomialNumerator₂ n β β x y /
        ((ascPochhammer ℂ n).eval (β + β) * Gamma (β + 1 / 2)) := by
  have htot : 0 < (β + β).re := by simp only [add_re]; linarith
  have hG := Gamma_ne_zero_of_re_pos htot
  have hGn : Gamma (β + β + n) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
  have hc : Gamma (β + 1 / 2) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simpa using (add_pos hβ
      (show 0 < (1 / 2 : ℂ).re by norm_num)))
  have hq : quadraticGammaRatio β ≠ 0 := by
    intro h
    have H := Gamma_mul_quadraticGammaRatio hβ
    rw [h, mul_zero] at H
    exact hc H.symm
  have hshift := Gamma_add_nat_div_Gamma_eq (β + β)
    (fun k hk => Gamma_ne_zero_of_re_pos htot ((Gamma_eq_zero_iff _).mpr ⟨k, hk⟩)) (n := n)
  have h := regCarlsonRPolynomial_pair_self_eq n β x y
  rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_pair, sum_pair] at h
  rw [← hshift]
  apply (mul_left_cancel₀ hq)
  rw [← h]
  rw [← Gamma_mul_quadraticGammaRatio hβ]
  generalize Gamma (β + β + n) = A at *
  generalize Gamma (β + β) = B at *
  generalize quadraticGammaRatio β = C at *
  field_simp

/-- Multiplying the entire equal-parameter moment by its total Pochhammer recovers
its numerator, including all removable parameter values. -/
theorem ascPochhammer_mul_regEqualRPolynomial (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (2 * β) * regEqualRPolynomial n β x y =
      carlsonRPolynomialNumerator₂ n β β x y / Gamma (β + 1 / 2) := by
  have hL : AnalyticOnNhd ℂ (fun s =>
      (ascPochhammer ℂ n).eval (2 * s) * regEqualRPolynomial n s x y) univ := by
    intro s _
    exact (((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n)) _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)).mul
      (analyticAt_regEqualRPolynomial_comp analyticAt_id analyticAt_const analyticAt_const n)
  have hN (s : ℂ) : AnalyticAt ℂ (fun z =>
      carlsonRPolynomialNumerator₂ n z z x y) s := by
    simp only [← carlsonRPolynomialNumerator_pair]
    apply (analyticOnNhd_carlsonRPolynomialNumerator_joint n _ (mem_univ _)).comp
      (f := fun z => (pair z z, pair x y))
    apply AnalyticAt.prod _ analyticAt_const
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i <;> exact analyticAt_id
  have hR : AnalyticOnNhd ℂ (fun s =>
      carlsonRPolynomialNumerator₂ n s s x y / Gamma (s + 1 / 2)) univ := by
    intro s _
    simp only [div_eq_mul_inv]
    exact (hN s).mul ((differentiable_one_div_Gamma.analyticAt _).comp
      (f := fun z : ℂ => z + 1 / 2) (analyticAt_id.add analyticAt_const))
  apply congrFun (hL.eq_of_eventuallyEq hR (z₀ := (1 : ℂ)) ?_) β
  filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with s hs
  rw [regEqualRPolynomial_eq_numerator n hs x y,
    show s + s = 2 * s by ring]
  have hp := ascPochhammer_eval_ne_zero_of_re_pos
    (show 0 < (2 * s).re by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hs) n
  field_simp

end Carlson.TwoVariable
