/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Normalization.EqualParameter
public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.TwoVariable.LQuadratic
public import SeveralComplexVariables.Derivatives

/-!
# The equal-parameter normalization on the full slit domain

Carlson's natural normalization of the two-variable equal-parameter family is
`R_t(β, β; x, y)/Γ(β + 1/2)` (Remark to Theorem 6.8-4). The values at `β = 0, -1, -2, …` are
removable, although they are zeros of the general regularization by `Γ(2β)`. The normalization
is defined directly, without proof arguments, by Legendre's duplication formula from the
function `Γ(β) R_t(β, β; x, y)/Γ(2β)` of Theorem 6.8-4:
`regEqualR t β x y = 2^{2β-1}/√π · Γ(β) R_t(β, β; x, y)/Γ(2β)`.
It is holomorphic in `(t, β, x, y)` jointly, for all complex `t, β` and all nodes in the slit
plane, and agrees with the native integral for `re β > 0` and right-half-plane nodes.

The two quadratic transformations 6.9-3 and 6.10-1 then hold in this normalization, retaining
the removable values at `β = 0, -1, -2, …`, on Carlson's full node domain `re x, re y > 0`; the
transformed nodes need only lie in the slit plane. The same holds for the exponent derivatives:
the L-function identities (6.4), (6.5) and (6.8) of Carlson (1987) are obtained by
differentiating in the exponent, with the parameter-transfer calculus of
`TwoVariable.LQuadratic`; (6.4) and (6.5) are extended from nodes with right-half-plane
transformed nodes by the identity theorem.

## Main definitions

* `Carlson.TwoVariable.regEqualR`: `R_t(β, β; x, y)/Γ(β + 1/2)` on slit-plane nodes.
* `Carlson.TwoVariable.equalRSlit`: the ordinary function `R_t(β, β; x, y)`.
* `Carlson.TwoVariable.regEqualL`, `equalLSlit`: the corresponding L-functions.

## Main results

* `Carlson.TwoVariable.analyticAt_regEqualR_comp`: joint holomorphy.
* `Carlson.TwoVariable.regCarlsonR_pair_self_eq`: `ℛ_t(β, β; x, y) = q(β) regEqualR t β x y`.
* `Carlson.TwoVariable.regEqualR_eq_integral`, `regEqualL_eq_integral`, `equalRSlit_eq_integral`,
  `equalLSlit_eq_integral`: agreement with the native integrals.
* `Carlson.TwoVariable.regEqualR_zero`, `equalRSlit_zero`: the exponent-zero values, including the
  removable values at `β = 0, -1, -2, …`.
* `Carlson.TwoVariable.regEqualR_firstQuadratic`, `regEqualR_secondQuadratic`, and their ordinary
  forms `equalRSlit_firstQuadratic`, `equalRSlit_secondQuadratic`: 6.9-3 and 6.10-1.
* `Carlson.TwoVariable.regEqualL_firstQuadratic_deriv`, `regEqualL_secondQuadratic_deriv`: the
  exponent derivatives of 6.9-3 and 6.10-1 with the parameter-transfer correction.
* `Carlson.TwoVariable.regEqualL_firstQuadratic`, `regEqualL_secondQuadratic`,
  `regEqualL_firstQuadratic_zero`, `regEqualL_secondQuadratic_zero`, and the ordinary forms
  `equalLSlit_firstQuadratic`, `equalLSlit_secondQuadratic`: Carlson (1987), (6.4), (6.5), (6.8).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§6.8–6.10.
* B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM J. Math. Anal. 18 (1987), 550–565.
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Equal parameters form the constant pair. -/
theorem pair_self (β : ℂ) : pair β β = fun _ => β := by
  funext i; fin_cases i <;> rfl

/-- **Carlson's equal-parameter normalization** `R_t(β, β; x, y)/Γ(β + 1/2)`, entire in `t` and
`β` and holomorphic in the nodes on the product slit plane. It is obtained from
`Γ(β) R_t(β, β; x, y)/Γ(2β)` (Theorem 6.8-4) by Legendre's duplication formula. -/
def regEqualR (t β x y : ℂ) : ℂ :=
  (2 : ℂ) ^ (2 * β - 1) / (Real.sqrt Real.pi : ℂ) * equalR t β (pair x y)

/-- Joint holomorphy of the equal-parameter normalization on the slit node domain. -/
theorem analyticAt_regEqualR_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t β x y : E → ℂ} {p : E} (ht : AnalyticAt ℂ t p) (hβ : AnalyticAt ℂ β p)
    (hx : AnalyticAt ℂ x p) (hy : AnalyticAt ℂ y p) (hxs : x p ∈ slitPlane)
    (hys : y p ∈ slitPlane) :
    AnalyticAt ℂ (fun w => regEqualR (t w) (β w) (x w) (y w)) p := by
  set Q : E → Option (Option (Fin 2)) → ℂ := fun w o =>
    optionPoint (β w) (optionPoint (t w) (pair (x w) (y w))) o
  have hQ : AnalyticAt ℂ Q p := by
    refine analyticAt_pi_iff.mpr fun o => ?_
    rcases o with _ | _ | i
    · exact hβ
    · exact ht
    · fin_cases i
      · exact hx
      · exact hy
  have hslit : (fun i => Q p (some (some i))) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hxs
    · exact hys
  have hE := (analyticOnNhd_equalR (ι := Fin 2) (Q p) hslit).comp_of_eq hQ rfl
  have h2 : AnalyticAt ℂ (fun w => (2 : ℂ) ^ (2 * β w - 1) / (Real.sqrt Real.pi : ℂ)) p :=
    (analyticAt_const.cpow ((analyticAt_const.mul hβ).sub analyticAt_const)
      (by simp)).div_const
  refine (h2.mul hE).congr (Eventually.of_forall fun w => ?_)
  simp only [Pi.mul_apply, Function.comp_apply, regEqualR, Q]
  rfl

/-- The general regularized R-function with equal parameters is Legendre's duplication ratio
times the equal-parameter normalization, for all `t, β` and slit-plane nodes. -/
theorem regCarlsonR_pair_self_eq (t β : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonR t (pair β β) (pair x y) = quadraticGammaRatio β * regEqualR t β x y := by
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  by_cases hβ : ∀ m : ℕ, β ≠ -m
  · rw [regEqualR, equalR_of_ne t hβ, pair_self, quadraticGammaRatio]
    have hG := Gamma_ne_zero hβ
    have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h2 : (2 : ℂ) ^ (1 - 2 * β) * (2 : ℂ) ^ (2 * β - 1) = 1 := by
      rw [← cpow_add _ _ two_ne_zero]; ring_nf; simp
    field_simp
    linear_combination (-regCarlsonR t (fun _ => β) (pair x y)) * h2
  · push Not at hβ
    obtain ⟨m, rfl⟩ := hβ
    rw [pair_self, regCarlsonR_const_neg_nat t m hz, quadraticGammaRatio, Gamma_neg_nat_eq_zero]
    simp

/-- Legendre's duplication ratio does not vanish on the right half-plane. -/
theorem quadraticGammaRatio_ne_zero {β : ℂ} (hβ : 0 < β.re) : quadraticGammaRatio β ≠ 0 := by
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold quadraticGammaRatio
  exact mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) hpi)
    (inv_ne_zero (Gamma_ne_zero_of_re_pos hβ))

/-- Entire functions of `β` agreeing after multiplication by Legendre's duplication ratio for
`re β > 0` are equal; the ratio's zeros at `β = 0, -1, -2, …` are removed by the identity
theorem. -/
theorem eq_of_quadraticGammaRatio_mul_eq {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ β, 0 < β.re → quadraticGammaRatio β * f β =
      quadraticGammaRatio β * g β) : f = g := by
  apply hf.eq_of_eventuallyEq hg (z₀ := (1 : ℂ))
  filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with β hβ
  exact mul_left_cancel₀ (quadraticGammaRatio_ne_zero hβ) (h β hβ)

/-- For fixed exponent and slit-plane nodes, `regEqualR` is entire in the parameter. -/
theorem analyticOnNhd_regEqualR_parameter (t : ℂ) {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) : AnalyticOnNhd ℂ (fun β => regEqualR t β x y) univ := fun _ _ =>
  analyticAt_regEqualR_comp analyticAt_const analyticAt_id analyticAt_const analyticAt_const hx hy

/-- For convergent parameters and right-half-plane nodes, `regEqualR` is the native integral
divided by `Γ(β + 1/2)`. -/
theorem regEqualR_eq_integral (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hβ : 0 < β.re) : regEqualR t β x y = rIntegral t β β x y / Gamma (β + 1 / 2) := by
  have hz : pair x y ∈ carlsonRVariableDomain := by intro i; fin_cases i <;> assumption
  have hb : pair β β ∈ mvBetaConvergent := by intro i; fin_cases i <;> exact hβ
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  have h := regCarlsonR_pair_self_eq t β (carlsonRightHalfPlane_subset_slitPlane hx)
    (carlsonRightHalfPlane_subset_slitPlane hy)
  rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz] at h
  rw [eq_div_iff (Gamma_ne_zero_of_re_pos hc), ← Gamma_mul_quadraticGammaRatio hβ]
  unfold rIntegral carlsonRIntegral
  rw [sum_pair, h]
  ring

/-- **Carlson 6.9-3 in the equal-parameter normalization** on Carlson's full node domain
`re x, re y > 0`, for all complex `t, β`, retaining the values at `β = 0, -1, -2, …`. -/
theorem regEqualR_firstQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regEqualR (2 * t) β x y = regCarlsonR t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  have hxs : x ∈ slitPlane := carlsonRightHalfPlane_subset_slitPlane hx
  have hys : y ∈ slitPlane := carlsonRightHalfPlane_subset_slitPlane hy
  have hm := meanSquares_mem_slitDomain hx hy
  refine congrFun (eq_of_quadraticGammaRatio_mul_eq
    (f := fun β => regEqualR (2 * t) β x y)
    (g := fun β => regCarlsonR t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)))
    (analyticOnNhd_regEqualR_parameter _ hxs hys) (fun β _ => analyticAt_regCarlsonR_comp
      analyticAt_const (b := fun β => pair (β + t) (1 / 2 - t)) (analyticAt_pi_iff.mpr fun i => by
        fin_cases i
        · exact analyticAt_id.add analyticAt_const
        · exact analyticAt_const) analyticAt_const hm) fun β _ => ?_) β
  rw [← regCarlsonR_pair_self_eq _ β hxs hys, regRSlit_firstQuadratic t β x y hx hy]

/-- **Carlson 6.10-1 in the equal-parameter normalization** on Carlson's full node domain
`re x, re y > 0`, for all complex `t, β`. The squared nodes may have negative real parts. -/
theorem regEqualR_secondQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regEqualR t β (x ^ 2) (y ^ 2) = regCarlsonR t (pair (2 * β + t) (1 / 2 - β - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  have hxs : x ^ 2 ∈ slitPlane := sq_mem_slitPlane_of_re_pos hx
  have hys : y ^ 2 ∈ slitPlane := sq_mem_slitPlane_of_re_pos hy
  have hm := meanSquares_mem_slitDomain hx hy
  refine congrFun (eq_of_quadraticGammaRatio_mul_eq
    (f := fun β => regEqualR t β (x ^ 2) (y ^ 2))
    (g := fun β => regCarlsonR t (pair (2 * β + t) (1 / 2 - β - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)))
    (analyticOnNhd_regEqualR_parameter _ hxs hys) (fun β _ => analyticAt_regCarlsonR_comp
      analyticAt_const (b := fun β => pair (2 * β + t) (1 / 2 - β - t))
      (analyticAt_pi_iff.mpr fun i => by
        fin_cases i
        · exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
        · exact (analyticAt_const.sub analyticAt_id).sub analyticAt_const) analyticAt_const hm)
    fun β _ => ?_) β
  rw [← regCarlsonR_pair_self_eq _ β hxs hys, regRSlit_secondQuadratic t β x y hx hy]

/-- The node pairs on the slit plane, as a subset of `Fin 2 → ℂ`. -/
theorem analyticOnNhd_regEqualR_nodes (t β : ℂ) :
    AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => regEqualR t β (w 0) (w 1)) carlsonRSlitDomain :=
  fun w hw => analyticAt_regEqualR_comp analyticAt_const analyticAt_const
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w)
    ((ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w) (hw 0) (hw 1)

/-- At exponent zero the equal-parameter normalization is `1/Γ(β + 1/2)` on the slit domain. -/
@[simp] theorem regEqualR_zero (β : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regEqualR 0 β x y = (Gamma (β + 1 / 2))⁻¹ := by
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have hg : AnalyticOnNhd ℂ (fun β : ℂ => (Gamma (β + 1 / 2))⁻¹) univ := fun β _ => by
    have h := (differentiable_one_div_Gamma.analyticAt (β + 1 / 2)).comp_of_eq
      (analyticAt_id.add analyticAt_const) rfl
    simpa [Function.comp_def, one_div] using h
  refine congrFun (eq_of_quadraticGammaRatio_mul_eq (f := fun β => regEqualR 0 β x y)
    (analyticOnNhd_regEqualR_parameter 0 hx hy) hg fun β hβ => ?_) β
  have hR := regCarlsonR_natCast 0 (pair β β) hz
  simp only [Nat.cast_zero, regCarlsonRPolynomial_zero, sum_pair] at hR
  have hG : Gamma (β + β) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re]; linarith)
  have hq := quadraticGammaRatio_ne_zero hβ
  rw [← regCarlsonR_pair_self_eq 0 β hx hy, hR, ← Gamma_mul_quadraticGammaRatio hβ]
  field_simp

/-- Carlson's ordinary equal-parameter function `R_t(β, β; x, y)`, as `Γ(β + 1/2)` times the
equal-parameter normalization. It is holomorphic wherever `β + 1/2` is not a nonpositive
integer, in particular at `β = 0, -1, -2, …`; at genuine poles the value is totalized. -/
def equalRSlit (t β x y : ℂ) : ℂ := Gamma (β + 1 / 2) * regEqualR t β x y

/-- Holomorphy of the ordinary equal-parameter function on Carlson's parameter domain. -/
theorem analyticAt_equalRSlit_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t β x y : E → ℂ} {p : E} (ht : AnalyticAt ℂ t p) (hβ : AnalyticAt ℂ β p)
    (hx : AnalyticAt ℂ x p) (hy : AnalyticAt ℂ y p) (hxs : x p ∈ slitPlane)
    (hys : y p ∈ slitPlane) (hreg : IsGammaRegular (β p + 1 / 2)) :
    AnalyticAt ℂ (fun w => equalRSlit (t w) (β w) (x w) (y w)) p := by
  have hG : AnalyticAt ℂ (fun w => Gamma (β w + 1 / 2)) p := by
    have hsum : AnalyticAt ℂ (fun w => β w + 1 / 2) p := hβ.add analyticAt_const
    have H := ((differentiable_one_div_Gamma.analyticAt (β p + 1 / 2)).comp_of_eq hsum rfl).inv
      (inv_ne_zero (Gamma_ne_zero hreg))
    change AnalyticAt ℂ (fun w => (Gamma (β w + 1 / 2))⁻¹⁻¹) p at H
    simpa only [inv_inv] using H
  exact hG.mul (analyticAt_regEqualR_comp ht hβ hx hy hxs hys)

/-- Agreement of the ordinary equal-parameter function with the native integral wherever that
integral converges. -/
theorem equalRSlit_eq_integral (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hβ : 0 < β.re) : equalRSlit t β x y = rIntegral t β β x y := by
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  rw [equalRSlit, regEqualR_eq_integral t β hx hy hβ]
  exact mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hc)

/-- The nonpositive integral parameters are in the domain of the ordinary equal-parameter
functions. -/
theorem isGammaRegular_neg_nat_add_half (n : ℕ) :
    IsGammaRegular (-(n : ℂ) + 1 / 2) := by
  intro m hm
  have H : (2 : ℂ) * m + 1 = 2 * n := by linear_combination 2 * hm
  have Hnat : 2 * m + 1 = 2 * n := by exact_mod_cast H
  omega

/-- At exponent zero the ordinary equal-parameter function is one, including at
`β = 0, -1, -2, …`. -/
theorem equalRSlit_zero {β x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hβ : IsGammaRegular (β + 1 / 2)) : equalRSlit 0 β x y = 1 := by
  rw [equalRSlit, regEqualR_zero β hx hy, mul_inv_cancel₀ (Gamma_ne_zero hβ)]

/-- **Carlson 6.9-3 in ordinary normalization** on the full domain `re x, re y > 0`. -/
theorem equalRSlit_firstQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    equalRSlit (2 * t) β x y = carlsonR t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  rw [equalRSlit, regEqualR_firstQuadratic t β hx hy, carlsonR, sum_pair]
  congr 2; ring

/-- **Carlson 6.10-1 in ordinary normalization** on the full domain `re x, re y > 0`. -/
theorem equalRSlit_secondQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    equalRSlit t β (x ^ 2) (y ^ 2) = carlsonR t (pair (2 * β + t) (1 / 2 - β - t))
      (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  rw [equalRSlit, regEqualR_secondQuadratic t β hx hy, carlsonR, sum_pair]
  congr 2; ring

/-! ### The equal-parameter L-function -/

/-- The equal-parameter normalization of Carlson's L-function, the exponent derivative of
`regEqualR`. -/
def regEqualL (t β x y : ℂ) : ℂ := deriv (fun s => regEqualR s β x y) t

/-- Joint holomorphy of `regEqualL` in exponent, parameter and slit-plane nodes. -/
theorem analyticOnNhd_regEqualL_joint :
    AnalyticOnNhd ℂ (fun p : Fin 4 → ℂ => regEqualL (p 0) (p 1) (p 2) (p 3))
      {p | p 2 ∈ slitPlane ∧ p 3 ∈ slitPlane} := by
  have hU : IsOpen {p : Fin 4 → ℂ | p 2 ∈ slitPlane ∧ p 3 ∈ slitPlane} := by
    apply IsOpen.inter
    · exact isOpen_slitPlane.preimage (continuous_apply 2 : Continuous fun p : Fin 4 → ℂ => p 2)
    · exact isOpen_slitPlane.preimage (continuous_apply 3 : Continuous fun p : Fin 4 → ℂ => p 3)
  have ha : AnalyticOnNhd ℂ (fun p : Fin 4 → ℂ => regEqualR (p 0) (p 1) (p 2) (p 3))
      {p | p 2 ∈ slitPlane ∧ p 3 ∈ slitPlane} := fun p hp =>
    analyticAt_regEqualR_comp ((analyticAt_pi_iff.mp analyticAt_id) 0)
      ((analyticAt_pi_iff.mp analyticAt_id) 1) ((analyticAt_pi_iff.mp analyticAt_id) 2)
      ((analyticAt_pi_iff.mp analyticAt_id) 3) hp.1 hp.2
  have h := ha.partialDeriv hU 0
  have heq : SeveralComplexVariables.partialDeriv 0
      (fun p : Fin 4 → ℂ => regEqualR (p 0) (p 1) (p 2) (p 3)) =
      (fun p => regEqualL (p 0) (p 1) (p 2) (p 3)) := by
    funext p
    simp only [SeveralComplexVariables.partialDeriv, regEqualL, Function.update_self]
    simp only [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
  rwa [heq] at h

/-- Analytic substitutions in `regEqualL`. -/
theorem analyticAt_regEqualL_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t β x y : E → ℂ} {p : E} (ht : AnalyticAt ℂ t p) (hβ : AnalyticAt ℂ β p)
    (hx : AnalyticAt ℂ x p) (hy : AnalyticAt ℂ y p) (hxs : x p ∈ slitPlane)
    (hys : y p ∈ slitPlane) :
    AnalyticAt ℂ (fun w => regEqualL (t w) (β w) (x w) (y w)) p := by
  set q : E → Fin 4 → ℂ := fun w => ![t w, β w, x w, y w]
  have hq : AnalyticAt ℂ q p := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact ht
    · exact hβ
    · exact hx
    · exact hy
  have h := (analyticOnNhd_regEqualL_joint (q p) ⟨hxs, hys⟩).comp hq
  exact h

/-- `regEqualL` is the exponent derivative of `regEqualR`. -/
theorem hasDerivAt_regEqualR_L (t β : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    HasDerivAt (fun s => regEqualR s β x y) (regEqualL t β x y) t :=
  (analyticAt_regEqualR_comp analyticAt_id analyticAt_const analyticAt_const analyticAt_const
    hx hy).differentiableAt.hasDerivAt

/-- The general regularized L-function with equal parameters is Legendre's duplication ratio
times `regEqualL`, for slit-plane nodes. -/
theorem regCarlsonL_pair_self_eq (t β : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonL t (pair β β) (pair x y) = quadraticGammaRatio β * regEqualL t β x y := by
  have heq : (fun s => regCarlsonR s (pair β β) (pair x y)) =
      (fun s => quadraticGammaRatio β * regEqualR s β x y) :=
    funext fun s => regCarlsonR_pair_self_eq s β hx hy
  rw [regCarlsonL, heq]
  exact ((hasDerivAt_regEqualR_L t β hx hy).const_mul _).deriv

/-- For convergent parameters and right-half-plane nodes, `regEqualL` is the native L-integral
divided by `Γ(β + 1/2)`. -/
theorem regEqualL_eq_integral (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hβ : 0 < β.re) :
    regEqualL t β x y = carlsonLIntegral t (pair β β) (pair x y) / Gamma (β + 1 / 2) := by
  have hz : pair x y ∈ carlsonRVariableDomain := by intro i; fin_cases i <;> assumption
  have hb : pair β β ∈ mvBetaConvergent := by intro i; fin_cases i <;> exact hβ
  have heq : (fun s => regEqualR s β x y) =
      (fun s => rIntegral s β β x y / Gamma (β + 1 / 2)) :=
    funext fun s => regEqualR_eq_integral s β hx hy hβ
  have h := hasDerivAt_regEqualR_L t β (carlsonRightHalfPlane_subset_slitPlane hx)
    (carlsonRightHalfPlane_subset_slitPlane hy)
  rw [heq] at h
  exact h.unique ((hasDerivAt_carlsonRIntegral_L t hb hz).div_const _)

/-- The exponent derivative of 6.9-3, with the full parameter-derivative correction, on
Carlson's node domain `re x, re y > 0`. -/
theorem regEqualL_firstQuadratic_deriv (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * regEqualL (2 * t) β x y =
      regCarlsonL t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) +
      regRParameterTransfer t (β + t) (1 / 2 - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  have h := (hasDerivAt_regEqualR_L (2 * t) β (carlsonRightHalfPlane_subset_slitPlane hx)
    (carlsonRightHalfPlane_subset_slitPlane hy)).comp t ((hasDerivAt_id t).const_mul 2)
  have heq : (fun s => regEqualR (2 * s) β x y) =
      (fun s => regCarlsonR s (pair (β + s) (1 / 2 - s))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y))) :=
    funext fun s => regEqualR_firstQuadratic s β hx hy
  have hd := h.deriv
  change deriv (fun s => regEqualR (2 * s) β x y) t = _ at hd
  rw [heq, deriv_regCarlsonR_exponent_transfer _ _ _ _ _ (meanSquares_mem_slitDomain hx hy)] at hd
  simpa [mul_comm] using hd.symm

/-- The exponent derivative of 6.10-1, with the full parameter-derivative correction, on
Carlson's node domain `re x, re y > 0`. -/
theorem regEqualL_secondQuadratic_deriv (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regEqualL t β (x ^ 2) (y ^ 2) =
      regCarlsonL t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) +
      regRParameterTransfer t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  have heq : (fun s => regEqualR s β (x ^ 2) (y ^ 2)) =
      (fun s => regCarlsonR s (pair (2 * β + s) (1 / 2 - β - s))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y))) :=
    funext fun s => regEqualR_secondQuadratic s β hx hy
  change deriv (fun s => regEqualR s β (x ^ 2) (y ^ 2)) t = _
  rw [heq]
  exact deriv_regCarlsonR_exponent_transfer t (2 * β) (1 / 2 - β)
    (arithmeticMeanSq x y) (geometricMeanSq x y) (meanSquares_mem_slitDomain hx hy)

/-- For right-half-plane nodes the ratio of the squared arithmetic and geometric means lies in
the slit plane: it is the square of `(u/v + v/u)/2` for sectorial square roots `u, v`. -/
theorem div_meanSquares_mem_slitPlane {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    arithmeticMeanSq x y / geometricMeanSq x y ∈ slitPlane := by
  obtain ⟨u, rfl, hu, hus⟩ := exists_sq_eq_of_re_pos hx
  obtain ⟨v, rfl, hv, hvs⟩ := exists_sq_eq_of_re_pos hy
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hkey : 0 < u.re * v.re + u.im * v.im := by
    have h1 : |u.im| * |v.im| < u.re * v.re :=
      mul_lt_mul'' hus hvs (abs_nonneg _) (abs_nonneg _)
    have h2 : -(u.im * v.im) ≤ |u.im| * |v.im| := by
      rw [← abs_mul]; exact neg_le_abs _
    linarith
  have hre : 0 < ((u / v + v / u) / 2).re := by
    have huv : 0 < (u / v).re := by
      rw [div_re]
      have := normSq_pos.mpr hv0
      rw [← add_div]
      exact div_pos (by nlinarith) this
    have hvu : 0 < (v / u).re := by
      rw [div_re]
      have := normSq_pos.mpr hu0
      rw [← add_div]
      exact div_pos (by nlinarith) this
    simp only [div_ofNat_re, add_re]; linarith
  have heq : arithmeticMeanSq (u ^ 2) (v ^ 2) / geometricMeanSq (u ^ 2) (v ^ 2) =
      ((u / v + v / u) / 2) ^ 2 := by
    simp only [arithmeticMeanSq, geometricMeanSq]
    field_simp
  rw [heq]
  exact sq_mem_slitPlane_of_re_pos hre

/-- Two node functions analytic on the right-half-plane pairs and agreeing on both quadratic
domains near `(1, 1)` agree on all right-half-plane pairs. -/
theorem eq_of_eventuallyEq_quadraticDomains {F G : (Fin 2 → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F carlsonRVariableDomain) (hG : AnalyticOnNhd ℂ G carlsonRVariableDomain)
    (h : ∀ w ∈ carlsonRVariableDomain, FirstQuadraticDomain (w 0) (w 1) →
      SecondQuadraticDomain (w 0) (w 1) → F w = G w)
    {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : F (pair x y) = G (pair x y) := by
  have h1 : (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain := fun _ => by
    simp [carlsonRightHalfPlane]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    convex_right_node_domain.isPreconnected h1 (by
      filter_upwards [eventually_quadraticDomains_one,
        isOpen_carlsonRVariableDomain.mem_nhds h1] with w hw hw'
      exact h w hw' hw.1 hw.2)
  exact heq (show pair x y ∈ carlsonRVariableDomain by intro i; fin_cases i <;> assumption)

/-- Analyticity of the pieces of the L-quadratic identities in the two nodes. -/
private theorem analyticAt_lQuadratic_rhs (t t' : ℂ) (b b' : Fin 2 → ℂ) {w : Fin 2 → ℂ}
    (hw : w ∈ carlsonRVariableDomain) :
    AnalyticAt ℂ (fun q : Fin 2 → ℂ =>
      regCarlsonL t b (pair (arithmeticMeanSq (q 0) (q 1)) (geometricMeanSq (q 0) (q 1))) -
      geometricMeanSq (q 0) (q 1) ^ t * regCarlsonL t' b'
        (pair (arithmeticMeanSq (q 0) (q 1) / geometricMeanSq (q 0) (q 1)) 1)) w := by
  have h0 := (ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w
  have h1 := (ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w
  have hA : AnalyticAt ℂ (fun q : Fin 2 → ℂ => arithmeticMeanSq (q 0) (q 1)) w :=
    ((h0.add h1).div_const (c := (2 : ℂ))).pow 2
  have hGm : AnalyticAt ℂ (fun q : Fin 2 → ℂ => geometricMeanSq (q 0) (q 1)) w := h0.mul h1
  have hGs : geometricMeanSq (w 0) (w 1) ∈ slitPlane := mul_mem_slitPlane_of_re_pos (hw 0) (hw 1)
  refine (analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const
    (analyticAt_meanSquares w) (meanSquares_mem_slitDomain (hw 0) (hw 1))).sub
    ((hGm.cpow analyticAt_const hGs).mul (analyticAt_regCarlsonL_comp analyticAt_const
      analyticAt_const ?_ ?_))
  · refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact hA.div hGm (slitPlane_ne_zero hGs)
    · exact analyticAt_const
  · intro i; fin_cases i
    · exact div_meanSquares_mem_slitPlane (hw 0) (hw 1)
    · exact one_mem_slitPlane

/-- **Carlson (1987), (6.4)**, in the equal-parameter normalization on the full node domain
`re x, re y > 0`, for all complex `t, β`. -/
theorem regEqualL_firstQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * regEqualL (2 * t) β x y =
      regCarlsonL t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * regCarlsonL (-(β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  refine eq_of_eventuallyEq_quadraticDomains
    (F := fun q => 2 * regEqualL (2 * t) β (q 0) (q 1)) (fun w hw => ?_)
    (fun w hw => analyticAt_lQuadratic_rhs _ _ _ _ hw) (fun w hw h1 _ => ?_) hx hy
  · exact analyticAt_const.mul (analyticAt_regEqualL_comp analyticAt_const analyticAt_const
      ((ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w)
      ((ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w)
      (carlsonRightHalfPlane_subset_slitPlane (hw 0))
      (carlsonRightHalfPlane_subset_slitPlane (hw 1)))
  · have h := regEqualL_firstQuadratic_deriv t β (hw 0) (hw 1)
    rw [regRParameterTransfer_eq_neg_L _ _ _ _ _ h1.2,
      show β + t + (1 / 2 - t) + t = β + 1 / 2 + t by ring] at h
    simpa only [sub_eq_add_neg] using h

/-- **Carlson (1987), (6.5)**, in the equal-parameter normalization on the full node domain
`re x, re y > 0`, for all complex `t, β`. -/
theorem regEqualL_secondQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regEqualL t β (x ^ 2) (y ^ 2) =
      regCarlsonL t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * regCarlsonL (-(2 * β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  refine eq_of_eventuallyEq_quadraticDomains
    (F := fun q => regEqualL t β (q 0 ^ 2) (q 1 ^ 2)) (fun w hw => ?_)
    (fun w hw => analyticAt_lQuadratic_rhs _ _ _ _ hw) (fun w hw _ h2 => ?_) hx hy
  · exact analyticAt_regEqualL_comp analyticAt_const analyticAt_const
      (((ContinuousLinearMap.proj 0 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w).pow 2)
      (((ContinuousLinearMap.proj 1 : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt w).pow 2)
      (sq_mem_slitPlane_of_re_pos (hw 0)) (sq_mem_slitPlane_of_re_pos (hw 1))
  · have h := regEqualL_secondQuadratic_deriv t β (hw 0) (hw 1)
    rw [regRParameterTransfer_eq_neg_L _ _ _ _ _ h2.2,
      show 2 * β + t + (1 / 2 - β - t) + t = β + 1 / 2 + t by ring] at h
    simpa only [sub_eq_add_neg] using h

/-- **Carlson (1987), first identity (6.8)**, on the full node domain `re x, re y > 0`. -/
theorem regEqualL_firstQuadratic_zero (β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * regEqualL 0 β x y =
      regCarlsonL 0 (pair β (1 / 2)) (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  simpa [regRParameterTransfer_zero _ _ _ _ (meanSquares_mem_slitDomain hx hy)] using
    regEqualL_firstQuadratic_deriv 0 β hx hy

/-- **Carlson (1987), second identity (6.8)**, on the full node domain `re x, re y > 0`. -/
theorem regEqualL_secondQuadratic_zero (β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regEqualL 0 β (x ^ 2) (y ^ 2) =
      regCarlsonL 0 (pair (2 * β) (1 / 2 - β))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  simpa [regRParameterTransfer_zero _ _ _ _ (meanSquares_mem_slitDomain hx hy)] using
    regEqualL_secondQuadratic_deriv 0 β hx hy

/-- Carlson's ordinary equal-parameter L-function `L_t(β, β; x, y)` on slit-plane nodes, as
`Γ(β + 1/2)` times `regEqualL`; finite at `β = 0, -1, -2, …`. -/
def equalLSlit (t β x y : ℂ) : ℂ := Gamma (β + 1 / 2) * regEqualL t β x y

/-- Agreement of the ordinary equal-parameter L-function with the native L-integral wherever
that integral converges. -/
theorem equalLSlit_eq_integral (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hβ : 0 < β.re) : equalLSlit t β x y = carlsonLIntegral t (pair β β) (pair x y) := by
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  rw [equalLSlit, regEqualL_eq_integral t β hx hy hβ]
  exact mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hc)

/-- The ordinary equal-parameter L-function is the exponent derivative of `equalRSlit`. -/
theorem hasDerivAt_equalRSlit_L (t β : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    HasDerivAt (fun s => equalRSlit s β x y) (equalLSlit t β x y) t :=
  (hasDerivAt_regEqualR_L t β hx hy).const_mul _

/-- **Carlson (1987), (6.4)**, in ordinary normalization on the full domain `re x, re y > 0`.
At genuine poles of `Γ(β + 1/2)` both sides are totalized expressions. -/
theorem equalLSlit_firstQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * equalLSlit (2 * t) β x y =
      carlsonL t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * carlsonL (-(β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := congrArg (fun w => Gamma (β + 1 / 2) * w) (regEqualL_firstQuadratic t β hx hy)
  simp only [equalLSlit, carlsonL, sum_pair]
  rw [show β + t + (1 / 2 - t) = β + 1 / 2 by ring,
    show -t + (β + 1 / 2 + t) = β + 1 / 2 by ring]
  linear_combination h

/-- **Carlson (1987), (6.5)**, in ordinary normalization on the full domain `re x, re y > 0`. -/
theorem equalLSlit_secondQuadratic (t β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    equalLSlit t β (x ^ 2) (y ^ 2) =
      carlsonL t (pair (2 * β + t) (1 / 2 - β - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) -
      geometricMeanSq x y ^ t * carlsonL (-(2 * β + t))
        (pair (-t) (β + 1 / 2 + t))
        (pair (arithmeticMeanSq x y / geometricMeanSq x y) 1) := by
  have h := congrArg (fun w => Gamma (β + 1 / 2) * w) (regEqualL_secondQuadratic t β hx hy)
  simp only [equalLSlit, carlsonL, sum_pair]
  rw [show 2 * β + t + (1 / 2 - β - t) = β + 1 / 2 by ring,
    show -t + (β + 1 / 2 + t) = β + 1 / 2 by ring]
  linear_combination h

end Carlson.TwoVariable
end
