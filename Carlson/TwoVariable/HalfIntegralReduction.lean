/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.ElementaryIndependence
public import Carlson.TwoVariable.Reduction
public import Carlson.R.AssociatedDependence

/-!
# General two-variable half-integral reduction

The two-variable step of Carlson's Theorem 8.5-4 reduces every associated function
`R_{-1/2+k}(1/2+m, 1+n; x,y)`, with arbitrary integer `k,m,n`, to the standard
functions `R_C(x,y)` and `x^(-1/2)`. The existing associated-function theorem supplies
a nontrivial relation between these three functions. Independence of the two standard
functions ensures that the coefficient of the function being reduced is nonzero.

The identities are denominator-cleared and hold on the entire product slit plane,
including coincident nodes. No positivity or sign restriction on the integer shifts is
needed. The reduction from an arbitrary number of nodes to this two-variable family,
including the branch-point split (8.5-5), is separate work.
-/

open Complex Set MvPolynomial

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The regularized elementary standard function is the algebraic basis element. -/
private theorem regCarlsonR_half_zero {x y : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y) =
      x ^ (-1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ := by
  simpa only [add_zero, neg_zero, cpow_zero, mul_one,
    show -(1 / 2 : ℂ) = -1 / 2 by ring] using
      regCarlsonR_pair_neg_sum (1 / 2) 0 hx hy

/-- The regularized `R_C` basis element, with its nonzero Gamma factor made explicit. -/
private theorem regCarlsonR_half_one (x y : ℂ) :
    regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) =
      (Gamma (3 / 2))⁻¹ * carlsonRC x y := by
  unfold carlsonRC carlsonR
  rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
    ← mul_assoc, inv_mul_cancel₀ (Gamma_ne_zero_of_re_pos (by norm_num)), one_mul]

/-- **Theorem 8.5-4, two-variable reduction step**: arbitrary integer shifts of the
half-integral family reduce to `R_C` and the algebraic function `x^(-1/2)`.
The nonzero polynomial denominator is cleared, so the identity also holds at its zeros. -/
theorem exists_polynomial_reduction_half_integral (k m n : ℤ) :
    ∃ D P Q : MvPolynomial (Fin 2) ℂ, D ≠ 0 ∧
      ∀ x y : ℂ, x ∈ slitPlane → y ∈ slitPlane →
        D.eval (pair x y) *
            regCarlsonR (-1 / 2 + k) (pair (1 / 2 + m) (1 + n)) (pair x y) =
          P.eval (pair x y) * carlsonRC x y +
            Q.eval (pair x y) * x ^ (-1 / 2 : ℂ) := by
  let s : Fin 3 → RAssociatedShift (Fin 2) :=
    ![⟨k, ![m, n]⟩, ⟨0, 0⟩, ⟨0, ![0, -1]⟩]
  obtain ⟨A, hA, hrel⟩ :=
    exists_polynomial_relation_associatedCarlsonR (-1 / 2) (pair (1 / 2) 1) s
  change Fin 3 → MvPolynomial (Fin 2) ℂ at A
  have hrelation (x y : ℂ) (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
      (A 0).eval (pair x y) *
          regCarlsonR (-1 / 2 + k) (pair (1 / 2 + m) (1 + n)) (pair x y) +
        (A 1).eval (pair x y) * ((Gamma (3 / 2))⁻¹ * carlsonRC x y) +
        (A 2).eval (pair x y) * (x ^ (-1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹) = 0 := by
    have hz : pair x y ∈ carlsonRSlitDomain := by
      intro i; fin_cases i
      · exact hx
      · exact hy
    have h := hrel (pair x y) hz
    change (∑ j : Fin 3, (A j).eval (pair x y) *
      regCarlsonR ((s j).exponentValue (-1 / 2))
        ((s j).parameterValue (pair (1 / 2) 1)) (pair x y)) = 0 at h
    have hp : (s 0).parameterValue (pair (1 / 2) 1) =
        pair (1 / 2 + m) (1 + n) := by
      funext i; fin_cases i <;> simp [s, RAssociatedShift.parameterValue, pair]
    have hc : (s 1).parameterValue (pair (1 / 2) 1) = pair (1 / 2) 1 := by
      funext i; fin_cases i <;> simp [s, RAssociatedShift.parameterValue, pair]
    have ha : (s 2).parameterValue (pair (1 / 2) 1) = pair (1 / 2) 0 := by
      funext i; fin_cases i <;> simp [s, RAssociatedShift.parameterValue, pair]
    rw [Fin.sum_univ_three, hp, hc, ha] at h
    simp only [RAssociatedShift.exponentValue] at h
    norm_num [s] at h
    rw [show -(1 / 2 : ℂ) = -1 / 2 by ring] at h
    rw [regCarlsonR_half_one, regCarlsonR_half_zero hx hy] at h
    exact h
  have hD : A 0 ≠ 0 := by
    intro hzero
    have hstd := carlsonRC_polynomial_independent
      (A 1 * C (Gamma (3 / 2))⁻¹) (A 2 * C (Gamma (1 / 2))⁻¹) (fun x y hx hy => by
        have h := hrelation x y (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
        rw [hzero, map_zero, zero_mul, zero_add] at h
        simp only [map_mul, eval_C]
        linear_combination h)
    have hG₁ : (C (Gamma (3 / 2))⁻¹ : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
      exact C_ne_zero.mpr (inv_ne_zero (Gamma_ne_zero_of_re_pos (by norm_num)))
    have hG₂ : (C (Gamma (1 / 2))⁻¹ : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
      exact C_ne_zero.mpr (inv_ne_zero (Gamma_ne_zero_of_re_pos (by norm_num)))
    have h₁ : A 1 = 0 := (mul_eq_zero.mp hstd.1).resolve_right hG₁
    have h₂ : A 2 = 0 := (mul_eq_zero.mp hstd.2).resolve_right hG₂
    obtain ⟨j, hj⟩ := hA
    fin_cases j <;> contradiction
  refine ⟨A 0, -(A 1 * C (Gamma (3 / 2))⁻¹),
    -(A 2 * C (Gamma (1 / 2))⁻¹), hD, fun x y hx hy => ?_⟩
  simp only [map_neg, map_mul, eval_C]
  linear_combination hrelation x y hx hy

/-- The ordinary normalization of the two-variable half-integral reduction.
The same denominator works for all nodes, including the diagonal. -/
theorem exists_polynomial_reduction_half_integral_carlsonR (k m n : ℤ) :
    ∃ D P Q : MvPolynomial (Fin 2) ℂ, D ≠ 0 ∧
      ∀ x y : ℂ, x ∈ slitPlane → y ∈ slitPlane →
        D.eval (pair x y) *
            carlsonR (-1 / 2 + k) (pair (1 / 2 + m) (1 + n)) (pair x y) =
          P.eval (pair x y) * carlsonRC x y +
            Q.eval (pair x y) * x ^ (-1 / 2 : ℂ) := by
  obtain ⟨D, P, Q, hD, h⟩ := exists_polynomial_reduction_half_integral k m n
  let G := Gamma ((1 / 2 + m : ℂ) + (1 + n))
  refine ⟨D, C G * P, C G * Q, hD, fun x y hx hy => ?_⟩
  simp only [map_mul, eval_C, carlsonR, sum_pair]
  linear_combination G * h x y hx hy

end Carlson.TwoVariable
