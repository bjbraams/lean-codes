/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AnalyticExpansion
public import Carlson.S

/-!
# The plane-wave expansion

The exponential function is entire, so its Jacobi expansion converges throughout the plane.
Its coefficients are the continued Dirichlet averages of `λⁿ exp (λ x)`, that is, Carlson's
`S`-functions. This is Carlson's Example 7.7-1, equation (2), at arbitrary complex endpoints
and complex parameters with admissible total.

## Main results

* `isRegCarlsonContinuation_iteratedDeriv_exp`: the `S`-function continues the averages.
* `hasSum_exp_jacobiOn`: `exp (λ x) = Σ λⁿ/n! S(1+α+n, 1+β+n; λr, λs) pₙ(x)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Example 7.7-1.
-/

@[expose] public noncomputable section
open Complex Set Metric Filter Polynomial Dirichlet
open scoped Topology

namespace Carlson.TwoVariable

/-- The regularized S-function supplies the entire continuation of the Dirichlet averages of
the derivatives of `x ↦ exp (λ x)`. -/
theorem isRegCarlsonContinuation_iteratedDeriv_exp (lam : ℂ) (n : ℕ) (z : Fin 2 → ℂ) :
    IsRegCarlsonContinuation (iteratedDeriv n fun x => exp (lam * x)) z
      (fun b => lam ^ n * Carlson.regCarlsonS b (fun i => lam * z i)) := by
  have h := (Carlson.isRegCarlsonSContinuation_series (fun i => lam * z i)).smul (lam ^ n)
  rw [iteratedDeriv_cexp_const_mul]
  have hg : (fun u : Fin 2 → ℝ => lam ^ n * exp (lam * carlsonAffineForm z u)) =
      fun u => lam ^ n * exp (carlsonAffineForm (fun i => lam * z i) u) := by
    funext u
    simp only [carlsonAffineForm, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl; intro i _; ring
  show IsRegDirichletContinuation _ _
  rw [hg]
  exact h

/-- Carlson's Example 7.7-1: the plane-wave expansion
`exp (λ x) = Σ λⁿ/n! S(1+α+n, 1+β+n; λr, λs) pₙ(x)`, for all complex `λ, x`, endpoints, and
parameters with admissible total. -/
theorem hasSum_exp_jacobiOn (α β r s : ℂ) (hc : IsGammaRegular (α + β + 2))
    (lam x : ℂ) :
    HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℂ) *
      Carlson.carlsonS (pair (1 + α + n) (1 + β + n)) (pair (lam * r) (lam * s)) *
        (jacobiOn α β r s n).eval x) (exp (lam * x)) := by
  set R : ℝ := 2 * (‖r‖ + ‖s‖) + 1
  have hR : 0 < R := by positivity
  set Γ : Cycle := Cycle.zsmulLoop 1 (Loop.ofPath (Path.circle 0 R))
  have hΓ : Γ.IsC1 := Cycle.zsmulLoop_isC1 _ (Path.contDiffOn_circle 0 R)
  have hball : ∀ w ∈ segment ℝ r s, w ∈ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_ball_zero_iff]
    have := norm_sub_le_of_mem_segment hw
    have h2 : ‖w‖ ≤ ‖w - r‖ + ‖r‖ := by simpa using norm_add_le (w - r) r
    have h3 : ‖s - r‖ ≤ ‖s‖ + ‖r‖ := norm_sub_le _ _
    have := norm_nonneg s
    simp only [R]
    linarith
  have hrange : Γ.range ⊆ sphere (0 : ℂ) R := by
    apply (Cycle.zsmulLoop_range_subset _ _).trans
    change range (Path.circle 0 R) ⊆ sphere 0 R
    rw [Path.range_circle, abs_of_pos hR]
  have havoid : Γ.range ⊆ (segment ℝ r s)ᶜ := fun z hz hzs => by
    have h1 := hrange hz
    have h2 := hball z hzs
    rw [mem_sphere_zero_iff_norm] at h1
    rw [mem_ball_zero_iff] at h2
    linarith
  have hind : Γ.index r = 1 := by
    rw [Cycle.index_zsmulLoop]
    change ((1 : ℤ) : ℂ) * curveIndex (Path.circle 0 R) r = 1
    rw [curveIndex_circle_of_mem_ball (hball r (left_mem_segment ℝ r s))]
    norm_num
  have hf : Differentiable ℂ fun x => exp (lam * x) := by fun_prop
  have hsum := hasSum_jacobiContourCoefficient_of_entire α β r s hc Γ hΓ havoid hind hf x
  convert hsum using 2 with n
  congr 1
  -- identify the contour coefficient with the S-function
  unfold jacobiContourCoefficient
  rw [Cycle.integral_zsmulLoop, one_smul]
  dsimp only [Loop.ofPath]
  rw [curveIntegral_circle,
    circleIntegral_jacobiSecondKind_mul α β r s n (isRegCarlsonContinuation_iteratedDeriv_exp lam n
      (pair r s)) hR hf.diffContOnCl (fun w ⟨i, hi⟩ => hi ▸ hball _ (by
        fin_cases i
        · exact left_mem_segment ℝ r s
        · exact right_mem_segment ℝ r s))]
  simp only [Carlson.carlsonS, sum_pair]
  have he (i : Fin 2) : lam * pair r s i = pair (lam * r) (lam * s) i := by fin_cases i <;> rfl
  simp only [he]
  rw [show α + n + 1 + (β + n + 1) = 1 + α + n + (1 + β + n) by ring,
    show pair (α + n + 1) (β + n + 1) = pair (1 + α + n) (1 + β + n) by
      funext i; fin_cases i <;> simp [pair] <;> ring]
  ring

end Carlson.TwoVariable
