/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexRodrigues
public import Carlson.Jacobi.WeightedIntegral

/-!
# Weighted Jacobi integrals at complex parameters

For `re α, re β > -1`, repeated integration by parts with the complex Jacobi
weight gives coefficient identities and bilinear orthogonality on the unit
interval. No complex conjugation occurs in these integrals: they continue the
real orthogonality identities analytically in the parameters. The derivative
tower may be complex valued and needs only continuity up to the endpoints.

## Main results

* `factorial_mul_integral_complexJacobiWeight`: the weighted derivative-tower identity.
* `integral_complexJacobiWeight_mul_eq_zero`: orthogonality against lower-degree polynomials.
* `integral_complexJacobiWeight_mul_shiftedJacobi_eq_zero`: pairwise bilinear orthogonality.
* `integral_complexJacobiWeight_sq`: the diagonal integral in Gamma-quotient form.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Representation 7.8-2 and Theorem 7.8-3.
-/

public noncomputable section
namespace Polynomial
open Complex MeasureTheory Set

/-- One integration by parts with the complex Jacobi weight. -/
theorem integral_complexJacobiWeight_mul_shiftedJacobi_succ {α β : ℂ}
    (hα : -1 < α.re) (hβ : -1 < β.re) (n : ℕ) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x) :
    (n + 1 : ℂ) * (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * f x *
      (shiftedJacobi α β (n + 1)).eval (x : ℂ)) =
      -(∫ x in (0 : ℝ)..1, complexJacobiWeight (α + 1) (β + 1) x * g x *
        (shiftedJacobi (α + 1) (β + 1) n).eval (x : ℂ)) := by
  have hf' : ContinuousOn f (uIcc (0 : ℝ) 1) := by simpa using hf
  have hg' : ContinuousOn g (uIcc (0 : ℝ) 1) := by simpa using hg
  have hv := (continuous_complexJacobiWeight_succ hα hβ).fun_mul
    ((shiftedJacobi (α + 1) (β + 1) n).continuous.comp continuous_ofReal)
  have hi := ((intervalIntegrable_complexJacobiWeight hα hβ).mul_continuousOn
    ((shiftedJacobi α β (n + 1)).continuous.comp continuous_ofReal).continuousOn).const_mul
      (n + 1 : ℂ)
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :=
    (hasDerivAt_complexJacobiWeight_mul_shiftedJacobi α β n
      (ofReal_mem_slitPlane.mpr hx.1)
      (by apply Or.inl; simp only [sub_re, one_re, ofReal_re]; linarith [hx.2])).comp_ofReal
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf' hv.continuousOn (by simpa using hfg) (by simpa [Function.comp_def] using hd)
    hg'.intervalIntegrable hi
  have hl : (∫ x in (0 : ℝ)..1, f x * ((n + 1 : ℂ) *
      (complexJacobiWeight α β x * (shiftedJacobi α β (n + 1)).eval (x : ℂ)))) =
      (n + 1 : ℂ) * (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * f x *
        (shiftedJacobi α β (n + 1)).eval (x : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  simp only [Function.comp_def, ofReal_one, ofReal_zero] at h
  rw [hl, complexJacobiWeight_succ_one hβ, complexJacobiWeight_succ_zero hα] at h
  simp only [zero_mul, mul_zero, sub_self, zero_sub] at h
  convert h using 1
  congr 2
  funext x
  ring

/-- Repeated weighted integration by parts for a complex-valued derivative tower
and complex Jacobi parameters in the full native convergence region. -/
theorem factorial_mul_integral_complexJacobiWeight {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) (f : ℕ → ℝ → ℂ)
    (hc : ∀ k ≤ n, ContinuousOn (f k) (Icc 0 1))
    (hd : ∀ k < n, ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (f k) (f (k + 1) x) x) :
    (n.factorial : ℂ) * (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * f 0 x *
      (shiftedJacobi α β n).eval (x : ℂ)) =
      (-1 : ℂ) ^ n * (∫ x in (0 : ℝ)..1,
        complexJacobiWeight (α + n) (β + n) x * f n x) := by
  induction n generalizing α β f with
  | zero => simp
  | succ n ih =>
    have hs := integral_complexJacobiWeight_mul_shiftedJacobi_succ hα hβ n (f 0) (f 1)
      (hc 0 (by omega)) (hc 1 (by omega)) (hd 0 (by omega))
    have hi := ih (α := α + 1) (β := β + 1)
      (by simp only [add_re, one_re]; linarith)
      (by simp only [add_re, one_re]; linarith)
      (fun k => f (k + 1)) (fun k hk => hc (k + 1) (by omega))
      (fun k hk => hd (k + 1) (by omega))
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [Nat.zero_add, add_assoc, add_comm (1 : ℂ) (n : ℂ)] at hi
    linear_combination (n.factorial : ℂ) * hs - hi

/-- The weighted integral against a Jacobi polynomial is a raised-weight average
of the derivative of the other polynomial. -/
theorem integral_complexJacobiWeight_mul_eq_derivative {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) (p : ℂ[X]) :
    (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * p.eval (x : ℂ) *
      (shiftedJacobi α β n).eval (x : ℂ)) =
      (-1 : ℂ) ^ n / n.factorial * (∫ x in (0 : ℝ)..1,
        complexJacobiWeight (α + n) (β + n) x * (derivative^[n] p).eval (x : ℂ)) := by
  have h := factorial_mul_integral_complexJacobiWeight hα hβ n
    (fun k x => (derivative^[k] p).eval (x : ℂ))
    (fun k _ => ((derivative^[k] p).continuous.comp continuous_ofReal).continuousOn)
    (fun k _ x _ => by simpa only [Function.iterate_succ_apply'] using
      ((derivative^[k] p).hasDerivAt (x : ℂ)).comp_ofReal)
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  dsimp only [Function.iterate_zero_apply] at h
  apply mul_left_cancel₀ hn
  rw [h]
  field_simp

/-- Complex Jacobi polynomials are bilinearly orthogonal to every polynomial of
smaller degree on the unit interval. -/
theorem integral_complexJacobiWeight_mul_eq_zero {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (n : ℕ) (p : ℂ[X]) (hp : p.natDegree < n) :
    (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x * p.eval (x : ℂ) *
      (shiftedJacobi α β n).eval (x : ℂ)) = 0 := by
  rw [integral_complexJacobiWeight_mul_eq_derivative hα hβ n p,
    iterate_derivative_eq_zero hp]
  simp

/-- Distinct shifted Jacobi polynomials are bilinearly orthogonal for complex
parameters with real parts greater than `-1`. -/
theorem integral_complexJacobiWeight_mul_shiftedJacobi_eq_zero {α β : ℂ}
    (hα : -1 < α.re) (hβ : -1 < β.re) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x *
      (shiftedJacobi α β m).eval (x : ℂ) * (shiftedJacobi α β n).eval (x : ℂ)) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact integral_complexJacobiWeight_mul_eq_zero hα hβ n _
      ((natDegree_shiftedJacobi_le α β m).trans_lt h)
  · have he (x : ℝ) : complexJacobiWeight α β x *
        (shiftedJacobi α β m).eval (x : ℂ) * (shiftedJacobi α β n).eval (x : ℂ) =
        complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ) *
          (shiftedJacobi α β m).eval (x : ℂ) := by ring
    simp_rw [he]
    exact integral_complexJacobiWeight_mul_eq_zero hα hβ m _
      ((natDegree_shiftedJacobi_le α β n).trans_lt h)

/-- The mass of the complex Jacobi weight is its Euler beta value. -/
theorem integral_complexJacobiWeight {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) :
    (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x) =
      Gamma (α + 1) * Gamma (β + 1) / Gamma (α + β + 2) := by
  have h := betaIntegral_eq_Gamma_mul_div (α + 1) (β + 1)
    (by simp only [add_re, one_re]; linarith) (by simp only [add_re, one_re]; linarith)
  simpa only [betaIntegral, add_sub_cancel_right,
    show α + 1 + (β + 1) = α + β + 2 by ring, complexJacobiWeight] using h

/-- The bilinear squared norm of a shifted Jacobi polynomial at complex
parameters. This form includes degree zero without a removable singularity. -/
theorem integral_complexJacobiWeight_sq {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    (n : ℕ) :
    (∫ x in (0 : ℝ)..1, complexJacobiWeight α β x *
      (shiftedJacobi α β n).eval (x : ℂ) ^ 2) =
      (ascPochhammer ℂ n).eval (α + β + n + 1) / n.factorial *
        (Gamma (α + n + 1) * Gamma (β + n + 1) /
          Gamma (α + n + (β + n) + 2)) := by
  have hd := iterate_derivative_shiftedJacobi α β 0 n
  simp only [Nat.zero_add, shiftedJacobi_zero, mul_one] at hd
  have h := integral_complexJacobiWeight_mul_eq_derivative hα hβ n (shiftedJacobi α β n)
  rw [hd] at h
  simp only [eval_C] at h
  rw [intervalIntegral.integral_mul_const, integral_complexJacobiWeight
    (by simp only [add_re, natCast_re]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
    (by simp only [add_re, natCast_re]; have := Nat.cast_nonneg (α := ℝ) n; linarith)] at h
  have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
  calc
    _ = _ := by simpa only [pow_two, ← mul_assoc] using h
    _ = _ := by
      calc
        _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
            ((ascPochhammer ℂ n).eval (α + β + n + 1) / n.factorial *
              (Gamma (α + n + 1) * Gamma (β + n + 1) /
                Gamma (α + n + (β + n) + 2))) := by ring
        _ = _ := by rw [hs, one_mul]

end Polynomial
