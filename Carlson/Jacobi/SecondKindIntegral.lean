/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKind
public import Carlson.Jacobi.ComplexWeightedIntegral
public import Dirichlet.Transform.Euler
public import Pochhammer.BetaIntegral

/-!
# Integral representations of the second-kind Jacobi function

For real Jacobi parameters greater than `-1`, the continued second-kind function
with endpoints `1, 0` agrees with its normalized Euler integral. Repeated weighted
integration by parts expresses it as the Cauchy transform of the Jacobi weight
times the shifted Jacobi polynomial. Evaluation points lie outside the closed unit segment.

## Main results

* `jacobiSecondKind_eq_eulerIntegral`: the normalized integer-kernel integral.
* `integral_shiftedJacobiWeight_mul_resolvent`: the weighted kernel identity.
* `jacobiSecondKind_eq_cauchyIntegral`: the normalized Cauchy representation.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Dirichlet Polynomial MeasureTheory Set

/-- A point with nonzero imaginary part lies outside the real unit segment. -/
theorem not_mem_unitSegment_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z ∉ segment ℝ (1 : ℂ) 0 := by
  rintro ⟨a, b, ha, hb, hab, rfl⟩
  simp [real_smul] at hz

/-- For real parameters in the orthogonality range, the second-kind function is
the normalized Euler integral of its integer resolvent kernel. -/
theorem jacobiSecondKind_eq_eulerIntegral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z =
      (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..1, (shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
          (z - t) ^ (-(n + 1 : ℤ)) := by
  have hb : pair ((α : ℂ) + n + 1) ((β : ℂ) + n + 1) ∈ mvBetaConvergent := by
    intro i
    fin_cases i <;> simp [pair]
    all_goals have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [jacobiSecondKind_eq_native _ _ _ _ _ n hb hz,
    carlsonDirichletAverage, sum_pair, regCarlsonDirichletAverage]
  have he (u : Fin 2 → ℝ) : carlsonAffineForm (pair 1 0) u = (u 0 : ℂ) := by
    simp [carlsonAffineForm, Fin.sum_univ_two]
  simp_rw [he]
  rw [show pair ((α : ℂ) + n + 1) ((β : ℂ) + n + 1) =
      ![((α + n + 1 : ℝ) : ℂ), ((β + n + 1 : ℝ) : ℂ)] by simp [pair],
    regDirichletIntegral_fin_two _ _ (fun t : ℝ => (z - t) ^ (-(n + 1 : ℤ))),
    regEulerIntegral, ← mul_assoc]
  have hn : Gamma ((α : ℂ) + n + 1 + ((β : ℂ) + n + 1)) *
      (Gamma ((α + n + 1 : ℝ) : ℂ) * Gamma ((β + n + 1 : ℝ) : ℂ))⁻¹ =
      (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)⁻¹ := by
    simp [ProbabilityTheory.beta, ofReal_mul, ← Gamma_ofReal,
      ofReal_add, ofReal_natCast, ofReal_one, div_eq_mul_inv]
  rw [hn, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioo]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hpow (a : ℝ) : (t : ℂ) ^ (((a + n + 1 : ℝ) : ℂ) - 1) =
      ((t ^ (a + n) : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, add_sub_cancel_right, ← ofReal_cpow ht.1.le]
  have hpow' (a : ℝ) : (1 - t : ℂ) ^ (((a + n + 1 : ℝ) : ℂ) - 1) =
      (((1 - t) ^ (a + n) : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_sub, add_sub_cancel_right,
      ← ofReal_cpow (by linarith [ht.2] : 0 ≤ 1 - t)]
  dsimp only
  rw [hpow, hpow']
  simp [shiftedJacobiWeight]

/-- The factorial-scaled integer kernels form a derivative tower on the real line
away from the exterior point. -/
theorem hasDerivAt_factorial_resolvent (k : ℕ) {z : ℂ}
    (t : ℝ) (hz : z ≠ (t : ℂ)) :
    HasDerivAt (fun u : ℝ => (k.factorial : ℂ) * (z - u) ^ (-(k + 1 : ℤ)))
      (((k + 1).factorial : ℂ) * (z - t) ^ (-((k + 1 : ℕ) + 1 : ℤ))) t := by
  have hn : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have h := ((hasDerivAt_zpow (-(k + 1 : ℤ)) (z - t) (Or.inl hn)).comp (t : ℂ)
    ((hasDerivAt_const (t : ℂ) z).sub (hasDerivAt_id (t : ℂ)))).comp_ofReal
  have he : -(k + 1 : ℤ) - 1 = -((k + 1 : ℕ) + 1 : ℤ) := by omega
  simp only [Function.comp_def, he, Int.cast_neg, Int.cast_add, Int.cast_natCast,
    Int.cast_one, zero_sub, mul_neg, mul_one, neg_mul, neg_neg] at h
  convert h.const_mul (k.factorial : ℂ) using 1
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Weighted integration by parts converts the higher resolvent into a Cauchy
kernel multiplied by the shifted Jacobi polynomial. -/
theorem integral_shiftedJacobiWeight_mul_resolvent {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    (∫ t in (0 : ℝ)..1, (shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
        (z - t) ^ (-(n + 1 : ℤ))) =
      (-1 : ℂ) ^ n * ∫ t in (0 : ℝ)..1,
        (shiftedJacobiWeight α β t * (shiftedJacobi α β n).eval t : ℝ) * (z - t)⁻¹ := by
  let f : ℕ → ℝ → ℂ := fun k t => (k.factorial : ℂ) * (z - t) ^ (-(k + 1 : ℤ))
  have hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z ≠ (t : ℂ) := by
    intro he
    apply hz
    rw [he]
    exact ⟨t, 1 - t, ht.1, sub_nonneg.mpr ht.2, by ring, by simp [real_smul]⟩
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (f k) (f (k + 1) t) t :=
    hasDerivAt_factorial_resolvent k t (hn t ht)
  have h := factorial_smul_integral_mul_shiftedJacobi hα hβ n f
    (fun k _ t ht => (hd k t ht).continuousAt.continuousWithinAt)
    (fun k _ t ht => hd k t ⟨ht.1.le, ht.2.le⟩)
  simp only [f, real_smul, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero,
    zero_add, zpow_neg_one, ofReal_pow, ofReal_neg, ofReal_one] at h
  have he : (fun t : ℝ => (shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
      ((n.factorial : ℂ) * (z - t) ^ (-(n + 1 : ℤ)))) =
      (fun t => (n.factorial : ℂ) * ((shiftedJacobiWeight (α + n) (β + n) t : ℂ) *
        (z - t) ^ (-(n + 1 : ℤ)))) := by funext t; ring
  rw [he, intervalIntegral.integral_const_mul] at h
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hh := congrArg (fun v : ℂ => (-1) ^ n * v) h
  simp only [← mul_assoc, hs, one_mul, ofReal_natCast] at hh
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ hn
  simpa only [ofReal_natCast, mul_assoc, mul_left_comm] using hh.symm

/-- The second-kind Jacobi function is the Cauchy transform of the weighted
shifted Jacobi polynomial, with Carlson's normalization. -/
theorem jacobiSecondKind_eq_cauchyIntegral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {z : ℂ} (hz : z ∉ segment ℝ (1 : ℂ) 0) :
    jacobiSecondKind α β 1 0 n z =
      ((-1 : ℂ) ^ n / (ProbabilityTheory.beta (α + n + 1) (β + n + 1) : ℂ)) *
        ∫ t in (0 : ℝ)..1,
          (shiftedJacobiWeight α β t * (shiftedJacobi α β n).eval t : ℝ) * (z - t)⁻¹ := by
  rw [jacobiSecondKind_eq_eulerIntegral hα hβ n hz,
    integral_shiftedJacobiWeight_mul_resolvent hα hβ n hz]
  ring

end Carlson.TwoVariable
