/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.WeightedIntegral

/-!
# Complex-valued weighted Jacobi integrals

The real weighted integration-by-parts identity extends to complex-valued
functions by applying the real and imaginary projections. Parameters remain real
and greater than `-1`; the functions need continuous derivative data only on the
closed unit interval, with derivative identities in its interior.

## Main results

* `factorial_smul_integral_mul_shiftedJacobi`: the complex-valued derivative-tower
  identity, obtained from the real theorem.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.8.
-/

public noncomputable section
namespace Polynomial
open MeasureTheory Set

/-- Repeated weighted integration by parts for complex-valued functions, with
continuous derivative data on the closed interval. -/
theorem factorial_smul_integral_mul_shiftedJacobi {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) (f : ℕ → ℝ → ℂ)
    (hc : ∀ k ≤ n, ContinuousOn (f k) (Icc 0 1))
    (hd : ∀ k < n, ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (f k) (f (k + 1) x) x) :
    (n.factorial : ℝ) • (∫ x in (0 : ℝ)..1,
      (shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x) • f 0 x) =
      (-1 : ℝ) ^ n • (∫ x in (0 : ℝ)..1,
        shiftedJacobiWeight (α + n) (β + n) x • f n x) := by
  have hi := ((intervalIntegrable_shiftedJacobiWeight hα hβ).mul_continuousOn
    (shiftedJacobi α β n).continuous.continuousOn).smul_continuousOn
      (by simpa using hc 0 (Nat.zero_le n))
  have hj := (intervalIntegrable_shiftedJacobiWeight
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 < α + n)
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 < β + n)).smul_continuousOn
      (by simpa using hc n le_rfl)
  have he (L : ℂ →L[ℝ] ℝ) :
      L ((n.factorial : ℝ) • (∫ x in (0 : ℝ)..1,
        (shiftedJacobiWeight α β x * (shiftedJacobi α β n).eval x) • f 0 x)) =
      L ((-1 : ℝ) ^ n • (∫ x in (0 : ℝ)..1,
        shiftedJacobiWeight (α + n) (β + n) x • f n x)) := by
    rw [map_smul, map_smul, ← L.intervalIntegral_comp_comm hi,
      ← L.intervalIntegral_comp_comm hj]
    simp only [map_smul, smul_eq_mul]
    have h := factorial_mul_integral_mul_shiftedJacobi hα hβ n (fun k x => L (f k x))
      (fun k hk => L.continuous.comp_continuousOn (hc k hk))
      (fun k hk x hx => L.hasFDerivAt.comp_hasDerivAt x (hd k hk x hx))
    simpa only [mul_right_comm] using h
  exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)

end Polynomial
