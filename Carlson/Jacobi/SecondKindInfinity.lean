/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKind
public import Dirichlet.Average.ResolventInfinity

/-!
# Normalization at infinity of Carlson's second-kind Jacobi functions

The product `x^(n+1) qₙ(x)` tends to one as `x` tends to infinity in any complex
direction, provided the Gamma normalization at this index is regular. After
inversion, it extends analytically across zero. Affine covariance includes arbitrary
complex endpoints and permits transport of segment formulas to other coordinates.

## Main results

* `jacobiSecondKind_affine`: covariance under invertible complex affine maps.
* `analyticAt_jacobiSecondKind_infinity`: analyticity of the normalized reciprocal chart.
* `tendsto_pow_mul_jacobiSecondKind`: the normalization `qₙ(x) ∼ x^(-n-1)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Dirichlet Complex Set Filter Bornology
open scoped Topology

/-- An invertible affine change of endpoints and evaluation point multiplies the
second-kind function by the corresponding negative integer power of the scale. -/
theorem jacobiSecondKind_affine (α β r s c d : ℂ) (n : ℕ) (hc : c ≠ 0)
    {x : ℂ} (hx : x ∉ segment ℝ r s) :
    jacobiSecondKind α β (c * r + d) (c * s + d) n (c * x + d) =
      c ^ (-(n + 1 : ℤ)) * jacobiSecondKind α β r s n x := by
  have he : pair (c * r + d) (c * s + d) = fun i => c * pair r s i + d := by
    ext i; fin_cases i <;> rfl
  unfold jacobiSecondKind
  rw [he, continuedRegCarlsonResolvent_affine n _ _ c d hc
    (mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair]))]
  ring

/-- In reciprocal coordinates the normalized second-kind function extends
analytically to infinity, at arbitrary complex Jacobi parameters. -/
theorem analyticAt_jacobiSecondKind_infinity (α β r s : ℂ) (n : ℕ) :
    AnalyticAt ℂ (fun w => jacobiSecondKind α β (w * r) (w * s) n 1) 0 := by
  have he (w : ℂ) : pair (w * r) (w * s) = fun i => w * pair r s i := by
    ext i; fin_cases i <;> rfl
  simp only [jacobiSecondKind, he]
  exact analyticAt_const.mul (analyticAt_continuedRegCarlsonResolvent_infinity n _ _)

/-- The leading asymptotic coefficient of Carlson's second-kind Jacobi function
is one. Only the Gamma factor at this particular index must be regular. -/
theorem tendsto_pow_mul_jacobiSecondKind (α β r s : ℂ) (n : ℕ)
    (hc : IsCarlsonGammaRegular (α + n + 1 + (β + n + 1))) :
    Tendsto (fun x => x ^ (n + 1) * jacobiSecondKind α β r s n x)
      (cobounded ℂ) (𝓝 1) := by
  have h := (tendsto_continuedRegCarlsonResolvent_infinity n
    (pair (α + n + 1) (β + n + 1)) (pair r s)).const_mul
      (Gamma (α + n + 1 + (β + n + 1)))
  rw [sum_pair, mul_inv_cancel₀ (Gamma_ne_zero hc)] at h
  simpa only [jacobiSecondKind, mul_left_comm] using h

end Carlson.TwoVariable
