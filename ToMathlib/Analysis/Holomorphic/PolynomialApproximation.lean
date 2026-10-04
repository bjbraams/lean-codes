/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import ToMathlib.Analysis.Analytic.PolynomialApproximation

/-!
# Polynomial approximation on complex disks and the plane

The approximation results build on Mathlib's Cauchy power-series expansion and locally
uniform convergence of power-series partial sums, as cited below. The explicit polynomial
construction is shared with `ToMathlib.Analysis.Analytic.PolynomialApproximation`.

The general explicit polynomial partial sums are provided by
`ToMathlib.Analysis.Analytic.PolynomialApproximation`. This module applies them
to holomorphic functions on disks and entire functions on the plane.

## Main results

* `HasFPowerSeriesOnBall.exists_polynomial_tendstoLocallyUniformlyOn`:
  polynomial approximation on a power series's disk of convergence.
* `Complex.exists_polynomial_tendstoLocallyUniformlyOn_on_ball`: approximation
  inside a disk for functions holomorphic on the disk.
* `Complex.exists_polynomial_tendstoLocallyUniformlyOn`: locally uniform polynomial
  approximation of an entire function.

## References

* `Mathlib.Analysis.Complex.CauchyIntegral`: the power-series expansion of an entire function.
* `Mathlib.Analysis.Analytic.Basic`: local uniform convergence of power-series partial sums.
-/

public noncomputable section
namespace Complex
open Polynomial Set Filter
open scoped Topology NNReal ENNReal

/-- Every entire complex function is the locally uniform limit of a sequence
of complex polynomials. -/
theorem exists_polynomial_tendstoLocallyUniformlyOn {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    ∃ p : ℕ → ℂ[X], TendstoLocallyUniformlyOn (fun N z => (p N).eval z) f atTop univ := by
  simpa only [Metric.eball_top] using
    (hf.hasFPowerSeriesOnBall 0 (R := 1) zero_lt_one).exists_polynomial_tendstoLocallyUniformlyOn

/-- A function holomorphic on an open complex disk is the locally uniform limit of polynomials. -/
theorem exists_polynomial_tendstoLocallyUniformlyOn_on_ball {f : ℂ → ℂ}
    {c : ℂ} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball c ρ)) :
    ∃ p : ℕ → ℂ[X], TendstoLocallyUniformlyOn (fun N z => (p N).eval z) f atTop
      (Metric.ball c ρ) := by
  have hsmall (r : ℝ≥0) (hr : 0 < r) (hrρ : r < ρ) :=
    (hf.mono (Metric.closedBall_subset_ball (show (r : ℝ) < ρ from hrρ))).hasFPowerSeriesOnBall hr
  have h := hsmall (ρ / 2) (by positivity) (by exact div_lt_self hρ (by norm_num))
  have H : HasFPowerSeriesOnBall f (cauchyPowerSeries f c (ρ / 2)) c ρ :=
    { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr hrρ =>
        (h.exchange_radius (hsmall r hr (ENNReal.coe_lt_coe.mp hrρ))).r_le
      r_pos := ENNReal.coe_pos.mpr hρ
      hasSum := fun {y} hy => by
        have hyρ : ‖y‖₊ < ρ := ENNReal.coe_lt_coe.mp (mem_eball_zero_iff.mp hy)
        obtain ⟨r, hyr, hrρ⟩ := exists_between hyρ
        exact (h.exchange_radius (hsmall r (lt_of_le_of_lt bot_le hyr) hrρ)).hasSum
          (mem_eball_zero_iff.mpr (ENNReal.coe_lt_coe.mpr hyr)) }
  simpa only [Metric.eball_coe] using H.exists_polynomial_tendstoLocallyUniformlyOn

end Complex
