/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Termwise beta integration

An absolutely summable family of continuous functions bounded by one can be integrated
termwise against a complex beta density with positive endpoint real parts.
The domination argument generalizes the one used for Carlson's single-integral series
in `Carlson.R.SingleIntegral.Series`, using Mathlib's dominated-convergence theorem.
The countable index type also permits double series.
-/

open Set MeasureTheory

public noncomputable section

namespace Complex

/-- Termwise integration against a complex beta kernel for an absolutely summable
countable family, with continuous factors of norm at most one. -/
theorem hasSum_integral_betaKernel_mul {ι : Type*} [Countable ι]
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {c : ι → ℂ} (hc : Summable c) {ψ : ι → ℝ → ℂ}
    (hψ : ∀ i, ContinuousOn (ψ i) (Icc 0 1))
    (hψnorm : ∀ i u, u ∈ Ioo 0 1 → ‖ψ i u‖ ≤ 1)
    {f : ℝ → ℂ} (hs : ∀ u ∈ Ioo 0 1, HasSum (fun i => c i * ψ i u) (f u)) :
    HasSum (fun i => ∫ u : ℝ in Ioo 0 1,
        (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) * (c i * ψ i u))
      (∫ u : ℝ in Ioo 0 1,
        (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) * f u) := by
  let K : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1)
  let B : ι → ℝ → ℝ := fun i u => ‖c i‖ * ‖K u‖
  have hK : IntegrableOn K (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent ha hb)
  have hi (i : ι) : IntegrableOn (fun u => K u * (c i * ψ i u)) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      ((betaIntegral_convergent ha hb).mul_continuousOn (by
        rw [uIcc_of_le zero_le_one]
        intro u hu
        exact (hψ i u hu).const_mul (c i)))
  have hBsum : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), Summable (fun i => B i u) := by
    filter_upwards with u
    exact hc.norm.mul_right _
  have hBint : Integrable (fun u => ∑' i, B i u) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    simp only [B, tsum_mul_right]
    exact hK.norm.const_mul _
  have hbound (i : ι) : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖K u * (c i * ψ i u)‖ ≤ B i u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    dsimp only [B]
    calc
      _ = ‖K u‖ * (‖c i‖ * ‖ψ i u‖) := by simp only [norm_mul]
      _ ≤ ‖K u‖ * (‖c i‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hψnorm i u hu) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      HasSum (fun i => K u * (c i * ψ i u)) (K u * f u) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (hs u hu).mul_left _
  exact hasSum_integral_of_dominated_convergence B (fun i => (hi i).aestronglyMeasurable)
    hbound hBsum hBint hlim

/-- Multiplying a beta kernel by integral powers shifts its two parameters. -/
theorem integral_betaKernel_mul_pow_mul_one_sub_pow (a b c : ℂ) (m n : ℕ) :
    (∫ u : ℝ in Ioo 0 1,
      (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
        (c * (u : ℂ) ^ m * (1 - (u : ℂ)) ^ n)) =
      c * betaIntegral (a + m) (b + n) := by
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  have hu1 : (1 - (u : ℂ)) ≠ 0 := by exact_mod_cast (sub_pos.mpr hu.2).ne'
  rw [show a + (m : ℂ) - 1 = (a - 1) + m by ring,
    show b + (n : ℂ) - 1 = (b - 1) + n by ring,
    cpow_add _ _ hu0, cpow_add _ _ hu1, cpow_natCast, cpow_natCast]
  ring

end Complex
