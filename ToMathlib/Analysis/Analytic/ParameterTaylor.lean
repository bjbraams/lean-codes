/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Taylor coefficients of holomorphic parameter families

A joint holomorphic family has holomorphic scalar Taylor coefficients. A local
power-series identity suffices to identify these coefficients; no uniform
summability in the auxiliary parameters is assumed. The proofs use Mathlib's
analytic Fréchet derivative and uniqueness of formal power series.
-/

open Complex Set Filter
open scoped Topology NNReal ENNReal
@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Repeated differentiation in the scalar coordinate of a parameter family. -/
def scalarParamDeriv : ℕ → (E × ℂ → ℂ) → E × ℂ → ℂ
  | 0, F => F
  | n + 1, F => fun p => fderiv ℂ (scalarParamDeriv n F) p (0, 1)

/-- Repeated scalar-coordinate differentiation preserves joint holomorphy. -/
theorem AnalyticOnNhd.scalarParamDeriv {U : Set (E × ℂ)} {F : E × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (n : ℕ) :
    AnalyticOnNhd ℂ (scalarParamDeriv n F) U := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).comp_analyticOnNhd ih.fderiv

/-- Scalar-coordinate derivatives agree with the derivatives of each scalar slice. -/
theorem scalarParamDeriv_eq_iteratedDeriv {U : Set (E × ℂ)} (hU : IsOpen U)
    {F : E × ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (n : ℕ) {p : E × ℂ} (hp : p ∈ U) :
    scalarParamDeriv n F p = iteratedDeriv n (fun w => F (p.1, w)) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have he : (fun w => scalarParamDeriv n F (p.1, w)) =ᶠ[𝓝 p.2]
        iteratedDeriv n (fun w => F (p.1, w)) := by
      filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually
        (hU.mem_nhds hp)] with w hw
      exact ih hw
    have hd := (((hF.scalarParamDeriv n) p hp).differentiableAt.hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) p.1 p.2)).hasDerivAt
    rw [scalarParamDeriv, iteratedDeriv_succ, ← he.deriv_eq]
    exact hd.deriv.symm

/-- Taylor coefficients are holomorphic in the auxiliary parameters. -/
theorem analyticOnNhd_iteratedDeriv_parameter {R : ℝ} (hR : 0 < R)
    {F : E × ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (univ ×ˢ Metric.ball 0 R)) (n : ℕ) :
    AnalyticOnNhd ℂ (fun p => iteratedDeriv n (fun w => F (p, w)) 0) univ := by
  have hD : AnalyticOnNhd ℂ (fun p => scalarParamDeriv n F (p, 0)) univ :=
    (hF.scalarParamDeriv n).comp (analyticOnNhd_id.prod analyticOnNhd_const)
      (fun _ _ => ⟨mem_univ _, by simpa using hR⟩)
  apply hD.congr isOpen_univ
  intro p _
  exact scalarParamDeriv_eq_iteratedDeriv (isOpen_univ.prod Metric.isOpen_ball) hF n
    ⟨mem_univ _, by simpa using hR⟩

/-- A power-series identity on a scalar disk determines every Taylor coefficient. -/
theorem taylorCoeff_eq_of_hasSum {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} {a : ℕ → ℂ}
    (ha : ∀ w : ℂ, ‖w‖ < R → HasSum (fun n => a n * w ^ n) (f w)) (n : ℕ) :
    iteratedDeriv n f 0 / (n.factorial : ℂ) = a n := by
  obtain ⟨r, hr, hrR⟩ := exists_between hR
  let r' : ℝ≥0 := ⟨r, hr.le⟩
  have hs := (ha (r : ℂ) (by simpa [abs_of_pos hr] using hrR)).summable.norm
  have hrad : (r' : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    change Summable (fun n => ‖FormalMultilinearSeries.ofScalars ℂ a n‖ * r ^ n)
    simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      norm_real, Real.norm_eq_abs, abs_of_pos hr, r'] using hs
  have hpower : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 r' := by
    refine ⟨hrad, by exact_mod_cast hr, ?_⟩
    intro w hw
    have hw' : ‖w‖ < r := by
      rw [Metric.eball_coe] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact hw
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      ha w (hw'.trans hrR)
  have he := hpower.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries
    hpower.hasFPowerSeriesAt
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hn
