/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial partial sums of scalar power series

The partial sums of a formal multilinear series over a normed field are ordinary
polynomials after translation to the expansion center. A convergent expansion is
approximated locally uniformly by these explicit polynomials.
-/

public noncomputable section
open Polynomial Filter
open scoped ENNReal

namespace FormalMultilinearSeries
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The polynomial given by the first `N` terms of a scalar power series centered at `c`. -/
@[expose] def partialSumPolynomial (a : FormalMultilinearSeries 𝕜 𝕜 𝕜) (c : 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ n ∈ Finset.range N, C (a n (fun _ ↦ 1)) * (X - C c) ^ n

/-- Evaluation of the polynomial partial sum agrees with the translated series partial sum. -/
@[simp] theorem eval_partialSumPolynomial (a : FormalMultilinearSeries 𝕜 𝕜 𝕜)
    (c : 𝕜) (N : ℕ) (z : 𝕜) :
    (a.partialSumPolynomial c N).eval z = a.partialSum N (z - c) := by
  simp only [partialSumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X,
    partialSum]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin, mul_comm] using
    ((a n).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm

end FormalMultilinearSeries

/-- The explicit polynomial partial sums converge locally uniformly on the expansion ball. -/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn_partialSumPolynomial
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {a : FormalMultilinearSeries 𝕜 𝕜 𝕜} {c : 𝕜} {ρ : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f a c ρ) :
    TendstoLocallyUniformlyOn (fun N z ↦ (a.partialSumPolynomial c N).eval z) f atTop
      (Metric.eball c ρ) := by
  simpa only [FormalMultilinearSeries.eval_partialSumPolynomial] using hf.tendstoLocallyUniformlyOn'

/-- A power-series expansion is the locally uniform limit of ordinary polynomials
on its open ball of convergence. -/
theorem HasFPowerSeriesOnBall.exists_polynomial_tendstoLocallyUniformlyOn
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {a : FormalMultilinearSeries 𝕜 𝕜 𝕜} {c : 𝕜} {ρ : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f a c ρ) :
    ∃ p : ℕ → 𝕜[X], TendstoLocallyUniformlyOn (fun N z ↦ (p N).eval z) f atTop
      (Metric.eball c ρ) :=
  ⟨a.partialSumPolynomial c, hf.tendstoLocallyUniformlyOn_partialSumPolynomial⟩
