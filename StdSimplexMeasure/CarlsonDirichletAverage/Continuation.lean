/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.DirichletTransform
import StdSimplexMeasure.CarlsonDirichletAverage.Deriv
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic continuation of Carlson's Dirichlet averages

This file develops Carlson's regularized Dirichlet average as an entire function of the
Dirichlet parameters.  It contains the abstract continuation predicate, the polynomial
construction, and the initial definitions for Carlson's Taylor-series and resolvent methods.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Chapter 6,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A function of `b` is a regularized Carlson continuation for `f` and `z` if it is entire
and agrees with the native regularized Dirichlet integral on its domain of absolute
convergence. -/
def IsRegCarlsonContinuation (f : ℂ → ℂ) (z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) : Prop :=
  AnalyticOnNhd ℂ G Set.univ ∧
    Set.EqOn G (fun b ↦ regCarlsonDirichletAverage b z f) mvBetaConvergent

/-- Construct a regularized Carlson continuation from entire dependence on `b` and agreement
with the native integral on the convergence region. -/
theorem IsRegCarlsonContinuation.mk' {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hEq : Set.EqOn G (fun b ↦ regCarlsonDirichletAverage b z f) mvBetaConvergent) :
    IsRegCarlsonContinuation f z G :=
  ⟨hG, hEq⟩

/-- A regularized Carlson continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonContinuation.analyticOnNhd {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G) :
    AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson continuation agrees with the native integral wherever that integral
is absolutely convergent. -/
theorem IsRegCarlsonContinuation.eq_native {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonDirichletAverage b z f :=
  hG.2 hb

/-- The ordinary convergence region for the Dirichlet parameters is open. -/
theorem isOpen_mvBetaConvergent : IsOpen (mvBetaConvergent : Set (ι → ℂ)) := by
  rw [show (mvBetaConvergent : Set (ι → ℂ)) =
      ⋂ i, {b : ι → ℂ | 0 < (b i).re} by
    ext b
    simp [mvBetaConvergent]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_apply i))

/-- Two entire functions of the Dirichlet parameters that agree throughout the ordinary
convergence region agree everywhere.  This is the common continuation step for the identities
proved from Carlson's native integral. -/
theorem analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    {G H : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hEq : Set.EqOn G H mvBetaConvergent) :
    G = H := by
  let b₀ : ι → ℂ := fun _ ↦ 1
  have hb₀ : b₀ ∈ mvBetaConvergent := by
    intro i
    simp [b₀]
  apply hG.eq_of_eventuallyEq hH (z₀ := b₀)
  filter_upwards [isOpen_mvBetaConvergent.eventually_mem hb₀] with b hb
  exact hEq hb

/-- The entire regularized Carlson continuation, if it exists, is unique. -/
theorem IsRegCarlsonContinuation.eq {f : ℂ → ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hH : IsRegCarlsonContinuation f z H) : G = H := by
  apply analyticOnNhd_eq_of_eqOn_mvBetaConvergent hG.1 hH.1
  intro b hb
  exact (hG.2 hb).trans (hH.2 hb).symm

/-- The entire regularized Carlson average of a nonnegative integral power. -/
def regCarlsonR (n : ℕ) (z b : ι → ℂ) : ℂ :=
  regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b

/-- On the ordinary convergence region, `regCarlsonR` agrees with the defining simplex
integral of the corresponding power. -/
theorem regCarlsonDirichletAverage_pow (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b z (fun w ↦ w ^ n) = regCarlsonR n z b := by
  unfold regCarlsonDirichletAverage regCarlsonR
  rw [← regDirichletIntegral_mvPolynomial b hb (carlsonPowerPolynomial n z)]
  congr 1
  funext u
  exact (eval_carlsonPowerPolynomial n z u).symm

/-- For fixed `n` and `z`, the regularized Carlson power average is entire in `b`. -/
theorem differentiable_regCarlsonR (n : ℕ) (z : ι → ℂ) :
    Differentiable ℂ (regCarlsonR n z) := by
  exact differentiable_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

/-- The native regularized average of Carlson's integer resolvent.  Its continuation in `b`
is the kernel used in Carlson's Cauchy-integral argument. -/
def regCarlsonResolvent (n : ℕ) (b z : ι → ℂ) (s : ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (fun w ↦ (s - w) ^ (-(n + 1 : ℤ)))

/-- The formal Taylor-series candidate for Carlson's regularized Dirichlet average. -/
def regCarlsonTaylorSeries (A : ℂ) (a : ℕ → ℂ) (z b : ι → ℂ) : ℂ :=
  ∑' n, a n * regCarlsonR n (fun i ↦ z i - A) b

/-- Each term of Carlson's Taylor-series construction is entire in the Dirichlet parameters. -/
theorem differentiable_regCarlsonTaylorTerm (A : ℂ) (a : ℕ → ℂ) (z : ι → ℂ) (n : ℕ) :
    Differentiable ℂ
      (fun b ↦ a n * regCarlsonR n (fun i ↦ z i - A) b) := by
  exact (differentiable_const (c := a n)).mul
    (differentiable_regCarlsonR n fun i ↦ z i - A)

/-- Every finite partial sum in Carlson's Taylor-series construction is entire in the
Dirichlet parameters. -/
theorem differentiable_regCarlsonTaylorPartialSum
    (A : ℂ) (a : ℕ → ℂ) (z : ι → ℂ) (N : ℕ) :
    Differentiable ℂ
      (fun b ↦ ∑ n ∈ Finset.range N, a n * regCarlsonR n (fun i ↦ z i - A) b) := by
  rw [show (fun b ↦ ∑ n ∈ Finset.range N,
      a n * regCarlsonR n (fun i ↦ z i - A) b) =
      ∑ n ∈ Finset.range N,
        (fun b ↦ a n * regCarlsonR n (fun i ↦ z i - A) b) by
    funext b
    simp]
  exact Differentiable.sum fun n _ ↦ differentiable_regCarlsonTaylorTerm A a z n

end DirichletTransform

end CarlsonDirichletAverage
