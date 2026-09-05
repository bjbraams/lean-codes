/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage

/-!
# Carlson's multivariate S-function

Carlson's `S(b,z)` is the Dirichlet average of the exponential function.  Section 5.8 of
[Carl77] defines it by an integral for Dirichlet parameters of positive real part.  Corollary
6.3-3 and formula (6.3-5) continue the regularized function `S(b,z) / Γ(∑ i, b i)` to all `b`.

This file separates the native integral from its continuation.  `regCarlsonSIntegral` and
`carlsonSIntegral` give the regularized and unregularized integral expressions.
`IsRegCarlsonSContinuation` specifies the global analytic object by entire dependence on `b`
and agreement with the native integral on `Complex.mvBetaConvergent`.

The series `regCarlsonSSeries` is the Taylor-series candidate corresponding to Carlson's
formula (6.3-5).  Establishing its convergence, analyticity, and agreement with the integral is
left to the subsequent analytic-continuation development; the definition itself makes none of
those claims.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, §§5.8 and 6.3,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonS

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The native regularized integral representing `S(b,z) / Γ(∑ i, b i)` when all Dirichlet
parameters have positive real part. -/
def regCarlsonSIntegral (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z exp

/-- Carlson's native, unregularized `S` integral.  Its intended integral interpretation
requires `b ∈ Complex.mvBetaConvergent`. -/
def carlsonSIntegral (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonSIntegral b z

/-- The unregularized and regularized native `S` integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonSIntegral_eq_Gamma_mul_reg (b z : ι → ℂ) :
    carlsonSIntegral b z = Gamma (∑ i, b i) * regCarlsonSIntegral b z := rfl

/-- A candidate is an entire regularized continuation of Carlson's `S` if it agrees with the
native regularized integral wherever all Dirichlet parameters have positive real part. -/
def IsRegCarlsonSContinuation (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation exp z G

/-- A regularized Carlson `S` continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonSContinuation.analyticOnNhd {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) : AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson `S` continuation agrees with the native integral on its ordinary
domain of absolute convergence. -/
theorem IsRegCarlsonSContinuation.eq_integral {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonSIntegral b z :=
  hG.2 hb

/-- An entire regularized continuation of Carlson's `S`, if it exists, is unique. -/
theorem IsRegCarlsonSContinuation.eq {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) (hH : IsRegCarlsonSContinuation z H) : G = H :=
  IsRegCarlsonContinuation.eq hG hH

/-- The series candidate for the entire regularized Carlson `S` function.  This is the
exponential specialization of Carlson's regularized Taylor construction. -/
def regCarlsonSSeries (z b : ι → ℂ) : ℂ :=
  regCarlsonTaylorSeries 0 (fun n ↦ (Nat.factorial n : ℂ)⁻¹) z b

/-- Simultaneous permutation of the Dirichlet parameters and variables leaves the native
regularized `S` integral unchanged. -/
theorem regCarlsonSIntegral_perm (b z : ι → ℂ) (σ : Equiv.Perm ι) :
    regCarlsonSIntegral (b ∘ σ) (z ∘ σ) = regCarlsonSIntegral b z :=
  regCarlsonDirichletAverage_perm b z exp σ

/-- Translating every variable by `a` multiplies the native regularized `S` integral by
`exp a`.  This is Carlson's exponential translation identity. -/
theorem regCarlsonSIntegral_add_const (b z : ι → ℂ) (a : ℂ) :
    regCarlsonSIntegral b (fun i ↦ z i + a) = exp a * regCarlsonSIntegral b z := by
  unfold regCarlsonSIntegral
  rw [show (fun i ↦ z i + a) = (fun i ↦ 1 * z i + a) by funext i; simp]
  rw [← regCarlsonDirichletAverage_comp_affine b z exp 1 a]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [one_mul, exp_add]
  ring

/-- At the zero variable vector, the native regularized `S` integral is the reciprocal Gamma
factor on the ordinary convergence domain. -/
theorem regCarlsonSIntegral_zero {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonSIntegral b (fun _ ↦ 0) = 1 / Gamma (∑ i, b i) := by
  simpa [regCarlsonSIntegral] using
    (regCarlsonDirichletAverage_const exp 0 hb)

/- TODO: Prove Carlson's Corollary 6.3-3 and formula (6.3-5): show that
`regCarlsonSSeries z` is entire in `b`, agrees with `regCarlsonSIntegral · z` on
`Complex.mvBetaConvergent`, and hence satisfies `IsRegCarlsonSContinuation z`. -/

end DirichletTransform

end CarlsonS
