/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-- For each simplex point, the exponential Carlson kernel is entire in all `z` variables. -/
theorem analyticOnNhd_exp_carlsonAffineForm (u : ι → ℝ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ ↦ exp (carlsonAffineForm z u)) Set.univ := by
  intro z _
  apply analyticAt_cexp.comp
  unfold carlsonAffineForm
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)

/-- Varying coordinate `i` of `z`, the derivative of the exponential Carlson kernel is the
kernel multiplied by the simplex coordinate `u i`. -/
theorem hasDerivAt_exp_carlsonAffineForm_update
    (z : ι → ℂ) (u : ι → ℝ) (i : ι) :
    HasDerivAt (fun w ↦ exp (carlsonAffineForm (Function.update z i w) u))
      ((u i : ℂ) * exp (carlsonAffineForm z u)) (z i) := by
  exact HasDerivAt.comp_carlsonAffineForm_update i
    (Complex.hasDerivAt_exp (carlsonAffineForm z u))

/-- Every iterated complex derivative of the exponential function is the exponential function
itself. -/
theorem iteratedDeriv_cexp_eq (n : ℕ) :
    iteratedDeriv n exp = exp := by
  simpa using iteratedDeriv_cexp_const_mul n 1

/-- Carlson's Theorem 5.8-2 in regularized integral form: replacing the averaged exponential
by any of its iterated derivatives does not change the `S` integral.  Carlson denotes the
left-hand side by `S⁽ⁿ⁾` and writes `S⁽ⁿ⁾ = S`. -/
theorem regCarlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      regCarlsonSIntegral b z := by
  rw [iteratedDeriv_cexp_eq]
  rfl

/-- Carlson's native, unregularized `S` integral.  Its intended integral interpretation
requires `b ∈ Complex.mvBetaConvergent`. -/
def carlsonSIntegral (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonSIntegral b z

/-- The unregularized and regularized native `S` integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonSIntegral_eq_Gamma_mul_reg (b z : ι → ℂ) :
    carlsonSIntegral b z = Gamma (∑ i, b i) * regCarlsonSIntegral b z := rfl

/-- Carlson's Theorem 5.8-2 for the unregularized native integral. -/
theorem carlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    Gamma (∑ i, b i) *
        regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      carlsonSIntegral b z := by
  rw [regCarlsonDirichletAverage_iteratedDeriv_exp]
  rfl

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

/-- Carlson's formula (6.3-5), exposing the regularized `S` candidate as the exponential
generating series of the regularized `R` polynomials. -/
theorem regCarlsonSSeries_eq_tsum_regCarlsonR (z b : ι → ℂ) :
    regCarlsonSSeries z b =
      ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b := by
  simp [regCarlsonSSeries, regCarlsonTaylorSeries]

/-- The `N`th partial sum in Carlson's exponential-series construction of the regularized
`S` function. -/
def regCarlsonSPartialSum (N : ℕ) (z b : ι → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b

/-- Every partial sum in Carlson's construction is entire in the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonSPartialSum (N : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonSPartialSum N z) Set.univ := by
  intro b _
  unfold regCarlsonSPartialSum
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul
    (analyticOnNhd_regCarlsonR n z b (Set.mem_univ b))

/-- Whenever Carlson's coefficient series is summable at `b`, its partial sums converge to
`regCarlsonSSeries z b`.  This separates the formal series construction from the estimates
needed to establish summability. -/
theorem tendsto_regCarlsonSPartialSum (z b : ι → ℂ)
    (h : Summable fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b) :
    Filter.Tendsto (fun N ↦ regCarlsonSPartialSum N z b) Filter.atTop
      (nhds (regCarlsonSSeries z b)) := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonR]
  exact h.hasSum.tendsto_sum_nat

/-- On the standard simplex, the norm of Carlson's affine form is bounded by the sum of the
norms of its variables.  This uniform bound is used to dominate the exponential series. -/
theorem norm_carlsonAffineForm_le_sum_norm (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
    ‖carlsonAffineForm z u‖ ≤ ∑ i, ‖z i‖ := by
  unfold carlsonAffineForm
  calc
    ‖∑ i, (u i : ℂ) * z i‖ ≤ ∑ i, ‖(u i : ℂ) * z i‖ := norm_sum_le _ _
    _ = ∑ i, u i * ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    _ ≤ ∑ i, ‖z i‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hui : u i ≤ 1 := by
        calc
          u i ≤ ∑ j, u j :=
            Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
          _ = 1 := hu.2
      exact mul_le_of_le_one_left (norm_nonneg _) hui

/-- The exponential series of the Carlson affine form converges pointwise to the exponential
kernel. -/
theorem hasSum_exp_carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) :
    HasSum (fun n : ℕ ↦ carlsonAffineForm z u ^ n / Nat.factorial n)
      (exp (carlsonAffineForm z u)) :=
  by
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (carlsonAffineForm z u))

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
`Complex.mvBetaConvergent`, and hence satisfies `IsRegCarlsonSContinuation z`.

The analytic development should also prove that `regCarlsonSIntegral b` and
`carlsonSIntegral b` are entire in `z` for `b ∈ Complex.mvBetaConvergent`, and that
`regCarlsonSSeries · b` is entire in `z` for every `b`.  The kernel theorem
`analyticOnNhd_exp_carlsonAffineForm` and its coordinate derivative formula above are the
pointwise inputs.  The integral result still needs a multivariate analytic-under-the-integral
argument; the series result needs locally uniform convergence on bounded subsets of the
`z`-space. -/

end DirichletTransform

end CarlsonS
