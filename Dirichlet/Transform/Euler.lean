/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Joint
public import StdSimplexMeasure.Integral.Interval

/-!
# Entire continuation of weighted Euler integrals

Regularization by both endpoint Gamma factors identifies a weighted Euler integral
with a two-coordinate Dirichlet transform. A kernel holomorphic near the closed interval
therefore gives a continuation entire in both endpoint exponents and jointly holomorphic
in its auxiliary parameters. This also permits analytic substitutions in the exponents.
-/

open Complex MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Dirichlet

/-- The native Euler integral, regularized by its two endpoint Gamma factors.
Outside its convergence region this definition is only a totalized integral. -/
def regEulerIntegral (a b : ℂ) (f : ℝ → ℂ) : ℂ :=
  (Gamma a * Gamma b)⁻¹ *
    ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (b - 1) * f u

/-- Positive endpoint exponents make a continuous weighted Euler kernel integrable. -/
theorem integrableOn_eulerKernel_mul {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (b - 1) * f u)
      (Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    ((betaIntegral_convergent ha hb).mul_continuousOn (by
      simpa only [uIcc_of_le zero_le_one] using hf))

/-- A two-coordinate regularized Dirichlet integral is a regularized Euler integral. -/
theorem regDirichletIntegral_fin_two (a b : ℂ) (f : ℝ → ℂ) :
    regDirichletIntegral ![a, b] (fun u => f (u 0)) = regEulerIntegral a b f := by
  rw [regDirichletIntegral, integral_stdSimplex_fin_two, integral_Icc_eq_integral_Ioo,
    regEulerIntegral, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  change regDirichletDensity ![a, b] ![u, 1 - u] * f u = _
  rw [regDirichletDensity, indicator_of_mem ((mem_stdSimplexInterior_fin_two u).mpr hu)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_sub, Complex.ofReal_one]
  ring

variable {κ : Type*} [Fintype κ]

/-- A holomorphic interval kernel has a joint continuation entire in both endpoint exponents.
The open complex neighborhood may depend on the auxiliary parameter. -/
theorem exists_joint_regEulerContinuation
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × ℂ)} (hW : IsOpen W)
    {H : ((κ → ℂ) × ℂ) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hWU : ∀ p ∈ U, ∀ u ∈ Icc (0 : ℝ) 1, (p, (u : ℂ)) ∈ W) :
    ∃ F : ((Fin 2 → ℂ) × (κ → ℂ)) → ℂ,
      AnalyticOnNhd ℂ F (univ ×ˢ U) ∧
      ∀ p ∈ U, ∀ a b : ℂ, 0 < a.re → 0 < b.re →
        F (![a, b], p) = regEulerIntegral a b (fun u => H (p, (u : ℂ))) := by
  let e : ((κ → ℂ) × (Fin 2 → ℂ)) → (κ → ℂ) × ℂ := fun p => (p.1, p.2 0)
  have he : AnalyticOnNhd ℂ e univ := by
    intro p _
    exact analyticAt_fst.prod
      (((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt p.2).comp analyticAt_snd)
  obtain ⟨F, hF⟩ := exists_isJointRegDirichletContinuation hU
    (hW.preimage (continuousOn_univ.mp he.continuousOn))
    (hH.comp (he.mono (subset_univ _)) (fun _ hp => hp)) (fun p hp u hu =>
      hWU p hp (u 0) (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu 0))
  refine ⟨F, hF.1, ?_⟩
  intro p hp a b ha hb
  rw [(hF.2 p hp).eq_native (by intro i; fin_cases i <;> assumption)]
  exact regDirichletIntegral_fin_two a b (fun u => H (p, (u : ℂ)))

/-- Analytic substitution in the endpoint exponents preserves the continued Euler integral.
Native agreement is asserted wherever both substituted exponents have positive real part. -/
theorem exists_analyticOnNhd_regEulerIntegral
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × ℂ)} (hW : IsOpen W)
    {H : ((κ → ℂ) × ℂ) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hWU : ∀ p ∈ U, ∀ u ∈ Icc (0 : ℝ) 1, (p, (u : ℂ)) ∈ W)
    {a b : (κ → ℂ) → ℂ} (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U) :
    ∃ F : (κ → ℂ) → ℂ, AnalyticOnNhd ℂ F U ∧
      ∀ p ∈ U, 0 < (a p).re → 0 < (b p).re →
        F p = regEulerIntegral (a p) (b p) (fun u => H (p, (u : ℂ))) := by
  obtain ⟨F, hF, heq⟩ := exists_joint_regEulerContinuation hU hW hH hWU
  refine ⟨fun p => F (![a p, b p], p), ?_, fun p hp => heq p hp (a p) (b p)⟩
  intro p hp
  apply (hF _ ⟨mem_univ _, hp⟩).comp
  refine AnalyticAt.prod ?_ analyticAt_id
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ha p hp
  · exact hb p hp

end Dirichlet
