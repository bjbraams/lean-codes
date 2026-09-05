/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.Dirichlet
import StdSimplexMeasure.MvBeta

/-!
# Regularized complex Dirichlet integrals on the standard simplex

This file defines regularized complex Dirichlet densities and their associated integral
functionals. These are complex-valued densities, not measures in the sense of Mathlib's
nonnegative `Measure` type.

## Main definitions and results

* `Complex.mvBeta_eq_integral`: the simplex integral representation of the multivariate Beta
  function.
* `regDirichletDensity`: the pointwise entire regularized Dirichlet density.
* `complexDirichletDensity`: the corresponding normalized complex density.
* `regDirichletIntegral`: integration against the regularized density.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex Fintype MeasureTheory MeasureTheory.Measure

public noncomputable section ComplexDirichlet

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The absolutely convergent simplex integral representation of the multivariate Beta
function. -/
theorem mvBeta_eq_integral {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = ∫ u in stdSimplex ℝ ι, ∏ i, (u i : ℂ) ^ (b i - 1) ∂stdSimplexMeasure := by
  sorry

end Complex

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The regularized Dirichlet density with parameters `b` on `stdSimplexInterior`. For each
fixed `u`, this is an entire function of `b`. -/
def regDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  stdSimplexInterior.indicator (fun u ↦ ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The normalized complex Dirichlet density with parameters `b` on
`stdSimplexInterior`. -/
def complexDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  Gamma (∑ i, b i) * regDirichletDensity b u

/-- Simultaneously permuting the parameters and coordinates leaves the regularized Dirichlet
density unchanged. -/
theorem regDirichletDensity_perm (b : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    regDirichletDensity (b ∘ σ) (u ∘ σ) = regDirichletDensity b u := by
  unfold regDirichletDensity
  have hinter : (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
    have hsimp : (u ∘ σ) ∈ stdSimplex ℝ ι ↔ u ∈ stdSimplex ℝ ι := by
      change u ∈ (fun v ↦ v ∘ σ) ⁻¹' stdSimplex ℝ ι ↔ _
      rw [preimage_stdSimplex_perm]
    simp only [stdSimplexInterior]
    constructor
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mp hu,
        fun i ↦ by simpa using hp (σ.symm i)⟩
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mpr hu, fun i ↦ hp (σ i)⟩
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ
        (fun i ↦ (u i : ℂ) ^ (b i - 1) / Gamma (b i)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- The regularized Dirichlet density is a measurable function. -/
theorem measurable_regDirichletDensity (b : ι → ℂ) :
    Measurable (regDirichletDensity b) := by
  unfold regDirichletDensity
  apply Measurable.indicator _ measurableSet_stdSimplexInterior
  fun_prop

/-- The regularized Dirichlet density integrated over the standard simplex. -/
theorem regDirichletIntegral_normalization (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    ∫ u in stdSimplex ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure =
    1 / Gamma (∑ i, b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [regDirichletDensity, stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      have hbpos (i : ι) : 0 < (b i).re := by
        simpa [mvBetaConvergent] using hb i
      have hgamma (i : ι) : Gamma (b i) ≠ 0 := Gamma_ne_zero_of_re_pos (hbpos i)
      have hprod_gamma : (∏ i, Gamma (b i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hgamma i)
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hfun :
          regDirichletDensity b =ᵐ[stdSimplexMeasure.restrict (stdSimplex ℝ ι)]
            fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) / ∏ i, Gamma (b i) := by
        have hmem := self_mem_ae_restrict
          (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
        filter_upwards [hmem, hae] with u hu hupos
        rw [regDirichletDensity, Set.indicator_of_mem]
        · rw [Finset.prod_div_distrib]
        · exact ⟨hu, hupos⟩
      rw [integral_congr_ae hfun, integral_div, ← mvBeta_eq_integral hb]
      rw [mvBeta_eq_prod_Gamma_div]
      field_simp

/-- Continuous functions are integrable over the standard simplex with respect to the
regularized Dirichlet density. -/
theorem integrableOn_regDirichletDensity_mul
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn
      (fun u => regDirichletDensity b u * f u)
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  sorry

/-- Integration of function `f` over the standard simplex with respect to the regularized
Dirichlet density. -/
def regDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in stdSimplex ℝ ι, regDirichletDensity b u * f u
    ∂stdSimplexMeasure

/-- `regDirichletIntegral` is additive. -/
theorem regDirichletIntegral_add (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hg : ContinuousOn g (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => f u + g u) =
    regDirichletIntegral b f + regDirichletIntegral b g := by
  unfold regDirichletIntegral
  rw [← integral_add
    (integrableOn_regDirichletDensity_mul b hb hf)
    (integrableOn_regDirichletDensity_mul b hb hg)]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- `regDirichletIntegral` commutes with complex scalar multiplication. -/
theorem regDirichletIntegral_smul (b : ι → ℂ) {f : (ι → ℝ) → ℂ} (c : ℂ)
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => c * f u) =
    c * regDirichletIntegral b f := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- The integral of `f` depends only on the values of `f` on the standard Simplex. -/
theorem regDirichletIntegral_congr
    (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    regDirichletIntegral b f =
      regDirichletIntegral b g := by
  unfold regDirichletIntegral
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [hfg hu]

/-- If `f` is continuous on the closed standard simplex, then
`b ↦ regDirichletIntegral b f` is analytic on the domain of absolute convergence. -/
theorem regDirichletIntegral_analyticOn {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    AnalyticOn ℂ (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  sorry

end ProbabilityTheory

end ComplexDirichlet
