/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonR.Basic
import StdSimplexMeasure.CarlsonS
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Laplace representation of Carlson's R-function

This file develops the inverse confluence formula of [Carl77, Theorem 5.10-2], which expresses
`R` as a one-dimensional Laplace--Mellin transform of `S`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.10,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical
public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The regularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def regCarlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- The unregularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def carlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * carlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- Regularization in the Dirichlet parameters commutes with Carlson's one-dimensional
Laplace--Mellin construction. -/
theorem carlsonRLaplaceIntegral_eq_Gamma_mul_reg (a : ℂ) (b z : ι → ℂ) :
    carlsonRLaplaceIntegral a b z =
      Gamma (∑ i, b i) * regCarlsonRLaplaceIntegral a b z := by
  simp only [carlsonRLaplaceIntegral, regCarlsonRLaplaceIntegral, carlsonSIntegral]
  calc
    1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) *
          (Gamma (∑ i, b i) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
      1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        Gamma (∑ i, b i) *
          ((y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
        congr 2
        funext y
        ring
    _ = 1 / Gamma a * (Gamma (∑ i, b i) * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          rw [integral_const_mul]
    _ = Gamma (∑ i, b i) * (1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          ring

/-- The scalar Gamma integral underlying Carlson's inverse confluence formula, for a positive
real decay rate. -/
theorem integral_carlsonLaplaceKernel_ofReal {a : ℂ} {r : ℝ}
    (ha : 0 < a.re) (hr : 0 < r) :
    ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(r * y)) =
      (1 / r : ℂ) ^ a * Gamma a :=
  integral_cpow_mul_exp_neg_mul_Ioi ha hr

/-- The complex-rate Gamma integral needed in Carlson's inverse confluence theorem. -/
theorem integral_carlsonLaplaceKernel {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w) =
      w ^ (-a) * Gamma a := by
  sorry

/-- Carlson's inverse confluence formula, Theorem 5.10-2, in regularized form. -/
theorem regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (-a) b z = regCarlsonRLaplaceIntegral a b z := by
  sorry

/-- Carlson's inverse confluence formula in the native unregularized normalization. -/
theorem carlsonRIntegral_eq_carlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRIntegral (-a) b z = carlsonRLaplaceIntegral a b z := by
  rw [carlsonRIntegral_eq_Gamma_mul_reg,
    carlsonRLaplaceIntegral_eq_Gamma_mul_reg,
    regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral ha hb hz]

end DirichletTransform
end CarlsonR
