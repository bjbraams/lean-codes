/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonR.SlitPlane
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Single-integral representations of Carlson's R-function

This file is the home for Carlson's Theorem 6.8-1.  The unit-interval and positive-ray
forms below are branch-safe because every Carlson variable is required to lie in the open
right half-plane.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonR

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The beta-weighted unit-interval integral in Carlson's single-integral representation. -/
def carlsonRUnitIntervalIntegral (a a' : ℂ) (b z : ι → ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioo 0 1,
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
      ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)

/-- Carlson's Theorem 6.8-1 in unit-interval form.  The homogeneity relation
`a + a' = ∑ i, b i` supplies the exponent at the endpoint `u = 1`. -/
theorem carlsonRUnitIntervalIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  /- This is the missing analytic content of Carlson's Section 6.8.  It can be proved by
  decomposing a product of Gamma integrals into radial and simplex coordinates, or from the
  Laplace representation in `CarlsonR.Laplace` followed by the beta substitution. -/
  sorry

/-- The positive-ray form of Carlson's single-integral representation. -/
def carlsonRPositiveRayIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,
    (s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i)

/-- Carlson's Theorem 6.8-1 in positive-ray form. -/
theorem carlsonRPositiveRayIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z =
      betaIntegral a a' * carlsonRIntegral (-a') b z := by
  /- This is equivalent to `carlsonRUnitIntervalIntegral_eq` under
  `s = u / (1 - u)`.  Its proof needs the corresponding improper-integral change-of-variables
  lemma with the endpoint integrability supplied by `ha` and `ha'`. -/
  sorry

end DirichletTransform

end CarlsonR
