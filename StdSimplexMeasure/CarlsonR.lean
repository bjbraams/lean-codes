/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage

/-!
# Carlson's multivariate R-function

This file introduces Carlson's function `R_t(b, z)` in a form compatible with both its native
Dirichlet-integral definition and analytic continuation in the Dirichlet parameters.  Following
Carlson's Definition 5.9-1, `carlsonRIntegral` is the ordinary, unregularized Dirichlet average of
the complex power `w ↦ w ^ t`.  Its regularized form is `regCarlsonRIntegral`.

The integral is mathematically canonical on the domain `Complex.mvBetaConvergent`, subject also
to the branch and holomorphy conditions on the power function over the convex hull of `z`.
Outside that domain the Bochner integral remains a Lean term, but is not asserted to represent
Carlson's function.

For analytic continuation, `IsRegCarlsonRContinuation` records that an entire function of `b`
agrees with the regularized integral on its native domain.  Carlson's explicit representation in
Corollary 6.3-4 should eventually provide the principal construction satisfying this predicate.

The existing `regCarlsonR` is the already constructed special case for nonnegative integral
exponents.  The results below place it in the general continuation interface.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, §§5.9 and 6.3,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonR

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The native regularized integral representing `R_t(b,z) / Γ(∑ i, b i)` on the domain of
absolute convergence.  The complex power uses Mathlib's principal branch. -/
def regCarlsonRIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (fun w ↦ w ^ t)

/-- Carlson's native, unregularized `R_t` integral.  Its intended integral interpretation
requires `b ∈ Complex.mvBetaConvergent` and suitable branch conditions on `z`. -/
def carlsonRIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonRIntegral t b z

/-- The unregularized and regularized native integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonRIntegral_eq_Gamma_mul_reg (t : ℂ) (b z : ι → ℂ) :
    carlsonRIntegral t b z = Gamma (∑ i, b i) * regCarlsonRIntegral t b z := rfl

/-- A candidate is an entire regularized continuation of Carlson's `R_t` if it agrees with
the native regularized integral wherever all Dirichlet parameters have positive real part. -/
def IsRegCarlsonRContinuation (t : ℂ) (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation (fun w ↦ w ^ t) z G

/-- A regularized Carlson `R_t` continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonRContinuation.analyticOnNhd {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G) :
    AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson `R_t` continuation agrees with the native integral on the ordinary
domain of absolute convergence. -/
theorem IsRegCarlsonRContinuation.eq_integral {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonRIntegral t b z :=
  hG.2 hb

/-- An entire regularized continuation of Carlson's `R_t`, if it exists, is unique. -/
theorem IsRegCarlsonRContinuation.eq {t : ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonRContinuation t z G)
    (hH : IsRegCarlsonRContinuation t z H) : G = H :=
  IsRegCarlsonContinuation.eq hG hH

/-- For a natural exponent, the native general-power integral is the polynomial Carlson
average already represented by `regCarlsonR`. -/
theorem regCarlsonRIntegral_natCast (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonRIntegral (n : ℂ) b z = regCarlsonR n z b := by
  rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_pow n z hb]
  congr 2
  funext w
  exact cpow_natCast w n

/- TODO: Implement Carlson's Corollary 6.3-4 representation, including its branch and
convergence hypotheses, and prove that it satisfies `IsRegCarlsonRContinuation`.  That
construction should become the preferred concrete regularized `R_t` for general complex `t`. -/

end DirichletTransform

end CarlsonR
