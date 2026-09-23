/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitDeriv

/-!
# The R Euler–Poisson system on the full slit domain

Carlson's Euler–Poisson differential equations (6.4-2) for the R-function, in the form
`carlsonEulerPoissonOperator i j b z (regCarlsonR t b) = 0`, for every complex exponent,
every complex Dirichlet parameter vector and every node vector in the product slit plane.

## Main results

* `Carlson.carlsonEulerPoissonOperator_regCarlsonR`: the system for the regularized function.
* `Carlson.carlsonEulerPoissonOperator_carlsonR`: the system for the ordinary normalization.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The Euler–Poisson system for R, for all complex parameters and slit-plane nodes.
Neither distinct indices nor separated nodes are required. -/
theorem carlsonEulerPoissonOperator_regCarlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (regCarlsonR t b) = 0 := by
  by_cases hij : i = j
  · subst j; exact carlsonEulerPoissonOperator_self i b z _
  unfold carlsonEulerPoissonOperator
  rw [carlsonPartialDeriv_carlsonPartialDeriv_regCarlsonR t b hz,
    carlsonPartialDeriv_regCarlsonR t b hz j,
    carlsonPartialDeriv_regCarlsonR t b hz i]
  rw [show addDirichletUnit b j i = b i by simp [addDirichletUnit, hij]]
  have h := regCarlsonR_tangent (t - 1) b hz i j
  rw [show t - 1 - 1 = t - 2 by ring] at h
  linear_combination t * b i * b j * h

/-- The ordinary normalization obeys the same Euler–Poisson system. At Gamma
poles this is an identity of totalized expressions, not a finite ordinary value. -/
theorem carlsonEulerPoissonOperator_carlsonR (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (carlsonR t b) = 0 := by
  change carlsonEulerPoissonOperator i j b z
    (fun w => Gamma (∑ k, b k) * regCarlsonR t b w) = 0
  rw [carlsonEulerPoissonOperator_const_mul,
    carlsonEulerPoissonOperator_regCarlsonR t b hz i j, mul_zero]

end Carlson
