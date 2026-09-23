/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import Carlson.R.Relations

/-!
# Associated R-relations on the full slit domain

The parameter-raising, parameter-lowering and tangential relations among associated
R-functions (Carlson's Section 5.9 and 6.8), extended from the native domain to all complex
Dirichlet parameters and all nodes in the product slit plane. The relations are stated without
dividing by the exponent or the total parameter, so they remain valid at the exceptional values.

## Main results

* `Carlson.regCarlsonR_eq_addDirichletUnit`: parameter raising.
* `Carlson.regCarlsonR_sub_dirichletUnit`: parameter lowering.
* `Carlson.regCarlsonR_tangent_sub`, `Carlson.regCarlsonR_tangent`: the tangential
  relations.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Parameter lowering without dividing by the total parameter minus one. -/
theorem regCarlsonR_sub_dirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonR t (b - Pi.single i 1) z =
      ((∑ j, b j) + t - 1) * regCarlsonR t b z -
        t * z i * regCarlsonR (t - 1) b z := by
  have hunit : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [addDirichletUnit]
    · simp [addDirichletUnit, hji]
  have hsum : (∑ j, ((b - Pi.single i (1 : ℂ)) : ι → ℂ) j) = (∑ j, b j) - 1 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib]
  have h := regCarlsonR_eq_addDirichletUnit t (b - Pi.single i 1) hz i
  rw [hunit, hsum] at h
  convert h using 1
  ring

open scoped Classical in
/-- The backward-shift tangential relation, including equal indices and coincident nodes. -/
theorem regCarlsonR_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonR (t - 1) b z) =
      regCarlsonR t (b - Pi.single j 1) z -
        regCarlsonR t (b - Pi.single i 1) z := by
  rw [regCarlsonR_sub_dirichletUnit t b hz j,
    regCarlsonR_sub_dirichletUnit t b hz i]
  ring

/-- The parameter-raised tangential relation on the full slit domain. -/
theorem regCarlsonR_tangent (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t *
      regCarlsonR (t - 1) (addDirichletUnit (addDirichletUnit b j) i) z) =
      regCarlsonR t (addDirichletUnit b i) z -
        regCarlsonR t (addDirichletUnit b j) z := by
  classical
  by_cases hij : i = j
  · subst j; simp
  have h₁ : addDirichletUnit (addDirichletUnit b j) i - Pi.single j 1 =
      addDirichletUnit b i := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit]
  have h₂ : addDirichletUnit (addDirichletUnit b j) i - Pi.single i 1 =
      addDirichletUnit b j := by
    ext k
    by_cases hki : k = i <;> simp_all [addDirichletUnit]
  simpa only [h₁, h₂] using
    regCarlsonR_tangent_sub t (addDirichletUnit (addDirichletUnit b j) i) hz i j

end Carlson
