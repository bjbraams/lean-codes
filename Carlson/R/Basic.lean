/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Carlson's R-function: basic definitions

The native integral definitions of Carlson's R-function with complex exponent `t`, Dirichlet
parameters `b` and nodes `z`, as the Dirichlet average of the power `w ↦ w ^ t`, and the
right-half-plane node domain on which the principal power is holomorphic along the whole
averaging kernel.

## Main definitions

* `Carlson.regCarlsonRIntegral`: the regularized native integral `R_t(b, z) / Γ(∑ i, b i)`.
* `Carlson.carlsonRIntegral`: the ordinary native integral `R_t(b, z)`.
* `Carlson.carlsonRVariableDomain`: node vectors with all coordinates in the right half-plane.

## Main results

* `Carlson.carlsonAffineForm_mem_slitPlane`: on that domain the affine kernel stays in the
  principal-branch slit plane.

The continuation of these integrals beyond the convergence region of the Dirichlet parameters
and beyond the right half-plane is developed in `Carlson.R.Continuation` and
`Carlson.R.SlitContinuation`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The native regularized integral representing `R_t(b,z) / Γ(∑ i, b i)`. -/
def regCarlsonRIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (fun w ↦ w ^ t)

/-- Carlson's native, unregularized `R_t` integral. -/
def carlsonRIntegral (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonRIntegral t b z

/-- The unregularized and regularized native integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonRIntegral_eq_Gamma_mul_reg (t : ℂ) (b z : ι → ℂ) :
    carlsonRIntegral t b z = Gamma (∑ i, b i) * regCarlsonRIntegral t b z := rfl

/-- The branch-safe domain where every Carlson variable lies in the open right half-plane. -/
def carlsonRVariableDomain : Set (ι → ℂ) :=
  {z | ∀ i, z i ∈ carlsonRightHalfPlane}

/-- Carlson's right-half-plane variable domain is open. -/
theorem isOpen_carlsonRVariableDomain : IsOpen (carlsonRVariableDomain : Set (ι → ℂ)) := by
  rw [show carlsonRVariableDomain (ι := ι) =
      ⋂ i, {z : ι → ℂ | z i ∈ carlsonRightHalfPlane} by ext z; simp [carlsonRVariableDomain]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_carlsonRightHalfPlane.preimage (continuous_apply i)

/-- A convex combination of points in the right half-plane remains there. -/
theorem carlsonAffineForm_mem_rightHalfPlane {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm z u ∈ carlsonRightHalfPlane := by
  have hsubset : Set.range z ⊆ carlsonRightHalfPlane := by
    intro w hw
    rcases hw with ⟨i, rfl⟩
    exact hz i
  exact convexHull_min hsubset convex_carlsonRightHalfPlane
    (carlsonAffineForm_mem_convexHull z hu)

/-- The right half-plane is contained in Mathlib's principal-branch slit plane. -/
theorem carlsonRightHalfPlane_subset_slitPlane : carlsonRightHalfPlane ⊆ slitPlane := by
  intro w hw
  rw [mem_slitPlane_iff]
  exact Or.inl hw

/-- On the Carlson variable domain, the affine kernel lies in the principal-branch slit plane. -/
theorem carlsonAffineForm_mem_slitPlane {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm z u ∈ slitPlane :=
  carlsonRightHalfPlane_subset_slitPlane (carlsonAffineForm_mem_rightHalfPlane hz hu)

end Carlson
end CarlsonR
