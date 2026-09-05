/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.ComplexDirichlet
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Convex

/-!
# Carlson's Dirichlet averages: basic definitions

This file specializes the regularized Dirichlet integral to a univariate function evaluated
at the affine form `∑ i, u i * z i`.  It contains the algebraic and convex-geometric material
used by both the native integral theory of Carlson's Chapter 5 and its analytic continuation
in Chapter 6.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Chapters 5 and 6,
  Academic Press, 1977.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The affine form on the standard simplex associated with the complex parameters `z`. -/
def carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) : ℂ :=
  ∑ i, (u i : ℂ) * z i

/-- The affine form associated with `z` is continuous in the simplex variable. -/
theorem continuous_carlsonAffineForm (z : ι → ℂ) :
    Continuous (carlsonAffineForm z) := by
  unfold carlsonAffineForm
  fun_prop

/-- The multivariate polynomial whose value is Carlson's affine form. -/
def carlsonAffinePolynomial (z : ι → ℂ) : MvPolynomial ι ℂ :=
  ∑ i, MvPolynomial.C (z i) * MvPolynomial.X i

/-- Evaluation of `carlsonAffinePolynomial` gives the corresponding affine form. -/
@[simp] theorem eval_carlsonAffinePolynomial (z x : ι → ℂ) :
    (carlsonAffinePolynomial z).eval x = ∑ i, x i * z i := by
  simp [carlsonAffinePolynomial, mul_comm]

/-- The polynomial representing the `n`th power of Carlson's affine form. -/
def carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) : MvPolynomial ι ℂ :=
  (carlsonAffinePolynomial z) ^ n

/-- Evaluation of `carlsonPowerPolynomial` gives the corresponding power of the affine form. -/
@[simp] theorem eval_carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) (u : ι → ℝ) :
    (carlsonPowerPolynomial n z).eval (fun i ↦ (u i : ℂ)) =
      carlsonAffineForm z u ^ n := by
  simp [carlsonPowerPolynomial, carlsonAffineForm]

/-- Carlson's Dirichlet average divided by `Γ(∑ i, b i)`, on the native integral domain.

The function supplied to the simplex integral is `u ↦ f (∑ i, u i * z i)`. -/
def regCarlsonDirichletAverage (b z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  regDirichletIntegral b (fun u ↦ f (carlsonAffineForm z u))

/-! ## The native averaging process -/

/-- Simultaneously permuting the simplex coordinates and the parameters of the affine form
does not change that affine form. -/
@[simp] theorem carlsonAffineForm_perm (z : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    carlsonAffineForm (z ∘ σ) (u ∘ σ) = carlsonAffineForm z u := by
  unfold carlsonAffineForm
  simpa only [Function.comp_apply] using
    Equiv.sum_comp σ (fun i ↦ (u i : ℂ) * z i)

/-- The affine form of a constant parameter vector is constant on the standard simplex. -/
theorem carlsonAffineForm_const {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) (w : ℂ) :
    carlsonAffineForm (fun _ ↦ w) u = w := by
  rw [carlsonAffineForm, ← Finset.sum_mul]
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  rw [hsum, one_mul]

/-- Simultaneous permutation of the Dirichlet parameters and the variables leaves the native
regularized Carlson average unchanged.  This is the regularized form of Carlson's
Theorem 5.2-3. -/
theorem regCarlsonDirichletAverage_perm (b z : ι → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm ι) :
    regCarlsonDirichletAverage (b ∘ σ) (z ∘ σ) f =
      regCarlsonDirichletAverage b z f := by
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_stdSimplex_comp_perm σ
    (fun u ↦ regDirichletDensity (b ∘ σ) u * f (carlsonAffineForm (z ∘ σ) u))]
  congr 1
  funext u
  rw [regDirichletDensity_perm, carlsonAffineForm_perm]

/-- On the diagonal, the native regularized Carlson average is `f(w) / Γ(∑ i, b i)`.
This is the regularized form of Carlson's equation (5.2-2). -/
theorem regCarlsonDirichletAverage_const (f : ℂ → ℂ) (w : ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b (fun _ ↦ w) f =
      f w / Gamma (∑ i, b i) := by
  unfold regCarlsonDirichletAverage
  rw [regDirichletIntegral_congr b
    (g := fun _ ↦ f w) (fun u hu ↦ congrArg f (carlsonAffineForm_const hu w))]
  have hsmul := regDirichletIntegral_smul b (c := f w)
    (f := fun _ ↦ (1 : ℂ)) (by fun_prop) hb
  simp only [mul_one] at hsmul
  rw [hsmul]
  rw [show regDirichletIntegral b (fun _ ↦ (1 : ℂ)) =
      ∫ u in stdSimplex ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure by
    simp [regDirichletIntegral]]
  rw [regDirichletIntegral_normalization b hb]
  simp [div_eq_mul_inv]

/-- Affine changes in the variables commute with Carlson's affine form on the standard
simplex. -/
theorem carlsonAffineForm_affine {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι)
    (a t : ℂ) (z : ι → ℂ) :
    carlsonAffineForm (fun i ↦ a * z i + t) u = a * carlsonAffineForm z u + t := by
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  unfold carlsonAffineForm
  calc
    ∑ i, (u i : ℂ) * (a * z i + t) =
        ∑ i, (a * ((u i : ℂ) * z i) + (u i : ℂ) * t) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * ∑ i, (u i : ℂ) * z i + (∑ i, (u i : ℂ)) * t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = a * ∑ i, (u i : ℂ) * z i + t := by rw [hsum, one_mul]

/-- Precomposing the averaged function by an affine map is equivalent to applying the same
affine map to every variable.  This is Carlson's Theorem 5.2-6. -/
theorem regCarlsonDirichletAverage_comp_affine (b z : ι → ℂ) (f : ℂ → ℂ) (a t : ℂ) :
    regCarlsonDirichletAverage b z (fun w ↦ f (a * w + t)) =
      regCarlsonDirichletAverage b (fun i ↦ a * z i + t) f := by
  unfold regCarlsonDirichletAverage
  apply regDirichletIntegral_congr
  intro u hu
  change f (a * carlsonAffineForm z u + t) =
    f (carlsonAffineForm (fun i ↦ a * z i + t) u)
  rw [carlsonAffineForm_affine hu]

/-- Carlson's affine form lies in the real convex hull of its parameters. -/
theorem carlsonAffineForm_mem_convexHull (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
    carlsonAffineForm z u ∈ convexHull ℝ (Set.range z) := by
  have h := affineCombination_mem_convexHull (s := Finset.univ) (v := z) (w := u)
    (fun i _ ↦ hu.1 i) hu.2
  rw [affineCombination_eq_centerMass hu.2] at h
  simpa [Finset.centerMass, hu.2, carlsonAffineForm, Complex.real_smul, mul_comm] using h

/-- The denominator in Carlson's resolvent is nonzero off the convex hull of `z`. -/
theorem sub_carlsonAffineForm_ne_zero {s : ℂ} {z : ι → ℂ} {u : ι → ℝ}
    (hs : s ∉ convexHull ℝ (Set.range z)) (hu : u ∈ stdSimplex ℝ ι) :
    s - carlsonAffineForm z u ≠ 0 := by
  intro h
  apply hs
  rw [sub_eq_zero.mp h]
  exact carlsonAffineForm_mem_convexHull z hu

/-- The open right half-plane, an important domain for Carlson's power and resolvent
constructions. -/
def carlsonRightHalfPlane : Set ℂ :=
  {w | 0 < w.re}

/-- The right half-plane is open. -/
theorem isOpen_carlsonRightHalfPlane : IsOpen carlsonRightHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- The right half-plane is convex over the real scalars. -/
theorem convex_carlsonRightHalfPlane : Convex ℝ carlsonRightHalfPlane := by
  exact convex_halfSpace_re_gt 0

/-- A convenient name for the hypothesis that a univariate function is holomorphic on the
right half-plane. -/
def HolomorphicOnCarlsonRightHalfPlane (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f carlsonRightHalfPlane

end DirichletTransform

end CarlsonDirichletAverage
