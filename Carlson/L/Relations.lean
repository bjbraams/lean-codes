/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Continuation
public import Carlson.R.EulerTransform

/-!
# Associated relations for Carlson's L-function

The parameter-raising relations (3.1), (3.2) and (3.4) of Carlson (1987) and the Euler
inversion (2.6), obtained by differentiating the corresponding R-relations in the exponent.
They hold for all complex exponents and Dirichlet parameters and all nodes in the product slit
plane, in the Gamma-regularized normalization and without dividing by the exponent or the
total parameter.

## Main results

* `Carlson.regCarlsonL_eq_sum_addDirichletUnit`: equation (3.1).
* `Carlson.regCarlsonL_add_one_eq_sum_mul_addDirichletUnit`: equation (3.2).
* `Carlson.regCarlsonL_eq_addDirichletUnit`: equation (3.4), with its two R-terms.
* `Carlson.regCarlsonL_euler`: equation (2.6).

## References

* B. C. Carlson, *A table of elliptic integrals of the third kind*, Math. Comp. 51 (1987);
  cited as Carlson (1987).
-/

open Dirichlet
open Complex ProbabilityTheory
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Equation (3.1), after Gamma regularization. -/
theorem regCarlsonL_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t b z = ∑ i, b i * regCarlsonL t (addDirichletUnit b i) z := by
  have h := hasDerivAt_regCarlsonR_L t b hz
  have heq : (fun s => regCarlsonR s b z) =
      (fun s => ∑ i, b i * regCarlsonR s (addDirichletUnit b i) z) :=
    funext fun s => regCarlsonR_eq_sum_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonR_L t (addDirichletUnit b i) hz).const_mul (b i))

/-- Equation (3.2), after Gamma regularization. -/
theorem regCarlsonL_add_one_eq_sum_mul_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL (t + 1) b z = ∑ i, b i * z i * regCarlsonL t (addDirichletUnit b i) z := by
  have h := (hasDerivAt_regCarlsonR_L (t + 1) b hz).comp t ((hasDerivAt_id t).add_const 1)
  simp only [mul_one, Function.comp_def, id_eq] at h
  have heq : (fun s => regCarlsonR (s + 1) b z) =
      (fun s => ∑ i, b i * z i * regCarlsonR s (addDirichletUnit b i) z) :=
    funext fun s => regCarlsonR_add_one_eq_sum_mul_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonR_L t (addDirichletUnit b i) hz).const_mul (b i * z i))

/-- Equation (3.4), with parameters raised instead of lowered. The two R-terms are essential:
L is not homogeneous in the exponent-dependent coefficients. -/
theorem regCarlsonL_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonL t b z =
      ((∑ j, b j) + t) * regCarlsonL t (addDirichletUnit b i) z -
        t * z i * regCarlsonL (t - 1) (addDirichletUnit b i) z +
        regCarlsonR t (addDirichletUnit b i) z -
        z i * regCarlsonR (t - 1) (addDirichletUnit b i) z := by
  have h := hasDerivAt_regCarlsonR_L t b hz
  have heq : (fun s => regCarlsonR s b z) =
      (fun s => ((∑ j, b j) + s) * regCarlsonR s (addDirichletUnit b i) z -
        s * z i * regCarlsonR (s - 1) (addDirichletUnit b i) z) :=
    funext fun s => regCarlsonR_eq_addDirichletUnit s b hz i
  rw [heq] at h
  have h₀ := hasDerivAt_regCarlsonR_L t (addDirichletUnit b i) hz
  have h₁ := (hasDerivAt_regCarlsonR_L (t - 1) (addDirichletUnit b i) hz).comp t
    ((hasDerivAt_id t).sub_const 1)
  have H := h.unique ((((hasDerivAt_id t).const_add (∑ j, b j)).mul h₀).sub
    (((hasDerivAt_id t).mul_const (z i)).mul h₁))
  simp only [id_eq] at H
  convert H using 1
  ring

/-- Equation (2.6): the Euler transformation for L has a minus sign from the reflected
exponent. -/
theorem regCarlsonL_euler (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonL t b z =
      -(∏ i, z i ^ (-b i)) * regCarlsonL (-(∑ i, b i) - t) b (fun i => (z i)⁻¹) := by
  have h := hasDerivAt_regCarlsonR_L t b hz
  have heq : (fun s => regCarlsonR s b z) =
      (fun s => (∏ i, z i ^ (-b i)) * regCarlsonR (-(∑ i, b i) - s) b (fun i => (z i)⁻¹)) :=
    funext fun s => regCarlsonR_euler s b hz
  rw [heq] at h
  have hd := ((hasDerivAt_regCarlsonR_L (-(∑ i, b i) - t) b (carlsonRSlitDomain_inv hz)).comp t
    ((hasDerivAt_id t).const_sub (-(∑ i, b i)))).const_mul (∏ i, z i ^ (-b i))
  convert h.unique hd using 1
  ring

end Carlson
