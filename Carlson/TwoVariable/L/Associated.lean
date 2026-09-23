/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.Associated
public import Carlson.L.Continuation

/-! # Two-variable associated L-relations

Carlson (1987), (3.10), including the factored and mixed-derivative forms. -/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The first equality of Carlson (1987), (3.10), including its R-correction.
The further factored and mixed-node-derivative forms are separate statements. -/
theorem regCarlsonL_pair_three_term (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    (u + v + t) * regCarlsonL (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonL t (pair u v) (pair x y) +
      t * x * y * regCarlsonL (t - 1) (pair u v) (pair x y) =
      -regCarlsonR (t + 1) (pair u v) (pair x y) +
        (x + y) * regCarlsonR t (pair u v) (pair x y) -
        x * y * regCarlsonR (t - 1) (pair u v) (pair x y) := by
  have hplus := (hasDerivAt_regCarlsonR_L (t + 1) (pair u v) hz).comp_of_eq t
    ((hasDerivAt_id t).add_const 1) rfl
  have h₀ := hasDerivAt_regCarlsonR_L t (pair u v) hz
  have hminus := (hasDerivAt_regCarlsonR_L (t - 1) (pair u v) hz).comp_of_eq t
    ((hasDerivAt_id t).sub_const 1) rfl
  have h := (((hasDerivAt_id t).const_add (u + v)).mul hplus |>.sub
    ((((hasDerivAt_id t).const_add u).mul_const x |>.add
      (((hasDerivAt_id t).const_add v).mul_const y)).mul h₀)).add
    ((((hasDerivAt_id t).mul_const x).mul_const y).mul hminus)
  change HasDerivAt (fun s =>
    (u + v + s) * regCarlsonR (s + 1) (pair u v) (pair x y) -
      ((u + s) * x + (v + s) * y) * regCarlsonR s (pair u v) (pair x y) +
      s * x * y * regCarlsonR (s - 1) (pair u v) (pair x y)) _ t at h
  have heq : (fun s =>
    (u + v + s) * regCarlsonR (s + 1) (pair u v) (pair x y) -
      ((u + s) * x + (v + s) * y) * regCarlsonR s (pair u v) (pair x y) +
      s * x * y * regCarlsonR (s - 1) (pair u v) (pair x y)) = (fun _ : ℂ => 0) :=
    funext fun s => regCarlsonR_pair_three_term s u v hz
  rw [heq] at h
  have H := h.unique (hasDerivAt_const t 0)
  dsimp only [Function.comp_def, id_eq, Pi.add_apply, Pi.mul_apply] at H
  linear_combination H

/-- The factored equality in Carlson (1987), (3.10), with all Gamma factors cleared. -/
theorem regCarlsonL_pair_three_term_factored (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    (u + v + t) * regCarlsonL (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonL t (pair u v) (pair x y) +
      t * x * y * regCarlsonL (t - 1) (pair u v) (pair x y) =
      u * v * (x - y) ^ 2 * regCarlsonR (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  rw [regCarlsonL_pair_three_term t u v hz,
    regCarlsonR_pair_correction_factor t u v hz]

/-- The mixed-derivative equality in (3.10), without dividing by `t * (t + 1)`.
This formulation includes `t = 0`, `t = -1`, and coincident nodes. -/
theorem regCarlsonL_pair_three_term_mixed (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    t * (t + 1) *
      ((u + v + t) * regCarlsonL (t + 1) (pair u v) (pair x y) -
        ((u + t) * x + (v + t) * y) * regCarlsonL t (pair u v) (pair x y) +
        t * x * y * regCarlsonL (t - 1) (pair u v) (pair x y)) =
      (x - y) ^ 2 * carlsonPartialDeriv 0
        (carlsonPartialDeriv 1 (regCarlsonR (t + 1) (pair u v))) (pair x y) := by
  rw [regCarlsonL_pair_three_term_factored t u v hz,
    carlsonPartialDeriv_regCarlsonR_pair_mixed t u v hz]
  ring

/-- The quotient form printed in (3.10), with its necessary exponent exclusions. -/
theorem regCarlsonL_pair_three_term_mixed_div (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) (ht : t ≠ 0) (ht₁ : t + 1 ≠ 0) :
    (u + v + t) * regCarlsonL (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonL t (pair u v) (pair x y) +
      t * x * y * regCarlsonL (t - 1) (pair u v) (pair x y) =
      (x - y) ^ 2 / (t * (t + 1)) * carlsonPartialDeriv 0
        (carlsonPartialDeriv 1 (regCarlsonR (t + 1) (pair u v))) (pair x y) := by
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht ht₁), mul_comm]
  exact regCarlsonL_pair_three_term_mixed t u v hz

end Carlson.TwoVariable
