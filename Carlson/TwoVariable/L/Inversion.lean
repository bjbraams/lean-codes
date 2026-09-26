/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.Inversion
public import Carlson.L.Continuation

/-!
# Two-variable L-inversion

The full slit-domain correction is `log x + log y`; the `log (x * y)` version
requires the branch-safe right-half-plane hypotheses.

## Main results

* `Carlson.TwoVariable.regCarlsonL_pair_inversion`: Carlson (1987), (2.11), in branch-correct
  form on the entire product slit plane. No Gamma-regularity assumptions are needed for these
  regularized functions.
* `Carlson.TwoVariable.regCarlsonL_pair_inversion_log_mul`: The paper's `log (x * y)` form of
  (2.11), on its branch-safe right half-plane.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Carlson (1987), (2.11), in branch-correct form on the entire product slit plane.
No Gamma-regularity assumptions are needed for these regularized functions. -/
theorem regCarlsonL_pair_inversion (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    regCarlsonL t (pair u v) (pair x y) =
      (log x + log y) * regCarlsonR t (pair u v) (pair x y) -
        x ^ (t + v) * y ^ (t + u) *
          regCarlsonL (-u - v - t) (pair v u) (pair x y) := by
  have hx₀ := slitPlane_ne_zero (hz 0)
  have hy₀ := slitPlane_ne_zero (hz 1)
  have hx := ((hasDerivAt_id t).add_const v).const_cpow (Or.inl hx₀)
  have hy := ((hasDerivAt_id t).add_const u).const_cpow (Or.inl hy₀)
  have hR := (hasDerivAt_regCarlsonR_L (-u - v - t) (pair v u) hz).comp_of_eq t
    ((hasDerivAt_id t).const_sub (-u - v)) rfl
  have h := (hx.mul hy).mul hR
  have heq : (fun s => x ^ (s + v) * y ^ (s + u) *
      regCarlsonR (-u - v - s) (pair v u) (pair x y)) =
      (fun s => regCarlsonR s (pair u v) (pair x y)) :=
    funext fun s => (regCarlsonR_pair_inversion s u v hz).symm
  change HasDerivAt (fun s => x ^ (s + v) * y ^ (s + u) *
    regCarlsonR (-u - v - s) (pair v u) (pair x y)) _ t at h
  rw [heq] at h
  have H := h.unique (hasDerivAt_regCarlsonR_L t (pair u v) hz)
  dsimp only [Function.comp_def, id_eq, Pi.add_apply, Pi.mul_apply, pair_zero, pair_one] at H
  rw [regCarlsonR_pair_inversion t u v hz]
  linear_combination -H

/-- The paper's `log (x * y)` form of (2.11), on its branch-safe right half-plane. -/
theorem regCarlsonL_pair_inversion_log_mul (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonL t (pair u v) (pair x y) =
      log (x * y) * regCarlsonR t (pair u v) (pair x y) -
        x ^ (t + v) * y ^ (t + u) *
          regCarlsonL (-u - v - t) (pair v u) (pair x y) := by
  have hxarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hyarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  rw [Complex.log_mul (ne_zero_of_re_pos hx) (ne_zero_of_re_pos hy)
    ⟨by linarith [hxarg.1, hyarg.1], by linarith [hxarg.2, hyarg.2]⟩]
  apply regCarlsonL_pair_inversion
  intro i; fin_cases i
  · exact carlsonRightHalfPlane_subset_slitPlane hx
  · exact carlsonRightHalfPlane_subset_slitPlane hy

end Carlson.TwoVariable
