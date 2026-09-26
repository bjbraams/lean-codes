/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.ParameterSymmetry
public import Carlson.R.EulerTransform

/-!
# Two-variable R-inversion on the full slit domain

Carlson's inversion formula for two nodes, expressing `R_t(b; x, y)` through
`R_{-t}(b'; x⁻¹, y⁻¹)` with separate principal powers of the nodes, valid on the whole slit
domain.

## Main results

* `Carlson.TwoVariable.regCarlsonR_pair_inversion`: the two-variable inversion formula.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- For right-half-plane nodes, two-variable inversion exchanges the parameters and replaces the
exponent by its complementary value, with the principal-power prefactor. -/
private theorem regCarlsonR_pair_inversion_of_right (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR t (pair u v) (pair x y) =
      x ^ (t + v) * y ^ (t + u) *
        regCarlsonR (-u - v - t) (pair v u) (pair x y) := by
  have hz : pair x y ∈ carlsonRVariableDomain := by
    intro i; fin_cases i <;> assumption
  have hx₀ := ne_zero_of_re_pos hx
  have hy₀ := ne_zero_of_re_pos hy
  have hxi : 0 < (x⁻¹).re := carlsonRVariableDomain_inv hz 0
  have hyi : 0 < (y⁻¹).re := carlsonRVariableDomain_inv hz 1
  have hi : (fun i => (pair x y i)⁻¹) = pair x⁻¹ y⁻¹ := by
    ext i; fin_cases i <;> rfl
  have h := regCarlsonR_euler t (pair u v) (carlsonRVariableDomain_subset_slitDomain hz)
  simp only [sum_pair, Fin.prod_univ_two, pair_zero, pair_one, hi,
    show -(u + v) - t = -u - v - t by ring] at h
  rw [h, regCarlsonR_normalize_first _ _ hxi hyi,
    ← regCarlsonR_pair_swap (-u - v - t) v u
      (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy),
    regCarlsonR_normalize_first _ _ hy hx, inv_div_inv]
  have hc : x ^ (-u) * y ^ (-v) * (x⁻¹) ^ (-u - v - t) =
      x ^ (t + v) * y ^ (t + u) * y ^ (-u - v - t) := by
    simp only [cpow_def_of_ne_zero hx₀, cpow_def_of_ne_zero hy₀,
      cpow_def_of_ne_zero (inv_ne_zero hx₀),
      log_inv x (slitPlane_arg_ne_pi (carlsonRightHalfPlane_subset_slitPlane hx)), ← exp_add]
    congr 1
    ring
  linear_combination hc * regCarlsonR (-u - v - t) (pair u v) (pair 1 (x / y))

/-- Two-variable R-inversion with separate principal powers, valid on the full slit domain. -/
theorem regCarlsonR_pair_inversion (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    regCarlsonR t (pair u v) (pair x y) =
      x ^ (t + v) * y ^ (t + u) *
        regCarlsonR (-u - v - t) (pair v u) (pair x y) := by
  have hright : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ =>
      z 0 ^ (t + v) * z 1 ^ (t + u) * regCarlsonR (-u - v - t) (pair v u) z)
      carlsonRSlitDomain := by
    intro z hz
    have hcoord (i : Fin 2) : AnalyticAt ℂ (fun w : Fin 2 → ℂ => w i) z :=
      (analyticAt_pi_iff.mp analyticAt_id) i
    exact (((hcoord 0).cpow analyticAt_const (hz 0)).mul
      ((hcoord 1).cpow analyticAt_const (hz 1))).mul
        (analyticOnNhd_regCarlsonR (-u - v - t) (pair v u) z hz)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonR t (pair u v)) hright ?_ hz
  intro z hz
  have heq : pair (z 0) (z 1) = z := by ext i; fin_cases i <;> rfl
  simpa only [heq] using regCarlsonR_pair_inversion_of_right t u v (hz 0) (hz 1)

end Carlson.TwoVariable
