/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Continuation
public import Carlson.L.Associated

/-!
# Associated relations for L on the full product slit plane

Carlson (1987), (2.6), (3.1)–(3.4), and (3.7), for arbitrary complex exponents
and Dirichlet parameters. The identities are regularized and have no exceptional
parameter hyperplanes. Euler inversion retains the minus sign from the reflected
exponent, and the lowering and tangent identities retain their inhomogeneous R-terms.

## Main results

* `Carlson.regCarlsonL_three_node`: Equation (3.3), allowing coincident indices and nodes.
* `Carlson.regCarlsonL_tangent_sub`: Equation (3.7), with its R-term and without parameter
  restrictions.
* `Carlson.regCarlsonL_sub_dirichletUnit`: Equation (3.4) in parameter-lowered form.
  Regularization eliminates the ordinary normalization's factor `c - 1`, so no exceptional
  parameter is excluded.
* `Carlson.regCarlsonL_weighted_tangent_sub`: Carlson (1987), (3.8), on the full slit domain.
  The undivided identity includes coincident nodes and equal indices.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Equation (3.3), including coincident nodes and indices. -/
private theorem regCarlsonL_three_node_of_mem_variableDomain (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i j k : ι) :
    (z i - z j) * regCarlsonL t (b - Pi.single k 1) z +
      (z j - z k) * regCarlsonL t (b - Pi.single i 1) z +
      (z k - z i) * regCarlsonL t (b - Pi.single j 1) z = 0 :=
  (isRegCarlsonLContinuation_regCarlsonL t hz).three_node convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
    (Set.range_subset_iff.mpr hz) isOpen_carlsonRightHalfPlane b i j k

open scoped Classical in
/-- Equation (3.7), in pole-free regularized form. -/
private theorem regCarlsonL_tangent_sub_of_mem_variableDomain (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonL (t - 1) b z +
      regCarlsonR (t - 1) b z) =
        regCarlsonL t (b - Pi.single j 1) z -
          regCarlsonL t (b - Pi.single i 1) z :=
  (isRegCarlsonLContinuation_regCarlsonL t hz).tangent_sub convex_carlsonRightHalfPlane
    ((analyticOnNhd_carlsonLKernel t).mono carlsonRightHalfPlane_subset_slitPlane)
    (Set.range_subset_iff.mpr hz) (isRegCarlsonContinuation_deriv_LKernel t hz) b i j

open scoped Classical in
/-- Equation (3.3), allowing coincident indices and nodes. -/
theorem regCarlsonL_three_node (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j k : ι) :
    (z i - z j) * regCarlsonL t (b - Pi.single k 1) z +
      (z j - z k) * regCarlsonL t (b - Pi.single i 1) z +
      (z k - z i) * regCarlsonL t (b - Pi.single j 1) z = 0 := by
  have hterm (i j k : ι) : AnalyticOnNhd ℂ
      (fun w => (w i - w j) * regCarlsonL t (b - Pi.single k 1) w) carlsonRSlitDomain := by
    intro w hw
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).sub
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        (analyticOnNhd_regCarlsonL t _ w hw)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (((hterm i j k).add (hterm j k i)).add (hterm k i j)) analyticOnNhd_const ?_ hz
  intro w hw
  change (w i - w j) * regCarlsonL t (b - Pi.single k 1) w +
    (w j - w k) * regCarlsonL t (b - Pi.single i 1) w +
    (w k - w i) * regCarlsonL t (b - Pi.single j 1) w = 0
  exact regCarlsonL_three_node_of_mem_variableDomain t b hw i j k

open scoped Classical in
/-- Equation (3.7), with its R-term and without parameter restrictions. -/
theorem regCarlsonL_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonL (t - 1) b z + regCarlsonR (t - 1) b z) =
      regCarlsonL t (b - Pi.single j 1) z - regCarlsonL t (b - Pi.single i 1) z := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ =>
      (w i - w j) * (t * regCarlsonL (t - 1) b w + regCarlsonR (t - 1) b w))
      carlsonRSlitDomain := by
    intro w hw
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).sub
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        ((analyticAt_const.mul (analyticOnNhd_regCarlsonL (t - 1) b w hw)).add
          (analyticOnNhd_regCarlsonR (t - 1) b w hw))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft
    ((analyticOnNhd_regCarlsonL t _).sub (analyticOnNhd_regCarlsonL t _)) ?_ hz
  intro w hw
  change (w i - w j) * (t * regCarlsonL (t - 1) b w + regCarlsonR (t - 1) b w) =
    regCarlsonL t (b - Pi.single j 1) w - regCarlsonL t (b - Pi.single i 1) w
  exact regCarlsonL_tangent_sub_of_mem_variableDomain t b hw i j

open scoped Classical in
/-- Equation (3.4) in parameter-lowered form. Regularization eliminates the
ordinary normalization's factor `c - 1`, so no exceptional parameter is excluded. -/
theorem regCarlsonL_sub_dirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonL t (b - Pi.single i 1) z =
      ((∑ j, b j) + t - 1) * regCarlsonL t b z -
        t * z i * regCarlsonL (t - 1) b z +
        regCarlsonR t b z - z i * regCarlsonR (t - 1) b z := by
  have hunit : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [addDirichletUnit]
    · simp [addDirichletUnit, hji]
  have hsum : (∑ j, ((b - Pi.single i (1 : ℂ)) : ι → ℂ) j) = (∑ j, b j) - 1 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib]
  have h := regCarlsonL_eq_addDirichletUnit t (b - Pi.single i 1) hz i
  rw [hunit, hsum] at h
  convert h using 1
  ring

open scoped Classical in
/-- Carlson (1987), (3.8), on the full slit domain. The undivided identity
includes coincident nodes and equal indices. -/
theorem regCarlsonL_weighted_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    ((∑ k, b k) + t - 1) * (z i - z j) * regCarlsonL t b z +
      z j * regCarlsonL t (b - Pi.single i 1) z -
      z i * regCarlsonL t (b - Pi.single j 1) z +
      (z i - z j) * regCarlsonR t b z = 0 := by
  linear_combination z j * regCarlsonL_sub_dirichletUnit t b hz i -
    z i * regCarlsonL_sub_dirichletUnit t b hz j

end Carlson
