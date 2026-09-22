/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SingleIntegral.Analytic

/-!
# The unit-interval representation and node analyticity

Analytic dependence of the unit-interval single integral on the nodes, throughout the product
slit plane, and Carlson's Theorem 6.8-1 in unit-interval form on the native domain.

## Main definitions

* `Carlson.singleIntegralKernel`: the product kernel `∏ i, (1 - u + u * z i) ^ (-b i)`.

## Main results

* `Carlson.analyticOnNhd_carlsonRUnitIntervalIntegral_slit`: node analyticity of the unit-interval
  integral on the full slit domain.
* `Carlson.carlsonRUnitIntervalIntegral_eq`: Carlson's Theorem 6.8-1 in unit-interval form.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The affine segment from `1` to a point in Carlson's right-half-plane domain remains in
that domain. -/
lemma affineSegment_mem_rightHalfPlane
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : ι) :
    (1 - u : ℂ) + (u : ℂ) * z i ∈ carlsonRightHalfPlane := by
  have hzi : 0 < (z i).re := hz i
  by_cases hu0 : u = 0
  · subst u
    simp [carlsonRightHalfPlane]
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hmul : 0 < u * (z i).re := mul_pos hupos hzi
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq]
  simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  exact add_pos_of_nonneg_of_pos hone hmul

/-- The product kernel in Carlson's single-integral formula. -/
def singleIntegralKernel (b z : ι → ℂ) (u : ℝ) : ℂ :=
  ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)

/-- At fixed Carlson variables in the slit plane, the product kernel is continuous on
the closed unit interval. -/
lemma continuousOn_singleIntegralKernel_fixed
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ContinuousOn (singleIntegralKernel b z) (Set.Icc 0 1) := by
  classical
  unfold singleIntegralKernel
  apply continuousOn_finsetProd
  intro i hi
  have hq : Continuous
      (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z i) := by fun_prop
  exact hq.continuousOn.cpow continuousOn_const (fun u hu =>
    carlsonRSegment_mem_slitPlane hz hu i)

/-- For positive beta exponents, the unit-interval integral is analytic in all Carlson
variables throughout the full product slit plane (Carlson's Theorem 6.8-1). -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral_slit
    (a a' : ℂ) (b : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re) :
    AnalyticOnNhd ℂ (carlsonRUnitIntervalIntegral a a' b)
      carlsonRSlitDomain :=
  analyticOnNhd_carlsonRUnitIntervalIntegral_comp isOpen_carlsonRSlitDomain
    analyticOnNhd_const analyticOnNhd_const analyticOnNhd_const analyticOnNhd_id
    (fun _ _ => ⟨ha, ha'⟩) (fun _ hz => hz)

/-- The right-half-plane restriction of the slit-plane analyticity theorem. -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral
    (a a' : ℂ) (b : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re) :
    AnalyticOnNhd ℂ (carlsonRUnitIntervalIntegral a a' b)
      carlsonRVariableDomain :=
  (analyticOnNhd_carlsonRUnitIntervalIntegral_slit a a' b ha ha').mono
    carlsonRVariableDomain_subset_slitDomain

/-- Carlson's Theorem 6.8-1 in unit-interval form.  The homogeneity relation
`a + a' = ∑ i, b i` supplies the exponent at the endpoint `u = 1`. -/
theorem carlsonRUnitIntervalIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  let one : ι → ℂ := fun _ => 1
  have hone : one ∈ carlsonRVariableDomain := by
    intro i
    simp [one, carlsonRightHalfPlane]
  have hconv : Convex ℝ (carlsonRVariableDomain : Set (ι → ℂ)) := by
    rw [show carlsonRVariableDomain (ι := ι) =
        Set.pi Set.univ (fun _ => carlsonRightHalfPlane) by
      ext w
      simp [carlsonRVariableDomain]]
    exact convex_pi (fun _ _ => convex_carlsonRightHalfPlane)
  have hleft := analyticOnNhd_carlsonRUnitIntervalIntegral a a' b ha ha'
  have hright : AnalyticOnNhd ℂ
      (fun w => betaIntegral a a' * carlsonRIntegral (-a) b w)
      carlsonRVariableDomain :=
    analyticOnNhd_const.mul (analyticOnNhd_carlsonRIntegral (-a) hb)
  refine hleft.eqOn_of_preconnected_of_eventuallyEq hright hconv.isPreconnected hone ?_ hz
  filter_upwards [Metric.ball_mem_nhds one zero_lt_one] with w hw
  apply carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one ha ha' hsum hb
  intro i
  calc
    ‖1 - w i‖ = ‖(w - one) i‖ := by
      change ‖(1 : ℂ) - w i‖ = ‖w i - 1‖
      exact norm_sub_rev _ _
    _ ≤ ‖w - one‖ := norm_le_pi_norm (w - one) i
    _ = dist w one := by rw [dist_eq_norm]
    _ < 1 := Metric.mem_ball.mp hw

end Carlson
