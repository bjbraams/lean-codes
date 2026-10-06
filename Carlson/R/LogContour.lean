/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitIntegral
public import Dirichlet.Average.CauchyCycle

/-!
# The logarithmic contour formula (Exercise 6.6-15)

The cycle form of Carlson's contour representation (6.3-6, 6.6-9) applied to `f = log` on the
slit plane represents the average of `log^{(n+1)}(w) = (-1)ⁿ n! w^{-n-1}`, which is
`(-1)ⁿ n! R_{-n-1}(b, z)`. The book's rectifiable Jordan curve is replaced by a `C¹` cycle with
prescribed winding numbers, as in `Dirichlet.isRegCarlsonContinuation_cycleIntegral`.

## Main results

* `Carlson.regCarlsonDirichletAverage_congr_convexHull`: averages depend only on the convex hull.
* `Carlson.iteratedDeriv_succ_log`: `(d/dw)^{n+1} log w = (-1)ⁿ n! w^{-n-1}`.
* `Carlson.regCarlsonR_neg_eq_cycleIntegral_log`: Exercise 6.6-15.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.6.
-/

open Complex Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- A regularized Carlson average only sees the integrand on the convex hull of the nodes. -/
theorem regCarlsonDirichletAverage_congr_convexHull {b z : ι → ℂ} {f g : ℂ → ℂ}
    (h : EqOn f g (convexHull ℝ (Set.range z))) :
    Dirichlet.regCarlsonDirichletAverage b z f = Dirichlet.regCarlsonDirichletAverage b z g := by
  unfold Dirichlet.regCarlsonDirichletAverage Dirichlet.regDirichletIntegral
  refine setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    fun u hu => ?_
  simp only
  rw [h (Dirichlet.carlsonAffineForm_mem_convexHull z hu)]

/-- `(d/dw)^{n+1} log w = (-1)ⁿ n! w^{-n-1}` on the slit plane. -/
theorem iteratedDeriv_succ_log {w : ℂ} (hw : w ∈ slitPlane) (n : ℕ) :
    iteratedDeriv (n + 1) log w = (-1) ^ n * n.factorial * w ^ (-((n : ℂ) + 1)) := by
  have hev : deriv log =ᶠ[𝓝 w] fun u => u ^ (-1 : ℤ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with u hu
    rw [(hasDerivAt_log hu).deriv, zpow_neg_one]
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hprod : ∏ i ∈ Finset.range n, (((-1 : ℤ) : ℂ) - i) = (-1) ^ n * n.factorial := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, pow_succ]; push_cast; ring
  rw [hprod, show (-1 : ℤ) - n = ((-((n : ℤ) + 1) : ℤ)) by ring, ← cpow_intCast]
  push_cast; ring_nf

/-- **Exercise 6.6-15** (logarithmic contour formula), on `C¹` cycles: if the convex hull of the
nodes lies in the slit plane, `Γ` is a `C¹` cycle in the slit plane avoiding the hull, with winding
number `0` about every point off the slit plane and winding number `m ≠ 0` about the hull, then
`R_{-n-1}(b, z)/Γ(c) = (-1)ⁿ (n + 1)/(2πi m) ∫_Γ log(s) R̃(b, s - z) ds`, where `R̃` is the
regularized resolvent `R_{-n-2}(b, s - z)/Γ(c)`. When `∑ bᵢ = n + 2` this resolvent is
`∏ (s - zᵢ)^{-bᵢ}/(n + 1)!` (6.6-5), and for a positively oriented Jordan curve `m = 1`. -/
theorem regCarlsonR_neg_eq_cycleIntegral_log (n : ℕ) {z : ι → ℂ}
    (hhull : convexHull ℝ (Set.range z) ⊆ slitPlane) (Γ : Cycle) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ slitPlane) (hind : ∀ w, w ∉ slitPlane → Γ.index w = 0)
    (havoid : Γ.range ⊆ (convexHull ℝ (Set.range z))ᶜ) {m : ℂ} (hm0 : m ≠ 0)
    (hm : ∀ w ∈ convexHull ℝ (Set.range z), Γ.index w = m) (b : ι → ℂ) :
    regCarlsonR (-((n : ℂ) + 1)) b z = (-1) ^ n * (n + 1) * m⁻¹ *
      (2 * (Real.pi : ℂ) * I)⁻¹ * Γ.integral (fun s =>
        toSpanSingleton ℂ (Dirichlet.continuedRegCarlsonResolvent (n + 1) b z s * log s)) := by
  have hlog : DifferentiableOn ℂ log slitPlane := fun w hw =>
    (differentiableAt_log hw).differentiableWithinAt
  have hG := Dirichlet.isRegCarlsonContinuation_cycleIntegral (n + 1) z isOpen_slitPlane Γ hΓ hΓU
    hind hhull havoid hm0 hm hlog
  have hR := isRegCarlsonRContinuation_regCarlsonR_of_convexHull (-((n : ℂ) + 1)) hhull
  have hH : Dirichlet.IsRegCarlsonContinuation (iteratedDeriv (n + 1) log) z
      (fun b => (-1) ^ n * (n.factorial : ℂ) * regCarlsonR (-((n : ℂ) + 1)) b z) := by
    refine Dirichlet.IsRegCarlsonContinuation.mk' ?_ fun b hb => ?_
    · intro b hb
      exact analyticAt_const.mul (hR.analyticOnNhd b hb)
    · simp only
      rw [hR.eq_native hb, ← Dirichlet.regCarlsonDirichletAverage_const_mul]
      exact regCarlsonDirichletAverage_congr_convexHull fun w hw =>
        (iteratedDeriv_succ_log (hhull hw) n).symm
  have heq := congrFun (hG.eq hH) b
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hsign : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [Nat.factorial_succ] at heq
  push_cast at heq
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) hn)
  rw [← heq]
  linear_combination (-(n + 1 : ℂ) * (n.factorial : ℂ) * m⁻¹ * (2 * (Real.pi : ℂ) * I)⁻¹ *
    Γ.integral (fun s => toSpanSingleton ℂ (Dirichlet.continuedRegCarlsonResolvent (n + 1) b z s *
      log s))) * hsign

end Carlson
