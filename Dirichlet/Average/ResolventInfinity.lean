/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.ResolventContinuation
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Affine covariance and normalization at infinity of the resolvent

An invertible complex affine change of nodes and evaluation point multiplies the
integer resolvent by its expected integer power. In the reciprocal coordinate
at infinity, the normalized resolvent is analytic near zero. Its value there is
reciprocal Gamma of the total Dirichlet parameter, including exceptional parameters.

## Main results

* `continuedRegCarlsonResolvent_affine`: affine covariance for all complex parameters.
* `analyticAt_continuedRegCarlsonResolvent_infinity`: the analytic reciprocal chart.
* `tendsto_continuedRegCarlsonResolvent_infinity`: the leading coefficient at infinity.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§5.11 and 7.1.
-/

public noncomputable section
namespace Dirichlet
open Complex Set Filter Bornology
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Invertible complex affine changes of nodes and exterior point preserve the
continued regularized resolvent up to the integer homogeneity factor. -/
theorem continuedRegCarlsonResolvent_affine (n : ℕ) (b z : ι → ℂ) (c d : ℂ)
    (hc : c ≠ 0) {x : ℂ} (hx : (x, z) ∈ carlsonResolventDomain) :
    continuedRegCarlsonResolvent n b (fun i => c * z i + d) (c * x + d) =
      c ^ (-(n + 1 : ℤ)) * continuedRegCarlsonResolvent n b z x := by
  have he {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
      c * x + d - carlsonAffineForm (fun i => c * z i + d) u =
        c * (x - carlsonAffineForm z u) := by rw [carlsonAffineForm_affine hu c d z]; ring
  have hnew : (c * x + d, fun i => c * z i + d) ∈ carlsonResolventDomain := by
    intro u hu
    rw [he hu]
    exact mul_ne_zero hc (hx u hu)
  have hF := isRegCarlsonContinuation_continuedRegCarlsonResolvent n hnew
  have hG : IsRegCarlsonContinuation (fun w => (c * x + d - w) ^ (-(n + 1 : ℤ)))
      (fun i => c * z i + d)
      (fun b => c ^ (-(n + 1 : ℤ)) * continuedRegCarlsonResolvent n b z x) :=
    (IsRegDirichletContinuation.smul
      (isRegCarlsonContinuation_continuedRegCarlsonResolvent n hx) (c ^ (-(n + 1 : ℤ)))).congr
      (fun u hu => by dsimp only; rw [he hu, mul_zpow])
  exact congrFun (hF.eq hG) b

/-- The normalized reciprocal chart of the resolvent is analytic at zero.
There are no restrictions on the Dirichlet parameters or nodes. -/
theorem analyticAt_continuedRegCarlsonResolvent_infinity (n : ℕ) (b z : ι → ℂ) :
    AnalyticAt ℂ (fun w => continuedRegCarlsonResolvent n b (fun i => w * z i) 1) 0 := by
  have hd : ((1 : ℂ), fun _ : ι => (0 : ℂ)) ∈ carlsonResolventDomain := by
    intro u hu
    simp [carlsonAffineForm]
  have hm : AnalyticAt ℂ (fun w : ℂ => (b, (1 : ℂ), fun i => w * z i)) 0 :=
    analyticAt_const.prod (analyticAt_const.prod (analyticAt_pi_iff.mpr fun _ =>
      analyticAt_id.mul analyticAt_const))
  exact (analyticOnNhd_continuedRegCarlsonResolvent n (b, 1, fun _ => 0) ⟨mem_univ _, hd⟩).comp_of_eq hm
    (by simp)

/-- Normalizing the resolvent by the leading power identifies it with its
reciprocal chart wherever the original exterior point is nonzero. -/
theorem pow_mul_continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ) {x : ℂ}
    (hx0 : x ≠ 0) (hx : (x, z) ∈ carlsonResolventDomain) :
    x ^ (n + 1) * continuedRegCarlsonResolvent n b z x =
      continuedRegCarlsonResolvent n b (fun i => x⁻¹ * z i) 1 := by
  have h := continuedRegCarlsonResolvent_affine n b z x⁻¹ 0 (inv_ne_zero hx0) hx
  have he : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  simpa only [add_zero, inv_mul_cancel₀ hx0, he, inv_zpow, zpow_neg, inv_inv,
    zpow_natCast, inv_pow] using h.symm

/-- The leading coefficient at infinity of the continued regularized resolvent
is reciprocal Gamma of the total parameter. The limit is in all complex directions. -/
theorem tendsto_continuedRegCarlsonResolvent_infinity (n : ℕ) (b z : ι → ℂ) :
    Tendsto (fun x => x ^ (n + 1) * continuedRegCarlsonResolvent n b z x)
      (cobounded ℂ) (𝓝 ((Gamma (∑ i, b i))⁻¹)) := by
  have h := (analyticAt_continuedRegCarlsonResolvent_infinity n b z).continuousAt.tendsto.comp
    (tendsto_inv₀_cobounded (α := ℂ))
  have hv : continuedRegCarlsonResolvent n b (fun i => (0 : ℂ) * z i) 1 =
      (Gamma (∑ i, b i))⁻¹ := by
    simp only [zero_mul]
    rw [continuedRegCarlsonResolvent_const_nodes n b (by norm_num : (1 : ℂ) ≠ 0)]
    simp
  rw [hv] at h
  apply h.congr'
  have hfar : ∀ᶠ x : ℂ in cobounded ℂ, x ∉ convexHull ℝ (range z) :=
    ((finite_range z).isCompact_convexHull ℝ).isBounded
  have hn : ∀ᶠ x : ℂ in cobounded ℂ, x ≠ 0 := isBounded_singleton
  filter_upwards [hfar, hn] with x hx hx0
  exact (pow_mul_continuedRegCarlsonResolvent n b z hx0
    (mem_carlsonResolventDomain_of_not_mem_convexHull hx)).symm

end Dirichlet
