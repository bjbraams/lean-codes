/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Continuation
public import Carlson.L.Deriv
public import Carlson.R.SlitIntegral

/-!
# Native power-logarithm averages on the slit plane

The slit L-function is the domain-aware continuation of `w ^ t * log w`.
Native-integral agreement and the exponent-derivative relation now hold whenever
the entire node convex hull lies in the slit plane. Merely asking that each node
avoid the cut would be insufficient. All statements allow empty index types.

## Main results

* `Carlson.isJointRegCarlsonContinuationOn_regCarlsonL`: The slit L-function is the domain-aware
  continuation of the power-logarithm kernel.
* `Carlson.isRegCarlsonContinuation_regCarlsonL_of_convexHull`: Entire-parameter
  characterization at every native-admissible slit tuple.
* `Carlson.regCarlsonL_eq_integral_of_convexHull`: Native L-integral agreement wherever the
  whole node convex hull avoids the cut.
* `Carlson.carlsonL_eq_integral_of_convexHull`: Native agreement with the ordinary
  L-normalization.
* `Carlson.hasDerivAt_regCarlsonRIntegral_L_of_convexHull`: Differentiating the native
  R-integral inserts the logarithm on the full convex-hull-admissible node domain, with no
  right-half-plane restriction.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The slit L-function is the domain-aware continuation of the power-logarithm kernel. -/
theorem isJointRegCarlsonContinuationOn_regCarlsonL (t : ℂ) :
    IsJointRegCarlsonContinuationOn slitPlane (carlsonLKernel t)
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonL t p.1 p.2) := by
  apply isJointRegCarlsonContinuationOn_of_convex_seed isOpen_slitPlane
    starConvex_one_slitPlane isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (show (1 : ℂ) ∈ carlsonRightHalfPlane by simp [carlsonRightHalfPlane])
    carlsonRightHalfPlane_subset_slitPlane (analyticOnNhd_carlsonLKernel t)
  · intro p hp
    exact analyticAt_regCarlsonL_comp analyticAt_const analyticAt_fst analyticAt_snd
      (fun i => hp ⟨i, rfl⟩)
  · intro z hz b hb
    exact regCarlsonL_eq_regCarlsonLIntegral t hb (fun i => hz ⟨i, rfl⟩)

/-- Entire-parameter characterization at every native-admissible slit tuple. -/
theorem isRegCarlsonContinuation_regCarlsonL_of_convexHull (t : ℂ)
    {z : ι → ℂ} (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    IsRegCarlsonContinuation (carlsonLKernel t) z (fun b => regCarlsonL t b z) :=
  (isJointRegCarlsonContinuationOn_regCarlsonL t).isRegCarlsonContinuation hz

/-- Native L-integral agreement wherever the whole node convex hull avoids the cut. -/
theorem regCarlsonL_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    regCarlsonL t b z = regCarlsonLIntegral t b z :=
  (isRegCarlsonContinuation_regCarlsonL_of_convexHull t hz).eq_native hb

/-- Native agreement with the ordinary L-normalization. -/
theorem carlsonL_eq_integral_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    carlsonL t b z = carlsonLIntegral t b z := by
  rw [carlsonL, carlsonLIntegral, regCarlsonL_eq_integral_of_convexHull t hb hz]

/-- Differentiating the native R-integral inserts the logarithm on the full
convex-hull-admissible node domain, with no right-half-plane restriction. -/
theorem hasDerivAt_regCarlsonRIntegral_L_of_convexHull (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    HasDerivAt (fun s => regCarlsonRIntegral s b z) (regCarlsonLIntegral t b z) t := by
  have heq : (fun s => regCarlsonRIntegral s b z) = (fun s => regCarlsonR s b z) :=
    funext fun s => (regCarlsonR_eq_regCarlsonRIntegral_of_convexHull s hb hz).symm
  rw [heq, ← regCarlsonL_eq_integral_of_convexHull t hb hz]
  exact hasDerivAt_regCarlsonR_L t b
    (fun i => hz (subset_convexHull ℝ (Set.range z) ⟨i, rfl⟩))

end Carlson
end
