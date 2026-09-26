/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.Basic
public import Carlson.T.SlitSeries
public import Dirichlet.Transform.Series

/-!
# The principal slit-plane continuation of Carlson's T-function

The normally convergent negative-R series defines a branch on the full product slit
plane, beyond the convex-hull domain of the native integral. Native agreement requires
the whole hull to remain in the slit plane. The native-domain function `regCarlsonT`
and this principal branch are therefore kept distinct.

## Main results

* `Carlson.regCarlsonTSlit_eq_integral`: native agreement on hull-admissible slit tuples.
* `Carlson.isJointRegCarlsonContinuationOn_regCarlsonTSlit`: joint continuation in all
  parameters and slit-plane nodes.
* `Carlson.regCarlsonTSlit_eq_regCarlsonT`: compatibility with the native-domain continuation.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

open Complex Dirichlet Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The principal T-series agrees with the native integral when the node convex hull
stays in the slit plane and the Dirichlet parameters have positive real parts. -/
theorem regCarlsonTSlit_eq_integral {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : convexHull ℝ (range z) ⊆ slitPlane) :
    regCarlsonTSlit b z = regCarlsonTIntegral b z := by
  have hnz : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, carlsonAffineForm z u ≠ 0 :=
    fun u hu => slitPlane_ne_zero (hz (carlsonAffineForm_mem_convexHull z hu))
  have hcont : ContinuousOn (fun u => (carlsonAffineForm z u)⁻¹)
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.inv₀ hnz
  obtain ⟨C, hC⟩ := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).bddAbove_image hcont.norm
  let g : ℕ → (ι → ℝ) → ℂ := fun n u =>
    (n.factorial : ℂ)⁻¹ * (carlsonAffineForm z u)⁻¹ ^ n
  have hs := hasSum_regDirichletIntegral hb g
    (fun u => carlsonTKernel (carlsonAffineForm z u))
    (fun n => (max C 0) ^ n / n.factorial)
    (fun n => continuousOn_const.mul (hcont.pow n))
    (Real.summable_pow_div_factorial (max C 0)) (fun n u hu => ?_) (fun u hu => ?_)
  · have heq : ∀ n : ℕ, regDirichletIntegral b (g n) =
        (n.factorial : ℂ)⁻¹ * regCarlsonR (-(n : ℂ)) b z := by
      intro n
      rw [regCarlsonR_eq_regCarlsonRIntegral_of_convexHull _ hb hz]
      simp only [g, regCarlsonRIntegral, regCarlsonDirichletAverage, cpow_neg,
        cpow_natCast, ← inv_pow]
      exact regDirichletIntegral_smul b _ _
    simpa only [heq, regCarlsonTSlit, regCarlsonTIntegral, regCarlsonDirichletAverage]
      using hs.tsum_eq
  · simp only [g, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    rw [div_eq_mul_inv, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (by simpa only [norm_inv] using
        (hC (mem_image_of_mem _ hu)).trans (le_max_left _ _)) n
  · simpa only [g, carlsonTKernel, Complex.exp_eq_exp_ℂ, div_eq_mul_inv, mul_comm] using
      NormedSpace.expSeries_div_hasSum_exp (carlsonAffineForm z u)⁻¹

/-- The principal T-branch is a joint continuation on the full product slit plane,
with native agreement on the hull-admissible subset. -/
theorem isJointRegCarlsonContinuationOn_regCarlsonTSlit :
    IsJointRegCarlsonContinuationOn slitPlane carlsonTKernel
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonTSlit p.1 p.2) := by
  refine ⟨?_, fun z hz b hb => regCarlsonTSlit_eq_integral hb hz⟩
  intro p hp
  exact analyticAt_regCarlsonTSlit_comp analyticAt_fst analyticAt_snd (fun i => hp ⟨i, rfl⟩)

/-- On hull-admissible slit tuples the principal and native-domain T-continuations
agree at every Dirichlet parameter, including exceptional total parameters. -/
theorem regCarlsonTSlit_eq_regCarlsonT (b : ι → ℂ) {z : ι → ℂ}
    (hz : convexHull ℝ (range z) ⊆ slitPlane) : regCarlsonTSlit b z = regCarlsonT b z := by
  have hT : z ∈ carlsonTVariableDomain := fun h => slitPlane_ne_zero (hz h) rfl
  exact congrFun ((isJointRegCarlsonContinuationOn_regCarlsonTSlit.isRegCarlsonContinuation hz).eq
    (isRegCarlsonTContinuation_regCarlsonT hT)) b

/-- The ordinary principal T-branch. Gamma-pole values are totalized, not removable
limits of the ordinary function. -/
def carlsonTSlit (b z : ι → ℂ) : ℂ := Gamma (∑ i, b i) * regCarlsonTSlit b z

/-- The ordinary principal T-branch agrees with its native integral on admissible tuples. -/
theorem carlsonTSlit_eq_integral {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : convexHull ℝ (range z) ⊆ slitPlane) : carlsonTSlit b z = carlsonTIntegral b z := by
  rw [carlsonTSlit, carlsonTIntegral, regCarlsonTSlit_eq_integral hb hz]

/-- The native-domain T-continuation also vanishes for an empty node index type. -/
@[simp] theorem regCarlsonT_eq_zero_of_isEmpty [IsEmpty ι] (b z : ι → ℂ) :
    regCarlsonT b z = 0 := by
  have hz : convexHull ℝ (range z) ⊆ slitPlane := by
    rw [range_eq_empty z, convexHull_empty]
    exact empty_subset _
  rw [← regCarlsonTSlit_eq_regCarlsonT b hz, regCarlsonTSlit_eq_zero_of_isEmpty]

end Carlson
