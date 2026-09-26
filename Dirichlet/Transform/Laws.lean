/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import Dirichlet.ParameterShift

/-!
# Structural laws of the continued Dirichlet transform

Coordinate multiplication, the simplex partition of unity, tangential differentiation,
and permutation act on arbitrary kernels, independently of Carlson's affine substitution.

## Main results

* `Dirichlet.analyticAt_addDirichletUnit`: Parameter shifts are translations, hence entire.
* `Dirichlet.regDirichletIntegral_perm`: Coordinate permutations preserve the native transform
  when parameters and kernel coordinates are permuted together.
* `Dirichlet.IsRegDirichletContinuation.perm`: Permuting a kernel permutes the arguments of its
  entire transform.
* `Dirichlet.IsRegDirichletContinuation.monomial_mul`: Multiplying by a monomial gives its
  Pochhammer factor and the corresponding multi-shift.
* `Dirichlet.IsRegDirichletContinuation.eq_zero_of_coordinate_mul`: A kernel divisible by a
  simplex coordinate has zero transform when that parameter is zero.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Parameter shifts are translations, hence entire. -/
theorem analyticAt_addDirichletUnit (i : ι) (b : ι → ℂ) :
    AnalyticAt ℂ (fun c => addDirichletUnit c i) b := by
  classical
  have h (c : ι → ℂ) : addDirichletUnit c i = c + Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [addDirichletUnit, hk]
  simp_rw [h]
  exact analyticAt_id.add analyticAt_const

/-- The simplex partition of unity gives the sum of the positive unit shifts. -/
theorem regDirichletIntegral_eq_sum_addDirichletUnit
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (f : (ι → ℝ) → ℂ)
    (hf : ContinuousOn (f)
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral b f =
      ∑ i, b i * regDirichletIntegral (addDirichletUnit b i) f := by
  simp_rw [mul_regDirichletIntegral_addDirichletUnit hb]
  unfold regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_mul]
    have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
    rw [hsum, one_mul]
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf)

/-- Multiplying a kernel by a coordinate becomes a unit shift of its entire transform. -/
theorem IsRegDirichletContinuation.coordinate_mul {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (i : ι) :
    IsRegDirichletContinuation (fun u => (u i : ℂ) * g u)
      (fun b => b i * F (addDirichletUnit b i)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro b _
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).mul
      ((hF.1 _ (mem_univ _)).comp_of_eq (analyticAt_addDirichletUnit i b) rfl)
  · dsimp only
    rw [hF.eq_native (addDirichletUnit_mem_mvBetaConvergent hb i),
      mul_regDirichletIntegral_addDirichletUnit hb]

/-- The entire transform satisfies the simplex sum-shift identity. -/
theorem IsRegDirichletContinuation.sum_shift {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) (b : ι → ℂ) :
    F b = ∑ i, b i * F (addDirichletUnit b i) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hF.1 ?_ ?_) b
  · intro c _
    exact Finset.analyticAt_fun_sum _ fun i _ => (hF.coordinate_mul i).1 c (mem_univ _)
  · intro c hc
    simp_rw [hF.eq_native hc,
      hF.eq_native (addDirichletUnit_mem_mvBetaConvergent hc _)]
    exact regDirichletIntegral_eq_sum_addDirichletUnit hc g hg

open scoped Classical in
/-- Tangential differentiation becomes a difference of negative parameter shifts.
The hypotheses concern only the kernel and its derivative on the closed simplex. -/
theorem IsRegDirichletContinuation.tangent {g : (ι → ℝ) → ℂ} {F H : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (i : ι) (j : {j : ι // j ≠ i})
    (hH : IsRegDirichletContinuation
      (fun u => fderiv ℝ g u (Pi.single (j : ι) 1 - Pi.single i 1)) H)
    (hg : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, DifferentiableAt ℝ g u)
    (hdg : ContinuousOn (fun u => fderiv ℝ g u (Pi.single (j : ι) 1 - Pi.single i 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) (b : ι → ℂ) :
    H b = F (b - Pi.single i 1) - F (b - Pi.single (j : ι) 1) := by
  have hr : AnalyticOnNhd ℂ (fun c : ι → ℂ => F (c - Pi.single i 1) - F (c - Pi.single (j : ι) 1))
      univ := by
    intro c _
    exact ((hF.1 _ (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl).sub
      ((hF.1 _ (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl)
  apply congrFun (hH.1.eq_of_eventuallyEq hr (z₀ := fun _ => (3 : ℂ)) ?_) b
  have he : ∀ᶠ c : ι → ℂ in nhds (fun _ => (3 : ℂ)), ∀ k, 2 < (c k).re := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply
        k))).eventually_mem
      (by norm_num)
  filter_upwards [he] with c hc
  have hc0 : c ∈ mvBetaConvergent := fun k => lt_trans (by norm_num) (hc k)
  have hlow (k : ι) : c - Pi.single k 1 ∈ mvBetaConvergent := by
    intro l
    by_cases hl : l = k
    · subst l; simp only [Pi.sub_apply, Pi.single_eq_same, sub_re, one_re]; linarith [hc k]
    · simpa [Pi.single_eq_of_ne hl] using hc0 l
  rw [hH.eq_native hc0, hF.eq_native (hlow i), hF.eq_native (hlow j)]
  exact regDirichletIntegral_tangent_ibp i j c hc hg hdg

/-- Coordinate permutations preserve the native transform when parameters and kernel
coordinates are permuted together. -/
theorem regDirichletIntegral_perm (b : ι → ℂ) (g : (ι → ℝ) → ℂ) (σ : Equiv.Perm ι) :
    regDirichletIntegral (b ∘ σ) (fun u => g (u ∘ σ.symm)) = regDirichletIntegral b g := by
  unfold regDirichletIntegral
  rw [← integral_stdSimplex_comp_perm σ
    (fun u => regDirichletDensity (b ∘ σ) u * g (u ∘ σ.symm))]
  apply integral_stdSimplex_congr
  intro u _
  simp [regDirichletDensity_perm, Function.comp_assoc]

/-- Permuting a kernel permutes the arguments of its entire transform. -/
theorem IsRegDirichletContinuation.perm {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (σ : Equiv.Perm ι) :
    IsRegDirichletContinuation (fun u => g (u ∘ σ.symm)) (fun b => F (b ∘ σ.symm)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro b _
    exact (hF.1 _ (mem_univ _)).comp_of_eq
      (analyticAt_pi_iff.mpr fun k =>
        (ContinuousLinearMap.proj (σ.symm k) : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) rfl
  · dsimp only
    rw [hF.eq_native (b := b ∘ σ.symm) (fun k => hb (σ.symm k))]
    simpa [Function.comp_assoc] using (regDirichletIntegral_perm (b ∘ σ.symm) g σ).symm

/-- Multiplying by a monomial gives its Pochhammer factor and the corresponding multi-shift. -/
theorem IsRegDirichletContinuation.monomial_mul {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (m : ι → ℕ) :
    IsRegDirichletContinuation (fun u => (∏ i, (u i : ℂ) ^ m i) * g u)
      (fun b => mvPochhammer b m * F (fun i => b i + m i)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro b _
    have hp : AnalyticAt ℂ (fun c : ι → ℂ => mvPochhammer c m) b := by
      unfold mvPochhammer
      apply Finset.analyticAt_fun_prod
      intro i _
      exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ (m i)))
          _ (mem_univ _)).comp_of_eq
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) rfl
    exact hp.mul ((hF.1 _ (mem_univ _)).comp_of_eq
      (analyticAt_id.add analyticAt_const) rfl)
  · dsimp only
    have hb' : (fun i => b i + (m i : ℂ)) ∈ mvBetaConvergent := by
      intro i
      simp only [add_re, natCast_re]
      exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)
    rw [hF.eq_native hb', regDirichletIntegral_monomial_mul hb]

/-- A kernel divisible by a simplex coordinate has zero transform when that parameter is zero. -/
theorem IsRegDirichletContinuation.eq_zero_of_coordinate_mul
    {g h : (ι → ℝ) → ℂ} {F H : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (hH : IsRegDirichletContinuation h H) (i : ι)
    (hgh : EqOn g (fun u => (u i : ℂ) * h u) (Convexity.StdSimplex.coordinateSet ℝ ι))
    {b : ι → ℂ} (hb : b i = 0) : F b = 0 := by
  have he := (hF.congr hgh).eq (hH.coordinate_mul i)
  simpa [hb] using congrFun he b

end Dirichlet
end
