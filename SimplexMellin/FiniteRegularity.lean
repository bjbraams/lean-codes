/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Schwartz
public import ToMathlib.Analysis.Fourier.Sobolev

/-!
# Finite-regularity inversion for boundary kernels

For a kernel with `N` continuous derivatives near the closed simplex, every angular
derivative up to order `N` is bounded. Multiplication by the double-exponential Schwartz
weight makes these derivatives integrable and square integrable. The Sobolev Fourier
criterion therefore gives absolute inversion when `2N > card ι`, without vanishing at
the faces. The earlier `N > card ι` interfaces are retained as wrappers.

This is a sufficient differentiability threshold, not a claim of optimality.

## Main results

* `integrable_simplexMellin_of_contDiffNear_of_card_lt_two_mul`.
* `regDirichletIntegral_inversion_exp_of_contDiffNear_of_card_lt_two_mul`.
* `memLp_iteratedFDeriv_radialLog_exp_of_contDiffNear`.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped ContDiff FourierTransform

@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Finite differentiability near the closed simplex gives the same regularity in
logarithmic angular coordinates. -/
theorem contDiff_simplexAngle_of_contDiffNear [Nonempty ι] {N : ℕ}
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    ContDiff ℝ N (simplexAngle g) := by
  obtain ⟨U, hU, hΔ, hgs⟩ := hg
  exact hgs.comp_contDiff (contDiff_simplexSoftmax.of_le (by simp))
    fun y => hΔ (simplexSoftmax_mem y)

/-- The exponential-profile logarithmic kernel factors into its angular part and the
universal double-exponential Schwartz weight, for arbitrary kernels. -/
theorem simplexAngle_smul_expExpSchwartz {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : (ι → ℝ) → ℂ) :
    (fun y => simplexAngle g y • expExpSchwartz c hc y) =
      radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g := by
  funext y
  rw [expExpSchwartz_apply]
  simp only [radialLog, simplexAngle, smul_eq_mul, piExp]
  rw [← Complex.coe_smul, smul_eq_mul, Finset.sum_sub_distrib, sub_eq_add_neg, Real.exp_add,
    ofReal_mul]
  ring

/-- The logarithmic kernel with exponential radial profile inherits finite smoothness near
the closed simplex. -/
theorem contDiff_radialLog_exp_of_contDiffNear [Nonempty ι] {N : ℕ}
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) :
    ContDiff ℝ N (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) := by
  rw [← simplexAngle_smul_expExpSchwartz hc g]
  exact (contDiff_simplexAngle_of_contDiffNear hg).smul ((expExpSchwartz c hc).smooth N)

/-- Derivatives of the exponential-profile logarithmic kernel through order `N` are
integrable for a `C^N` kernel near the closed simplex, including nonzero boundary values. -/
theorem integrable_iteratedFDeriv_radialLog_exp_of_contDiffNear [Nonempty ι]
    {N n : ℕ} {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (hn : n ≤ N) :
    Integrable (iteratedFDeriv ℝ n
      (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g)) := by
  rw [← simplexAngle_smul_expExpSchwartz hc g]
  exact (expExpSchwartz c hc).integrable_iteratedFDeriv_smul_of_bounded
    (contDiff_simplexAngle_of_contDiffNear hg)
    (fun k hk => exists_bound_iteratedFDeriv_simplexAngle k (hg.of_le hk)) hn

/-- Derivatives of the logarithmic kernel through order `N` belong to `L²` for `C^N`
boundary kernels. This gives the Sobolev improvement of the inversion threshold. -/
theorem memLp_iteratedFDeriv_radialLog_exp_of_contDiffNear [Nonempty ι]
    {N n : ℕ} {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (hn : n ≤ N) :
    MemLp (iteratedFDeriv ℝ n
      (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g)) 2 := by
  rw [← simplexAngle_smul_expExpSchwartz hc g]
  exact (expExpSchwartz c hc).memLp_two_iteratedFDeriv_smul_of_bounded
    (contDiff_simplexAngle_of_contDiffNear hg)
    (fun k hk => exists_bound_iteratedFDeriv_simplexAngle k (hg.of_le hk)) hn

/-- More than half the number of coordinates many continuous derivatives suffice for
absolute integrability on positive vertical planes. This is a sufficient Sobolev bound. -/
theorem integrable_simplexMellin_of_contDiffNear_of_card_lt_two_mul [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  have hsm : ContDiff ℝ N (radialLog c φ g) := contDiff_radialLog_exp_of_contDiffNear hc hg
  have hF := Real.integrable_fourier_of_memLp_iteratedFDeriv
    (by simpa using hN) hsm (integrable_radialLog_exp hc hg.continuousOn)
    (fun n hn => memLp_iteratedFDeriv_radialLog_exp_of_contDiffNear hc hg hn)
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hg.continuousOn (by fun_prop)),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  refine hF.congr (Filter.Eventually.of_forall fun ξ => ?_)
  apply simplexMellinRadial_exp_eq
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty

/-- More than `card ι` continuous derivatives near the closed simplex suffice for
integrability of the exponential-profile transform on every positive vertical plane. -/
theorem integrable_simplexMellin_of_contDiffNear [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g :=
  integrable_simplexMellin_of_contDiffNear_of_card_lt_two_mul (by omega) hc hg

/-- Interior inversion with the exponential profile for `C^N` kernels near the closed
simplex, with `N > card ι`. Boundary vanishing is not required. -/
theorem regDirichletIntegral_inversion_exp_of_contDiffNear [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hg.continuousOn
    (integrable_simplexMellin_of_contDiffNear hN hc hg) hu

/-- Interior inversion for `C^N` boundary kernels with `2N > card ι`, using the
exponential profile. The endpoint and optimality are not asserted. -/
theorem regDirichletIntegral_inversion_exp_of_contDiffNear_of_card_lt_two_mul
    [Nonempty ι] {N : ℕ} (hN : Fintype.card ι < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hg.continuousOn
    (integrable_simplexMellin_of_contDiffNear_of_card_lt_two_mul hN hc hg) hu

end Dirichlet
end
