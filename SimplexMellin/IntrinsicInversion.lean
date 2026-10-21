/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.RadialProfile
public import ToMathlib.Analysis.Fourier.DiagonalSobolev

/-!
# Full-plane inversion at the intrinsic derivative count

The angular factor is constant under diagonal translations in logarithmic coordinates.
Consequently a diagonal derivative of a Schwartz weight times the angular factor
does not consume an additional derivative of the simplex kernel. The anisotropic
Sobolev Fourier criterion in `ToMathlib.Analysis.Fourier.DiagonalSobolev` therefore
gives full-plane absolute inversion for `C^N` boundary kernels when `2N > card ι - 1`.

Both the exponential radial profile and smooth compact radial profiles satisfy this
bound. No face vanishing is required. This is a sufficient threshold, with no claim
about the endpoint or optimality. The earlier stronger-hypothesis interfaces remain valid.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped ContDiff FourierTransform Classical

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- Diagonal translation invariance makes the corresponding angular derivative zero. -/
theorem fderiv_simplexAngle_diagonal_eq_zero [Nonempty ι] {N : ℕ} (hN : 1 ≤ N)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) (y : EuclideanSpace ℝ ι) :
    fderiv ℝ (simplexAngle g) y (WithLp.toLp 2 (fun _ : ι => (1 : ℝ))) = 0 := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have heq : (fun t : ℝ => simplexAngle g (y + t • v)) = fun _ => simplexAngle g y := by
    funext t
    simpa only [neg_smul, sub_neg_eq_add] using simplexAngle_sub_smul_one g y (-t)
  have hz : HasLineDerivAt ℝ (simplexAngle g) 0 y v := by
    change HasDerivAt (fun t : ℝ => simplexAngle g (y + t • v)) 0 0
    rw [heq]
    exact hasDerivAt_const 0 _
  exact (((contDiff_simplexAngle_of_contDiffNear hg).differentiable
    (by exact_mod_cast (show N ≠ 0 by omega)) y).hasFDerivAt.hasLineDerivAt v).unique hz

/-- Schwartz logarithmic weights times finite-regularity angular kernels have an integrable
Fourier transform at the intrinsic sufficient derivative count. -/
theorem integrable_fourier_simplexAngle_smul_schwartz_of_card_sub_one_lt_two_mul [Nonempty ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : ℕ} (hN : Fintype.card ι - 1 < 2 * N) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (S : SchwartzMap (EuclideanSpace ℝ ι) H) :
    Integrable (𝓕 (fun y => simplexAngle g y • S y)) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact S.integrable_fourier_smul_of_bounded_of_diagonal_deriv_eq_zero i₀
    (by simpa [Fintype.card_subtype_compl] using hN)
    (contDiff_simplexAngle_of_contDiffNear hg)
    (fun n hn => exists_bound_iteratedFDeriv_simplexAngle n (hg.of_le hn))
    (fderiv_simplexAngle_diagonal_eq_zero (by omega) hg)

/-- The exponential-profile transform is absolutely integrable on the full positive
vertical plane when `2N > card ι - 1`, including for nonzero boundary values. -/
theorem integrable_simplexMellin_of_contDiffNear_of_card_sub_one_lt_two_mul [Nonempty ι]
    {N : ℕ} (hN : Fintype.card ι - 1 < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  have hF := integrable_fourier_simplexAngle_smul_schwartz_of_card_sub_one_lt_two_mul
    hN hg (expExpSchwartz c hc)
  rw [simplexAngle_smul_expExpSchwartz hc g] at hF
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hg.continuousOn (by fun_prop)),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  refine hF.congr (Filter.Eventually.of_forall fun ξ => ?_)
  apply simplexMellinRadial_exp_eq
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty

/-- Full-plane exponential-profile inversion with the intrinsic sufficient count
`2N > card ι - 1` for kernels with arbitrary boundary values. -/
theorem regDirichletIntegral_inversion_exp_of_contDiffNear_of_card_sub_one_lt_two_mul
    [Nonempty ι] {N : ℕ} (hN : Fintype.card ι - 1 < 2 * N) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hg.continuousOn
    (integrable_simplexMellin_of_contDiffNear_of_card_sub_one_lt_two_mul hN hc hg) hu

/-- Every smooth compact radial profile gives full-plane absolute integrability at
the intrinsic derivative count, allowing arbitrary face values of the kernel. -/
theorem integrable_simplexMellinRadial_of_contDiffNear_of_card_sub_one_lt_two_mul [Nonempty ι]
    {N : ℕ} (hN : Fintype.card ι - 1 < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    Integrable fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_radialLog_one hc hφs hφsupp
  have hF := integrable_fourier_simplexAngle_smul_schwartz_of_card_sub_one_lt_two_mul hN hg S
  rw [hS, simplexAngle_smul_radialLog_one c φ g] at hF
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hg.continuousOn hφs.continuous.continuousOn),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  exact hF

/-- Full-plane inversion with a compact positive smooth radial profile, using
`2N > card ι - 1` derivatives of a kernel with arbitrary boundary values. -/
theorem regDirichletIntegral_inversion_radial_of_contDiffNear_of_card_sub_one_lt_two_mul
    [Nonempty ι] {N : ℕ} (hN : Fintype.card ι - 1 < 2 * N) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) (hφ1 : φ 1 ≠ 0)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = (φ 1)⁻¹ * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellinRadial φ (mellinPlane c ξ) g := by
  have hsupp : HasCompactSupport φ := by
    apply HasCompactSupport.intro isCompact_Icc
    intro t ht
    by_contra hne
    exact ht (hφsupp t hne)
  exact regDirichletIntegral_inversion_radial hc hg.continuousOn hφs.continuous.continuousOn
    (mellinConvergent_of_support_subset_Icc hφs.continuous.continuousOn hr₀ hφsupp _) hφ1
    (integrable_simplexMellinRadial_of_contDiffNear_of_card_sub_one_lt_two_mul
      hN hc hg hφs hsupp) hu

end Dirichlet
