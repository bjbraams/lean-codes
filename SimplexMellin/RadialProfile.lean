/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.FiniteRegularity
public import ToMathlib.Analysis.SchwartzSumExp

/-!
# General radial profiles for kernels with nonzero boundary values

For a smooth compactly supported profile `φ`, the logarithmic radial weight is Schwartz:
write it as the double-exponential Schwartz weight times
`ψ (∑ exp y i)`, where `ψ(t) = exp(t) φ(t)` is Schwartz and its composition has temperate
growth (`ToMathlib.Analysis.SchwartzSumExp`).

Multiplication by the angular kernel gives integrable derivatives through order `N`
for kernels `C^N` near the closed simplex. If `2N > card ι`, the radial Mellin transform is
integrable on each positive vertical plane. Interior inversion holds for profiles supported
in a compact positive interval and nonzero at `1`. For smooth boundary kernels,
the logarithmic kernel is Schwartz and the general radial Plancherel identity follows.
No vanishing of the kernel at the simplex faces is assumed.

## Main results

* `integrable_simplexMellinRadial_of_contDiffNear_of_card_lt_two_mul`.
* `regDirichletIntegral_inversion_radial_of_contDiffNear_of_card_lt_two_mul`.
* `integral_norm_sq_simplexMellinRadial_of_smoothNear`.
-/

open Complex Real MeasureTheory Set
open MvMellin
open scoped ContDiff FourierTransform
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Compactly supported smooth radial profiles give a Schwartz logarithmic radial weight. -/
theorem exists_schwartzMap_radialLog_one {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ ι) ℂ, ⇑S = radialLog c φ (fun _ => 1) := by
  let ψ : SchwartzMap ℝ ℂ := (hφsupp.mul_left (f := fun t => ((Real.exp t : ℝ) : ℂ))).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul hφs)
  have hψ (t : ℝ) : ψ t = ((Real.exp t : ℝ) : ℂ) * φ t := rfl
  have htemp := ψ.hasTemperateGrowth_comp_sum_exp (ι := ι)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y => ψ (∑ i, Real.exp (y i)))
    (expExpSchwartz c hc), ?_⟩
  funext y
  rw [SchwartzMap.smulLeftCLM_apply_apply htemp, expExpSchwartz_apply, hψ]
  simp only [radialLog, smul_eq_mul, mul_one, piExp, real_smul]
  have he : ((Real.exp (∑ i, Real.exp (y i)) : ℝ) : ℂ) *
      ((Real.exp (∑ i, (c i * y i - Real.exp (y i))) : ℝ) : ℂ) =
      ((Real.exp (∑ i, c i * y i) : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add, Finset.sum_sub_distrib]
    congr 2
    ring
  calc
    (((Real.exp (∑ i, Real.exp (y i)) : ℝ) : ℂ) * φ (∑ i, Real.exp (y i))) *
        ((Real.exp (∑ i, (c i * y i - Real.exp (y i))) : ℝ) : ℂ) =
      (((Real.exp (∑ i, Real.exp (y i)) : ℝ) : ℂ) *
        ((Real.exp (∑ i, (c i * y i - Real.exp (y i))) : ℝ) : ℂ)) *
          φ (∑ i, Real.exp (y i)) := by ring
    _ = _ := by rw [he]

/-- An arbitrary logarithmic kernel factors into its angular part and its radial weight. -/
theorem simplexAngle_smul_radialLog_one (c : ι → ℝ) (φ : ℝ → ℂ) (g : (ι → ℝ) → ℂ) :
    (fun y => simplexAngle g y • radialLog c φ (fun _ => 1) y) = radialLog c φ g := by
  funext y
  simp only [simplexAngle, radialLog, smul_eq_mul, mul_one, real_smul]
  ring

/-- Derivatives through order `N` of a compact-profile logarithmic kernel are integrable
for `C^N` kernels near the closed simplex, without boundary vanishing. -/
theorem integrable_iteratedFDeriv_radialLog_of_contDiffNear [Nonempty ι]
    {N n : ℕ} {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) (hn : n ≤ N) :
    Integrable (iteratedFDeriv ℝ n (radialLog c φ g)) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_radialLog_one hc hφs hφsupp
  rw [← simplexAngle_smul_radialLog_one c φ g, ← hS]
  exact S.integrable_iteratedFDeriv_smul_of_bounded
    (contDiff_simplexAngle_of_contDiffNear hg)
    (fun k hk => exists_bound_iteratedFDeriv_simplexAngle k (hg.of_le hk)) hn

/-- Derivatives through order `N` of the compact-profile logarithmic kernel belong to
`L²` for kernels `C^N` near the closed simplex, without any face vanishing. -/
theorem memLp_iteratedFDeriv_radialLog_of_contDiffNear [Nonempty ι]
    {N n : ℕ} {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) (hn : n ≤ N) :
    MemLp (iteratedFDeriv ℝ n (radialLog c φ g)) 2 := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_radialLog_one hc hφs hφsupp
  rw [← simplexAngle_smul_radialLog_one c φ g, ← hS]
  exact S.memLp_two_iteratedFDeriv_smul_of_bounded
    (contDiff_simplexAngle_of_contDiffNear hg)
    (fun k hk => exists_bound_iteratedFDeriv_simplexAngle k (hg.of_le hk)) hn

/-- More than half the number of coordinates many derivatives suffice for vertical-plane
integrability with every smooth compact radial profile, allowing nonzero face values. -/
theorem integrable_simplexMellinRadial_of_contDiffNear_of_card_lt_two_mul [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    Integrable fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_radialLog_one hc hφs hφsupp
  have hsm : ContDiff ℝ N (radialLog c φ g) := by
    rw [← simplexAngle_smul_radialLog_one c φ g, ← hS]
    exact (contDiff_simplexAngle_of_contDiffNear hg).smul (S.smooth N)
  have hI : Integrable (radialLog c φ g) := by
    apply (integrable_norm_iff hsm.continuous.aestronglyMeasurable).mp
    simpa only [norm_iteratedFDeriv_zero] using
      (integrable_iteratedFDeriv_radialLog_of_contDiffNear hc hg hφs hφsupp (n := 0)
        (Nat.zero_le N)).norm
  have hF := Real.integrable_fourier_of_memLp_iteratedFDeriv
    (by simpa using hN) hsm hI
    (fun n hn => memLp_iteratedFDeriv_radialLog_of_contDiffNear hc hg hφs hφsupp hn)
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hg.continuousOn hφs.continuous.continuousOn),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  exact hF
/-- More than `card ι` derivatives suffice for vertical-plane integrability with any smooth
compactly supported radial profile, including for kernels nonzero on the faces. -/
theorem integrable_simplexMellinRadial_of_contDiffNear [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    Integrable fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g :=
  integrable_simplexMellinRadial_of_contDiffNear_of_card_lt_two_mul (by omega) hc hg hφs hφsupp

/-- A smooth boundary kernel and any compactly supported smooth radial profile give a
Schwartz logarithmic kernel. -/
theorem exists_schwartzMap_radialLog_of_smoothNear [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ ι) ℂ, ⇑S = radialLog c φ g := by
  obtain ⟨A, hA⟩ := exists_schwartzMap_radialLog_one hc hφs hφsupp
  have htemp := hasTemperateGrowth_simplexAngle_of_smoothNear hg
  refine ⟨SchwartzMap.smulLeftCLM ℂ (simplexAngle g) A, ?_⟩
  funext y
  rw [SchwartzMap.smulLeftCLM_apply_apply htemp]
  change simplexAngle g y • (⇑A) y = _
  rw [hA]
  exact congrFun (simplexAngle_smul_radialLog_one c φ g) y

/-- Sobolev-improved inversion with a compact positive smooth profile and `2N > card ι`;
the boundary kernel may have arbitrary face values. -/
theorem regDirichletIntegral_inversion_radial_of_contDiffNear_of_card_lt_two_mul [Nonempty ι] {N :
  ℕ}
    (hN : Fintype.card ι < 2 * N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
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
    (integrable_simplexMellinRadial_of_contDiffNear_of_card_lt_two_mul hN hc hg hφs hsupp) hu

/-- Finite-regularity inversion for a smooth profile supported in a compact positive interval;
the kernel is allowed arbitrary values on the simplex faces. -/
theorem regDirichletIntegral_inversion_radial_of_contDiffNear [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι < N) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) {φ : ℝ → ℂ}
    (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) (hφ1 : φ 1 ≠ 0)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = (φ 1)⁻¹ * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellinRadial φ (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion_radial_of_contDiffNear_of_card_lt_two_mul (by omega)
    hc hg hφs hr₀ hφsupp hφ1 hu

/-- General compact-profile Plancherel for all smooth boundary kernels. -/
theorem integral_norm_sq_simplexMellinRadial_of_smoothNear [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) (hφsupp : HasCompactSupport φ) :
    ((∫ ξ : ι → ℝ, ‖simplexMellinRadial φ (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ)) (fun i => ((2 * c i : ℝ) : ℂ))
        (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) :=
  integral_norm_sq_simplexMellinRadial_of_schwartz hc hg.continuousOn hφs.continuous.continuousOn
    (exists_schwartzMap_radialLog_of_smoothNear hc hg hφs hφsupp)

end Dirichlet

end
