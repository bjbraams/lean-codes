/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Inversion
public import ToMathlib.Analysis.Fourier.Plancherel

/-!
# Plancherel for continuous simplex kernels

Positive simplex weights make every continuous boundary kernel square integrable.
For a radial profile with convergent first and second weighted Mellin integrals,
the logarithmic kernel belongs to `L¹ ∩ L²`. Classical Plancherel, identified with
Mathlib's `L²` isometry through tempered distributions, therefore applies without
any differentiability or face-vanishing assumption.

The abstract inverse Fourier transform recovers the logarithmic kernel in `L²`.
This is distinct from the pointwise simplex inversion formula, which still requires
integrability of the transform. The complete weighted simplex space of measurable
equivalence classes is treated for the exponential profile in `SimplexMellin.WeightedL2`,
by isometric extension from the dense Schwartz core.
-/

open Complex MeasureTheory Set
open scoped FourierTransform

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The radial simplex Mellin transform in `L²`, defined by Fourier transformation in
logarithmic coordinates. It also applies when the native Mellin integral does not converge. -/
def simplexMellinRadialL2 (c : ι → ℝ) (φ : ℝ → ℂ) (g : (ι → ℝ) → ℂ)
    (h₂ : MemLp (radialLog c φ g) 2) : Lp (α := EuclideanSpace ℝ ι) ℂ 2 :=
  𝓕 (h₂.toLp (radialLog c φ g))

/-- The `L²` radial transform preserves the norm of the logarithmic kernel. -/
theorem norm_simplexMellinRadialL2 (c : ι → ℝ) (φ : ℝ → ℂ) (g : (ι → ℝ) → ℂ)
    (h₂ : MemLp (radialLog c φ g) 2) :
    ‖simplexMellinRadialL2 c φ g h₂‖ = ‖h₂.toLp (radialLog c φ g)‖ :=
  Lp.norm_fourier_eq _

/-- Inversion of the radial transform in `L²`, with no `L¹` or smoothness requirement. -/
theorem fourierInv_simplexMellinRadialL2 (c : ι → ℝ) (φ : ℝ → ℂ) (g : (ι → ℝ) → ℂ)
    (h₂ : MemLp (radialLog c φ g) 2) :
    𝓕⁻ (simplexMellinRadialL2 c φ g h₂) = h₂.toLp (radialLog c φ g) :=
  FourierTransform.fourierInv_fourier_eq _

/-- Stability of the `L²` radial transform: distances between transforms equal distances
between their logarithmic kernels. This includes nonsmooth and nonintegrable kernels. -/
theorem dist_simplexMellinRadialL2 (c : ι → ℝ) (φ : ℝ → ℂ) (g₁ g₂ : (ι → ℝ) → ℂ)
    (h₁ : MemLp (radialLog c φ g₁) 2) (h₂ : MemLp (radialLog c φ g₂) 2) :
    dist (simplexMellinRadialL2 c φ g₁ h₁) (simplexMellinRadialL2 c φ g₂ h₂) =
      dist (h₁.toLp (radialLog c φ g₁)) (h₂.toLp (radialLog c φ g₂)) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).isometry.dist_eq _ _

/-- On integrable logarithmic kernels, the `L²` radial transform agrees almost everywhere
with the native simplex Mellin transform on the vertical plane. -/
theorem simplexMellinRadialL2_ae_eq [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    (h₁ : Integrable (radialLog c φ g)) (h₂ : MemLp (radialLog c φ g) 2) :
    simplexMellinRadialL2 c φ g h₂ =ᵐ[volume]
      (fun ξ : EuclideanSpace ℝ ι => simplexMellinRadial φ (mellinPlane c ξ) g) := by
  have h := Real.fourier_toLp_ae_eq h₁ h₂
  exact h.mono fun ξ hξ => hξ.trans (fourier_radialLog hc hg hφ ξ)

/-- The logarithmic kernel of a continuous boundary kernel belongs to `L²` whenever
the squared radial profile has a convergent Mellin integral at twice the total abscissa. -/
theorem memLp_radialLog [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    (hφ₂ : MellinConvergent (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
      (∑ i, ((2 * c i : ℝ) : ℂ))) :
    MemLp (radialLog c φ g) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_radialLog c hg hφ).aestronglyMeasurable).mpr
  have h := integrable_radialLog (c := fun i => 2 * c i) (fun i => mul_pos zero_lt_two (hc i))
    (g := fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ))
    (φ := fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
    (continuous_ofReal.comp_continuousOn (hg.norm.pow 2))
    (continuous_ofReal.comp_continuousOn (hφ.norm.pow 2)) hφ₂
  have heq : (fun y => ((‖radialLog c φ g y‖ ^ 2 : ℝ) : ℂ)) =
      radialLog (fun i => 2 * c i) (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
        (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) :=
    funext (ofReal_norm_sq_radialLog c φ g)
  rw [← heq] at h
  simpa only [RCLike.re_to_complex, ofReal_re] using h.re

/-- The radial simplex Mellin transform of a continuous boundary kernel is square
integrable on every positive vertical plane, under first and second radial convergence. -/
theorem memLp_simplexMellinRadial [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    (hφ₁ : MellinConvergent φ (∑ i, (c i : ℂ)))
    (hφ₂ : MellinConvergent (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
      (∑ i, ((2 * c i : ℝ) : ℂ))) :
    MemLp (fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g) 2 := by
  have h := (Real.memLp_fourier_of_integrable_memLp
    (integrable_radialLog hc hg hφ hφ₁) (memLp_radialLog hc hg hφ hφ₂)).comp_measurePreserving
      (PiLp.volume_preserving_toLp ι)
  have heq : (𝓕 (radialLog c φ g) ∘ WithLp.toLp 2) =
      (fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g) := by
    funext ξ
    dsimp only [Function.comp_apply]
    rw [fourier_radialLog hc hg hφ]
  rwa [heq] at h

/-- Plancherel for continuous kernels on the closed simplex. Only convergence of the
first and second radial Mellin integrals is required; the Fourier transform may fail to be `L¹`. -/
theorem integral_norm_sq_simplexMellinRadial_of_continuous [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    (hφ₁ : MellinConvergent φ (∑ i, (c i : ℂ)))
    (hφ₂ : MellinConvergent (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
      (∑ i, ((2 * c i : ℝ) : ℂ))) :
    ((∫ ξ : ι → ℝ, ‖simplexMellinRadial φ (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ)) (fun i => ((2 * c i : ℝ) : ℂ))
        (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) :=
  integral_norm_sq_simplexMellinRadial_of_memLp hc hg hφ
    (integrable_radialLog hc hg hφ hφ₁) (memLp_radialLog hc hg hφ hφ₂)

/-- Continuous profiles supported in a compact positive interval satisfy Plancherel for
every continuous boundary kernel. Neither factor needs to be differentiable. -/
theorem integral_norm_sq_simplexMellinRadial_of_support_subset_Icc [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    ((∫ ξ : ι → ℝ, ‖simplexMellinRadial φ (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ)) (fun i => ((2 * c i : ℝ) : ℂ))
        (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) := by
  apply integral_norm_sq_simplexMellinRadial_of_continuous hc hg hφ
    (mellinConvergent_of_support_subset_Icc hφ hr₀ hsupp _)
  refine mellinConvergent_of_support_subset_Icc
    (φ := fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
    (r₁ := r₁) (continuous_ofReal.comp_continuousOn (hφ.norm.pow 2)) hr₀ (fun t ht => ?_) _
  apply hsupp t
  intro hzero
  simp [hzero] at ht

/-- The exponential profile has a convergent Mellin integral in the positive half-plane. -/
private theorem mellinConvergent_exp_neg {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t => ((Real.exp (-t) : ℝ) : ℂ)) s := by
  simpa [MellinConvergent, smul_eq_mul, mul_comm] using GammaIntegral_convergent hs

/-- The squared exponential profile has a convergent Mellin integral in the positive
half-plane, by dilation of the Gamma integral. -/
private theorem mellinConvergent_norm_sq_exp_neg {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t => ((‖((Real.exp (-t) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)) s := by
  have h := (MellinConvergent.comp_mul_left (a := 2) (by norm_num)).mpr
    (mellinConvergent_exp_neg hs)
  convert h using 1
  funext t
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 2
  ring

/-- The exponential logarithmic kernel of every continuous boundary kernel is integrable. -/
theorem integrable_radialLog_exp [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Integrable (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) := by
  apply integrable_radialLog hc hg (by fun_prop)
  apply mellinConvergent_exp_neg
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty

/-- The exponential logarithmic kernel of every continuous boundary kernel belongs to `L²`. -/
theorem memLp_radialLog_exp [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    MemLp (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) 2 := by
  apply memLp_radialLog hc hg (by fun_prop)
  apply mellinConvergent_norm_sq_exp_neg
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => mul_pos zero_lt_two (hc i)) Finset.univ_nonempty

/-- Every continuous kernel on the closed simplex has a square-integrable exponential
Mellin transform on positive vertical planes, including kernels nonzero at the faces. -/
theorem memLp_simplexMellin [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    MemLp (fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g) 2 := by
  have hsum {d : ι → ℝ} (hd : ∀ i, 0 < d i) : 0 < (∑ i, (d i : ℂ)).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa using hd i) Finset.univ_nonempty
  have h := memLp_simplexMellinRadial hc hg (φ := fun t => ((Real.exp (-t) : ℝ) : ℂ))
    (by fun_prop) (mellinConvergent_exp_neg (hsum hc))
    (mellinConvergent_norm_sq_exp_neg (hsum fun i => mul_pos zero_lt_two (hc i)))
  have heq (ξ : ι → ℝ) :
      simplexMellinRadial (fun t => ((Real.exp (-t) : ℝ) : ℂ)) (mellinPlane c ξ) g =
        simplexMellin (mellinPlane c ξ) g := by
    apply simplexMellinRadial_exp_eq
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty
  simpa only [heq] using h

/-- Exponential-profile Plancherel for every continuous kernel on the closed simplex.
This requires no derivatives, boundary vanishing, or `L¹` convergence on the vertical plane. -/
theorem integral_norm_sq_simplexMellin_of_continuous [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ((∫ ξ : ι → ℝ, ‖simplexMellin (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((Real.exp (-t) ^ 2 : ℝ) : ℂ))
        (fun i => ((2 * c i : ℝ) : ℂ)) (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) := by
  have hsum {d : ι → ℝ} (hd : ∀ i, 0 < d i) : 0 < (∑ i, (d i : ℂ)).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa using hd i) Finset.univ_nonempty
  have h := integral_norm_sq_simplexMellinRadial_of_continuous hc hg
    (φ := fun t => ((Real.exp (-t) : ℝ) : ℂ)) (by fun_prop)
    (mellinConvergent_exp_neg (hsum hc))
    (mellinConvergent_norm_sq_exp_neg (hsum fun i => mul_pos zero_lt_two (hc i)))
  have heq (ξ : ι → ℝ) :
      simplexMellinRadial (fun t => ((Real.exp (-t) : ℝ) : ℂ)) (mellinPlane c ξ) g =
        simplexMellin (mellinPlane c ξ) g := by
    apply simplexMellinRadial_exp_eq
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty
  simpa only [heq, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h

end Dirichlet
