/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Bridge
public import Mathlib.Analysis.Fourier.Inversion
public import TauCeti.Analysis.Fourier.Integrable
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Inversion of the regularized Dirichlet transform

A kernel continuous on the standard simplex is recovered at each interior point from its
regularized Dirichlet transform on a vertical plane `Re b = c` (all `c i > 0`):

`g u = e · ∫_{ξ ∈ ℝ^ι} (∏ i, u i ^ (-b i)) Γ(∑ b) (∏ i, Γ(b i)) T_b[g] dξ`,
`b = c - 2πiξ`,

provided the integrand `ξ ↦ Γ(∑ b) ∏ Γ(b i) T_b[g]` is integrable on the plane. By the Mellin
bridge (`Dirichlet.mvMellin_exp_neg_mul_eq`) this function is the multivariable Mellin transform
of `x ↦ e^(-∑ x) g(x / ∑ x)`; in exponential coordinates it is a Fourier transform
(`mvMellin_eq_fourier`), and the formula is Fourier inversion
(`MeasureTheory.Integrable.fourierInv_fourier_eq`) evaluated at `log u`. The factor `e` undoes
`e^(-∑ u) = e^(-1)` on the simplex.

The same argument works with any radial profile `φ` in place of `e^(-t)`; the factor `e` becomes
`φ(1)⁻¹`. The integrability hypothesis is a smoothness condition on `g` in logarithmic
coordinates near the faces of the simplex. For the profile `e^(-t)` it is kept as a hypothesis.
For a smooth profile with compact support in `(0, ∞)` and a smooth kernel vanishing near the
faces, the function being inverted is smooth with compact support in logarithmic coordinates,
so the hypothesis holds by the integrability of Fourier transforms of test functions
(`TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`, by the Tau Ceti contributors).

## Main results

* `Dirichlet.fourier_radialLog`: the Fourier transform of the function in logarithmic
  coordinates is the full Mellin transform on the vertical plane.
* `Dirichlet.regDirichletIntegral_inversion_radial`: inversion with a general radial profile `φ`,
  `g u = φ(1)⁻¹ ∫ (∏ u i ^ (-b i)) ℳ[φ](∑ b) ∏ Γ(b i) T_b[g] dξ`, assuming integrability on the
  plane.
* `Dirichlet.regDirichletIntegral_inversion`: the case `φ(t) = e^(-t)`.
* `Dirichlet.integrable_simplexMellinRadial`: for a smooth profile with compact support in
  `(0, ∞)` and a smooth kernel vanishing near the faces of the simplex, the integrability
  hypothesis holds: the function in logarithmic coordinates is smooth with compact support.
* `Dirichlet.regDirichletIntegral_inversion_of_contDiff`: hence an unconditional inversion formula
  for such kernels.
* `Dirichlet.integral_norm_sq_simplexMellinRadial`: Plancherel,
  `∫ |ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]|² dξ = ℳ[|φ|²](2 ∑ c) ∏ Γ(2 c i) T_(2c)[|g|²]`.

## References

* `Mathlib.Analysis.MellinInversion`: the one-variable Mellin inversion formula, proved in the same
  way from Fourier inversion.
* `TauCeti.Analysis.Fourier.Integrable`: integrability of Fourier transforms of smooth compactly
  supported functions.
-/

open Complex MeasureTheory Set
open scoped FourierTransform ContDiff

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The parameters on the vertical plane `Re b = c` over the frequency `ξ`: `b = c - 2πiξ`. -/
def mellinPlane (c : ι → ℝ) (ξ : ι → ℝ) : ι → ℂ := fun i => (c i : ℂ) - 2 * Real.pi * ξ i * I

/-- The full Mellin transform of a simplex kernel: `Γ(∑ b) ∏ Γ(b i) T_b[g]`, the multivariable
Mellin transform of `x ↦ e^(-∑ x) g(x / ∑ x)`. -/
def simplexMellin (b : ι → ℂ) (g : (ι → ℝ) → ℂ) : ℂ :=
  Gamma (∑ i, b i) * ((∏ i, Gamma (b i)) * regDirichletIntegral b g)

omit [Fintype ι] in
/-- Parameters on a vertical plane with positive abscissae are in the convergence region. -/
theorem mellinPlane_mem {c : ι → ℝ} (hc : ∀ i, 0 < c i) (ξ : ι → ℝ) :
    mellinPlane c ξ ∈ mvBetaConvergent := fun i => by
  simpa [mellinPlane] using hc i

/-- The full Mellin transform with radial profile `φ`: `ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]`, the
multivariable Mellin transform of `x ↦ φ(∑ x) g(x / ∑ x)`. -/
def simplexMellinRadial (φ : ℝ → ℂ) (b : ι → ℂ) (g : (ι → ℝ) → ℂ) : ℂ :=
  mellin φ (∑ i, b i) * ((∏ i, Gamma (b i)) * regDirichletIntegral b g)

/-- The function inverted by Fourier inversion: `x ↦ φ(∑ x) g(x / ∑ x)` in exponential
coordinates, weighted by `e^(⟨c, y⟩)`. -/
def radialLog (c : ι → ℝ) (φ : ℝ → ℂ) (g : (ι → ℝ) → ℂ) (y : EuclideanSpace ℝ ι) : ℂ :=
  Real.exp (∑ i, c i * y i) •
    (φ (∑ i, piExp y.ofLp i) * g ((∑ i, piExp y.ofLp i)⁻¹ • piExp y.ofLp))

/-- The Fourier transform of `radialLog c φ g` is the full Mellin transform on the vertical
plane `b = c - 2πiξ`. -/
theorem fourier_radialLog [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) (ξ : EuclideanSpace ℝ ι) :
    𝓕 (radialLog c φ g) ξ = simplexMellinRadial φ (mellinPlane c ξ) g := by
  have h1 := mvMellin_eq_fourier (fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x))
    (mellinPlane c ξ)
  rw [mvMellin_radial_mul_eq (mellinPlane_mem hc ξ) hg hφ] at h1
  rw [simplexMellinRadial, h1]
  have hre : ∀ i, (mellinPlane c ξ i).re = c i := fun i => by simp [mellinPlane]
  have him : (WithLp.toLp 2 fun i => -(mellinPlane c ξ i).im / (2 * Real.pi)) = ξ := by
    ext i
    simp [mellinPlane, Real.pi_ne_zero]
  simp only [hre, him]
  rfl

/-- `radialLog c φ g` is continuous. -/
theorem continuous_radialLog [Nonempty ι] (c : ι → ℝ)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) : Continuous (radialLog c φ g) := by
  have hofc : Continuous fun y : EuclideanSpace ℝ ι => (y.ofLp : ι → ℝ) :=
    PiLp.continuous_ofLp 2 _
  have hpe : Continuous fun y : EuclideanSpace ℝ ι => piExp y.ofLp :=
    continuous_pi fun i => Real.continuous_exp.comp ((continuous_apply i).comp hofc)
  have hmem : ∀ y : EuclideanSpace ℝ ι, piExp y.ofLp ∈ posOrthant ι :=
    fun y i _ => Real.exp_pos _
  have hsum : ∀ y : EuclideanSpace ℝ ι, 0 < ∑ i, piExp y.ofLp i := fun y =>
    Finset.sum_pos (fun i _ => hmem y i (mem_univ i)) Finset.univ_nonempty
  have hsc : Continuous fun y : EuclideanSpace ℝ ι => ∑ i, piExp y.ofLp i :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp hpe
  have hgc : Continuous fun y : EuclideanSpace ℝ ι =>
      g ((∑ i, piExp y.ofLp i)⁻¹ • piExp y.ofLp) :=
    hg.comp_continuous ((hsc.inv₀ fun y => (hsum y).ne').smul hpe)
      fun y => inv_sum_smul_mem_coordinateSet (hmem y)
  refine (Real.continuous_exp.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp hofc))).smul ?_
  exact (hφ.comp_continuous hsc hsum).mul hgc

/-- `radialLog c φ g` is integrable when the Mellin integral of `φ` converges at `∑ c`. -/
theorem integrable_radialLog [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) (hφm : MellinConvergent φ (∑ i, (c i : ℂ))) :
    Integrable (radialLog c φ g) := by
  have hKc := mvMellinConvergent_radial_mul (b := fun i => (c i : ℂ))
    (fun i => by simpa using hc i) hg hφ hφm
  have h1 := (mvMellinConvergent_iff_integrable_exp _ _).mp hKc
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, radialLog]
  rw [← Complex.coe_smul, Complex.ofReal_exp]
  push_cast
  rfl

/-- **Inversion with a radial profile.** Let `g` be continuous on the simplex, `c i > 0`, and let
`φ` be continuous on `(0, ∞)` with convergent Mellin integral at `∑ c` and `φ 1 ≠ 0`. If
`ξ ↦ ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]` with `b = c - 2πiξ` is integrable over `ℝ^ι`, then at every
interior point `u` of the simplex,
`g u = φ(1)⁻¹ ∫ (∏ i, u i ^ (-b i)) ℳ[φ](∑ b) ∏ Γ(b i) T_b[g] dξ`. -/
theorem regDirichletIntegral_inversion_radial [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) (hφm : MellinConvergent φ (∑ i, (c i : ℂ)))
    (hφ1 : φ 1 ≠ 0)
    (hint : Integrable fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = (φ 1)⁻¹ * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellinRadial φ (mellinPlane c ξ) g := by
  set h := radialLog c φ g
  have hfour : ∀ ξ, 𝓕 h ξ = simplexMellinRadial φ (mellinPlane c ξ) g :=
    fourier_radialLog hc hg hφ
  have hhi : Integrable h := integrable_radialLog hc hg hφ hφm
  have hFi : Integrable (𝓕 h) := by
    rw [show 𝓕 h = fun ξ : EuclideanSpace ℝ ι => simplexMellinRadial φ (mellinPlane c ξ) g from
      funext hfour, ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    exact hint
  -- Fourier inversion at `log u`.
  set y₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i => Real.log (u i)
  have hinv := hhi.fourierInv_fourier_eq hFi (v := y₀)
    (continuous_radialLog c hg hφ).continuousAt
  have hpu : piExp y₀.ofLp = u := funext fun i => Real.exp_log (hu.2 i)
  have hsu : ∑ i, u i = 1 := hu.1.2
  set S : ℝ := ∑ i, c i * Real.log (u i)
  have hhy : h y₀ = Real.exp S • (φ 1 * g u) := by
    simp only [h, radialLog, hpu, hsu, inv_one, one_smul]
    rfl
  rw [Real.fourierInv_eq', hhy, ← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hinv
  have hprod : ∀ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellinRadial φ (mellinPlane c ξ) g =
        ((Real.exp (-S) : ℝ) : ℂ) *
          (Complex.exp (↑(2 * Real.pi * inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ ι) y₀) * I) •
            𝓕 h (WithLp.toLp 2 ξ)) := by
    intro ξ
    rw [hfour, smul_eq_mul, ← mul_assoc]
    congr 1
    have hlog : ∀ i, (u i : ℂ) ^ (-mellinPlane c ξ i) =
        Complex.exp (Real.log (u i) * (-mellinPlane c ξ i)) := fun i => by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (hu.2 i).ne'), ofReal_log (hu.2 i).le]
    simp_rw [hlog]
    rw [← Complex.exp_sum, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [mellinPlane, S, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, y₀]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hE : ((Real.exp (-S) : ℝ) : ℂ) * ((Real.exp S : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ofReal_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod), integral_const_mul, hinv,
    real_smul, ← mul_assoc (((Real.exp (-S) : ℝ) : ℂ)), hE, one_mul, ← mul_assoc,
    inv_mul_cancel₀ hφ1, one_mul]

/-- **Inversion of the regularized Dirichlet transform.** Let `g` be continuous on the simplex,
`c i > 0`, and assume that `ξ ↦ Γ(∑ b) ∏ Γ(b i) T_b[g]` with `b = c - 2πiξ` is integrable over
`ℝ^ι`. Then at every interior point `u` of the simplex,
`g u = e · ∫ (∏ i, u i ^ (-b i)) Γ(∑ b) ∏ Γ(b i) T_b[g] dξ`. -/
theorem regDirichletIntegral_inversion [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hint : Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  have hB : ∀ ξ : ι → ℝ, 0 < (∑ i, mellinPlane c ξ i).re := fun ξ => by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty
  have hsame : ∀ ξ : ι → ℝ,
      simplexMellinRadial φ (mellinPlane c ξ) g = simplexMellin (mellinPlane c ξ) g := by
    intro ξ
    rw [simplexMellinRadial, simplexMellin, Gamma_eq_integral (hB ξ), GammaIntegral_eq_mellin]
  have hc' : 0 < (∑ i, (c i : ℂ)).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa using hc i) Finset.univ_nonempty
  have hφm : MellinConvergent φ (∑ i, (c i : ℂ)) := by
    simpa [MellinConvergent, smul_eq_mul, mul_comm, φ] using Complex.GammaIntegral_convergent hc'
  have h := regDirichletIntegral_inversion_radial hc hg (φ := φ) (by fun_prop) hφm
    (by simp [φ]) (by simpa only [hsame] using hint) hu
  simp only [hsame] at h
  rw [h]
  congr 1
  simp only [φ, ofReal_exp]
  rw [← Complex.exp_neg]
  push_cast
  ring_nf

/-! ### An unconditional inversion formula for kernels vanishing near the faces -/

/-- For a smooth radial profile and a smooth kernel, `radialLog c φ g` is smooth. -/
theorem contDiff_radialLog [Nonempty ι] (c : ι → ℝ) {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (radialLog c φ g) := by
  have hof : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => (y.ofLp : ι → ℝ) := PiLp.contDiff_ofLp
  have hpe : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => piExp y.ofLp :=
    contDiff_pi.mpr fun i => Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ i).comp hof)
  have hsc : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => ∑ i, piExp y.ofLp i :=
    ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).comp hpe
  have hpos : ∀ y : EuclideanSpace ℝ ι, ∑ i, piExp y.ofLp i ≠ 0 := fun y =>
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  refine (Real.contDiff_exp.comp (ContDiff.sum fun i _ =>
    contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp hof))).smul ?_
  exact (hφ.comp hsc).mul (hg.comp ((hsc.inv hpos).smul hpe))

/-- **Compact support in logarithmic coordinates.** If `φ` vanishes outside `[r₀, r₁]` with
`r₀ > 0`, and `g` vanishes at the points of the simplex with a coordinate below `δ > 0`, then
`radialLog c φ g` has compact support. -/
theorem hasCompactSupport_radialLog [Nonempty ι] (c : ι → ℝ) {g : (ι → ℝ) → ℂ} {δ : ℝ}
    (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {φ : ℝ → ℂ} {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    HasCompactSupport (radialLog c φ g) := by
  set K : Set (EuclideanSpace ℝ ι) := WithLp.toLp 2 ''
    (univ.pi fun _ => Icc (Real.log (δ * r₀)) (Real.log r₁))
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  set r := ∑ i, piExp y.ofLp i
  have hr : 0 < r := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hmem : r⁻¹ • piExp y.ofLp ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
    inv_sum_smul_mem_coordinateSet fun i _ => Real.exp_pos _
  simp only [radialLog, smul_eq_zero, Real.exp_ne_zero, false_or, mul_eq_zero,
    not_or] at hne
  obtain ⟨hφr, hgu⟩ := hne
  obtain ⟨hr₀r, hrr₁⟩ := hφsupp r hφr
  have hδu := hgsupp _ hmem hgu
  refine ⟨y.ofLp, fun i _ => ⟨?_, ?_⟩, rfl⟩
  · have h1 : δ * r₀ ≤ Real.exp (y.ofLp i) := by
      have := hδu i
      simp only [Pi.smul_apply, smul_eq_mul, piExp] at this
      have h2 : δ * r ≤ Real.exp (y.ofLp i) := by
        rw [le_inv_mul_iff₀ hr] at this
        linarith [mul_comm δ r]
      nlinarith
    rw [Real.log_le_iff_le_exp (mul_pos hδ hr₀)]
    exact h1
  · have h1 : Real.exp (y.ofLp i) ≤ r :=
      Finset.single_le_sum (f := fun j => piExp y.ofLp j) (fun j _ => (Real.exp_pos _).le)
        (Finset.mem_univ i)
    rw [Real.le_log_iff_exp_le (hr₀.trans_le (hr₀r.trans hrr₁))]
    linarith

/-- A continuous radial profile vanishing outside `[r₀, r₁]` with `r₀ > 0` has convergent Mellin
integral at every exponent. -/
theorem mellinConvergent_of_support_subset_Icc {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) (s : ℂ) :
    MellinConvergent φ s := by
  have hsub : Icc r₀ r₁ ⊆ Ioi 0 := fun t ht => hr₀.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • φ t) (Icc r₀ r₁) := by
    have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Icc r₀ r₁) := fun t ht =>
      (ContinuousAt.cpow (continuous_ofReal.continuousAt) continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr (hsub ht))).continuousWithinAt
    exact hpow.mul (hφ.mono hsub)
  refine (hcont.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
    fun t ht => ?_
  by_contra hne
  exact ht.2 (hφsupp t (right_ne_zero_of_smul hne))

/-- **Integrability on vertical planes.** For a smooth radial profile `φ` vanishing outside
`[r₀, r₁] ⊂ (0, ∞)` and a smooth kernel `g` vanishing near the faces of the simplex, the full
Mellin transform `ξ ↦ ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]`, `b = c - 2πiξ`, is integrable on every vertical
plane with `c i > 0`: it is the Fourier transform of a smooth compactly supported function. -/
theorem integrable_simplexMellinRadial [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    Integrable fun ξ : ι → ℝ => simplexMellinRadial φ (mellinPlane c ξ) g := by
  have hF := TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport
    (contDiff_radialLog c hgs hφs) (hasCompactSupport_radialLog c hδ hgsupp hr₀ hφsupp)
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hgs.continuous.continuousOn hφs.continuous.continuousOn),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  exact hF

/-- **Unconditional inversion for kernels vanishing near the faces.** Let `g` be smooth and vanish
at the points of the simplex with a coordinate below some `δ > 0`, and let `φ` be a smooth radial
profile vanishing outside `[r₀, r₁] ⊂ (0, ∞)` with `φ 1 ≠ 0`. Then for every `c` with positive
coordinates and every interior point `u` of the simplex,
`g u = φ(1)⁻¹ ∫ (∏ i, u i ^ (-b i)) ℳ[φ](∑ b) ∏ Γ(b i) T_b[g] dξ`, `b = c - 2πiξ`. -/
theorem regDirichletIntegral_inversion_of_contDiff [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) (hφ1 : φ 1 ≠ 0)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = (φ 1)⁻¹ * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellinRadial φ (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion_radial hc hgs.continuous.continuousOn
    hφs.continuous.continuousOn
    (mellinConvergent_of_support_subset_Icc hφs.continuous.continuousOn hr₀ hφsupp _) hφ1
    (integrable_simplexMellinRadial hc hgs hδ hgsupp hφs hr₀ hφsupp) hu

/-! ### Plancherel -/

/-- **Plancherel for the simplex Mellin transform.** For a smooth radial profile `φ` vanishing
outside `[r₀, r₁] ⊂ (0, ∞)` and a smooth kernel `g` vanishing near the faces of the simplex, the
`L²` norm of `ξ ↦ ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]` on the vertical plane `b = c - 2πiξ` is the same
transform at `2c` of `|φ|²` and `|g|²`:

`∫ |ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]|² dξ = ℳ[|φ|²](2 ∑ c) ∏ Γ(2 c i) T_(2c)[|g|²]`.

Equivalently (by the definition of `T_(2c)`) it is
`(∫₀^∞ t^(2∑c - 1) |φ t|² dt) · ∫_Δ ∏ u i ^ (2 c i - 1) |g u|² du`. The proof is Plancherel's
theorem for Schwartz functions in logarithmic coordinates, followed by the Mellin bridge at `2c`.
-/
theorem integral_norm_sq_simplexMellinRadial [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    ((∫ ξ : ι → ℝ, ‖simplexMellinRadial φ (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ)) (fun i => ((2 * c i : ℝ) : ℂ))
        (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) := by
  set h := radialLog c φ g
  have hsupp := hasCompactSupport_radialLog c hδ hgsupp hr₀ hφsupp
  have hsm := contDiff_radialLog c hgs hφs
  have hcoe : ⇑(hsupp.toSchwartzMap hsm) = h := by
    ext x
    simp
    rfl
  have hP := SchwartzMap.integral_norm_sq_fourier (hsupp.toSchwartzMap hsm)
  simp only [SchwartzMap.fourier_coe, hcoe] at hP
  have hLHS : ∫ ξ : ι → ℝ, ‖simplexMellinRadial φ (mellinPlane c ξ) g‖ ^ 2 =
      ∫ ξ : EuclideanSpace ℝ ι, ‖𝓕 h ξ‖ ^ 2 := by
    rw [← (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_radialLog hc hgs.continuous.continuousOn hφs.continuous.continuousOn]
  rw [hLHS, hP, ← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding, ← integral_complex_ofReal]
  have hb : (fun i => ((2 * c i : ℝ) : ℂ)) ∈ mvBetaConvergent := fun i => by
    simpa using hc i
  have hbr := mvMellin_radial_mul_eq hb
    (g := fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ))
    (continuous_ofReal.comp (hgs.continuous.norm.pow 2)).continuousOn
    (φ := fun t => ((‖φ t‖ ^ 2 : ℝ) : ℂ))
    (continuous_ofReal.comp (hφs.continuous.norm.pow 2)).continuousOn
  rw [simplexMellinRadial, ← hbr, mvMellin_eq_integral_exp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [h, radialLog, norm_smul, norm_mul, mul_pow, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), smul_eq_mul]
  rw [← Real.exp_nat_mul]
  push_cast
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Dirichlet

end
