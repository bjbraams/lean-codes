/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Inversion
public import Pochhammer.Gamma

/-!
# Paley–Wiener estimates for the simplex Mellin transform

Let `g` be continuous on the standard simplex and vanish at the points with a coordinate below
some `δ > 0`. In logarithmic coordinates `y = log u` its support lies in the box
`log δ ≤ y i ≤ 0`, and the simplex Mellin transform

`S_g(b) = ∫_Δ (∏ i, u i ^ (b i - 1)) g(u) du = ∏ i, Γ(b i) · T_b[g]`

behaves like a Fourier–Laplace transform of a compactly supported function. This file proves the
necessity half of a Paley–Wiener description of the image:

* the native regularized integral `b ↦ T_b[g]` is itself entire (no continuation is needed);
* `S_g` is of exponential type: `|S_g(b)| ≤ ‖g‖₁ ∏ i, max 1 (δ ^ (Re b i - 1))`, uniformly in
  `Im b`;
* with a smooth radial profile `φ` compactly supported in `(0, ∞)`, the function
  `ξ ↦ ℳ[φ](∑ b) S_g(b)` on a vertical plane `b = c - 2πiξ` is a Schwartz function.

`S_g` itself does not decay rapidly in all imaginary directions: in a direction where all
`Im b i` have the same sign the phase `⟨Im b, log u⟩` is stationary on the simplex (at `u`
proportional to `Im b`), and stationary phase gives decay of order `|Im b| ^ (-(card ι - 1) / 2)`
only (this remark is not formalized). The radial factor `ℳ[φ](∑ b)` supplies the missing
decay.

The functional equation `S_g(b) = ∑ i, S_g(b + e i)`, the sum-shift law, is
`Dirichlet.IsRegDirichletContinuation.sum_shift` in regularized form.

## Main results

* `Dirichlet.regDirichletIntegral_eq_ascPochhammer_mul`: the Pochhammer shift identity, valid for
  every kernel and every parameter.
* `Dirichlet.analyticOnNhd_regDirichletIntegral_of_vanish`: the native integral is entire.
* `Dirichlet.isRegDirichletContinuation_regDirichletIntegral_of_vanish`: it is the transform.
* `Dirichlet.norm_integral_monomial_mul_le_of_vanish`: the exponential-type bound.
* `Dirichlet.exists_schwartzMap_simplexMellinRadial`: Schwartz decay on vertical planes.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983,
  Theorem 7.3.1 (the Paley–Wiener–Schwartz theorem).
-/

open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform ContDiff

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- Division of a kernel vanishing near the faces by the monomial `∏ i, u i ^ m`. -/
def divMonomial (m : ℕ) (g : (ι → ℝ) → ℂ) (u : ι → ℝ) : ℂ := g u / ((∏ i, u i) ^ m : ℝ)

/-- Dividing a kernel that vanishes near the faces by a monomial keeps it continuous on the
simplex. -/
theorem continuousOn_divMonomial {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) (m : ℕ) :
    ContinuousOn (divMonomial m g) (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  intro u hu
  by_cases hpos : ∀ i, 0 < u i
  · have hP : ((∏ i, u i) ^ m : ℝ) ≠ 0 :=
      pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne')
    refine (hg u hu).div (Continuous.continuousWithinAt ?_) (ofReal_ne_zero.mpr hP)
    fun_prop
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi0 : u i = 0 := le_antisymm hi (hu.1 i)
    have hnear : ∀ᶠ v in 𝓝[Convexity.StdSimplex.coordinateSet ℝ ι] u,
        divMonomial m g v = 0 := by
      have hev : ∀ᶠ v in 𝓝 u, v i < δ :=
        (continuous_apply i).continuousAt.eventually
          (gt_mem_nhds (show u i < δ by rw [hi0]; exact hδ))
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvΔ
      by_contra hne
      have hgv : g v ≠ 0 := fun h => hne (by simp [divMonomial, h])
      exact absurd (hgsupp v hvΔ hgv i) (not_le.mpr hv)
    have hu0 : divMonomial m g u = 0 := by
      by_contra hne
      have hgu : g u ≠ 0 := fun h => hne (by simp [divMonomial, h])
      exact absurd (hgsupp u hu hgu i) (by rw [hi0]; exact not_le.mpr hδ)
    rw [ContinuousWithinAt, hu0]
    exact tendsto_nhds_of_eventually_eq hnear

/-- **The shift identity.** Lowering every parameter by a natural number `m` multiplies the native
integral by Pochhammer factors (an identity of Bochner integrals, valid for every kernel):
`T_b[g] = ∏ i, (b i)_m · T_(b + m)[g / ∏ u^m]`, for all complex `b`. -/
theorem regDirichletIntegral_eq_ascPochhammer_mul (g : (ι → ℝ) → ℂ) (m : ℕ) (b : ι → ℂ) :
    regDirichletIntegral b g = (∏ i, (ascPochhammer ℂ m).eval (b i)) *
      regDirichletIntegral (fun i => b i + m) (divMonomial m g) := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_stdSimplexInterior (ι := ι)] with u hu
  simp only [regDirichletDensity, indicator_of_mem hu]
  have hpos : ∀ i, 0 < u i := hu.2
  have hP : ((∏ i, u i) ^ m : ℝ) ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne')
  have hfac : ∀ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i) =
      (ascPochhammer ℂ m).eval (b i) * ((u i : ℂ) ^ (b i + m - 1) / Gamma (b i + m)) *
        (u i : ℂ) ^ (-(m : ℂ)) := by
    intro i
    have hu0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos i).ne'
    rw [div_eq_mul_inv, div_eq_mul_inv, one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat]
    rw [show b i + m - 1 = (b i - 1) + m by ring, cpow_add _ _ hu0]
    have : (u i : ℂ) ^ (m : ℂ) * (u i : ℂ) ^ (-(m : ℂ)) = 1 := by
      rw [← cpow_add _ _ hu0, add_neg_cancel, cpow_zero]
    linear_combination (-((u i : ℂ) ^ (b i - 1) * (ascPochhammer ℂ m).eval (b i) *
      (Gamma (b i + m))⁻¹)) * this
  have hmono : ∏ i, (u i : ℂ) ^ (-(m : ℂ)) = (((∏ i, u i) ^ m : ℝ) : ℂ)⁻¹ := by
    rw [ofReal_pow, ofReal_prod, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [cpow_neg, cpow_natCast]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hmono, divMonomial, div_eq_mul_inv]
  ring

/-- **The native integral is entire.** For a kernel continuous on the simplex and vanishing at
the points with a coordinate below `δ > 0`, `b ↦ T_b[g]` (the native regularized integral) is
entire. -/
theorem analyticOnNhd_regDirichletIntegral_of_vanish {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    AnalyticOnNhd ℂ (fun b => regDirichletIntegral b g) univ := by
  intro b₀ _
  obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, |(b₀ i).re|)
  have hshift : (fun i => b₀ i + m) ∈ mvBetaConvergent := fun i => by
    have : |(b₀ i).re| ≤ ∑ j, |(b₀ j).re| :=
      Finset.single_le_sum (f := fun j => |(b₀ j).re|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    simp only [add_re, natCast_re]
    linarith [neg_abs_le (b₀ i).re]
  have hT : AnalyticAt ℂ (fun c => regDirichletIntegral c (divMonomial m g))
      (fun i => b₀ i + m) :=
    (regDirichletIntegral_analyticOn (continuousOn_divMonomial hg hδ hgsupp m)).analyticAt
      (Complex.isOpen_mvBetaConvergent.mem_nhds hshift)
  have hadd : AnalyticAt ℂ (fun b : ι → ℂ => fun i => b i + m) b₀ :=
    analyticAt_id.add analyticAt_const
  have hpoly : AnalyticAt ℂ (fun b : ι → ℂ => ∏ i, (ascPochhammer ℂ m).eval (b i)) b₀ :=
    Finset.analyticAt_fun_prod _ fun i _ =>
      ((Polynomial.differentiable _).analyticAt _).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b₀)
  have hfun : (fun b => regDirichletIntegral b g) = fun b =>
      (∏ i, (ascPochhammer ℂ m).eval (b i)) *
        regDirichletIntegral (fun i => b i + m) (divMonomial m g) :=
    funext (regDirichletIntegral_eq_ascPochhammer_mul g m)
  rw [hfun]
  exact hpoly.mul (hT.comp_of_eq hadd rfl)

/-- For a kernel vanishing near the faces, the native integral is the entire regularized
transform. -/
theorem isRegDirichletContinuation_regDirichletIntegral_of_vanish {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    IsRegDirichletContinuation g (fun b => regDirichletIntegral b g) :=
  ⟨analyticOnNhd_regDirichletIntegral_of_vanish hg hδ hgsupp, fun _ _ => rfl⟩

/-- **Exponential type.** For a kernel vanishing at the points of the simplex with a coordinate
below `δ ∈ (0, 1]`, the simplex Mellin transform `S_g(b) = ∫_Δ ∏ u^(b - 1) g` satisfies
`|S_g(b)| ≤ ‖g‖₁ ∏ i, max 1 (δ ^ (Re b i - 1))` for all complex `b`. -/
theorem norm_integral_monomial_mul_le_of_vanish {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (b : ι → ℂ) :
    ‖∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (∏ i, (u i : ℂ) ^ (b i - 1)) * g u
        ∂Measure.stdSimplexMeasure‖ ≤
      (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g u‖ ∂Measure.stdSimplexMeasure) *
        ∏ i, max 1 (δ ^ ((b i).re - 1)) := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hgi : IntegrableOn (fun u => ‖g u‖) (Convexity.StdSimplex.coordinateSet ℝ ι)
      Measure.stdSimplexMeasure := by
    have h := hg.norm.integrableOn_compact (μ := Measure.stdSimplexMeasure.restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι))
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    rwa [IntegrableOn, Measure.restrict_restrict hS, inter_self] at h
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hgi.mul_const _) ?_
  filter_upwards [ae_restrict_mem hS] with u hu
  by_cases hgu : g u = 0
  · simp only [hgu, mul_zero, norm_zero, zero_mul, le_refl]
  · have hδu := hgsupp u hu hgu
    rw [norm_mul, mul_comm]
    gcongr
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
    have hui : 0 < u i := hδ.trans_le (hδu i)
    have hu1 : u i ≤ 1 := (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
    rw [norm_cpow_eq_rpow_re_of_pos hui]
    simp only [sub_re, one_re]
    rcases le_total 0 ((b i).re - 1) with hx | hx
    · exact (Real.rpow_le_one hui.le hu1 hx).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hδ (hδu i) hx).trans (le_max_right _ _)

/-- **Schwartz decay on vertical planes.** For a smooth kernel vanishing near the faces and a
smooth radial profile `φ` vanishing outside `[r₀, r₁] ⊂ (0, ∞)`, the full Mellin transform
`ξ ↦ ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]`, `b = c - 2πiξ`, is a Schwartz function on every vertical plane
with `c i > 0`. -/
theorem exists_schwartzMap_simplexMellinRadial [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {φ : ℝ → ℂ} (hφs : ContDiff ℝ ∞ φ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    ∃ Ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      ∀ ξ, Ψ ξ = simplexMellinRadial φ (mellinPlane c ξ) g := by
  have hsupp := hasCompactSupport_radialLog c hδ hgsupp hr₀ hφsupp
  have hsm := contDiff_radialLog c hgs hφs
  refine ⟨𝓕 (hsupp.toSchwartzMap hsm), fun ξ => ?_⟩
  have hcoe : ⇑(hsupp.toSchwartzMap hsm) = radialLog c φ g := by
    ext x
    simp
  rw [SchwartzMap.fourier_coe, hcoe,
    fourier_radialLog hc hgs.continuous.continuousOn hφs.continuous.continuousOn]

end Dirichlet

end
