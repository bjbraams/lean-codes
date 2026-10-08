/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Inversion
public import ToMathlib.Analysis.SchwartzExpExp
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Inversion with the exponential profile for kernels vanishing near the faces

For a smooth kernel `g` vanishing near the faces of the simplex, the function inverted in
`Dirichlet.regDirichletIntegral_inversion` (radial profile `e^(-t)`) is a Schwartz function in
logarithmic coordinates. It factors as `G(y) · A(y)` with

* `A(y) = exp (∑ i, (c i y i - e^(y i)))`, a Schwartz function (`expExpSchwartz`), and
* `G(y) = g(e^y / ∑ e^y)`, which is constant along the diagonal and, after a linear change of
  coordinates `y ↦ y - y i₀ 𝟙`, coincides with a smooth compactly supported function; it is
  therefore of temperate growth.

Hence the Fourier transform is integrable, the integrability hypothesis of the inversion formula
holds, and the formula with the Gamma factors `Γ(∑ b) ∏ Γ(b i)` is unconditional for such
kernels.

## Main results

* `Dirichlet.hasTemperateGrowth_simplexAngle`: the angular factor has temperate growth.
* `Dirichlet.integrable_simplexMellin`: integrability of `ξ ↦ Γ(∑ b) ∏ Γ(b i) T_b[g]`.
* `Dirichlet.regDirichletIntegral_inversion_exp_of_contDiff`: the unconditional inversion
  formula with the exponential profile.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped FourierTransform ContDiff

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The angular factor in logarithmic coordinates: `y ↦ g(e^y / ∑ e^y)`. -/
def simplexAngle (g : (ι → ℝ) → ℂ) (y : EuclideanSpace ℝ ι) : ℂ :=
  g ((∑ i, piExp y.ofLp i)⁻¹ • piExp y.ofLp)

/-- The angular factor is smooth when the kernel is. -/
theorem contDiff_simplexAngle [Nonempty ι] {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (simplexAngle g) := by
  have hof : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => (y.ofLp : ι → ℝ) := PiLp.contDiff_ofLp
  have hpe : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => piExp y.ofLp :=
    contDiff_pi.mpr fun i => Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ i).comp hof)
  have hsc : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => ∑ i, piExp y.ofLp i :=
    ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).comp hpe
  have hpos : ∀ y : EuclideanSpace ℝ ι, ∑ i, piExp y.ofLp i ≠ 0 := fun y =>
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  exact hg.comp ((hsc.inv hpos).smul hpe)

/-- The angular factor is invariant under translation along the diagonal. -/
theorem simplexAngle_sub_smul_one (g : (ι → ℝ) → ℂ) (y : EuclideanSpace ℝ ι) (a : ℝ) :
    simplexAngle g (y - a • WithLp.toLp 2 (fun _ => (1 : ℝ))) = simplexAngle g y := by
  unfold simplexAngle
  have hpe : piExp (y - a • WithLp.toLp 2 (fun _ => (1 : ℝ))).ofLp =
      Real.exp (-a) • piExp y.ofLp := by
    funext i
    simp only [piExp, Pi.smul_apply, smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    simp
    ring
  rw [hpe]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, smul_smul]
  congr 1
  have := (Real.exp_pos (-a)).ne'
  field_simp

/-- **Temperate growth of the angular factor.** If `g` is smooth and vanishes at the points of the
simplex with a coordinate below `δ > 0`, then `y ↦ g(e^y / ∑ e^y)` has temperate growth. -/
theorem hasTemperateGrowth_simplexAngle [Nonempty ι] {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g)
    {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    (simplexAngle g).HasTemperateGrowth := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  let ρ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  -- A compactly supported smooth function that agrees with the angular factor on `y i₀ = 0`.
  let g' : EuclideanSpace ℝ ι → ℂ := fun w => (ρ (w i₀) : ℂ) * simplexAngle g w
  have hprj : ContDiff ℝ ∞ fun w : EuclideanSpace ℝ ι => w i₀ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i₀).contDiff
  have hg's : ContDiff ℝ ∞ g' :=
    (Complex.ofRealCLM.contDiff.comp (ρ.contDiff.comp hprj)).mul (contDiff_simplexAngle hgs)
  set R : ℝ := 1 + |Real.log δ|
  have hg'supp : HasCompactSupport g' := by
    set K : Set (EuclideanSpace ℝ ι) := WithLp.toLp 2 '' (univ.pi fun _ => Icc (-R) R)
    have hK : IsCompact K :=
      (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    refine HasCompactSupport.intro hK fun w hw => ?_
    by_contra hne
    apply hw
    simp only [g', mul_ne_zero_iff] at hne
    obtain ⟨hρ, hG⟩ := hne
    have hw₀ : |w i₀| < 1 := by
      have : w i₀ ∈ Function.support ρ := ofReal_ne_zero.mp hρ
      rw [ρ.support_eq] at this
      simpa [Metric.mem_ball, Real.dist_eq] using this
    set S := ∑ i, piExp w.ofLp i
    have hS : 0 < S := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    have hmem : S⁻¹ • piExp w.ofLp ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
      inv_sum_smul_mem_coordinateSet fun i _ => Real.exp_pos _
    have hδu := hgsupp _ hmem hG
    have hu1 : ∀ i, (S⁻¹ • piExp w.ofLp) i ≤ 1 := fun i =>
      (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hmem i).2
    have hratio : ∀ j, w j - w i₀ =
        Real.log ((S⁻¹ • piExp w.ofLp) j / (S⁻¹ • piExp w.ofLp) i₀) := by
      intro j
      simp only [Pi.smul_apply, smul_eq_mul, piExp]
      rw [mul_div_mul_left _ _ (inv_ne_zero hS.ne'), ← Real.exp_sub, Real.log_exp]
    refine ⟨w.ofLp, fun j _ => ?_, rfl⟩
    have hδ1 : δ ≤ 1 := (hδu i₀).trans (hu1 i₀)
    have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
    have hpos : ∀ i, 0 < (S⁻¹ • piExp w.ofLp) i := fun i => hδ.trans_le (hδu i)
    have hlo : Real.log δ ≤ w j - w i₀ := by
      rw [hratio, Real.log_div (hpos j).ne' (hpos i₀).ne']
      have h1 := Real.log_le_log hδ (hδu j)
      have h2 := Real.log_nonpos (hpos i₀).le (hu1 i₀)
      linarith
    have hhi : w j - w i₀ ≤ -Real.log δ := by
      rw [hratio, Real.log_div (hpos j).ne' (hpos i₀).ne']
      have h1 := Real.log_nonpos (hpos j).le (hu1 j)
      have h2 := Real.log_le_log hδ (hδu i₀)
      linarith
    have habs : |Real.log δ| = -Real.log δ := abs_of_nonpos hlogδ
    rw [abs_lt] at hw₀
    exact ⟨by simp only [R]; linarith, by simp only [R]; linarith⟩
  have hg'temp : g'.HasTemperateGrowth := by
    have h := (hg'supp.toSchwartzMap hg's).hasTemperateGrowth
    have hcoe : ⇑(hg'supp.toSchwartzMap hg's) = g' := by
      ext x
      simp
    rwa [hcoe] at h
  -- The linear map `y ↦ y - y i₀ 𝟙`.
  let Q : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    ContinuousLinearMap.id ℝ _ -
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i₀).smulRight (WithLp.toLp 2 fun _ => (1 : ℝ))
  have hQ : ∀ y, g' (Q y) = simplexAngle g y := by
    intro y
    have hQy : Q y = y - y i₀ • WithLp.toLp 2 (fun _ => (1 : ℝ)) := rfl
    have hQ0 : (Q y) i₀ = 0 := by
      rw [hQy]
      simp
    show (ρ ((Q y) i₀) : ℂ) * simplexAngle g (Q y) = simplexAngle g y
    rw [hQ0, ρ.one_of_mem_closedBall (by simp [ρ]), ofReal_one, one_mul, hQy,
      simplexAngle_sub_smul_one]
  have hcomp := hg'temp.comp Q.hasTemperateGrowth
  have hfun : g' ∘ Q = simplexAngle g := funext hQ
  rwa [hfun] at hcomp

/-- `simplexMellinRadial` with the exponential profile is `simplexMellin`. -/
theorem simplexMellinRadial_exp_eq {b : ι → ℂ} (hb : 0 < (∑ i, b i).re) (g : (ι → ℝ) → ℂ) :
    simplexMellinRadial (fun t => ((Real.exp (-t) : ℝ) : ℂ)) b g = simplexMellin b g := by
  rw [simplexMellinRadial, simplexMellin, Gamma_eq_integral hb, GammaIntegral_eq_mellin]

/-- **Integrability for the exponential profile.** For a smooth kernel vanishing near the faces
of the simplex, `ξ ↦ Γ(∑ b) ∏ Γ(b i) T_b[g]`, `b = c - 2πiξ`, is integrable on every vertical
plane with `c i > 0`. -/
theorem integrable_simplexMellin [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  have hG := hasTemperateGrowth_simplexAngle hgs hδ hgsupp
  set S := SchwartzMap.smulLeftCLM ℂ (simplexAngle g) (expExpSchwartz c hc)
  have hS : ⇑S = radialLog c φ g := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hG, expExpSchwartz_apply]
    simp only [radialLog, simplexAngle, φ, smul_eq_mul, piExp]
    rw [← Complex.coe_smul, smul_eq_mul, Finset.sum_sub_distrib, sub_eq_add_neg, Real.exp_add,
      ofReal_mul]
    ring
  have hF : Integrable (𝓕 (radialLog c φ g)) := by
    rw [← hS, ← SchwartzMap.fourier_coe]
    exact (𝓕 S).integrable
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hgs.continuous.continuousOn (by fun_prop)),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  refine hF.congr (Filter.Eventually.of_forall fun ξ => ?_)
  refine simplexMellinRadial_exp_eq ?_ g
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty

/-- **Unconditional inversion with the exponential profile.** For a smooth kernel `g` vanishing at
the points of the simplex with a coordinate below some `δ > 0`, every `c` with positive
coordinates and every interior point `u` of the simplex,
`g u = e ∫ (∏ i, u i ^ (-b i)) Γ(∑ b) ∏ Γ(b i) T_b[g] dξ`, `b = c - 2πiξ`. -/
theorem regDirichletIntegral_inversion_exp_of_contDiff [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hgs.continuous.continuousOn
    (integrable_simplexMellin hc hgs hδ hgsupp) hu

end Dirichlet

end
