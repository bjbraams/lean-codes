/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import StdSimplexMeasure.Radial
public import ToMathlib.Analysis.MvMellinTransform

/-!
# The Mellin bridge for the regularized Dirichlet transform

In simplicial polar coordinates `x = t • u` (`t = ∑ i, x i`, `u` in the standard simplex), the
multivariable Mellin transform of a function `φ(t) g(u)` factors into the one-variable Mellin
transform of the radial profile `φ` at the total parameter and the simplex Mellin transform of
`g`:

`mvMellin (x ↦ φ (∑ x) g (x / ∑ x)) b = mellin φ (∑ i, b i) · ∏ i, Γ(b i) · T_b[g]`,

where `T_b[g] = regDirichletIntegral b g` is the regularized Dirichlet transform. For
`φ(t) = e^(-t)` the radial factor is `Γ(∑ i, b i)`. Thus the regularized Dirichlet transform is
the angular part of the multivariable Mellin transform, with the Gamma factors divided out.

The identity holds without integrability assumptions: the polar decomposition is an identity
of measures (`MeasureTheory.map_polarMap`), and the factorization uses
`MeasureTheory.integral_prod_mul`, so both sides are equal as Bochner integrals.

## Main results

* `Dirichlet.mvMellin_radial_mul_eq`: the bridge for a continuous radial profile.
* `Dirichlet.mvMellin_exp_neg_mul_eq`: the case `φ(t) = e^(-t)`.
* `Dirichlet.indicator_mvMellinIntegrand_radial_smul`: the pointwise factorization in polar
  coordinates.
* `Dirichlet.mvMellinConvergent_radial_mul`: convergence of the multivariable Mellin integral
  from convergence of the radial Mellin integral.
* `Dirichlet.mvMellin_radial_eq_prod_Gamma_mul`, `Dirichlet.mvMellin_exp_neg_eq_Gamma_mul`: the
  continued form; for a smooth kernel the multivariable Mellin transform is `∏ Γ(b i)` (and
  `Γ(∑ b)` for the exponential profile) times an entire function.

## References

* `Mathlib.Analysis.MellinTransform`: the one-variable Mellin transform.
* `Dirichlet.Gamma`: the probabilistic form of the same polar decomposition (normalized Gamma
  variables are Dirichlet distributed).
-/

open Complex MeasureTheory Set
open MvMellin

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- A product of complex powers of one nonzero base is a power with the summed exponent. -/
theorem prod_cpow_eq_cpow_sum {z : ℂ} (hz : z ≠ 0) (c : ι → ℂ) :
    ∏ i, z ^ c i = z ^ ∑ i, c i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, cpow_add _ _ hz]

/-- The normalization `x / ∑ x` of a point of the open positive orthant lies in the simplex. -/
theorem inv_sum_smul_mem_coordinateSet [Nonempty ι] {x : ι → ℝ} (hx : x ∈ posOrthant ι) :
    (∑ i, x i)⁻¹ • x ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  have hpos : 0 < ∑ i, x i :=
    Finset.sum_pos (fun i _ => hx i (mem_univ i)) Finset.univ_nonempty
  refine ⟨fun i => ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr hpos.le) (hx i (mem_univ i)).le
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hpos.ne'

/-- The Mellin integrand `x ↦ ∏ i, x i ^ (b i - 1) • φ (∑ x) g (x / ∑ x)` of a radial profile
times a simplex kernel is continuous on the open positive orthant. -/
theorem continuousOn_mvMellinIntegrand_radial [Nonempty ι] (b : ι → ℂ)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) :
    ContinuousOn (fun x => mvMellinWeight b x • (φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)))
      (posOrthant ι) := by
  have hsum : ∀ x ∈ posOrthant ι, 0 < ∑ i, x i := fun x hx =>
    Finset.sum_pos (fun i _ => hx i (mem_univ i)) Finset.univ_nonempty
  have hW : ContinuousOn (mvMellinWeight b) (posOrthant ι) := by
    refine continuousOn_finsetProd _ fun i _ x hx => ?_
    exact (ContinuousAt.cpow (f := fun x : ι → ℝ => ((x i : ℝ) : ℂ))
      (continuous_ofReal.comp (continuous_apply i)).continuousAt
      continuousAt_const (Complex.ofReal_mem_slitPlane.mpr (hx i (mem_univ i)))).continuousWithinAt
  have hφs : ContinuousOn (fun x : ι → ℝ => φ (∑ i, x i)) (posOrthant ι) :=
    hφ.comp (by fun_prop : Continuous fun x : ι → ℝ => ∑ i, x i).continuousOn
      fun x hx => hsum x hx
  have hgs : ContinuousOn (fun x : ι → ℝ => g ((∑ i, x i)⁻¹ • x)) (posOrthant ι) := by
    refine hg.comp ?_ fun x hx => inv_sum_smul_mem_coordinateSet hx
    exact ContinuousOn.smul (ContinuousOn.inv₀ (by fun_prop) fun x hx => (hsum x hx).ne')
      continuousOn_id
  exact hW.smul (hφs.mul hgs)

/-- **Factorization in polar coordinates.** At `t • u` with `t > 0` and `u` in the simplex, the
Mellin integrand of `φ(∑ x) g(x / ∑ x)`, extended by zero off the open orthant, is the product of
the radial factor `t^(∑ b - card ι) φ(t)` and the angular factor `∏ Γ(b i)` times the
regularized Dirichlet density times `g`. -/
theorem indicator_mvMellinIntegrand_radial_smul {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (g : (ι → ℝ) → ℂ) (φ : ℝ → ℂ) {t : ℝ} (ht : 0 < t) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (posOrthant ι).indicator
        (fun x => mvMellinWeight b x • (φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x))) (t • u) =
      ((t : ℂ) ^ (∑ i, b i - Fintype.card ι) * φ t) *
        ((∏ i, Gamma (b i)) * (regDirichletDensity b u * g u)) := by
  have hΓ : ∀ i, Gamma (b i) ≠ 0 := fun i => Gamma_ne_zero_of_re_pos (hb i)
  have hsu : ∑ i, u i = 1 := hu.2
  by_cases hint : ∀ i, 0 < u i
  · have hmem : t • u ∈ posOrthant ι := fun i _ => mul_pos ht (hint i)
    simp only [indicator_of_mem hmem, regDirichletDensity,
      indicator_of_mem (show u ∈ stdSimplexInterior from ⟨hu, hint⟩)]
    have hts : ∑ i, (t • u) i = t := by
      simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsu]
    rw [hts, inv_smul_smul₀ ht.ne']
    have hW : mvMellinWeight b (t • u) =
        (t : ℂ) ^ (∑ i, b i - Fintype.card ι) * ∏ i, (u i : ℂ) ^ (b i - 1) := by
      rw [mvMellinWeight]
      simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul]
      simp_rw [mul_cpow_ofReal_nonneg ht.le (hint _).le]
      rw [Finset.prod_mul_distrib, prod_cpow_eq_cpow_sum (ofReal_ne_zero.mpr ht.ne')]
      congr 2
      simp [Finset.sum_sub_distrib]
    rw [hW, smul_eq_mul, Finset.prod_div_distrib]
    field_simp [Finset.prod_ne_zero_iff.mpr fun i _ => hΓ i]
  · push Not at hint
    obtain ⟨i, hi⟩ := hint
    have hnot : t • u ∉ posOrthant ι := fun h => by
      have := h i (mem_univ i)
      simp only [mem_Ioi, Pi.smul_apply, smul_eq_mul] at this
      nlinarith [hu.1 i]
    have hnot' : u ∉ stdSimplexInterior := fun h => by linarith [h.2 i]
    simp [indicator_of_notMem hnot, regDirichletDensity, indicator_of_notMem hnot']

/-- The factorization holds almost everywhere for `t^(card ι - 1) dt ⊗ du`. -/
theorem ae_indicator_mvMellinIntegrand_radial_polarMap {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (g : (ι → ℝ) → ℂ) (φ : ℝ → ℂ) :
    ∀ᵐ p ∂(MeasureTheory.radialMeasure ι).prod
        (Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)),
      (posOrthant ι).indicator
          (fun x => mvMellinWeight b x • (φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)))
          (MeasureTheory.polarMap p) =
        ((p.1 : ℂ) ^ (∑ i, b i - Fintype.card ι) * φ p.1) *
          ((∏ i, Gamma (b i)) * (regDirichletDensity b p.2 * g p.2)) := by
  have h₁ : ∀ᵐ t ∂MeasureTheory.radialMeasure ι, t ∈ Ioi (0 : ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have h₂ : ∀ᵐ u ∂Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι),
      u ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
    ae_restrict_mem (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h₁,
    Measure.quasiMeasurePreserving_snd.ae h₂] with p ht hu
  exact indicator_mvMellinIntegrand_radial_smul hb g φ ht hu

/-- The Mellin integrand, extended by zero off the open orthant, is a.e. strongly measurable on
the closed orthant. -/
theorem aestronglyMeasurable_indicator_mvMellinIntegrand_radial [Nonempty ι] (b : ι → ℂ)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) :
    AEStronglyMeasurable ((posOrthant ι).indicator
        (fun x => mvMellinWeight b x • (φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x))))
      (volume.restrict MeasureTheory.nonnegOrthant) := by
  have hposnn : posOrthant ι ⊆ MeasureTheory.nonnegOrthant :=
    fun x hx i => (hx i (mem_univ i)).le
  refine (aestronglyMeasurable_indicator_iff measurableSet_posOrthant).mpr ?_
  rw [Measure.restrict_restrict measurableSet_posOrthant, inter_eq_left.mpr hposnn]
  exact (continuousOn_mvMellinIntegrand_radial b hg hφ).aestronglyMeasurable
    measurableSet_posOrthant

/-- **The Mellin bridge.** For a radial profile `φ` continuous on `(0, ∞)`, a kernel `g`
continuous on the simplex and parameters with positive real parts, the multivariable Mellin
transform of `x ↦ φ (∑ x) g (x / ∑ x)` is the Mellin transform of `φ` at the total parameter,
times `∏ i, Γ(b i)`, times the regularized Dirichlet transform of `g`. No integrability is
assumed: both sides are Bochner integrals, equal in all cases. -/
theorem mvMellin_radial_mul_eq [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) :
    mvMellin (fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) b =
      mellin φ (∑ i, b i) * ((∏ i, Gamma (b i)) * regDirichletIntegral b g) := by
  set Δ := Convexity.StdSimplex.coordinateSet ℝ ι
  set k := Fintype.card ι
  set B := ∑ i, b i
  set G : (ι → ℝ) → ℂ := (posOrthant ι).indicator
    (fun x => mvMellinWeight b x • (φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)))
  have hk : 1 ≤ k := Fintype.card_pos
  have hposnn : posOrthant ι ⊆ MeasureTheory.nonnegOrthant :=
    fun x hx i => (hx i (mem_univ i)).le
  have hGm := aestronglyMeasurable_indicator_mvMellinIntegrand_radial b hg hφ
  set f₁ : ℝ → ℂ := fun t => (t : ℂ) ^ (B - k) * φ t
  set f₂ : (ι → ℝ) → ℂ := fun u => (∏ i, Gamma (b i)) * (regDirichletDensity b u * g u)
  have hρ : ∫ t, f₁ t ∂MeasureTheory.radialMeasure ι = mellin φ B := by
    rw [MeasureTheory.radialMeasure, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [mem_Ioi] at ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [ENNReal.toReal_ofReal (pow_nonneg ht.le _), smul_eq_mul, real_smul, ofReal_pow,
      ← cpow_natCast, ← mul_assoc, ← cpow_add _ _ ht0, Nat.cast_sub hk]
    congr 2
    push_cast
    ring
  have hν : ∫ u, f₂ u ∂Measure.stdSimplexMeasure.restrict Δ =
      (∏ i, Gamma (b i)) * regDirichletIntegral b g := by
    rw [integral_const_mul]
    rfl
  calc mvMellin (fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) b
      = ∫ x, G x ∂volume.restrict MeasureTheory.nonnegOrthant := by
        rw [mvMellin, ← integral_indicator measurableSet_posOrthant,
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
            indicator_of_notMem (fun h => hx (hposnn h)) _]
    _ = ∫ p, G (MeasureTheory.polarMap p)
          ∂(MeasureTheory.radialMeasure ι).prod (Measure.stdSimplexMeasure.restrict Δ) := by
        rw [← MeasureTheory.map_polarMap, integral_map
          MeasureTheory.continuous_polarMap.measurable.aemeasurable
          (by rwa [MeasureTheory.map_polarMap])]
    _ = ∫ p, f₁ p.1 * f₂ p.2
          ∂(MeasureTheory.radialMeasure ι).prod (Measure.stdSimplexMeasure.restrict Δ) :=
        integral_congr_ae (ae_indicator_mvMellinIntegrand_radial_polarMap hb g φ)
    _ = mellin φ B * ((∏ i, Gamma (b i)) * regDirichletIntegral b g) := by
        rw [integral_prod_mul, hρ, hν]

/-- **Convergence of the radial Mellin integral.** If the Mellin integral of the radial profile
converges at the total parameter, the multivariable Mellin integral of `φ(∑ x) g(x / ∑ x)`
converges, for `g` continuous on the simplex and parameters with positive real parts. -/
theorem mvMellinConvergent_radial_mul [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) (hφm : MellinConvergent φ (∑ i, b i)) :
    MvMellinConvergent (fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) b := by
  set Δ := Convexity.StdSimplex.coordinateSet ℝ ι
  set k := Fintype.card ι
  have hk : 1 ≤ k := Fintype.card_pos
  have hposnn : posOrthant ι ⊆ MeasureTheory.nonnegOrthant :=
    fun x hx i => (hx i (mem_univ i)).le
  have hGm := aestronglyMeasurable_indicator_mvMellinIntegrand_radial b hg hφ
  -- The radial factor is integrable for `t^(k - 1) dt`.
  have h₁ : Integrable (fun t : ℝ => (t : ℂ) ^ (∑ i, b i - k) * φ t)
      (MeasureTheory.radialMeasure ι) := by
    rw [MeasureTheory.radialMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mp hφm
    simp only [mem_Ioi] at ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [ENNReal.toReal_ofReal (pow_nonneg ht.le _), smul_eq_mul, real_smul, ofReal_pow,
      ← cpow_natCast, ← mul_assoc, ← cpow_add _ _ ht0, Nat.cast_sub hk]
    congr 2
    push_cast
    ring
  -- The angular factor is integrable on the simplex.
  have h₂ : Integrable (fun u => (∏ i, Gamma (b i)) * (regDirichletDensity b u * g u))
      (Measure.stdSimplexMeasure.restrict Δ) :=
    (integrableOn_regDirichletDensity_mul b hb hg).const_mul _
  have hprod := (h₁.mul_prod h₂).congr
    ((ae_indicator_mvMellinIntegrand_radial_polarMap hb g φ).mono fun p hp => hp.symm)
  rw [MeasureTheory.integrable_comp_polarMap_iff hGm, IntegrableOn,
    integrable_indicator_iff measurableSet_posOrthant, IntegrableOn, Measure.restrict_restrict
      measurableSet_posOrthant, inter_eq_left.mpr hposnn] at hprod
  exact hprod

/-- **The Mellin bridge for the exponential profile.** The multivariable Mellin transform of
`x ↦ e^(-∑ x) g (x / ∑ x)` is `Γ(∑ i, b i) ∏ i, Γ(b i) T_b[g]`. -/
theorem mvMellin_exp_neg_mul_eq [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    mvMellin (fun x => ((Real.exp (-∑ i, x i) : ℝ) : ℂ) * g ((∑ i, x i)⁻¹ • x)) b =
      Gamma (∑ i, b i) * ((∏ i, Gamma (b i)) * regDirichletIntegral b g) := by
  have hB : 0 < (∑ i, b i).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  rw [mvMellin_radial_mul_eq hb hg (φ := fun t => ((Real.exp (-t) : ℝ) : ℂ)) (by fun_prop),
    Gamma_eq_integral hB, GammaIntegral_eq_mellin]

/-! ### The continued form -/

/-- A radial profile continuous on `(0, ∞)` and vanishing outside `[r₀, r₁]` with `r₀ > 0` has
an entire Mellin transform. -/
theorem differentiable_mellin_of_support_subset_Icc {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hφsupp : ∀ t, φ t ≠ 0 → r₀ ≤ t ∧ t ≤ r₁) :
    Differentiable ℂ (mellin φ) := by
  intro s
  have hzero_top : φ =ᶠ[Filter.atTop] 0 := by
    filter_upwards [Filter.eventually_gt_atTop r₁] with t ht
    by_contra hne
    exact absurd (hφsupp t hne).2 (not_le.mpr ht)
  have hzero_bot : φ =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
    filter_upwards [Ioo_mem_nhdsGT hr₀] with t ht
    by_contra hne
    exact absurd (hφsupp t hne).1 (not_le.mpr ht.2)
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hφ.locallyIntegrableOn measurableSet_Ioi)
    (hzero_top.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)
    (hzero_bot.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)

/-- **The continued form of the Mellin bridge.** For a smooth kernel `g` and a radial profile `φ`
with entire Mellin transform, the multivariable Mellin transform of `φ(∑ x) g(x / ∑ x)` is
`∏ i, Γ(b i)` times the entire function `b ↦ ℳ[φ](∑ b) F(b)`, with `F` the entire regularized
Dirichlet transform of `g`. Hence its continuation is meromorphic in each `b i`, with poles only at
the nonpositive integers (where the face formulas of `SimplexMellin.Face` give the
residues). -/
theorem mvMellin_radial_eq_prod_Gamma_mul [Nonempty ι] {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0))
    (hφe : Differentiable ℂ (mellin φ)) :
    Differentiable ℂ (fun b : ι → ℂ => mellin φ (∑ i, b i) * regDirichletTransform g hg b) ∧
      ∀ b ∈ mvBetaConvergent,
        mvMellin (fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) b =
          (∏ i, Gamma (b i)) * (mellin φ (∑ i, b i) * regDirichletTransform g hg b) := by
  have hF := isRegDirichletContinuation_transform hg
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · exact ((hφe _).comp b (by fun_prop)).mul (hF.1 b (mem_univ _)).differentiableAt
  · rw [mvMellin_radial_mul_eq hb hg.continuousOn hφ, hF.eq_native hb]
    ring

/-- **The continued form for the exponential profile.** For a smooth kernel `g`, the
multivariable Mellin transform of `e^(-∑ x) g(x / ∑ x)` is `Γ(∑ b) ∏ Γ(b i) F(b)` on the convergence
region, with `F` the entire regularized Dirichlet transform. -/
theorem mvMellin_exp_neg_eq_Gamma_mul [Nonempty ι] {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvMellin (fun x => ((Real.exp (-∑ i, x i) : ℝ) : ℂ) * g ((∑ i, x i)⁻¹ • x)) b =
      Gamma (∑ i, b i) * ((∏ i, Gamma (b i)) * regDirichletTransform g hg b) := by
  rw [mvMellin_exp_neg_mul_eq hb hg.continuousOn,
    (isRegDirichletContinuation_transform hg).eq_native hb]

end Dirichlet

end
