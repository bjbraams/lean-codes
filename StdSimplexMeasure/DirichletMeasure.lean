/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.LebesgueMeasure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real normalized Dirichlet measure on the standard simplex

The multivariate Dirichlet measure [KBJ00, Ch 49] is defined on the standard simplex in
symmetric variables, i.e. `stdSimplex ℝ ι`, or $E^{k-1}$ embedded in $ℝ^k$ where
`k = card ι`.

## Main definitions and results

## References

[KBJ00] Kotz, Samuel, Narayanaswamy Balakrishnan, and Norman L. Johnson. "Continuous
multivariate distributions, Volume 1: Models and applications." John Wiley & Sons, 2000.
Online: https://dx.doi.org/10.1002/0471722065.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable section DirichletMeasure

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Allow `ι` to have noncomputable equality. -/
local instance stdSimplexDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The multivariate real Beta function. -/
noncomputable def mvBeta (b : ι → ℝ) : ℝ :=
  (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- Domain for `b` where the Beta function is defined as an integral. -/
def mvBetaDomain : Set (ι → ℝ) :=
  {b | ∀ i, 0 < b i}

/-- `mvBeta` is positive on `mvBetaDomain`. -/
theorem mvBeta_pos [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    0 < mvBeta b := by
  refine div_pos (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (hb i)) ?_
  exact Real.Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty)

/-- The integral representation of `mvBeta`. -/
theorem mvBeta_eq_integral {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    mvBeta b =
      ∫ u in stdSimplex ℝ ι, ∏ i, u i ^ (b i - 1) ∂stdSimplexMeasure := by
  sorry

/-- The interior of `stdSimplex ℝ ι` relative to its affine hull. -/
def stdSimplexInterior : Set (ι → ℝ) :=
  {u | u ∈ stdSimplex ℝ ι ∧ ∀ i, 0 < u i}

/-- The real-valued Dirichlet PDF with parameters `b`. This PDF is supported on
`stdSimplexInterior ι`. -/
def dirichletPdfReal (b : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / mvBeta b) *
    stdSimplexInterior.indicator (fun u ↦ ∏ i, u i ^ (b i - 1)) u

/-- The `ENNReal`-valued Dirichlet PDF. -/
def dirichletPdf (b : ι → ℝ) (u : ι → ℝ) : ENNReal :=
  ENNReal.ofReal (dirichletPdfReal b u)

/-- The Dirichlet measure on the standard simplex. -/
def dirichletMeasure
    (b : ι → ℝ) : Measure (ι → ℝ) :=
  stdSimplexMeasure.withDensity (dirichletPdf b)

/-- The `stdSimplexInterior` is a measurable set. -/
theorem measurableSet_stdSimplexInterior :
    MeasurableSet (stdSimplexInterior (ι := ι)) := by
  have hpos : IsOpen {u : ι → ℝ | ∀ i, 0 < u i} := by
    rw [show {u : ι → ℝ | ∀ i, 0 < u i} =
        ⋂ i, {u : ι → ℝ | 0 < u i} by
      ext u
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)
  change MeasurableSet (stdSimplex ℝ ι ∩ {u : ι → ℝ | ∀ i, 0 < u i})
  exact (isClosed_stdSimplex ℝ ι).measurableSet.inter hpos.measurableSet

/-- The real-valued Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdfReal (b : ι → ℝ) :
    Measurable (dirichletPdfReal b) := by
  unfold dirichletPdfReal
  exact measurable_const.mul
    ((by
      fun_prop :
      Measurable (fun u : ι → ℝ => ∏ i, u i ^ (b i - 1))).indicator
        (measurableSet_stdSimplexInterior (ι := ι)))

/-- The (ENNReal) Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdf (b : ι → ℝ) :
    Measurable (dirichletPdf b) := by
  exact ENNReal.measurable_ofReal.comp
    (measurable_dirichletPdfReal b)

/-- `stdSimplexMeasure` is a `SigmaFinite` measure. -/
instance :
    SigmaFinite (stdSimplexMeasure (ι := ι)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      rw [stdSimplexMeasure_empty]
      infer_instance
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.sigmaFinite_map

/-- The Radon-Nikodym derivative of the Dirichlet measure is almost everywhere
equal to the Dirichlet PDF. -/
theorem rnDeriv_dirichletMeasure {b : ι → ℝ} (_ : b ∈ mvBetaDomain) :
    (dirichletMeasure b).rnDeriv stdSimplexMeasure =ᵐ[stdSimplexMeasure]
      dirichletPdf b := by
  rw [dirichletMeasure]
  exact Measure.rnDeriv_withDensity _ (measurable_dirichletPdf b)

/-- The real-valued Dirichlet density is nonnegative. -/
theorem dirichletPdfReal_nonneg [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain)
    (u : ι → ℝ) :
    0 ≤ dirichletPdfReal b u := by
  unfold dirichletPdfReal
  refine mul_nonneg
    (le_of_lt (one_div_pos.mpr (mvBeta_pos hb))) ?_
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu]
    exact Finset.prod_nonneg fun i _ =>
      (Real.rpow_pos_of_pos (hu.2 i) _).le
  · simp [Set.indicator_of_notMem hu]

/-- Unwraps an integral against the Dirichlet measure into an integral against the
standard simplex measure, explicitly multiplying the function by the Dirichlet density. -/
theorem integral_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain)
    (f : (ι → ℝ) → ℝ) :
    ∫ u, f u ∂(dirichletMeasure b) =
      ∫ u in stdSimplex ℝ ι,
        f u * dirichletPdfReal b u ∂stdSimplexMeasure := by
  rw [dirichletMeasure]
  have hlt :
      ∀ᵐ u ∂stdSimplexMeasure, dirichletPdf b u < ⊤ := by
    filter_upwards with u
    simp [dirichletPdf]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_dirichletPdf b) hlt f]
  rw [← integral_indicator
    (isClosed_stdSimplex ℝ ι).measurableSet]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ stdSimplex ℝ ι
  · have hnonneg := dirichletPdfReal_nonneg hb u
    simp [hu, dirichletPdf,
      ENNReal.toReal_ofReal hnonneg, mul_comm]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- The measure of the standard simplex under the Dirichlet measure equals 1. -/
theorem dirichletMeasure_stdSimplex
    [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    dirichletMeasure b (stdSimplex ℝ ι) = 1 := by
  let p : (ι → ℝ) → ℝ := fun u => ∏ i, u i ^ (b i - 1)
  have hp_int : IntegrableOn p (stdSimplex ℝ ι) stdSimplexMeasure := by
    apply Integrable.of_integral_ne_zero
    rw [← mvBeta_eq_integral hb]
    exact ne_of_gt (mvBeta_pos hb)
  have hd_int : IntegrableOn (dirichletPdfReal b) (stdSimplex ℝ ι)
      stdSimplexMeasure := by
    apply hp_int.const_mul (1 / mvBeta b) |>.congr
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
    filter_upwards [hmem, hae] with u hu hpos
    simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
  have hd_integral :
      ∫ u in stdSimplex ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure = 1 := by
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
    calc
      ∫ u in stdSimplex ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure =
          ∫ u in stdSimplex ℝ ι, (1 / mvBeta b) * p u ∂stdSimplexMeasure := by
            apply integral_congr_ae
            filter_upwards [hmem, hae] with u hu hpos
            simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
      _ = (1 / mvBeta b) * ∫ u in stdSimplex ℝ ι, p u ∂stdSimplexMeasure := by
        rw [MeasureTheory.integral_const_mul]
      _ = 1 := by
        rw [← mvBeta_eq_integral hb]
        field_simp [ne_of_gt (mvBeta_pos hb)]
  unfold dirichletMeasure
  rw [withDensity_apply _ (isClosed_stdSimplex ℝ ι).measurableSet]
  unfold dirichletPdf
  rw [← ofReal_integral_eq_lintegral_ofReal hd_int]
  · rw [hd_integral]
    simp
  · filter_upwards with u
    exact dirichletPdfReal_nonneg hb u

/-- The Dirichlet density vanishes outside `stdSimplex ℝ ι`. -/
theorem dirichletPdf_eq_zero_of_not_mem_stdSimplex
    (b : ι → ℝ) {u : ι → ℝ} (hu : u ∉ stdSimplex ℝ ι) :
    dirichletPdf b u = 0 := by
  simp [dirichletPdf, dirichletPdfReal, stdSimplexInterior, hu]

/-- The Dirichlet measure is restricted to the standard simplex. -/
theorem dirichletMeasure_restrict (b : ι → ℝ) :
    (dirichletMeasure b).restrict (stdSimplex ℝ ι) =
      dirichletMeasure b := by
  unfold dirichletMeasure
  rw [restrict_withDensity
    (isClosed_stdSimplex ℝ ι).measurableSet]
  rw [← withDensity_indicator
    (isClosed_stdSimplex ℝ ι).measurableSet]
  apply withDensity_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ stdSimplex ℝ ι
  · simp [hu]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- The Dirichlet measure satisfies `isProbabilityMeasure`. -/
theorem isProbabilityMeasure_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    IsProbabilityMeasure (dirichletMeasure b) := by
  refine ⟨?_⟩
  rw [← dirichletMeasure_restrict b]
  rw [Measure.restrict_apply_univ]
  exact dirichletMeasure_stdSimplex hb

/-- The total mass / integral of the constant function 1 with respect to the Dirichlet
measure is 1. -/
theorem integral_dirichletMeasure_one [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    ∫ _, (1 : ℝ) ∂(dirichletMeasure b) = 1 := by
  let : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure hb
  simp

/-- The Dirichlet measure is absolutely continuous with respect to the Lebesgue measure. -/
theorem absolutelyContinuous_dirichletMeasure (b : ι → ℝ) :
    dirichletMeasure b ≪ stdSimplexMeasure :=
  withDensity_absolutelyContinuous _ _

/-- Defining the Dirichlet measure for the case of all `b` parameters equal. -/
def dirichletMeasureUniform (α : ℝ) : Measure (ι → ℝ) :=
  dirichletMeasure (fun _ => α)

/-- The case of all `b` parameters equal to 1 reduces to scaled Lebesgue measure. -/
theorem dirichletMeasureUniform_one :
    dirichletMeasureUniform (ι := ι) 1 =
      (1 / stdSimplexMeasure (stdSimplex ℝ ι)) •
      stdSimplexMeasure.restrict (stdSimplex ℝ ι) := by
  sorry

private lemma dirichletPdf_perm (b : ι → ℝ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    dirichletPdf (b ∘ σ) (u ∘ σ) = dirichletPdf b u := by
  unfold dirichletPdf dirichletPdfReal
  have hbeta : mvBeta (b ∘ σ) = mvBeta b := by
    unfold mvBeta
    simp only [Function.comp_apply, Equiv.sum_comp]
    congr 1
    exact Equiv.prod_comp σ (fun i => Gamma (b i))
  have hinter : (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
    have hsimp : (u ∘ σ) ∈ stdSimplex ℝ ι ↔ u ∈ stdSimplex ℝ ι := by
      change u ∈ (fun v => v ∘ σ) ⁻¹' stdSimplex ℝ ι ↔ _
      rw [preimage_stdSimplex_perm]
    simp only [stdSimplexInterior]
    constructor
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mp hu, fun i => by simpa using hp (σ.symm i)⟩
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mpr hu, fun i => hp (σ i)⟩
  rw [hbeta]
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    congr 2
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ (fun i => u i ^ (b i - 1)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- Permuting coordinates together with parameters is a measure-preserving transformation of
`dirichletMeasure`. -/
theorem measurePreserving_dirichletMeasure_perm (b : ι → ℝ) (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    (dirichletMeasure b) (dirichletMeasure (b ∘ σ)) := by
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun x := x ∘ σ
    invFun x := x ∘ σ.symm
    left_inv x := by funext i; simp
    right_inv x := by funext i; simp
    measurable_toFun := continuous_pi (fun i => continuous_apply (σ i)) |>.measurable
    measurable_invFun := continuous_pi (fun i => continuous_apply (σ.symm i)) |>.measurable
  }
  have hg : MeasurePreserving g stdSimplexMeasure stdSimplexMeasure := by
    simpa [g] using measurePreserving_stdSimplexMeasure_perm σ
  refine ⟨g.measurable, ?_⟩
  change Measure.map g (dirichletMeasure b) = dirichletMeasure (b ∘ σ)
  unfold dirichletMeasure
  ext s hs
  rw [Measure.map_apply g.measurable hs]
  rw [withDensity_apply _ (g.measurable hs), withDensity_apply _ hs]
  have hchange := hg.setLIntegral_comp_preimage hs (measurable_dirichletPdf (b ∘ σ))
  rw [← hchange]
  apply setLIntegral_congr_fun (g.measurable hs)
  intro x hx
  exact (dirichletPdf_perm b σ x).symm

/-- Dirichlet measure is closed under marginalisation or coarsening: pushing
`dirichletMeasure b` forward along `stdSimplexAggregate f` gives the Dirichlet
measure for the aggregated parameter vector. -/
theorem measurePreserving_stdSimplexAggregate_dirichletMeasure
    {κ : Type*} [Fintype κ] [DecidableEq κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    MeasurePreserving (stdSimplexAggregate f)
      (dirichletMeasure b) (dirichletMeasure (stdSimplexAggregate f b)) := by
  sorry

/-- Coordinate aggregation restated via the explicit density, unfolding
`measurePreserving_stdSimplexAggregate_dirichletMeasure` in terms of `stdSimplexMeasure` and
`dirichletPdf` directly rather than the bundled `dirichletMeasure`. -/
theorem stdSimplexAggregate_withDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) :
    Measure.map (stdSimplexAggregate f)
      (stdSimplexMeasure.withDensity (fun u ↦ ENNReal.ofReal (dirichletPdfReal b u))) =
      stdSimplexMeasure.withDensity
        (fun v ↦ ENNReal.ofReal (dirichletPdfReal (stdSimplexAggregate f b) v)) :=
  (measurePreserving_stdSimplexAggregate_dirichletMeasure hf hb).map_eq

/-- Marginalization of the Dirichlet density with respect to the `i` coordinate. -/
theorem betaMarginal [Nontrivial ι] {b : ι → ℝ} (hb : b ∈ mvBetaDomain) (i : ι) :
    Measure.map (fun u ↦ u i) (dirichletMeasure b) =
      betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) := by
  sorry

/-- The integral of a power product (generalized monomial) against the Dirichlet measure. -/
theorem integral_dirichletMeasure_power_product {b : ι → ℝ} (hb : b ∈ mvBetaDomain)
    (m : ι → ℝ) (hm : b + m ∈ mvBetaDomain) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (Gamma (∑ i, b i) / Gamma (∑ i, (b i + m i))) *
        ∏ i, (Gamma (b i + m i) / Gamma (b i)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp [dirichletMeasure, stdSimplexMeasure_empty]
  | inr h =>
      let : Nonempty ι := h
      rw [integral_dirichletMeasure hb]
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
      have hint :
          (∫ u in stdSimplex ℝ ι,
            (∏ i, u i ^ m i) * dirichletPdfReal b u ∂stdSimplexMeasure) =
          (1 / mvBeta b) *
            ∫ u in stdSimplex ℝ ι, ∏ i, u i ^ ((b + m) i - 1)
              ∂stdSimplexMeasure := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hmem, hae] with u hu hpos
        have hui : u ∈ stdSimplexInterior := ⟨hu, hpos⟩
        rw [dirichletPdfReal, Set.indicator_of_mem hui]
        rw [show (∏ i, u i ^ m i) * ((1 / mvBeta b) * ∏ i, u i ^ (b i - 1)) =
          (1 / mvBeta b) * ((∏ i, u i ^ m i) * ∏ i, u i ^ (b i - 1)) by ring]
        rw [← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          u i ^ m i * u i ^ (b i - 1) = u i ^ (m i + (b i - 1)) :=
            (Real.rpow_add (hpos i) (m i) (b i - 1)).symm
          _ = u i ^ ((b + m) i - 1) := by
            congr 1
            simp only [Pi.add_apply]
            ring
      rw [hint, ← mvBeta_eq_integral hm]
      unfold mvBeta
      simp only [Pi.add_apply]
      have hb_sum : Gamma (∑ i, b i) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty))
      have hm_sum : Gamma (∑ i, (b i + m i)) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos
          (Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty))
      have hb_each : ∀ i, Gamma (b i) ≠ 0 := fun i =>
        ne_of_gt (Gamma_pos_of_pos (hb i))
      rw [Finset.prod_div_distrib]
      field_simp

private lemma gamma_add_nat_div_gamma_eq_ascPochhammer
    (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) / Gamma x = (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [ne_of_gt (Gamma_pos_of_pos hx)]
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show x + ((n : ℝ) + 1) = (x + n) + 1 by ring]
      rw [Gamma_add_one (by positivity : x + (n : ℝ) ≠ 0)]
      rw [ascPochhammer_succ_eval]
      rw [mul_div_assoc, ih]
      ring

/-- The integral of a monomial against the Dirichlet measure. -/
/- The `[Nonempty ι]` hypothesis is essential.  For an empty index type the left side is
zero, while the empty products and the degree-zero rising factorial make the right side one. -/
theorem integral_dirichletMeasure_monomial [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain)
    (m : ι → ℕ) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (∏ i, (ascPochhammer ℝ (m i)).eval (b i)) /
        (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) := by
  let mr : ι → ℝ := fun i => m i
  have hm : b + mr ∈ mvBetaDomain := by
    intro i
    exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)
  have hpow := integral_dirichletMeasure_power_product hb mr hm
  have hfun : (fun u : ι → ℝ => ∏ i, u i ^ mr i) = fun u => ∏ i, u i ^ m i := by
    funext u
    simp [mr, Real.rpow_natCast]
  rw [hfun] at hpow
  rw [hpow]
  have hsum_pos : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hsum : (∑ i, (b i + mr i)) = (∑ i, b i) + (∑ i, m i) := by
    simp [mr, Finset.sum_add_distrib]
  rw [hsum]
  have hnum : Gamma ((∑ i, b i) + (∑ i, m i)) / Gamma (∑ i, b i) =
      (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) :=
    gamma_add_nat_div_gamma_eq_ascPochhammer _ hsum_pos _
  have hprod : ∏ i, (Gamma (b i + mr i) / Gamma (b i)) =
      ∏ i, (ascPochhammer ℝ (m i)).eval (b i) := by
    apply Finset.prod_congr rfl
    intro i _
    simpa [mr] using gamma_add_nat_div_gamma_eq_ascPochhammer (b i) (hb i) (m i)
  rw [hprod]
  have hG : Gamma (∑ i, b i) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hGN : Gamma ((∑ i, b i) + (∑ i, m i)) ≠ 0 := by
    apply ne_of_gt (Gamma_pos_of_pos ?_)
    have hm_nonneg : (0 : ℝ) ≤ ∑ i, m i := by positivity
    linarith
  have hP : (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) ≠ 0 := by
    rw [← hnum]
    exact div_ne_zero hGN hG
  have hratio : Gamma (∑ i, b i) / Gamma ((∑ i, b i) + (∑ i, m i)) =
      ((ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i))⁻¹ := by
    rw [← hnum]
    field_simp
  rw [hratio, div_eq_mul_inv, mul_comm]

/-- The mean of a single `u i`; a specialization of monomial integration. -/
theorem integral_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) (i : ι) :
    ∫ u, (u i) ∂(dirichletMeasure b) = (b i) / (∑ j, b j) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℝ := fun j => if j = i then 1 else 0
  have hm : b + m ∈ mvBetaDomain := by
    intro j
    dsimp [m]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (hb j) zero_le_one
    · simpa using hb j
  have hpow := integral_dirichletMeasure_power_product hb m hm
  have hsum_pos : 0 < ∑ j, b j :=
    Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hgamma_sum : Gamma (∑ j, b j) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i := by
    funext u
    simp [m]
  rw [hprod] at hpow
  have hsum_m : ∑ j, (b j + m j) = (∑ j, b j) + 1 := by
    simp [m, Finset.sum_add_distrib]
  have hprod_m : ∏ j, (Gamma (b j + m j) / Gamma (b j)) = b i := by
    calc
      ∏ j, (Gamma (b j + m j) / Gamma (b j)) =
          ∏ j, if j = i then b i else 1 := by
            apply Finset.prod_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp [m, Gamma_add_one, (hb i).ne',
                ne_of_gt (Gamma_pos_of_pos (hb i))]
            · simp [m, hji, ne_of_gt (Gamma_pos_of_pos (hb j))]
      _ = b i := by simp
  rw [hpow, hsum_m, hprod_m, Gamma_add_one hsum_pos.ne']
  field_simp

/-- The variance of the coordinate `u i`. -/
theorem variance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) (i : ι) :
    ∫ u, (u i - b i / ∑ j, b j) ^ 2 ∂(dirichletMeasure b) =
      (b i) * (∑ j, b j - b i) / ((∑ j, b j) ^ 2 * (∑ j, b j + 1)) := by
  sorry

/-- The covariance of distinct coordinates `u i` and `u j`. -/
theorem covariance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, (u i - b i / ∑ k, b k) * (u j - b j / ∑ k, b k)
      ∂(dirichletMeasure b) =
      -(b i) * (b j) / ((∑ k, b k) ^ 2 * (∑ k, b k + 1)) := by
  sorry

/- Specializations to the two-variable Dirichlet (Beta) density and measure that is defined
in Mathlib `ProbabilityTheory.betaMeasure`. -/

/-- For two parameters, `mvBetaDomain` is just positivity of both parameters. -/
@[simp] theorem mem_mvBetaDomain_fin_two (α β : ℝ) :
    (![α, β] : Fin 2 → ℝ) ∈ mvBetaDomain ↔
      0 < α ∧ 0 < β := by
  simp [mvBetaDomain]

/-- In the two-variable case, `mvBeta` is the ordinary beta function. -/
@[simp] theorem mvBeta_fin_two (α β : ℝ) :
    mvBeta (![α, β] : Fin 2 → ℝ) = beta α β := by
  simp [mvBeta, beta]

/-- Under `x ↦ ![x, 1 - x]`, the relative interior of the two-coordinate simplex
corresponds to the open unit interval. -/
@[simp] theorem mem_stdSimplexInterior_fin_two (x : ℝ) :
    (![x, 1 - x] : Fin 2 → ℝ) ∈ stdSimplexInterior ↔
      0 < x ∧ x < 1 := by
  constructor
  · intro h
    constructor
    · simpa using h.2 (0 : Fin 2)
    · have h1 : 0 < 1 - x := by
        simpa using h.2 (1 : Fin 2)
      exact sub_pos.mp h1
  · rintro ⟨hx0, hx1⟩
    constructor
    · change
        (∀ i : Fin 2, 0 ≤ (![x, 1 - x] : Fin 2 → ℝ) i) ∧
          ∑ i : Fin 2, (![x, 1 - x] : Fin 2 → ℝ) i = 1
      constructor
      · rw [Fin.forall_fin_two]
        constructor
        · simpa using hx0.le
        · simpa using (sub_pos.mpr hx1).le
      · simp
    · rw [Fin.forall_fin_two]
      constructor
      · simpa using hx0
      · simpa using sub_pos.mpr hx1

/-- The two-variable real Dirichlet density is the beta density under the
parametrization `x ↦ ![x, 1 - x]`. -/
@[simp] theorem dirichletPdfReal_fin_two (α β x : ℝ) :
    dirichletPdfReal (![α, β] : Fin 2 → ℝ) ![x, 1 - x] =
      betaPDFReal α β x := by
  rw [dirichletPdfReal, betaPDFReal, mvBeta_fin_two]
  by_cases hx : 0 < x ∧ x < 1
  · simp [hx, mul_assoc]
  · rw [ite_eq_right hx]
    simp [mem_stdSimplexInterior_fin_two, hx]

/-- The two-variable `ENNReal`-valued Dirichlet density is the beta density. -/
@[simp] theorem dirichletPdf_fin_two (α β x : ℝ) :
    dirichletPdf (![α, β] : Fin 2 → ℝ) ![x, 1 - x] = betaPDF α β x := by
  simp [dirichletPdf, betaPDF]

/-- The push-forward of the two-variable Dirichlet measure under the first
coordinate is the beta measure. -/
theorem map_dirichletMeasure_fin_two
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![α, β])) = betaMeasure α β := by
  have hb : (![α, β] : Fin 2 → ℝ) ∈ mvBetaDomain := by
    simpa using And.intro hα hβ
  simpa using
    (betaMarginal (b := (![α, β] : Fin 2 → ℝ)) hb (0 : Fin 2))

/- TODO: The Gamma ratio characterization. If X_i are independent Gamma(b_i, 1)-distributed
then (X_i / ∑_j X_j)_i is Dirichlet(b)-distributed. -/

end ProbabilityTheory

end DirichletMeasure
-- #lint
