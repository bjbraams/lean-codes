/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Integral
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Radial integration over the positive orthant

The radial coordinate is the sum of the coordinates. Its angular measure is the
coordinate-normalized standard-simplex measure, so the radial factor is `t^(card ι - 1)`.

## Main results

* `MeasureTheory.radial_slice_smul`: Scaling free coordinates in a slice of fixed coordinate sum
  scales its simplex chart.
* `MeasureTheory.lintegral_eq_lintegral_sum_slice`: Lebesgue integration with the sum of the
  coordinates as the first coordinate.
* `MeasureTheory.sum_radial_slice`: The affine slice with total `t` has coordinate sum `t`.
* `MeasureTheory.nonneg_radial_slice_iff`: Nonnegative points on the slice of total `t` are
  parametrized by the positive simplex of radius `t` in the free coordinates.
* `MeasureTheory.lintegral_eq_radial_stdSimplex`: Radial integration for a measurable
  nonnegative function supported on the positive orthant. The simplex measure is the
  coordinate-normalized one, with no Euclidean area factor.
* `MeasureTheory.map_polarMap`: in simplicial polar coordinates `(t, u) ↦ t • u`, Lebesgue
  measure on the closed positive orthant is the image of `t^(card ι - 1) dt ⊗ du`.
* `MeasureTheory.integrable_comp_polarMap_iff`: integrability transfers to polar coordinates.
* `MeasureTheory.integral_eq_radial_stdSimplex`: radial integration for integrable functions with
  values in a Banach space, supported on the closed positive orthant.

## References

* `Mathlib.MeasureTheory.Group.LIntegral`: formal background used by this module.
* The polar decomposition is the measure-theoretic content of the Gamma normalization of the
  Dirichlet distribution (`Dirichlet.Gamma`) and of the Mellin bridge for the regularized
  Dirichlet transform (`DirichletTransformProgram.md`, step 5).
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Scaling free coordinates in a slice of fixed coordinate sum scales its simplex chart. -/
theorem radial_slice_smul (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    (Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, t * v j, t • v) =
      t • stdSimplexCoordMap i v := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [stdSimplexCoordMap, ← Finset.mul_sum, mul_sub]
  · simp [stdSimplexCoordMap, hj]

open scoped Classical in
/-- Lebesgue integration with the sum of the coordinates as the first coordinate. -/
theorem lintegral_eq_lintegral_sum_slice (i : ι) (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ t : ℝ, ∫⁻ v : {j : ι // j ≠ i} → ℝ,
      f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v)) := by
  let e := Homeomorph.funSplitAt ℝ i
  have hf' : Measurable (fun p => f (e.symm p)) := hf.comp e.symm.measurable
  have H : (∫⁻ x, f x) = ∫⁻ p, f (e.symm p) ∂(volume.prod volume) := by
    simpa only [e, Homeomorph.symm_apply_apply] using
      (volume_preserving_funSplitAt i).lintegral_comp hf'
  rw [H]
  rw [lintegral_prod_symm _ hf'.aemeasurable]
  have ht (v : {j : ι // j ≠ i} → ℝ) :=
    lintegral_sub_right_eq_self (μ := volume) (fun t : ℝ => f (e.symm (t, v))) (∑ j, v j)
  simp_rw [← ht]
  exact lintegral_lintegral_swap (by fun_prop)

open scoped Classical in
/-- The affine slice with total `t` has coordinate sum `t`. -/
theorem sum_radial_slice (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    ∑ j, (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j = t := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
  have hsum : (∑ j : {j : ι // j ≠ i},
      (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j) = ∑ j, v j :=
    Finset.sum_congr rfl (fun j _ => by simp [j.property])
  rw [hsum]
  simp

open scoped Classical in
/-- Nonnegative points on the slice of total `t` are parametrized by the positive simplex
of radius `t` in the free coordinates. -/
theorem nonneg_radial_slice_iff (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    (∀ j, 0 ≤ (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j) ↔
      v ∈ posSimplex {j : ι // j ≠ i} t := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · simpa [j.property] using h j
    · have H := h i
      simpa using H
  · rintro ⟨hv, hs⟩ j
    by_cases hj : j = i
    · subst j
      simpa using sub_nonneg.mpr hs
    · simpa [hj] using hv ⟨j, hj⟩

open scoped Classical in
/-- Radial integration for a measurable nonnegative function supported on the positive
orthant. The simplex measure is the coordinate-normalized one, with no Euclidean area factor. -/
theorem lintegral_eq_radial_stdSimplex [Nonempty ι]
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hsupp : ∀ x, ¬ (∀ i, 0 ≤ x i) → f x = 0) :
    ∫⁻ x, f x = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (Fintype.card ι - 1)) *
      ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, f (t • u) ∂stdSimplexMeasure := by
  let i : ι := Classical.choice inferInstance
  rw [lintegral_eq_lintegral_sum_slice i f hf, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht0
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hs : (∫⁻ v : {j : ι // j ≠ i} → ℝ,
        f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v))) =
        ∫⁻ v in posSimplex {j : ι // j ≠ i} t,
          f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v)) := by
      rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
      apply lintegral_congr
      intro v
      by_cases hv : v ∈ posSimplex {j : ι // j ≠ i} t
      · rw [Set.indicator_of_mem hv]
      · rw [Set.indicator_of_notMem hv]
        exact hsupp _ (fun h => hv ((nonneg_radial_slice_iff i t v).mp h))
    rw [hs, lintegral_posSimplex_scale i t ht,
      lintegral_stdSimplex_eq_lintegral_freeCoords i]
    congr 1
    apply lintegral_congr
    intro v
    simp only [Pi.smul_apply, smul_eq_mul, radial_slice_smul]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro v
    apply hsupp
    intro hv
    have H := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hv j)
    rw [sum_radial_slice] at H
    exact ht0 (le_antisymm (le_of_not_gt ht) H)

/-! ### Polar coordinates as a measure identity -/

variable (ι) in
/-- The radial measure `t^(card ι - 1) dt` on `(0, ∞)`. -/
def radialMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (t ^ (Fintype.card ι - 1))

/-- The radial measure is s-finite. -/
instance : SFinite (radialMeasure ι) := by
  unfold radialMeasure
  infer_instance

/-- Simplicial polar coordinates: a radius `t` and a point `u` of the simplex give `t • u`. -/
def polarMap (p : ℝ × (ι → ℝ)) : ι → ℝ := p.1 • p.2

omit [Fintype ι] in
/-- Simplicial polar coordinates are continuous. -/
theorem continuous_polarMap : Continuous (polarMap (ι := ι)) := by
  unfold polarMap
  fun_prop

/-- The closed positive orthant. -/
def nonnegOrthant : Set (ι → ℝ) := {x | ∀ i, 0 ≤ x i}

/-- The closed positive orthant is measurable. -/
theorem measurableSet_nonnegOrthant : MeasurableSet (nonnegOrthant (ι := ι)) := by
  have : nonnegOrthant (ι := ι) = Set.univ.pi fun _ => Ici 0 := by
    ext x; simp [nonnegOrthant, Pi.le_def]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ici

/-- A positive multiple of a simplex point lies in the closed positive orthant. -/
theorem smul_mem_nonnegOrthant {t : ℝ} (ht : 0 ≤ t) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) : t • u ∈ nonnegOrthant :=
  fun i => mul_nonneg ht (hu.1 i)

/-- **Polar coordinates for Lebesgue measure on the orthant.** Lebesgue measure on the closed
positive orthant is the image of `t^(card ι - 1) dt ⊗ du` under `(t, u) ↦ t • u`, with `du` the
coordinate-normalized simplex measure. -/
theorem map_polarMap [Nonempty ι] :
    Measure.map polarMap ((radialMeasure ι).prod
      (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))) =
      volume.restrict nonnegOrthant := by
  set Δ := Convexity.StdSimplex.coordinateSet ℝ ι
  have hΔ : MeasurableSet Δ := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hw : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (Fintype.card ι - 1)) := by fun_prop
  ext s hs
  have hs' : MeasurableSet (polarMap ⁻¹' s) := continuous_polarMap.measurable hs
  rw [Measure.map_apply continuous_polarMap.measurable hs, Measure.restrict_apply hs,
    Measure.prod_apply hs', radialMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hw (measurable_measure_prodMk_left hs'),
    ← lintegral_indicator_one (hs.inter measurableSet_nonnegOrthant),
    lintegral_eq_radial_stdSimplex ((s ∩ nonnegOrthant).indicator 1) (measurable_one.indicator
      (hs.inter measurableSet_nonnegOrthant))
      (fun x hx => indicator_of_notMem (fun h => hx h.2) _)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [Pi.mul_apply]
  congr 1
  rw [← lintegral_indicator_one (measurable_prodMk_left hs')]
  refine setLIntegral_congr_fun hΔ fun u hu => ?_
  by_cases h : t • u ∈ s
  · rw [indicator_of_mem (show u ∈ Prod.mk t ⁻¹' (polarMap ⁻¹' s) from h),
      indicator_of_mem (show t • u ∈ s ∩ nonnegOrthant from
        ⟨h, smul_mem_nonnegOrthant (le_of_lt ht) hu⟩)]
    rfl
  · rw [indicator_of_notMem (show u ∉ Prod.mk t ⁻¹' (polarMap ⁻¹' s) from h),
      indicator_of_notMem (show t • u ∉ s ∩ nonnegOrthant from fun h' => h h'.1)]

/-- **Integrability in polar coordinates.** A function is integrable on the closed positive
orthant if and only if its composition with simplicial polar coordinates is integrable for
`t^(card ι - 1) dt ⊗ du`. -/
theorem integrable_comp_polarMap_iff [Nonempty ι] {E : Type*} [NormedAddCommGroup E]
    {G : (ι → ℝ) → E} (hG : AEStronglyMeasurable G (volume.restrict nonnegOrthant)) :
    Integrable (fun p => G (polarMap p)) ((radialMeasure ι).prod
      (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))) ↔
      IntegrableOn G nonnegOrthant := by
  rw [IntegrableOn, ← map_polarMap] at *
  exact (integrable_map_measure hG continuous_polarMap.measurable.aemeasurable).symm

/-- **Integration in simplicial polar coordinates.** For an integrable function supported on the
closed positive orthant,
`∫ G = ∫_{t > 0} t^(card ι - 1) • ∫_Δ G (t • u) du dt`. -/
theorem integral_eq_radial_stdSimplex [Nonempty ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : (ι → ℝ) → E} (hG : Integrable G)
    (hsupp : ∀ x, ¬ (∀ i, 0 ≤ x i) → G x = 0) :
    ∫ x, G x = ∫ t in Ioi (0 : ℝ), (t ^ (Fintype.card ι - 1)) •
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, G (t • u) ∂stdSimplexMeasure := by
  have hw : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (Fintype.card ι - 1)) := by fun_prop
  have hGm : AEStronglyMeasurable G (volume.restrict nonnegOrthant) := hG.1.restrict
  have hGi := (integrable_comp_polarMap_iff hGm).mpr hG.integrableOn
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := nonnegOrthant)
      (fun x hx => hsupp x hx), ← map_polarMap,
    integral_map continuous_polarMap.measurable.aemeasurable (by rwa [map_polarMap]),
    integral_prod _ hGi, radialMeasure,
    integral_withDensity_eq_integral_toReal_smul hw
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [polarMap]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt ht) _)]

end MeasureTheory

end
