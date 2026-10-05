/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Integral
public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Moment determination for measures supported on the standard simplex

Finite measures supported on the standard simplex in a finite real coordinate space are
determined by their monomial moments. This specializes the imported compact-support
determinacy theorem of the Tau Ceti contributors in
`TauCeti.Probability.Moments.CompactDeterminacy`. Integrability, polynomial integration and
almost-everywhere support lemmas supply the local measure-theoretic interface.

## Main results

* `MeasureTheory.integrable_of_continuous_of_restrict_stdSimplex`: A continuous real function is
  integrable against a finite measure supported on the simplex.
* `MeasureTheory.ae_mem_of_restrict_eq_self`: A measure equal to its restriction to a
  measurable set is concentrated on that set.
* `MeasureTheory.integral_mvPolynomial_eval_eq_of_forall_monomial`: Two finite measures on the
  simplex with the same monomial moments integrate every polynomial alike.
* `MeasureTheory.eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex`: Finite Borel
  measures supported on the standard simplex are determined by their monomial moments.
  This is an adapter to TauCeti's general compact-support theorem.
* `MeasureTheory.ae_eq_zero_of_forall_monomial_integral_mul_eq_zero_of_restrict_stdSimplex`:
  a complex function on the simplex all of whose monomial moments vanish vanishes almost
  everywhere (the `_real` version is the real case).
* `MeasureTheory.eqOn_zero_of_ae_eq_zero_stdSimplexMeasure`: a function continuous on the
  simplex and almost everywhere zero for the simplex measure vanishes on the simplex.

## References

* `Mathlib.Algebra.MvPolynomial.Eval`: formal background used by this module.
* `TauCeti.Probability.Moments.CompactDeterminacy`: compact-support moment determinacy.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section

namespace MeasureTheory

open scoped ENNReal

/-- A continuous real function is integrable against a finite measure supported on the simplex. -/
theorem integrable_of_continuous_of_restrict_stdSimplex
    {α : Type*} [Fintype α] {μ : Measure (α → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ) {g : (α → ℝ) → ℝ}
    (hg : Continuous g) : Integrable g μ := by
  have hint : IntegrableOn g (Convexity.StdSimplex.coordinateSet ℝ α) μ :=
    hg.continuousOn.integrableOn_compact (Convexity.StdSimplex.isCompact_coordinateSet ℝ α)
  rwa [IntegrableOn, hμ] at hint

/-- A measure equal to its restriction to a measurable set is concentrated on that set. -/
theorem ae_mem_of_restrict_eq_self {β : Type*} [MeasurableSpace β] {μ : Measure β} {s : Set β}
    (hs : MeasurableSet s) (hμ : μ.restrict s = μ) : ∀ᵐ x ∂μ, x ∈ s :=
  hμ ▸ ae_restrict_mem hs

/-- Two finite measures on the simplex with the same monomial moments integrate every
polynomial alike. -/
theorem integral_mvPolynomial_eval_eq_of_forall_monomial
    {α : Type*} [Fintype α]
    {μ ν : Measure (α → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ)
    (hν : ν.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = ν)
    (h : ∀ m : α → ℕ, ∫ x, (∏ i, x i ^ m i) ∂μ = ∫ x, (∏ i, x i ^ m i) ∂ν)
    (q : MvPolynomial α ℝ) :
    ∫ x, MvPolynomial.eval x q ∂μ = ∫ x, MvPolynomial.eval x q ∂ν := by
  simp_rw [MvPolynomial.eval_eq']
  have hterm (d : α →₀ ℕ) :
      Integrable (fun x : α → ℝ => q.coeff d * ∏ i, x i ^ d i) μ :=
    (integrable_of_continuous_of_restrict_stdSimplex hμ (by fun_prop)).const_mul _
  have hterm' (d : α →₀ ℕ) :
      Integrable (fun x : α → ℝ => q.coeff d * ∏ i, x i ^ d i) ν :=
    (integrable_of_continuous_of_restrict_stdSimplex hν (by fun_prop)).const_mul _
  rw [integral_finsetSum _ fun d _ => hterm d, integral_finsetSum _ fun d _ => hterm' d]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul, integral_const_mul, h fun i => d i]

/-- Finite Borel measures supported on the standard simplex are determined by their
monomial moments.

Uses `TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support`, converting the restriction
hypotheses to almost-everywhere support on the compact simplex. -/
theorem eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex
    {α : Type*} [Fintype α]
    {μ ν : Measure (α → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ)
    (hν : ν.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = ν)
    (h : ∀ m : α → ℕ, ∫ x, (∏ i, x i ^ m i) ∂μ = ∫ x, (∏ i, x i ^ m i) ∂ν) :
    μ = ν := by
  have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
  exact TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ α)
    (ae_iff.mp (ae_mem_of_restrict_eq_self hs hμ))
    (ae_iff.mp (ae_mem_of_restrict_eq_self hs hν)) h

/-- On a measure supported on the simplex, monomial multiples of an integrable function are
integrable: the monomials are bounded by one there. -/
theorem integrable_monomial_mul_of_restrict_stdSimplex
    {α : Type*} [Fintype α] {μ : Measure (α → ℝ)}
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ) {h : (α → ℝ) → ℂ}
    (hh : Integrable h μ) (m : α → ℕ) :
    Integrable (fun x => ((∏ i, x i ^ m i : ℝ) : ℂ) * h x) μ := by
  have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
  refine hh.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_mem_of_restrict_eq_self hs hμ] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow, abs_of_nonneg (hx.1 i)]
  exact pow_le_one₀ (hx.1 i) (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hx i).2

/-- **Vanishing moments, real form.** A real function integrable against a finite measure
supported on the standard simplex, all of whose monomial moments vanish, vanishes almost
everywhere. The positive and negative parts define two measures with the same moments. -/
theorem ae_eq_zero_of_forall_monomial_integral_mul_eq_zero_of_restrict_stdSimplex_real
    {α : Type*} [Fintype α] {μ : Measure (α → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ) {h : (α → ℝ) → ℝ}
    (hh : Integrable h μ) (hmom : ∀ m : α → ℕ, ∫ x, (∏ i, x i ^ m i) * h x ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
  have := isFiniteMeasure_withDensity_ofReal hh.2
  have := isFiniteMeasure_withDensity_ofReal hh.neg.2
  have hsupp (f : (α → ℝ) → ℝ) : (μ.withDensity fun x => ENNReal.ofReal (f x)).restrict
      (Convexity.StdSimplex.coordinateSet ℝ α) = μ.withDensity fun x => ENNReal.ofReal (f x) := by
    rw [restrict_withDensity hs, hμ]
  have hbound : ∀ᵐ x ∂μ, ∀ m : α → ℕ, ‖∏ i, x i ^ m i‖ ≤ 1 := by
    filter_upwards [ae_mem_of_restrict_eq_self hs hμ] with x hx m
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
    rw [abs_pow, abs_of_nonneg (hx.1 i)]
    exact pow_le_one₀ (hx.1 i) (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hx i).2
  have hint (f : (α → ℝ) → ℝ) (hf : Integrable f μ) (m : α → ℕ) :
      Integrable (fun x => max (f x) 0 * ∏ i, x i ^ m i) μ :=
    hf.pos_part.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (hbound.mono fun x hx => hx m)
  have hmoment (f : (α → ℝ) → ℝ) (hf : Integrable f μ) (m : α → ℕ) :
      ∫ x, ∏ i, x i ^ m i ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) =
        ∫ x, max (f x) 0 * ∏ i, x i ^ m i ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.1.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  have heq := eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex (hsupp h) (hsupp (-h))
    fun m => by
      rw [hmoment h hh, hmoment (-h) hh.neg, ← sub_eq_zero, ← integral_sub (hint h hh m)
        (hint (-h) hh.neg m)]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (hmom m)
      simp only [Pi.neg_apply]
      rcases le_total (h x) 0 with hx | hx
      · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; ring
      · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
  rw [withDensity_eq_iff hh.1.aemeasurable.ennreal_ofReal
    hh.neg.1.aemeasurable.ennreal_ofReal
    ((lintegral_mono fun x => Real.ofReal_le_enorm (h x)).trans_lt hh.2).ne] at heq
  filter_upwards [heq] with x hx
  simp only [Pi.neg_apply, Pi.zero_apply] at hx ⊢
  rcases le_total (h x) 0 with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0, eq_comm, ENNReal.ofReal_eq_zero] at hx; linarith
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h0), ENNReal.ofReal_eq_zero] at hx; linarith

/-- **Vanishing moments, complex form.** A complex function integrable against a finite
measure supported on the standard simplex, all of whose monomial moments vanish, vanishes
almost everywhere. -/
theorem ae_eq_zero_of_forall_monomial_integral_mul_eq_zero_of_restrict_stdSimplex
    {α : Type*} [Fintype α] {μ : Measure (α → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ) {h : (α → ℝ) → ℂ}
    (hh : Integrable h μ)
    (hmom : ∀ m : α → ℕ, ∫ x, ((∏ i, x i ^ m i : ℝ) : ℂ) * h x ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  have hpart (f : ℂ → ℝ) (hf : ∀ (r : ℝ) (z : ℂ), f ((r : ℂ) * z) = r * f z)
      (hfi : ∀ m : α → ℕ, ∫ x, f (((∏ i, x i ^ m i : ℝ) : ℂ) * h x) ∂μ =
        f (∫ x, ((∏ i, x i ^ m i : ℝ) : ℂ) * h x ∂μ)) (hf0 : f 0 = 0)
      (hint : Integrable (fun x => f (h x)) μ) : (fun x => f (h x)) =ᵐ[μ] 0 :=
    ae_eq_zero_of_forall_monomial_integral_mul_eq_zero_of_restrict_stdSimplex_real hμ hint
      fun m => by simp_rw [← hf, hfi, hmom, hf0]
  have hre := hpart Complex.re (fun r z => by simp)
    (fun m => integral_re (integrable_monomial_mul_of_restrict_stdSimplex hμ hh m)) rfl hh.re
  have him := hpart Complex.im (fun r z => by simp)
    (fun m => integral_im (integrable_monomial_mul_of_restrict_stdSimplex hμ hh m)) rfl hh.im
  filter_upwards [hre, him] with x h1 h2
  exact Complex.ext h1 h2

open scoped Classical in
/-- A function continuous on the standard simplex which vanishes almost everywhere for the
simplex measure vanishes on the whole simplex. In free coordinates the simplex is a convex
body with nonempty interior, on which Lebesgue measure charges every nonempty open set. -/
theorem eqOn_zero_of_ae_eq_zero_stdSimplexMeasure {α : Type*} [Fintype α] {h : (α → ℝ) → ℂ}
    (hc : ContinuousOn h (Convexity.StdSimplex.coordinateSet ℝ α))
    (hh : h =ᵐ[Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ α)] 0) :
    Set.EqOn h 0 (Convexity.StdSimplex.coordinateSet ℝ α) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
    intro u hu
    have := hu.2
    simp at this
  | inr hα =>
  obtain ⟨i⟩ := id hα
  set S := Convexity.StdSimplex.coordinateSet ℝ α
  set φ := stdSimplexCoordMap (R := ℝ) i
  have hφ : Continuous φ := continuous_stdSimplexCoordMap i
  have hpre : φ ⁻¹' S = stdSimplexFreeCoords i := preimage_stdSimplexCoordMap i
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
  rw [Measure.stdSimplexMeasure_eq_at i, Measure.stdSimplexMeasureAt_eq_map,
    Measure.restrict_map hφ.measurable hS] at hh
  replace hh := ae_of_ae_map hφ.measurable.aemeasurable hh
  · -- Transfer to free coordinates, where Lebesgue measure is positive on open sets.
    have hfree : Set.EqOn (h ∘ φ) 0 (stdSimplexFreeCoords i) := by
      rw [← hpre]
      refine Measure.eqOn_of_ae_eq (μ := volume) hh (hc.comp hφ.continuousOn fun _ hx => hx)
        continuousOn_const ?_
      rw [hpre]
      -- The free simplex is convex with nonempty interior.
      have hconv : Convex ℝ (stdSimplexFreeCoords (R := ℝ) i) := by
        intro x hx y hy a b ha hb hab
        refine ⟨fun j => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum]
          nlinarith [hx.2, hy.2]
      set n : ℝ := Fintype.card {j : α // j ≠ i} + 1
      have hn : 0 < n := by positivity
      have hint : (fun _ => 1 / (2 * n) : {j : α // j ≠ i} → ℝ) ∈
          interior (stdSimplexFreeCoords (R := ℝ) i) := by
        refine interior_maximal
          (t := {x : {j : α // j ≠ i} → ℝ | (∀ j, 0 < x j) ∧ ∑ j, x j < 1}) ?_ ?_ ?_
        · exact fun x hx => ⟨fun j => (hx.1 j).le, hx.2.le⟩
        · simp only [Set.ofPred_and]
          refine IsOpen.inter ?_ (isOpen_lt (by fun_prop) continuous_const)
          simp only [Set.ofPred_forall]
          exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)
        · refine ⟨fun _ => by positivity, ?_⟩
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [mul_one_div, div_lt_one (by positivity)]
          simp only [n]; linarith
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨_, hint⟩]
      exact subset_closure
    intro u hu
    have hu' : stdSimplexCoordMap i (stdSimplexCoordProj i u) = u :=
      stdSimplexCoordMap_coordProj i (mem_fintypeAffineCoords_iff_sum.mpr hu.2)
    have hv : stdSimplexCoordProj i u ∈ stdSimplexFreeCoords i := by
      rw [← hpre]
      simpa [Set.mem_preimage, φ, hu'] using hu
    have := hfree hv
    simpa [φ, hu'] using this

end MeasureTheory

end
