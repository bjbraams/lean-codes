/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Moments.Variance
public import Dirichlet.Real
public import StdSimplexMeasure.MomentDetermination

import Pochhammer.Gamma
import Pochhammer.Vandermonde
import all StdSimplexMeasure.Measure

/-!
# Moments and aggregation of Dirichlet measure

This file records monomial moments of `dirichletMeasure`, the aggregation (marginalisation)
theorem, coordinate means/variances, and the identification of the two-variable case with
Mathlib's `betaMeasure`.

The construction of the measure itself is in `Dirichlet.Real`.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- Aggregating a Dirichlet parameter vector along a surjection stays in the
positive parameter domain. -/
theorem mem_mvRealBetaDomain_stdSimplexAggregate
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    stdSimplexAggregate f b ∈ mvRealBetaDomain :=
  stdSimplexAggregate_pos hf hb

/-- Coordinate aggregation is continuous, as a linear map on a finite product. -/
theorem continuous_stdSimplexAggregate {κ : Type*} [Fintype κ] (f : ι → κ) :
    Continuous (stdSimplexAggregate (R := ℝ) f) :=
  _root_.continuous_stdSimplexAggregate f

/-- The integral of a power product (generalized monomial) against the Dirichlet measure. -/
theorem integral_dirichletMeasure_power_product {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℝ) (hm : b + m ∈ mvRealBetaDomain) :
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
          (1 / mvRealBeta b) *
            ∫ u in stdSimplex ℝ ι, ∏ i, u i ^ ((b + m) i - 1)
              ∂stdSimplexMeasure := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hmem, hae] with u hu hpos
        have hui : u ∈ stdSimplexInterior := ⟨hu, hpos⟩
        rw [dirichletPdfReal, Set.indicator_of_mem hui]
        rw [show (∏ i, u i ^ m i) * ((1 / mvRealBeta b) * ∏ i, u i ^ (b i - 1)) =
          (1 / mvRealBeta b) * ((∏ i, u i ^ m i) * ∏ i, u i ^ (b i - 1)) by ring]
        rw [← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          u i ^ m i * u i ^ (b i - 1) = u i ^ (m i + (b i - 1)) :=
            (rpow_add (hpos i) (m i) (b i - 1)).symm
          _ = u i ^ ((b + m) i - 1) := by
            congr 1
            simp only [Pi.add_apply]
            ring
      rw [hint, ← mvRealBeta_eq_integral hm]
      unfold mvRealBeta
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

/-- The integral of a monomial against the Dirichlet measure. -/
/- The `[Nonempty ι]` hypothesis is essential.  For an empty index type the left side is
zero, while the empty products and the degree-zero rising factorial make the right side one. -/
theorem integral_dirichletMeasure_monomial [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℕ) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (∏ i, (ascPochhammer ℝ (m i)).eval (b i)) /
        (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) := by
  let mr : ι → ℝ := fun i => m i
  have hm : b + mr ∈ mvRealBetaDomain := by
    intro i
    exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)
  have hpow := integral_dirichletMeasure_power_product hb mr hm
  have hfun : (fun u : ι → ℝ => ∏ i, u i ^ mr i) = fun u => ∏ i, u i ^ m i := by
    funext u
    simp [mr, rpow_natCast]
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

/-- Pushing a Dirichlet monomial forward under coordinate aggregation yields the
Dirichlet monomial for the aggregated parameters. This is the moment form of the
multinomial Chu–Vandermonde identity. -/
theorem integral_dirichletMeasure_comp_stdSimplexAggregate_monomial
    [Nonempty ι] {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (m : κ → ℕ) :
    ∫ u, (∏ k, stdSimplexAggregate f u k ^ m k) ∂(dirichletMeasure b) =
      ∫ v, (∏ k, v k ^ m k) ∂(dirichletMeasure (stdSimplexAggregate f b)) := by
  classical
  have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
  let fiber (k : κ) : Finset ι := Finset.univ.filter (fun i => f i = k)
  have hAgg (u : ι → ℝ) (k : κ) :
      stdSimplexAggregate f u k = ∑ i ∈ fiber k, u i := by
    simp [fiber, stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  have hb' : stdSimplexAggregate f b ∈ mvRealBetaDomain :=
    mem_mvRealBetaDomain_stdSimplexAggregate hf hb
  have hsum_b : ∑ i, b i = ∑ k, stdSimplexAggregate f b k := by
    simp_rw [hAgg]
    exact (Finset.sum_fiberwise (Finset.univ : Finset ι) f b).symm
  have hexpand (u : ι → ℝ) :
      ∏ k, stdSimplexAggregate f u k ^ m k =
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
            ∏ i, u i ^ p (f i) i := by
    simp_rw [hAgg]
    have hbinoms (k : κ) :
        (∑ i ∈ fiber k, u i) ^ m k =
          ∑ α ∈ Finset.piAntidiag (fiber k) (m k),
            (Nat.multinomial (fiber k) α : ℝ) * ∏ i ∈ fiber k, u i ^ α i :=
      Finset.sum_pow_eq_sum_piAntidiag (fiber k) (fun i => u i) (m k)
    simp_rw [hbinoms]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    have hcoord :
        ∏ k, ∏ i ∈ fiber k, u i ^ p k i =
          ∏ k, ∏ i ∈ fiber k, u i ^ p (f i) i := by
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    rw [hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]
  have hdeg (p : κ → (ι → ℕ))
      (hp : p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k))) :
      ∑ i, p (f i) i = ∑ k, m k := by
    have hp' : ∀ k, p k ∈ Finset.piAntidiag (fiber k) (m k) := by
      simpa [Fintype.mem_piFinset] using hp
    calc
      ∑ i, p (f i) i
          = ∑ k, ∑ i ∈ fiber k, p (f i) i :=
            (Finset.sum_fiberwise (Finset.univ : Finset ι) f
              (fun i => p (f i) i)).symm
      _ = ∑ k, ∑ i ∈ fiber k, p k i := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
            have hik : f i = k := (Finset.mem_filter.mp hi).2
            simp [hik]
      _ = ∑ k, m k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact (Finset.mem_piAntidiag.mp (hp' k)).1
  have hsum_pos : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hDpos :
      0 < (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
    rw [← gamma_add_nat_div_gamma_eq_ascPochhammer _ hsum_pos]
    positivity
  have hDne : (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) ≠ 0 := ne_of_gt hDpos
  have hN (p : κ → (ι → ℕ)) :
      ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
        ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i) := by
    have hcoord :
        ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
          ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i) := by
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    rw [← hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  have hterm (p : κ → (ι → ℕ)) :
      Integrable (fun u : ι → ℝ =>
        (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
          ∏ i, u i ^ p (f i) i) (dirichletMeasure b) := by
    let : IsProbabilityMeasure (dirichletMeasure b) :=
      isProbabilityMeasure_dirichletMeasure hb
    exact (integrable_of_continuous_of_restrict_stdSimplex
      (dirichletMeasure_restrict b) (by fun_prop)).const_mul _
  rw [integral_finsetSum _ fun p _ => hterm p]
  simp_rw [integral_const_mul]
  have hsum :
      ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
            ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
        (∏ k, (ascPochhammer ℝ (m k)).eval (stdSimplexAggregate f b k)) /
          (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
    have hinter (p : κ → ι → ℕ)
        (hp : p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k))) :
        ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
          (∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
            (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
      rw [integral_dirichletMeasure_monomial hb (fun i => p (f i) i), hdeg p hp]
    have h1 :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
          ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) :=
      Finset.sum_congr rfl fun p hp => by rw [hinter p hp]
    rw [h1]
    have hvander :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
          ∏ k, (ascPochhammer ℝ (m k)).eval (stdSimplexAggregate f b k) := by
      have hprod (p : κ → ι → ℕ) :
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
            ∏ k, ((Nat.multinomial (fiber k) (p k) : ℝ) *
              ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i)) := by
        rw [hN p, ← Finset.prod_mul_distrib]
      rw [Finset.sum_congr rfl fun p _ => hprod p]
      rw [← Finset.prod_univ_sum
        (t := fun k => Finset.piAntidiag (fiber k) (m k))
        (f := fun k α =>
          (Nat.multinomial (fiber k) α : ℝ) *
            ∏ i ∈ fiber k, (ascPochhammer ℝ (α i)).eval (b i))]
      refine Finset.prod_congr rfl fun k _ => ?_
      simpa [hAgg] using
        (ascPochhammer_eval_sum (fiber k) b (m k)).symm
    have h2 :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) =
          (∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
            (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
      have h2a :
          ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                  (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) =
            ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              ((∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) *
                ((ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i))⁻¹ :=
        Finset.sum_congr rfl fun p _ => by rw [div_eq_mul_inv, mul_assoc]
      rw [h2a, ← Finset.sum_mul, ← div_eq_mul_inv]
    rw [h2, hvander]
  rw [hsum, integral_dirichletMeasure_monomial hb' m, hsum_b]

/-- Dirichlet measure is closed under marginalisation or coarsening: pushing
`dirichletMeasure b` forward along `stdSimplexAggregate f` gives the Dirichlet
measure for the aggregated parameter vector. -/
theorem measurePreserving_stdSimplexAggregate_dirichletMeasure
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    MeasurePreserving (stdSimplexAggregate f)
      (dirichletMeasure b) (dirichletMeasure (stdSimplexAggregate f b)) := by
  classical
  have hT : Continuous (stdSimplexAggregate (R := ℝ) f) :=
    continuous_stdSimplexAggregate f
  refine ⟨hT.measurable, ?_⟩
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      have : IsEmpty κ := ⟨fun k => (hf k).elim fun a _ => isEmptyElim a⟩
      unfold dirichletMeasure
      simp [stdSimplexMeasure_empty]
  | inr _ =>
      have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
      have hb' : stdSimplexAggregate f b ∈ mvRealBetaDomain :=
        mem_mvRealBetaDomain_stdSimplexAggregate hf hb
      let : IsProbabilityMeasure (dirichletMeasure b) :=
        isProbabilityMeasure_dirichletMeasure hb
      let : IsProbabilityMeasure (dirichletMeasure (stdSimplexAggregate f b)) :=
        isProbabilityMeasure_dirichletMeasure hb'
      let : IsProbabilityMeasure
          (Measure.map (stdSimplexAggregate f) (dirichletMeasure b)) :=
        isProbabilityMeasure_map hT.aemeasurable
      refine eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex ?_ ?_ ?_
      · refine Measure.restrict_eq_self_of_ae_mem ?_
        rw [ae_iff]
        change Measure.map (stdSimplexAggregate f) (dirichletMeasure b)
          (stdSimplex ℝ κ)ᶜ = 0
        rw [Measure.map_apply hT.measurable
          (isClosed_stdSimplex ℝ κ).measurableSet.compl]
        have hsub : stdSimplex ℝ ι ⊆ stdSimplexAggregate f ⁻¹' stdSimplex ℝ κ := by
          intro u hu
          exact stdSimplexAggregate_mem_stdSimplex hu
        refine measure_mono_null (fun u hu huι => hu (hsub huι)) ?_
        change dirichletMeasure b (stdSimplex ℝ ι)ᶜ = 0
        have hs := (isClosed_stdSimplex ℝ ι).measurableSet
        have h' := congrArg (fun η : Measure (ι → ℝ) => η (stdSimplex ℝ ι)ᶜ)
          (dirichletMeasure_restrict (ι := ι) b)
        rw [Measure.restrict_apply hs.compl] at h'
        simpa [Set.inter_compl_self] using h'.symm
      · exact dirichletMeasure_restrict _
      · intro m
        have hcont : Continuous (fun v : κ → ℝ => ∏ k, v k ^ m k) := by fun_prop
        rw [integral_map hT.aemeasurable hcont.aestronglyMeasurable]
        exact integral_dirichletMeasure_comp_stdSimplexAggregate_monomial hf hb m

/-- Coordinate aggregation restated via the explicit density, unfolding
`measurePreserving_stdSimplexAggregate_dirichletMeasure` in terms of `stdSimplexMeasure` and
`dirichletPdf` directly rather than the bundled `dirichletMeasure`. -/
theorem stdSimplexAggregate_withDensity
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    Measure.map (stdSimplexAggregate f)
      (stdSimplexMeasure.withDensity (fun u ↦ ENNReal.ofReal (dirichletPdfReal b u))) =
      stdSimplexMeasure.withDensity
        (fun v ↦ ENNReal.ofReal (dirichletPdfReal (stdSimplexAggregate f b) v)) :=
  (measurePreserving_stdSimplexAggregate_dirichletMeasure hf hb).map_eq

/-- The mean of a single `u i`; a specialization of monomial integration. -/
theorem integral_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ∂(dirichletMeasure b) = (b i) / (∑ j, b j) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℝ := fun j => if j = i then 1 else 0
  have hm : b + m ∈ mvRealBetaDomain := by
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

/-- The second raw moment of one coordinate under a Dirichlet measure. -/
theorem integral_dirichletMeasure_coordinate_sq
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ^ 2 ∂(dirichletMeasure b) =
      b i * (b i + 1) / ((∑ j, b j) * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun j => if j = i then 2 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i ^ 2 := by
    funext u
    simp [m]
  rw [hprod] at h
  rw [h]
  have hnum : ∏ j, (ascPochhammer ℝ (m j)).eval (b j) = b i * (b i + 1) := by
    calc
      _ = ∏ j, if j = i then b i * (b i + 1) else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [m, ascPochhammer_succ_eval]
        · simp [m, hji]
      _ = _ := by simp
  have hsum : ∑ j, m j = 2 := by simp [m]
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

/-- The mixed raw moment of two distinct coordinates under a Dirichlet measure. -/
theorem integral_dirichletMeasure_two_coordinates
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, u i * u j ∂(dirichletMeasure b) =
      b i * b j / ((∑ k, b k) * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun k => if k = i then 1 else if k = j then 1 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ k, u k ^ m k) = fun u => u i * u j := by
    funext u
    simp only [m, pow_ite, pow_one, pow_zero]
    rw [show (∏ k, if k = i then u k else if k = j then u k else 1) =
        ∏ k, (if k = i then u i else 1) * (if k = j then u j else 1) by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hprod] at h
  rw [h]
  have hnum : ∏ k, (ascPochhammer ℝ (m k)).eval (b k) = b i * b j := by
    calc
      _ = ∏ k, if k = i then b i else if k = j then b j else 1 := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [m]
        · by_cases hkj : k = j
          · subst k
            simp [m, hki]
          · simp [m, hki, hkj]
      _ = ∏ k, (if k = i then b i else 1) * (if k = j then b j else 1) := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp [hki, hkj, hij, hij.symm]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsum : ∑ k, m k = 2 := by
    simp only [m]
    rw [show (∑ k, if k = i then 1 else if k = j then 1 else 0) =
        (∑ k, if k = i then 1 else 0) + ∑ k, (if k = j then 1 else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    simp
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

/-- The variance of the coordinate `u i`. -/
theorem variance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i - b i / ∑ j, b j) ^ 2 ∂(dirichletMeasure b) =
      (b i) * (∑ j, b j - b i) / ((∑ j, b j) ^ 2 * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  have hmean := integral_dirichletMeasure_coordinate hb i
  have hsquare := integral_dirichletMeasure_coordinate_sq hb i
  calc
    _ = variance (fun u : ι → ℝ => u i) (dirichletMeasure b) := by
      rw [variance_eq_integral (measurable_pi_apply i).aemeasurable, hmean]
    _ = (∫ u, u i ^ 2 ∂dirichletMeasure b) -
        (∫ u, u i ∂dirichletMeasure b) ^ 2 :=
      variance_eq_sub (memLp_dirichletMeasure_coordinate hb i 2)
    _ = _ := by
      rw [hsquare, hmean]
      have hS : 0 < ∑ k, b k :=
        Finset.sum_pos (fun k _ => hb k) Finset.univ_nonempty
      field_simp
      ring

/-- The covariance of distinct coordinates `u i` and `u j`. -/
theorem covariance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, (u i - b i / ∑ k, b k) * (u j - b j / ∑ k, b k)
      ∂(dirichletMeasure b) =
      -(b i) * (b j) / ((∑ k, b k) ^ 2 * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  have hmeani := integral_dirichletMeasure_coordinate hb i
  have hmeanj := integral_dirichletMeasure_coordinate hb j
  have hcross := integral_dirichletMeasure_two_coordinates hb hij
  calc
    _ = covariance (fun u : ι → ℝ => u i) (fun u => u j) (dirichletMeasure b) := by
      simp only [covariance, hmeani, hmeanj]
    _ = (∫ u, u i * u j ∂dirichletMeasure b) -
        (∫ u, u i ∂dirichletMeasure b) * (∫ u, u j ∂dirichletMeasure b) :=
      covariance_eq_sub (memLp_dirichletMeasure_coordinate hb i 2)
        (memLp_dirichletMeasure_coordinate hb j 2)
    _ = _ := by
      rw [hcross, hmeani, hmeanj]
      have hS : 0 < ∑ k, b k :=
        Finset.sum_pos (fun k _ => hb k) Finset.univ_nonempty
      field_simp
      ring

/- Specializations to the two-variable Dirichlet (Beta) density and measure that is defined
in Mathlib `ProbabilityTheory.betaMeasure`. -/

/-- For two parameters, `mvRealBetaDomain` is just positivity of both parameters. -/
@[simp] theorem mem_mvRealBetaDomain_fin_two (α β : ℝ) :
    (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain ↔
      0 < α ∧ 0 < β := by
  simp [mvRealBetaDomain]

/-- In the two-variable case, `mvRealBeta` is the ordinary beta function. -/
@[simp] theorem mvRealBeta_fin_two (α β : ℝ) :
    mvRealBeta (![α, β] : Fin 2 → ℝ) = beta α β := by
  simp [mvRealBeta, beta]

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
  rw [dirichletPdfReal, betaPDFReal, mvRealBeta_fin_two]
  by_cases hx : 0 < x ∧ x < 1
  · simp [hx, mul_assoc]
  · rw [if_neg hx]
    simp [mem_stdSimplexInterior_fin_two, hx]

/-- The two-variable `ENNReal`-valued Dirichlet density is the beta density. -/
@[simp] theorem dirichletPdf_fin_two (α β x : ℝ) :
    dirichletPdf (![α, β] : Fin 2 → ℝ) ![x, 1 - x] = betaPDF α β x := by
  simp [dirichletPdf, betaPDF]

/-- Projection onto the first coordinate sends the coordinate measure on the
two-coordinate affine simplex to Lebesgue measure. -/
private theorem map_stdSimplexMeasure_fin_two :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (stdSimplexMeasure (ι := Fin 2)) = volume := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [stdSimplexMeasure_eq_at (1 : Fin 2)]
  unfold stdSimplexMeasureAt
  rw [Measure.map_map]
  · let A := {j : Fin 2 // j ≠ 1}
    let e : A ≃ Fin 1 :=
      Fintype.equivOfCardEq (by simp [A, Fintype.card_subtype_compl])
    let T := MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm
    have hT : Measure.map T volume = volume :=
      (volume_measurePreserving_piCongrLeft (fun _ : A => ℝ) e.symm).map_eq
    let U := MeasurableEquiv.funUnique (Fin 1) ℝ
    have hU : Measure.map U volume = volume :=
      (volume_preserving_funUnique (Fin 1) ℝ).map_eq
    rw [← hU]
    calc
      Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
          (volume : Measure (A → ℝ)) =
          Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
            (Measure.map T volume) := by rw [hT]
      _ = Measure.map
          (((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1) ∘ T) volume :=
        Measure.map_map
          ((measurable_pi_apply 0).comp (measurable_stdSimplexCoordMap 1)) T.measurable
      _ = Measure.map U volume := by
        congr 1
        funext x
        simp only [Function.comp_apply]
        rw [stdSimplexCoordMap_apply_of_ne (R := ℝ) (1 : Fin 2) (0 : Fin 2) (by omega)]
        have he : (⟨0, by omega⟩ : A) = e.symm (e ⟨0, by omega⟩) := by simp
        rw [he, MeasurableEquiv.piCongrLeft_apply_apply]
        change x (e ⟨0, by omega⟩) = x default
        exact congrArg x (Subsingleton.elim _ _)
  · exact measurable_pi_apply 0
  · exact measurable_stdSimplexCoordMap (1 : Fin 2)

/-- The first-coordinate push-forward of a two-coordinate Dirichlet measure is Mathlib's
beta measure. -/
private theorem map_dirichletMeasure_fin_two_direct (a b : ℝ) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![a, b])) = betaMeasure a b := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply 0) hs]
  rw [dirichletMeasure, withDensity_apply _ ((measurable_pi_apply 0) hs)]
  rw [betaMeasure, withDensity_apply _ hs]
  rw [← map_stdSimplexMeasure_fin_two]
  rw [← lintegral_indicator hs]
  have hpdf : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [lintegral_map (hpdf.indicator hs) (measurable_pi_apply 0)]
  rw [← lintegral_indicator ((measurable_pi_apply 0) hs)]
  apply lintegral_congr_ae
  have hmem : ∀ᵐ u ∂(stdSimplexMeasure (ι := Fin 2)),
      u ∈ stdSimplexAffineSet (R := ℝ) := by
    rw [stdSimplexMeasure_restrict_stdSimplexAffineSet]
    exact self_mem_ae_restrict isClosed_stdSimplexAffineSet.measurableSet
  filter_upwards [hmem] with u hu
  by_cases hus : u ∈ (fun u : Fin 2 → ℝ => u 0) ⁻¹' s
  · simp only [Set.mem_preimage] at hus
    simp [hus]
    have hu1 : u 1 = 1 - u 0 := by
      have hsum : ∑ i, u i = 1 := mem_fintypeAffineCoords_iff_sum.mp hu
      simpa [Fin.sum_univ_two] using congrArg (fun x => x - u 0) hsum
    have huv : u = ![u 0, 1 - u 0] := by
      funext j
      fin_cases j <;> simp [hu1]
    rw [huv]
    exact dirichletPdf_fin_two a b _
  · simp only [Set.mem_preimage] at hus
    simp [hus]

/-- Marginalization of the Dirichlet density with respect to the `i` coordinate. -/
theorem betaMarginal [Nontrivial ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    Measure.map (fun u ↦ u i) (dirichletMeasure b) =
      betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) := by
  classical
  let q : ι → Fin 2 := fun j => if j = i then 0 else 1
  have hq : Function.Surjective q := by
    intro k
    fin_cases k
    · exact ⟨i, by simp [q]⟩
    · obtain ⟨j, hji⟩ := exists_ne i
      exact ⟨j, by simp [q, hji]⟩
  have hcoord (u : ι → ℝ) : stdSimplexAggregate q u 0 = u i := by
    change (FunOnFinite.linearMap ℝ ℝ q) u 0 = u i
    rw [FunOnFinite.linearMap_apply_apply]
    have hfilter : Finset.univ.filter (fun x => q x = (0 : Fin 2)) = {i} := by
      ext j
      simp [q]
    rw [hfilter]
    simp
  have hparam : stdSimplexAggregate q b =
      (![b i, ∑ j ∈ Finset.univ.erase i, b j] : Fin 2 → ℝ) := by
    funext k
    fin_cases k
    · exact hcoord b
    · change (FunOnFinite.linearMap ℝ ℝ q) b 1 = _
      rw [FunOnFinite.linearMap_apply_apply]
      have hfilter : Finset.univ.filter (fun x => q x = (1 : Fin 2)) =
          Finset.univ.erase i := by
        ext j
        simp [q]
      rw [hfilter]
      simp
  have hp := measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb
  calc
    Measure.map (fun u : ι → ℝ => u i) (dirichletMeasure b) =
        Measure.map (fun v : Fin 2 → ℝ => v 0)
          (Measure.map (stdSimplexAggregate q) (dirichletMeasure b)) := by
            rw [Measure.map_map]
            · congr 1
              funext u
              exact (hcoord u).symm
            · exact measurable_pi_apply 0
            · fun_prop
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (stdSimplexAggregate q b)) := by rw [hp.map_eq]
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (![b i, ∑ j ∈ Finset.univ.erase i, b j])) := by rw [hparam]
    _ = betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) :=
      map_dirichletMeasure_fin_two_direct _ _

/-- The push-forward of the two-variable Dirichlet measure under the first
coordinate is the beta measure. -/
theorem map_dirichletMeasure_fin_two
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![α, β])) = betaMeasure α β := by
  have hb : (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain := by
    simpa using And.intro hα hβ
  simpa using
    (betaMarginal (b := (![α, β] : Fin 2 → ℝ)) hb (0 : Fin 2))

/- TODO: The Gamma ratio characterization. If X_i are independent Gamma(b_i, 1)-distributed
then (X_i / ∑_j X_j)_i is Dirichlet(b)-distributed. -/

end ProbabilityTheory

end DirichletDistribution
-- #lint
