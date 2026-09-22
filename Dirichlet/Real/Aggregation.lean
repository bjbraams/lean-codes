/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Moments

public import Mathlib.Probability.Moments.Variance
public import Dirichlet.Real
public import StdSimplexMeasure.MomentDetermination

import Pochhammer.Gamma
import Pochhammer.Vandermonde
import all StdSimplexMeasure.Measure.Basic

/-!
# Aggregation of the real Dirichlet distribution

Coarsening the coordinates of a Dirichlet random vector along a surjection produces a
Dirichlet random vector whose parameters are the sums of the parameters over the fibers. The
proof identifies moments and uses moment determination on the compact simplex.

## Main results

* `ProbabilityTheory.measurePreserving_stdSimplexAggregate_dirichletMeasure`: the pushforward of
  `dirichletMeasure b` along `stdSimplexAggregate f` is `dirichletMeasure` of the aggregated
  parameters.
* `ProbabilityTheory.stdSimplexAggregate_withDensity`: the same statement through densities.
-/

open Dirichlet
open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]


/-- Aggregating a Dirichlet parameter vector along a surjection stays in the
positive parameter domain. -/
theorem mem_mvRealBetaDomain_stdSimplexAggregate
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    stdSimplexAggregate f b ∈ mvRealBetaDomain :=
  stdSimplexAggregate_pos hf hb

open scoped Classical in
/-- An aggregated coordinate is the sum of the coordinates in its fibre. -/
theorem stdSimplexAggregate_apply_eq_sum_filter {κ : Type*} [Fintype κ] (f : ι → κ)
    (u : ι → ℝ) (k : κ) :
    stdSimplexAggregate f u k = ∑ i ∈ Finset.univ.filter (fun i => f i = k), u i := by
  simp [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]

open scoped Classical in
/-- Multinomial expansion of a monomial in the aggregated coordinates: a sum over fibrewise
compositions of the exponents, with the product of the fibre multinomial coefficients. -/
private theorem prod_stdSimplexAggregate_pow_eq_sum {κ : Type*} [Fintype κ] (f : ι → κ)
    (m : κ → ℕ) (u : ι → ℝ) :
    ∏ k, stdSimplexAggregate f u k ^ m k =
      ∑ p ∈ Fintype.piFinset
          (fun k => Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k)),
        (∏ k, (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) (p k) : ℝ)) *
          ∏ i, u i ^ p (f i) i := by
  simp_rw [stdSimplexAggregate_apply_eq_sum_filter]
  have hbinoms (k : κ) :
      (∑ i ∈ Finset.univ.filter (fun i => f i = k), u i) ^ m k =
        ∑ α ∈ Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k),
          (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) α : ℝ) *
            ∏ i ∈ Finset.univ.filter (fun i => f i = k), u i ^ α i :=
    Finset.sum_pow_eq_sum_piAntidiag _ (fun i => u i) (m k)
  simp_rw [hbinoms]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  have hcoord :
      ∏ k, ∏ i ∈ Finset.univ.filter (fun i => f i = k), u i ^ p k i =
        ∏ k, ∏ i ∈ Finset.univ.filter (fun i => f i = k), u i ^ p (f i) i := by
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
    have hik : f i = k := (Finset.mem_filter.mp hi).2
    simp [hik]
  rw [hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]

open scoped Classical in
/-- A fibrewise composition of the exponents has total degree `∑ k, m k`. -/
private theorem sum_apply_comp_eq_sum_of_mem_piFinset {κ : Type*} [Fintype κ] (f : ι → κ)
    (m : κ → ℕ) {p : κ → ι → ℕ}
    (hp : p ∈ Fintype.piFinset
      (fun k => Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k))) :
    ∑ i, p (f i) i = ∑ k, m k := by
  have hp' : ∀ k, p k ∈ Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k) := by
    simpa [Fintype.mem_piFinset] using hp
  calc
    ∑ i, p (f i) i = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), p (f i) i :=
      (Finset.sum_fiberwise (Finset.univ : Finset ι) f (fun i => p (f i) i)).symm
    _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), p k i := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    _ = ∑ k, m k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact (Finset.mem_piAntidiag.mp (hp' k)).1

open scoped Classical in
/-- The multinomial Chu--Vandermonde identity for rising factorials, fibre by fibre: summing
the products of rising factorials over all fibrewise compositions of the exponents gives the
rising factorials of the aggregated parameters. -/
private theorem sum_multinomial_mul_prod_ascPochhammer {κ : Type*} [Fintype κ] (f : ι → κ)
    (m : κ → ℕ) (b : ι → ℝ) :
    ∑ p ∈ Fintype.piFinset
        (fun k => Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k)),
        (∏ k, (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) (p k) : ℝ)) *
          ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
      ∏ k, (ascPochhammer ℝ (m k)).eval (stdSimplexAggregate f b k) := by
  have hN (p : κ → (ι → ℕ)) :
      ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
        ∏ k, ∏ i ∈ Finset.univ.filter (fun i => f i = k),
          (ascPochhammer ℝ (p k i)).eval (b i) := by
    have hcoord :
        ∏ k, ∏ i ∈ Finset.univ.filter (fun i => f i = k),
            (ascPochhammer ℝ (p (f i) i)).eval (b i) =
          ∏ k, ∏ i ∈ Finset.univ.filter (fun i => f i = k),
            (ascPochhammer ℝ (p k i)).eval (b i) := by
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    rw [← hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]
  have hprod (p : κ → ι → ℕ) :
      (∏ k, (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) (p k) : ℝ)) *
          ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
        ∏ k, ((Nat.multinomial (Finset.univ.filter (fun i => f i = k)) (p k) : ℝ) *
          ∏ i ∈ Finset.univ.filter (fun i => f i = k), (ascPochhammer ℝ (p k i)).eval (b i)) := by
    rw [hN p, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun p _ => hprod p]
  rw [← Finset.prod_univ_sum
    (t := fun k => Finset.piAntidiag (Finset.univ.filter (fun i => f i = k)) (m k))
    (f := fun k α =>
      (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) α : ℝ) *
        ∏ i ∈ Finset.univ.filter (fun i => f i = k), (ascPochhammer ℝ (α i)).eval (b i))]
  refine Finset.prod_congr rfl fun k _ => ?_
  simpa [stdSimplexAggregate_apply_eq_sum_filter] using
    (ascPochhammer_eval_sum (Finset.univ.filter (fun i => f i = k)) b (m k)).symm

/-- Pushing a Dirichlet monomial forward under coordinate aggregation yields the
Dirichlet monomial for the aggregated parameters. This is the moment form of the
multinomial Chu–Vandermonde identity: the aggregated monomial is expanded fibrewise, each term
is a Dirichlet moment, and the resulting sum of rising factorials is recombined. -/
theorem integral_dirichletMeasure_comp_stdSimplexAggregate_monomial
    [Nonempty ι] {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (m : κ → ℕ) :
    ∫ u, (∏ k, stdSimplexAggregate f u k ^ m k) ∂(dirichletMeasure b) =
      ∫ v, (∏ k, v k ^ m k) ∂(dirichletMeasure (stdSimplexAggregate f b)) := by
  classical
  have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
  have hb' : stdSimplexAggregate f b ∈ mvRealBetaDomain :=
    mem_mvRealBetaDomain_stdSimplexAggregate hf hb
  have hsum_b : ∑ i, b i = ∑ k, stdSimplexAggregate f b k := by
    simp_rw [stdSimplexAggregate_apply_eq_sum_filter]
    exact (Finset.sum_fiberwise (Finset.univ : Finset ι) f b).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall (prod_stdSimplexAggregate_pow_eq_sum f m))]
  have hterm (p : κ → (ι → ℕ)) :
      Integrable (fun u : ι → ℝ =>
        (∏ k, (Nat.multinomial (Finset.univ.filter (fun i => f i = k)) (p k) : ℝ)) *
          ∏ i, u i ^ p (f i) i) (dirichletMeasure b) := by
    let : IsProbabilityMeasure (dirichletMeasure b) :=
      isProbabilityMeasure_dirichletMeasure hb
    exact (integrable_of_continuous_of_restrict_stdSimplex
      (dirichletMeasure_restrict b) (by fun_prop)).const_mul _
  rw [integral_finsetSum _ fun p _ => hterm p]
  simp_rw [integral_const_mul]
  rw [integral_dirichletMeasure_monomial hb' m, ← hsum_b, ← sum_multinomial_mul_prod_ascPochhammer,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_dirichletMeasure_monomial hb (fun i => p (f i) i),
    sum_apply_comp_eq_sum_of_mem_piFinset f m hp, mul_div_assoc]

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
      refine eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex ?_ ?_ ?_
      · refine Measure.restrict_eq_self_of_ae_mem ?_
        rw [ae_iff]
        change Measure.map (stdSimplexAggregate f) (dirichletMeasure b)
          (Convexity.StdSimplex.coordinateSet ℝ κ)ᶜ = 0
        rw [Measure.map_apply hT.measurable
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet.compl]
        have hsub : Convexity.StdSimplex.coordinateSet ℝ ι ⊆ stdSimplexAggregate f ⁻¹'
            Convexity.StdSimplex.coordinateSet ℝ κ := by
          intro u hu
          exact stdSimplexAggregate_mem_stdSimplex hu
        refine measure_mono_null (fun u hu huι => hu (hsub huι)) ?_
        change dirichletMeasure b (Convexity.StdSimplex.coordinateSet ℝ ι)ᶜ = 0
        have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        have h' := congrArg (fun η : Measure (ι → ℝ) => η (Convexity.StdSimplex.coordinateSet ℝ ι)ᶜ)
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

end ProbabilityTheory

end DirichletDistribution
