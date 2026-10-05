/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.TauCetiBridge
public import TauCeti.Probability.Distributions.Dirichlet.Aggregation

public import Dirichlet.Real


/-!
# Aggregation of the real Dirichlet distribution

Coarsening the coordinates of a Dirichlet random vector along a surjection produces a
Dirichlet random vector whose parameters are the sums of the parameters over the fibers. The
proof is transferred through `Dirichlet.TauCetiBridge` from
`TauCeti.Probability.Distributions.Dirichlet.Aggregation`, by the Tau Ceti contributors. The
moment form, a multinomial Chu–Vandermonde identity, follows as a corollary.

## Main results

* `ProbabilityTheory.measurePreserving_stdSimplexAggregate_dirichletMeasure`: the pushforward of
  `dirichletMeasure b` along `stdSimplexAggregate f` is `dirichletMeasure` of the aggregated
  parameters.
* `ProbabilityTheory.stdSimplexAggregate_withDensity`: the same statement through densities.
* `ProbabilityTheory.integral_dirichletMeasure_comp_stdSimplexAggregate_monomial`: the moment
  form.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
* `TauCeti.Probability.Distributions.Dirichlet.Aggregation`.
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

/-- Dirichlet measure is closed under marginalisation or coarsening: pushing
`dirichletMeasure b` forward along `stdSimplexAggregate f` gives the Dirichlet
measure for the aggregated parameter vector. For a nonempty index type this is
`TauCeti.Probability.map_euclideanFiberSum_dirichletMeasure`, by the Tau Ceti contributors. -/
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
      have hagg : stdSimplexAggregate f b = fun j ↦ ∑ i with f i = j, b i :=
        funext (stdSimplexAggregate_apply_eq_sum_filter f b)
      rw [dirichletMeasure_eq_map_tauCeti hb,
        dirichletMeasure_eq_map_tauCeti (mem_mvRealBetaDomain_stdSimplexAggregate hf hb), hagg,
        ← TauCeti.Probability.map_euclideanFiberSum_dirichletMeasure hf hb,
        Measure.map_map hT.measurable (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      ext j
      simp [stdSimplexAggregate_apply_eq_sum_filter]

/-- Pushing a Dirichlet monomial forward under coordinate aggregation yields the
Dirichlet monomial for the aggregated parameters. This is the moment form of the
multinomial Chu–Vandermonde identity. -/
theorem integral_dirichletMeasure_comp_stdSimplexAggregate_monomial
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (m : κ → ℕ) :
    ∫ u, (∏ k, stdSimplexAggregate f u k ^ m k) ∂(dirichletMeasure b) =
      ∫ v, (∏ k, v k ^ m k) ∂(dirichletMeasure (stdSimplexAggregate f b)) := by
  have hp := measurePreserving_stdSimplexAggregate_dirichletMeasure hf hb
  have hcont : Continuous (fun v : κ → ℝ ↦ ∏ k, v k ^ m k) := by fun_prop
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hcont.aestronglyMeasurable]

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
