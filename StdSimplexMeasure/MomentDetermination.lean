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
* `MeasureTheory.ae_mem_of_restrict_eq_self`: A finite measure equal to its restriction to a
  measurable set is concentrated on that set.
* `MeasureTheory.integral_mvPolynomial_eval_eq_of_forall_monomial`: Two finite measures on the
  simplex with the same monomial moments integrate every polynomial alike.
* `MeasureTheory.eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex`: Finite Borel
  measures supported on the standard simplex are determined by their monomial moments.
  This is an adapter to TauCeti's general compact-support theorem.

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

/-- A finite measure equal to its restriction to a measurable set is concentrated on that set. -/
theorem ae_mem_of_restrict_eq_self {β : Type*} [MeasurableSpace β] {μ : Measure β} {s : Set β}
    (hs : MeasurableSet s) (hμ : μ.restrict s = μ) : ∀ᵐ x ∂μ, x ∈ s := by
  rw [ae_iff]
  change μ sᶜ = 0
  have h' := congrArg (fun η : Measure β => η sᶜ) hμ
  rw [Measure.restrict_apply hs.compl] at h'
  simpa [Set.inter_compl_self] using h'.symm

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

end MeasureTheory

end
