/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Integral
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Moment determination for measures supported on the standard simplex
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

/-- If two finite measures on the simplex integrate `p` alike and `g` is uniformly within `ε` of
`p` on the simplex, then the integrals of `g` differ by at most `ε` times the total masses. -/
private theorem abs_integral_sub_integral_le_of_approx
    {α : Type*} [Fintype α]
    {μ ν : Measure (α → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ)
    (hν : ν.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = ν)
    {g p : (α → ℝ) → ℝ} (hg : Continuous g) (hp : Continuous p) {ε : ℝ}
    (happrox : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ α, ‖g x - p x‖ ≤ ε)
    (hpeq : ∫ x, p x ∂μ = ∫ x, p x ∂ν) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ ε * (μ.real Set.univ + ν.real Set.univ) := by
  have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ α).measurableSet
  have hgμ : Integrable g μ := integrable_of_continuous_of_restrict_stdSimplex hμ hg
  have hgν : Integrable g ν := integrable_of_continuous_of_restrict_stdSimplex hν hg
  have hpμ : Integrable p μ := integrable_of_continuous_of_restrict_stdSimplex hμ hp
  have hpν : Integrable p ν := integrable_of_continuous_of_restrict_stdSimplex hν hp
  have hμ' : |∫ x, g x ∂μ - ∫ x, p x ∂μ| ≤ ε * μ.real Set.univ := by
    rw [← integral_sub hgμ hpμ, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [ae_mem_of_restrict_eq_self hs hμ] with x hx using happrox x hx
  have hν' : |∫ x, g x ∂ν - ∫ x, p x ∂ν| ≤ ε * ν.real Set.univ := by
    rw [← integral_sub hgν hpν, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [ae_mem_of_restrict_eq_self hs hν] with x hx using happrox x hx
  calc
    |∫ x, g x ∂μ - ∫ x, g x ∂ν|
        = |(∫ x, g x ∂μ - ∫ x, p x ∂μ) + (∫ x, p x ∂ν - ∫ x, g x ∂ν)| := by
          rw [hpeq]; ring_nf
    _ ≤ |∫ x, g x ∂μ - ∫ x, p x ∂μ| + |∫ x, p x ∂ν - ∫ x, g x ∂ν| := abs_add_le _ _
    _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ := by
        rw [abs_sub_comm (∫ x, p x ∂ν)]
        exact add_le_add hμ' hν'
    _ = ε * (μ.real Set.univ + ν.real Set.univ) := by ring

/-- Two real numbers whose difference is bounded by every positive multiple of a fixed
nonnegative constant are equal. -/
private theorem eq_of_forall_abs_sub_le_mul {a b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, |a - b| ≤ ε * C) : a = b := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hC0 : C = 0
  · have := h 1 one_pos
    simp only [hC0, mul_zero] at this
    linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have := h (ε / C) (div_pos hε hCpos)
    have hcancel : ε / C * C = ε := div_mul_cancel₀ ε (ne_of_gt hCpos)
    linarith

/-- Finite Borel measures supported on the standard simplex are determined by their
monomial moments. Polynomials are dense in the continuous functions on the compact simplex by
Stone--Weierstrass, and the two measures integrate every polynomial alike. -/
theorem eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex
    {α : Type*} [Fintype α]
    {μ ν : Measure (α → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = μ)
    (hν : ν.restrict (Convexity.StdSimplex.coordinateSet ℝ α) = ν)
    (h : ∀ m : α → ℕ, ∫ x, (∏ i, x i ^ m i) ∂μ = ∫ x, (∏ i, x i ^ m i) ∂ν) :
    μ = ν := by
  classical
  let coord : α → C(α → ℝ, ℝ) := fun k =>
    ⟨fun v => v k, continuous_apply k⟩
  let A : Subalgebra ℝ C(α → ℝ, ℝ) := (MvPolynomial.aeval coord).range
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨k, hk⟩ := not_forall.mp (mt funext hxy)
    refine ⟨(coord k : (α → ℝ) → ℝ), ?_, hk⟩
    exact ⟨coord k, ⟨MvPolynomial.X k, MvPolynomial.aeval_X coord k⟩, rfl⟩
  have heval (q : MvPolynomial α ℝ) (v : α → ℝ) :
      (MvPolynomial.aeval coord q) v = MvPolynomial.eval v q := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
    simp [coord, algebraMap_apply]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  refine eq_of_forall_abs_sub_le_mul (C := μ.real Set.univ + ν.real Set.univ) (by positivity)
    fun ε hε => ?_
  obtain ⟨p, hpA, hpapprox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hA g.toContinuousMap (Convexity.StdSimplex.isCompact_coordinateSet ℝ α) hε
  obtain ⟨q, hq⟩ : ∃ q, MvPolynomial.aeval coord q = p := by
    simpa [A, AlgHom.mem_range] using hpA
  refine abs_integral_sub_integral_le_of_approx hμ hν g.continuous p.continuous
    (fun x hx => ?_) ?_
  · rw [show (g : (α → ℝ) → ℝ) x = g.toContinuousMap x from rfl, norm_sub_rev]
    exact (hpapprox x hx).le
  · simpa [← hq, heval] using integral_mvPolynomial_eval_eq_of_forall_monomial hμ hν h q

end MeasureTheory

end
