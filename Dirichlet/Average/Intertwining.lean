/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Associated.Deriv

/-!
# Averaging intertwines Carlson's differential operators

Carlson's formula (5.3-4): with `δ = α + β d/dx + γ x d/dx` acting on functions of one variable
and `Δ = α + β ∑ Dᵢ + γ ∑ zᵢ Dᵢ` acting on functions of the nodes, the Dirichlet average of
`δⁿ f` is `Δⁿ F`, where `F` is the average of `f`. The first-order case follows from
differentiation under the average, because the simplex coordinates sum to one and
`∑ uᵢ zᵢ` is the averaged point; the general case follows by induction, since `Δ` only
depends on the germ of a function and `δ` preserves holomorphy.

## Main results

* `Dirichlet.carlsonDelta`, `Dirichlet.carlsonCapDelta`: the operators `δ` and `Δ`.
* `Dirichlet.carlsonCapDelta_regCarlsonDirichletAverage`: the first-order case.
* `Dirichlet.carlsonCapDelta_iterate_regCarlsonDirichletAverage`: formula (5.3-4) for every
  power.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.3.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
@[expose] public noncomputable section

namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Carlson's one-variable operator `δ = α + β d/dx + γ x d/dx` of (5.3-4). -/
def carlsonDelta (α β γ : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun x => α * f x + (β + γ * x) * deriv f x

/-- Carlson's operator `Δ = α + β ∑ Dᵢ + γ ∑ zᵢ Dᵢ` of (5.3-4). -/
def carlsonCapDelta (α β γ : ℂ) (G : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  fun z => α * G z + ∑ i, (β + γ * z i) * carlsonPartialDeriv i G z

/-- The operator `δ` preserves holomorphy on open sets. -/
theorem AnalyticOnNhd.carlsonDelta {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (α β γ : ℂ) :
    AnalyticOnNhd ℂ (carlsonDelta α β γ f) Ω := fun x hx =>
  (analyticAt_const.mul (hf x hx)).add ((analyticAt_const.add (analyticAt_const.mul
    analyticAt_id)).mul (hf.deriv_of_isOpen hΩ x hx))

open scoped Classical in
omit [Fintype ι] in
/-- Carlson's partial derivatives only depend on the germ of the function. -/
theorem carlsonPartialDeriv_congr_of_eventuallyEq {G H : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (h : G =ᶠ[𝓝 z] H) (i : ι) : carlsonPartialDeriv i G z = carlsonPartialDeriv i H z := by
  unfold carlsonPartialDeriv
  apply Filter.EventuallyEq.deriv_eq
  have hc : ContinuousAt (fun w : ℂ => Function.update z i w) (z i) :=
    (continuous_const.update i continuous_id).continuousAt
  have := hc.tendsto
  rw [Function.update_eq_self] at this
  exact this.eventually h

omit [Fintype ι] in
/-- The operator `Δ` only depends on the germ of the function. -/
theorem carlsonCapDelta_congr_of_eventuallyEq [Fintype ι] {G H : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (h : G =ᶠ[𝓝 z] H) (α β γ : ℂ) : carlsonCapDelta α β γ G z = carlsonCapDelta α β γ H z := by
  unfold carlsonCapDelta
  rw [h.eq_of_nhds]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [carlsonPartialDeriv_congr_of_eventuallyEq h i]

/-- **Formula (5.3-4), first order.** For `f` holomorphic on an open convex set containing the
nodes, `Δ F = (δ f)` averaged: `Δ F(b, z) = F_{δ f}(b, z)` (regularized native averages). -/
theorem carlsonCapDelta_regCarlsonDirichletAverage {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω) (α β γ : ℂ) :
    carlsonCapDelta α β γ (fun w => regCarlsonDirichletAverage b w f) z =
      regCarlsonDirichletAverage b z (carlsonDelta α β γ f) := by
  classical
  set K := Convexity.StdSimplex.coordinateSet ℝ ι
  have hK : ∀ u ∈ K, carlsonAffineForm z u ∈ Ω := fun u hu =>
    convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu)
  have hcont : ∀ g : ℂ → ℂ,
      ContinuousOn g Ω → ContinuousOn (fun u => g (carlsonAffineForm z u)) K :=
    fun g hg => hg.comp (continuous_carlsonAffineForm z).continuousOn hK
  have hfc : ContinuousOn f Ω := hf.continuousOn
  have hf'c : ContinuousOn (deriv f) Ω := (hf.deriv_of_isOpen hΩopen).continuousOn
  have hint : ∀ g : (ι → ℝ) → ℂ, ContinuousOn g K →
      IntegrableOn
          (fun u => regDirichletDensity b u * g u) K MeasureTheory.Measure.stdSimplexMeasure :=
    fun g hg => integrableOn_regDirichletDensity_mul b hb hg
  unfold carlsonCapDelta
  simp only [carlsonPartialDeriv,
    (hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd hΩopen hΩconv hf hb hz _).deriv]
  unfold regCarlsonDirichletAverage regDirichletIntegral carlsonDelta
  rw [← integral_const_mul]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum, ← integral_add]
  · refine setIntegral_congr_fun
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet fun u hu => ?_
    have h1 : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
    have h2 : ∑ i, (β + γ * z i) * (regDirichletDensity b u *
        ((u i : ℂ) * deriv f (carlsonAffineForm z u))) =
        regDirichletDensity b u * ((β * ∑ i, (u i : ℂ) + γ * ∑ i, (u i : ℂ) * z i) *
          deriv f (carlsonAffineForm z u)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2, h1]
    simp only [carlsonAffineForm]
    ring
  · exact (hint _ (hcont f hfc)).const_mul α
  · exact integrable_finsetSum _ fun i _ =>
      (hint _ (continuous_ofReal.comp (continuous_apply i) |>.continuousOn.mul
        (hcont _ hf'c))).const_mul _
  · exact fun i _ => (hint _ (continuous_ofReal.comp (continuous_apply i) |>.continuousOn.mul
        (hcont _ hf'c))).const_mul _

/-- **Formula (5.3-4)** for every power: `Δⁿ F(b, z)` is the average of `δⁿ f`, for `f`
holomorphic on an open convex set containing the nodes (regularized native averages). -/
theorem carlsonCapDelta_iterate_regCarlsonDirichletAverage {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (α β γ : ℂ) (n : ℕ) {z : ι → ℂ}
    (hz : Set.range z ⊆ Ω) :
    (carlsonCapDelta α β γ)^[n] (fun w => regCarlsonDirichletAverage b w f) z =
      regCarlsonDirichletAverage b z ((carlsonDelta α β γ)^[n] f) := by
  have hN : IsOpen {w : ι → ℂ | Set.range w ⊆ Ω} := by
    rw [show {w : ι → ℂ | Set.range w ⊆ Ω} = ⋂ i, {w | w i ∈ Ω} by
      ext w; simp [Set.range_subset_iff]]
    exact isOpen_iInter_of_finite fun i => hΩopen.preimage (continuous_apply i)
  have han : ∀ m, AnalyticOnNhd ℂ ((carlsonDelta α β γ)^[m] f) Ω := by
    intro m
    induction m with
    | zero => exact hf
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact AnalyticOnNhd.carlsonDelta hΩopen ih α β γ
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have he : (carlsonCapDelta α β γ)^[n] (fun w => regCarlsonDirichletAverage b w f) =ᶠ[𝓝 z]
        fun w => regCarlsonDirichletAverage b w ((carlsonDelta α β γ)^[n] f) := by
      filter_upwards [hN.mem_nhds hz] with w hw using ih hw
    rw [carlsonCapDelta_congr_of_eventuallyEq he,
      carlsonCapDelta_regCarlsonDirichletAverage hΩopen hΩconv (han n) hb hz]

end Dirichlet
