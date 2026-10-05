/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence
public import SeveralComplexVariables.SeparateAnalytic
public import ComplexAnalysis.BranchLog.Analytic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Convex.Contractible

/-!
# Convex charts of simply connected domains

A simply connected open set `D ⊆ ℂ` is the biholomorphic image of a convex open set `V`: of the
unit disc by the Riemann mapping theorem of the Tau Ceti contributors, or of `ℂ` itself when
`D = ℂ`. For a chart `φ : V → D` the difference quotient `Q(s, t) = (φ s - φ t) / (s - t)`,
completed by `φ' s` on the diagonal, is jointly holomorphic and nonvanishing on `V × V`, and has
a holomorphic logarithm there.

These are the tools used to pull a two-node Dirichlet average on `D` back to a straight segment
in the convex set `V`.

## Main definitions

* `Dirichlet.chartQuot`: the difference quotient `Q(v 0, v 1)` of a chart, as a function of a
  node pair `v : Fin 2 → ℂ`.

## Main results

* `Dirichlet.exists_convex_chart`: a convex chart of a simply connected open set.
* `Dirichlet.analyticOnNhd_chartQuot`: joint holomorphy of the difference quotient, by Hartogs'
  theorem on separate analyticity.
* `Dirichlet.chartQuot_ne_zero`: the difference quotient of an injective chart does not vanish.
* `Dirichlet.exists_chartLog`: a holomorphic logarithm of the difference quotient.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 1 (the Riemann mapping theorem).
-/

open Complex Set Filter Function
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

/-- **Convex charts.** A simply connected open subset of the plane is the image of a convex open
set under a holomorphic map with a holomorphic inverse. -/
theorem exists_convex_chart {D : Set ℂ} (hDo : IsOpen D) (hDs : IsSimplyConnected D) :
    ∃ (V : Set ℂ) (φ ψ : ℂ → ℂ), IsOpen V ∧ Convex ℝ V ∧ V.Nonempty ∧
      AnalyticOnNhd ℂ φ V ∧ AnalyticOnNhd ℂ ψ D ∧ MapsTo φ V D ∧ MapsTo ψ D V ∧
      (∀ s ∈ V, ψ (φ s) = s) ∧ (∀ w ∈ D, φ (ψ w) = w) := by
  by_cases hD : D = univ
  · subst hD
    exact ⟨univ, id, id, isOpen_univ, convex_univ, univ_nonempty,
      fun _ _ => analyticAt_id, fun _ _ => analyticAt_id, mapsTo_univ _ _, mapsTo_univ _ _,
      fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨f, hbij, hfd, hgd, hleft, hright⟩ :=
    TauCeti.exists_bijOn_ball_differentiableOn_invFunOn hDo hDs hD
  refine ⟨Metric.ball 0 1, Function.invFunOn f D, f, Metric.isOpen_ball, convex_ball 0 1,
    ⟨0, Metric.mem_ball_self one_pos⟩, hgd.analyticOnNhd Metric.isOpen_ball,
    hfd.analyticOnNhd hDo, ?_, hbij.mapsTo, fun s hs => hright hs, fun w hw => hleft hw⟩
  intro s hs
  exact Function.invFunOn_mem (hbij.surjOn hs)

/-- A chart with a holomorphic left inverse has nonvanishing derivative. -/
theorem deriv_ne_zero_of_leftInv {V D : Set ℂ} (hV : IsOpen V) {φ ψ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ V) (hψ : AnalyticOnNhd ℂ ψ D) (hmaps : MapsTo φ V D)
    (hleft : ∀ s ∈ V, ψ (φ s) = s) {s : ℂ} (hs : s ∈ V) : deriv φ s ≠ 0 := by
  have h := (hψ (φ s) (hmaps hs)).differentiableAt.hasDerivAt.comp s
    (hφ s hs).differentiableAt.hasDerivAt
  have hid : HasDerivAt (ψ ∘ φ) 1 s := (hasDerivAt_id s).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hV.mem_nhds hs) fun t ht => hleft t ht)
  intro h0
  have := h.unique hid
  rw [h0, mul_zero] at this
  exact zero_ne_one this

/-- The difference quotient of a chart, as a function of a node pair: `Q(v 0, v 1)`. -/
def chartQuot (φ : ℂ → ℂ) (v : Fin 2 → ℂ) : ℂ := dslope φ (v 1) (v 0)

/-- The completed difference quotient is symmetric. -/
theorem dslope_comm (φ : ℂ → ℂ) (a b : ℂ) : dslope φ a b = dslope φ b a := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  · rw [dslope_of_ne _ hab.symm, dslope_of_ne _ hab, slope_comm]

/-- The difference quotient times the difference of the points is the difference of values. -/
theorem sub_mul_chartQuot (φ : ℂ → ℂ) (v : Fin 2 → ℂ) :
    (v 0 - v 1) * chartQuot φ v = φ (v 0) - φ (v 1) := by
  simpa [chartQuot, smul_eq_mul] using sub_smul_dslope φ (v 1) (v 0)

/-- On the diagonal the difference quotient is the derivative. -/
theorem chartQuot_self (φ : ℂ → ℂ) (s : ℂ) : chartQuot φ ![s, s] = deriv φ s := by
  simp [chartQuot, dslope_same]

/-- The node pairs in a set. -/
def pairDomain (V : Set ℂ) : Set (Fin 2 → ℂ) := {v | v 0 ∈ V ∧ v 1 ∈ V}

/-- Node pairs in an open set form an open set. -/
theorem isOpen_pairDomain {V : Set ℂ} (hV : IsOpen V) : IsOpen (pairDomain V) :=
  (hV.preimage (continuous_apply 0)).inter (hV.preimage (continuous_apply 1))

/-- Node pairs in a convex set form a convex set. -/
theorem convex_pairDomain {V : Set ℂ} (hV : Convex ℝ V) : Convex ℝ (pairDomain V) := by
  intro x hx y hy a b ha hb hab
  exact ⟨hV hx.1 hy.1 ha hb hab, hV hx.2 hy.2 ha hb hab⟩

/-- **Joint holomorphy of the difference quotient**, by Hartogs' theorem: it is holomorphic in
each point separately by the removable singularity theorem. -/
theorem analyticOnNhd_chartQuot {V : Set ℂ} (hV : IsOpen V) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ V) : AnalyticOnNhd ℂ (chartQuot φ) (pairDomain V) := by
  have hd {c : ℂ} (hc : c ∈ V) : AnalyticOnNhd ℂ (dslope φ c) V :=
    ((differentiableOn_dslope (hV.mem_nhds hc)).mpr hφ.differentiableOn).analyticOnNhd hV
  apply SeveralComplexVariables.analyticOnNhd_of_separately_analytic (isOpen_pairDomain hV)
  intro v hv i
  fin_cases i
  · simpa [chartQuot] using hd hv.2 (v 0) hv.1
  · have : (fun w => chartQuot φ (update v 1 w)) = dslope φ (v 0) := by
      funext w; simp [chartQuot, dslope_comm φ w]
    simpa [this] using hd hv.1 (v 1) hv.2

/-- The difference quotient of an injective chart with nonvanishing derivative does not
vanish. -/
theorem chartQuot_ne_zero {V : Set ℂ} {φ : ℂ → ℂ} (hinj : InjOn φ V)
    (hder : ∀ s ∈ V, deriv φ s ≠ 0) {v : Fin 2 → ℂ} (hv : v ∈ pairDomain V) :
    chartQuot φ v ≠ 0 := by
  rcases eq_or_ne (v 0) (v 1) with h | h
  · rw [chartQuot, h, dslope_same]
    exact hder _ hv.2
  · intro h0
    have := sub_mul_chartQuot φ v
    rw [h0, mul_zero] at this
    exact h (hinj hv.1 hv.2 (sub_eq_zero.mp this.symm))

/-- **A logarithm of the difference quotient.** On a nonempty convex open set, the difference
quotient of an injective chart with nonvanishing derivative has a holomorphic logarithm on the
node pairs. -/
theorem exists_chartLog {V : Set ℂ} (hVo : IsOpen V) (hVc : Convex ℝ V) (hVn : V.Nonempty)
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) (hinj : InjOn φ V)
    (hder : ∀ s ∈ V, deriv φ s ≠ 0) :
    ∃ L : (Fin 2 → ℂ) → ℂ, AnalyticOnNhd ℂ L (pairDomain V) ∧
      ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v := by
  obtain ⟨s, hs⟩ := hVn
  have hne : (pairDomain V).Nonempty := ⟨![s, s], by simp [pairDomain, hs]⟩
  have hsc : IsSimplyConnected (pairDomain V) := by
    have := (convex_pairDomain hVc).contractibleSpace hne
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, heq⟩ := Complex.exists_analyticOnNhd_logBranch_of_analyticOnNhd
    (isOpen_pairDomain hVo) hsc (analyticOnNhd_chartQuot hVo hφ)
    (fun v hv => chartQuot_ne_zero hinj hder hv)
  exact ⟨L, hL, fun v hv => heq hv⟩

end Dirichlet

end
