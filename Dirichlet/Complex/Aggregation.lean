/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Complex.Analytic
public import Dirichlet.Transform.Aggregation
public import Dirichlet.Transform.Euler

/-!
# Native complex Dirichlet aggregation

Carlson (1977), Theorem 4.4-3: summing coordinate blocks sums the corresponding
complex parameters, for any kernel continuous on the closed simplex. Only positive
real parts are required; no entire continuation of the kernel is assumed. Analytic
uniqueness on the product of right half-planes extends the probability identity.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- On the native convergence region, agreement at positive real vectors determines an
analytic function. The functions need not extend across the boundary of that region. -/
theorem eqOn_mvBetaConvergent_of_eqOn_posReal
    {F G : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F mvBetaConvergent)
    (hG : AnalyticOnNhd ℂ G mvBetaConvergent)
    (hEq : ∀ b : ι → ℝ, (∀ i, 0 < b i) →
      F (fun i => (b i : ℂ)) = G (fun i => (b i : ℂ))) :
    EqOn F G mvBetaConvergent := by
  classical
  let P : Set ℂ := {w | 0 < w.re}
  have hP : Convex ℝ P := convex_halfSpace_re_gt 0
  have hstep : ∀ s : Finset ι, ∀ b ∈ mvBetaConvergent,
      (∀ i, i ∉ s → ∃ x : ℝ, 0 < x ∧ b i = (x : ℂ)) → F b = G b := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro b hb hr
      choose r hr hbr using fun i => hr i (by simp)
      have he : b = fun i => (r i : ℂ) := funext hbr
      rw [he]
      exact hEq r hr
    | @insert a s ha ih =>
      intro b hb hr
      let L : ℂ → (ι → ℂ) := fun w => Function.update b a w
      have hL : AnalyticOnNhd ℂ L univ := by
        intro w _
        apply analyticAt_pi_iff.mpr
        intro i
        by_cases hi : i = a
        · subst i
          have he : (fun x : ℂ => L x a) = id := by funext x; simp [L]
          rw [he]
          exact analyticAt_id
        · simpa [L, hi] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => b i) w)
      have hLP : ∀ w ∈ P, L w ∈ mvBetaConvergent := by
        intro w hw i
        by_cases hi : i = a
        · subst i; simpa [L] using (show 0 < w.re from hw)
        · simpa [L, hi] using hb i
      have hreal : ∀ᶠ x : ℝ in 𝓝 1, F (L x) = G (L x) := by
        filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
        apply ih _ (hLP _ (by simpa [P] using hx))
        intro i his
        by_cases hi : i = a
        · subst i; exact ⟨x, hx, by simp [L]⟩
        · simpa [L, hi] using hr i (by simp [his, hi])
      have he := (hF.comp (hL.mono (subset_univ P)) hLP).eqOn_of_eventuallyEq_ofReal
        (hG.comp (hL.mono (subset_univ P)) hLP) hP.isPreconnected
        (by norm_num [P] : (1 : ℂ) ∈ P) hreal
      simpa [L] using he (hb a)
  intro b hb
  exact hstep Finset.univ b hb (by simp)

/-- Summing a nonempty block of complex parameters with positive real parts preserves
the native convergence condition. -/
theorem mvBetaConvergent_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    stdSimplexAggregate q b ∈ mvBetaConvergent := by
  classical
  intro k
  obtain ⟨i, hi⟩ := hq k
  rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  rw [Complex.re_sum]
  exact Finset.sum_pos (fun j _ => hb j) ⟨i, by simp [hi]⟩

/-- **Carlson 4.4-3, regularized.** Native aggregation for continuous kernels and
arbitrary complex parameters in the domain of absolute convergence. -/
theorem regDirichletIntegral_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {g : (κ → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ κ)) :
    regDirichletIntegral b (fun u => g (stdSimplexAggregate q u)) =
      regDirichletIntegral (stdSimplexAggregate q b) g := by
  have hcomp : ContinuousOn (fun u => g (stdSimplexAggregate q u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hg.comp (continuous_stdSimplexAggregate q).continuousOn
      (fun _ hu => stdSimplexAggregate_mem_stdSimplex hu)
  have hleft := isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
    (regDirichletIntegral_analyticOn hcomp)
  have hright : AnalyticOnNhd ℂ
      (fun c : ι → ℂ => regDirichletIntegral (stdSimplexAggregate q c) g) mvBetaConvergent :=
    (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
      (regDirichletIntegral_analyticOn hg)).comp
      ((FunOnFinite.linearMap ℂ ℂ q).toContinuousLinearMap.analyticOnNhd _)
      (fun _ hc => mvBetaConvergent_aggregate hq hc)
  apply eqOn_mvBetaConvergent_of_eqOn_posReal hleft hright (fun c hc => ?_) hb
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have : IsEmpty κ := ⟨fun k => (hq k).elim fun i _ => isEmptyElim i⟩
    simp [regDirichletIntegral, MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
    have : Nonempty κ := ⟨q (Classical.arbitrary ι)⟩
    have hcast : stdSimplexAggregate q (fun i => (c i : ℂ)) =
        fun k => ((stdSimplexAggregate q c k : ℝ) : ℂ) := by
      simpa only [Complex.ofRealHom_eq_coe] using stdSimplexAggregate_map Complex.ofRealHom q c
    rw [hcast, regDirichletIntegral_ofReal hc,
      regDirichletIntegral_ofReal (mem_mvRealBetaDomain_stdSimplexAggregate hq hc),
      integral_dirichletMeasure_comp_aggregate hq hc hg]
    congr 2
    rw [← hcast, sum_aggregate_dirichletParameters]

/-- **Carlson 4.4-3.** Normalized complex Dirichlet integration conserves sums of
coordinates, with no smoothness or continuation assumption on the continuous kernel. -/
theorem complexDirichletIntegral_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {g : (κ → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ κ)) :
    complexDirichletIntegral b (fun u => g (stdSimplexAggregate q u)) =
      complexDirichletIntegral (stdSimplexAggregate q b) g := by
  rw [complexDirichletIntegral_eq_Gamma_mul, complexDirichletIntegral_eq_Gamma_mul,
    regDirichletIntegral_aggregate hq hb hg, sum_aggregate_dirichletParameters]

/-- **Carlson Corollary 4.4-4.** A continuous function of the sum of one coordinate
block has a single Euler beta integral, with the two block sums as parameters. -/
theorem complexDirichletIntegral_aggregate_fin_two {q : ι → Fin 2}
    (hq : Function.Surjective q) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) :
    complexDirichletIntegral b (fun u => f (stdSimplexAggregate q u 0)) =
      Gamma (∑ i, b i) * regEulerIntegral
        (stdSimplexAggregate q b 0) (stdSimplexAggregate q b 1) f := by
  have hg : ContinuousOn (fun u : Fin 2 → ℝ => f (u 0))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :=
    hf.comp (continuous_apply 0).continuousOn (fun _ hu =>
      Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu 0)
  rw [complexDirichletIntegral_aggregate hq hb hg,
    complexDirichletIntegral_eq_Gamma_mul, sum_aggregate_dirichletParameters]
  congr 1
  convert regDirichletIntegral_fin_two (stdSimplexAggregate q b 0)
    (stdSimplexAggregate q b 1) f using 1
  congr 1
  ext i
  fin_cases i <;> simp

end Dirichlet
