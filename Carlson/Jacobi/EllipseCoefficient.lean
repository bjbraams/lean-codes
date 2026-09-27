/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipticExpansion

/-!
# Jacobi coefficients as Dirichlet averages on elliptic disks

For a function `f` holomorphic on an open elliptic disk with foci `r, s`, the contour integral
of the continued resolvent against `f` over a confocal ellipse is entire in the Dirichlet
parameters. For polynomials it reproduces the regularized average of the `n`-th derivative;
approximating `f` by its Legendre-type Jacobi partial sums shows the same on the native
parameter region, so the contour expression is the unique regularized continuation of the
averages of `f⁽ⁿ⁾`. This gives Carlson's formula (7.6-8),
`aₙ = F⁽ⁿ⁾(1+α+n, 1+β+n; r, s)/n!`, for every elliptic disk and all complex parameters.

## Main results

* `analyticOnNhd_cycleIntegral_continuedRegCarlsonResolvent`: entire parameter dependence.
* `isRegCarlsonContinuation_jacobiEllipseCycle`: the continuation property.
* `jacobiContourCoefficient_jacobiEllipseCycle_eq_continuation`: formula (7.6-8), regularized.
* `jacobiContourCoefficient_jacobiEllipseCycle_eq_average`: formula (7.6-8), native form.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Theorem 7.6-2, equation (8).
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial Dirichlet MeasureTheory ContinuousLinearMap
open scoped Topology

namespace Carlson.TwoVariable

/-- The continued two-node resolvent integrated against a continuous function over a `C¹` cycle
avoiding the segment is entire in the Dirichlet parameters. -/
theorem analyticOnNhd_cycleIntegral_continuedRegCarlsonResolvent (n : ℕ) {r s : ℂ}
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.range) :
    AnalyticOnNhd ℂ (fun b : Fin 2 → ℂ => Γ.integral (fun z =>
      toSpanSingleton ℂ (continuedRegCarlsonResolvent n b (pair r s) z * f z))) Set.univ := by
  set W : Set ((Fin 2 → ℂ) × ℂ) := {p | (p.2, pair r s) ∈ carlsonResolventDomain}
  have hH : AnalyticOnNhd ℂ (fun p : (Fin 2 → ℂ) × ℂ =>
      continuedRegCarlsonResolvent n p.1 (pair r s) p.2) W := by
    intro p hp
    exact (analyticOnNhd_continuedRegCarlsonResolvent n (p.1, p.2, pair r s)
      ⟨mem_univ _, hp⟩).comp_of_eq (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)) rfl
  have hmem : ∀ i (t : ℝ), (Γ.loop i).2.extend t ∈ Γ.range := fun i t =>
    Γ.loop_extend_mem_range i t
  have hWmem : ∀ i (t : ℝ), ∀ b : Fin 2 → ℂ, (b, (Γ.loop i).2.extend t) ∈ W := by
    intro i t b
    apply mem_carlsonResolventDomain_of_not_mem_convexHull
    rw [convexHull_range_pair]
    exact havoid (hmem i t)
  unfold Cycle.integral
  refine Finset.analyticOnNhd_fun_sum _ (fun i _ => ?_)
  set γ := (Γ.loop i).2
  have hγc : ContinuousOn γ.extend (Icc (0 : ℝ) 1) := γ.continuous_extend.continuousOn
  have hd : ContinuousOn (fun t => derivWithin γ.extend unitInterval t) (Icc (0 : ℝ) 1) :=
    (hΓ i).continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hg : IntegrableOn (fun t : ℝ => derivWithin γ.extend unitInterval t * f (γ.extend t))
      (Icc 0 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (hd.mul ?_)
    exact hf.comp hγc (fun t _ => hmem i t)
  have hint := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc hg hγc
    isOpen_univ hH (fun b _ t _ => hWmem i t b)
  refine hint.congr isOpen_univ (fun b _ => ?_)
  rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  rw [curveIntegralFun_def]
  simp only [toSpanSingleton_apply, smul_eq_mul]
  ring

/-- Native regularized two-node averages depend continuously on the function, for uniform
convergence on the segment. -/
theorem tendsto_regCarlsonDirichletAverage_pair {b : Fin 2 → ℂ} (hb : b ∈ mvBetaConvergent)
    {r s : ℂ} {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hG : ∀ N, ContinuousOn (G N) (segment ℝ r s))
    (hg : ContinuousOn g (segment ℝ r s)) (hlim : TendstoUniformlyOn G g atTop (segment ℝ r s)) :
    Tendsto (fun N => regCarlsonDirichletAverage b (pair r s) (G N)) atTop
      (𝓝 (regCarlsonDirichletAverage b (pair r s) g)) := by
  set K := Convexity.StdSimplex.coordinateSet ℝ (Fin 2)
  have hK : IsCompact K := Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 2)
  have haff : ∀ u ∈ K, carlsonAffineForm (pair r s) u ∈ segment ℝ r s := fun u hu => by
    have := carlsonAffineForm_mem_convexHull (pair r s) hu
    rwa [convexHull_range_pair] at this
  have hcont (h : ℂ → ℂ) (hh : ContinuousOn h (segment ℝ r s)) :
      ContinuousOn (fun u => h (carlsonAffineForm (pair r s) u)) K :=
    hh.comp (continuous_carlsonAffineForm _).continuousOn haff
  have hdens := integrableOn_regDirichletDensity b hb
  set D := ∫ u in K, ‖regDirichletDensity b u‖ ∂Measure.stdSimplexMeasure
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, δ * (D + 1) < ε :=
    ⟨ε / (2 * (D + 1)), by positivity, by field_simp; linarith⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) δ hδ] with N hN
  rw [dist_eq_norm]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_sub (integrableOn_regDirichletDensity_mul b hb (hcont _ (hG N)))
    (integrableOn_regDirichletDensity_mul b hb (hcont _ hg))]
  calc
    _ ≤ ∫ u in K, ‖regDirichletDensity b u‖ * δ ∂Measure.stdSimplexMeasure := by
      apply norm_integral_le_of_norm_le (hdens.norm.mul_const δ)
      filter_upwards [ae_restrict_mem (Convexity.StdSimplex.isClosed_coordinateSet ℝ
        (Fin 2)).measurableSet] with u hu
      rw [← mul_sub, norm_mul]
      gcongr
      have := hN _ (haff u hu)
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    _ = D * δ := by rw [integral_mul_const]
    _ < ε := by nlinarith

/-- For polynomials, the cycle integral of the continued resolvent reproduces the regularized
native average of the `n`-th derivative, weighted by the index. -/
theorem cycleIntegral_continuedRegCarlsonResolvent_polynomial (n : ℕ) {b : Fin 2 → ℂ}
    (hb : b ∈ mvBetaConvergent) {r s : ℂ} (P : ℂ[X]) (Γ : Cycle) (hΓ : Γ.IsC1)
    (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ * Γ.integral (fun z =>
      toSpanSingleton ℂ (continuedRegCarlsonResolvent n b (pair r s) z * P.eval z)) =
      Γ.index r * regCarlsonDirichletAverage b (pair r s) (fun x => (derivative^[n] P).eval x) := by
  set α := b 0 - n - 1
  set β := b 1 - n - 1
  have hbp : pair (α + n + 1) (β + n + 1) = b := by
    funext i; fin_cases i <;> simp [α, β, pair] <;> ring
  have hsum : α + n + 1 + (β + n + 1) = b 0 + b 1 := by simp only [α, β]; ring
  have hc : 0 < (α + n + 1 + (β + n + 1)).re := by
    have h0 := hb 0; have h1 := hb 1
    rw [hsum, add_re]
    linarith
  have hG : Gamma (α + n + 1 + (β + n + 1)) ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have h := cycleIntegral_jacobiSecondKind_mul_polynomial α β r s n P Γ hΓ havoid
  rw [carlsonJacobiCoefficient_apply, carlsonPolynomialAverage, hbp, Fin.sum_univ_two,
    LinearMap.smul_apply, regCarlsonPolynomialAverage_eq_native _ _ hb, smul_eq_mul] at h
  have he : (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * P.eval z)) =
      (Gamma (α + n + 1 + (β + n + 1))) • (fun z => toSpanSingleton ℂ
        (continuedRegCarlsonResolvent n b (pair r s) z * P.eval z)) := by
    funext z; ext
    simp only [jacobiSecondKind, hbp, Pi.smul_apply, smul_apply, toSpanSingleton_apply,
      smul_eq_mul]
    ring
  rw [he, Cycle.integral_smul, smul_eq_mul] at h
  rw [hsum] at h hG
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp at h ⊢
  linear_combination h

/-- The contour expression over a confocal ellipse is the regularized continuation of the
Dirichlet averages of `f⁽ⁿ⁾`, for `f` holomorphic on a larger elliptic disk. -/
theorem isRegCarlsonContinuation_jacobiEllipseCycle (n : ℕ) {r s : ℂ} {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) :
    IsRegCarlsonContinuation (iteratedDeriv n f) (pair r s) (fun b =>
      (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ * (jacobiEllipseCycle r s hσ0).integral
        (fun z => toSpanSingleton ℂ (continuedRegCarlsonResolvent n b (pair r s) z * f z))) := by
  set Γ := jacobiEllipseCycle r s hσ0
  have hΓ := jacobiEllipseCycle_isC1 r s hσ0
  have hΓσ : ∀ z ∈ Γ.range, jacobiEllipseRadius r s z = σ := fun z hz =>
    jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hz
  have havoid : Γ.range ⊆ (segment ℝ r s)ᶜ := fun z hz =>
    not_mem_segment_of_lt_jacobiEllipseRadius (by rw [hΓσ z hz]; exact hσ)
  have hind : Γ.index r = 1 :=
    index_jacobiEllipseCycle_of_lt r s hσ0 hσ (by rw [jacobiEllipseRadius_left]; exact hσ)
  have hO : IsOpen (jacobiEllipseDisk r s τ) :=
    isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const
  have hΓU : Γ.range ⊆ jacobiEllipseDisk r s τ := fun z hz =>
    show jacobiEllipseRadius r s z < τ by rw [hΓσ z hz]; exact hστ
  have hfc : ContinuousOn f Γ.range := hf.continuousOn.mono hΓU
  refine ⟨fun b _ => (analyticAt_const.mul
    (analyticOnNhd_cycleIntegral_continuedRegCarlsonResolvent n Γ hΓ havoid hfc b (mem_univ _))),
    fun b hb => ?_⟩
  -- approximating polynomials from the Legendre-type Jacobi expansion
  set ρ := σ + (τ - σ) / 3
  set σ' := σ + 2 * (τ - σ) / 3
  have hρ : ‖r - s‖ / 4 < ρ := by simp only [ρ]; linarith
  have hσρ : σ < ρ := by simp only [ρ]; linarith
  have hρσ' : ρ < σ' := by simp only [ρ, σ']; linarith
  have hσ'τ : σ' < τ := by simp only [σ']; linarith
  have hσ'0 : 0 < σ' := by linarith
  have hc0 : IsCarlsonGammaRegular ((0 : ℂ) + 0 + 2) := by
    intro k h
    have := congrArg re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  set a : ℕ → ℂ := fun m => jacobiContourCoefficient 0 0 r s m (jacobiEllipseCycle r s hσ'0) f
  set P : ℕ → ℂ[X] := fun N => ∑ m ∈ Finset.range N, C (a m) * jacobiOn 0 0 r s m
  have hPeval (N : ℕ) (x : ℂ) : (P N).eval x = ∑ m ∈ Finset.range N,
      a m * (jacobiOn 0 0 r s m).eval x := by
    simp only [P, eval_finsetSum, eval_mul, eval_C]
  have hunif := tendstoUniformlyOn_sum_jacobiContourCoefficient_jacobiEllipseCycle 0 0 r s hc0 hf
    hσ'0 hρ hρσ' hσ'τ
  have hunifP : TendstoUniformlyOn (fun N x => (P N).eval x) f atTop
      {x | jacobiEllipseRadius r s x ≤ ρ} := by
    simpa only [hPeval] using hunif
  -- the left side
  have hRdom : ∀ z ∈ Γ.range, (z, pair r s) ∈ carlsonResolventDomain := fun z hz =>
    mem_carlsonResolventDomain_of_not_mem_convexHull (by
      rw [convexHull_range_pair]; exact havoid hz)
  have hRc : ContinuousOn (fun z => continuedRegCarlsonResolvent n b (pair r s) z) Γ.range :=
    fun z hz => ((analyticOnNhd_continuedRegCarlsonResolvent n (b, z, pair r s)
      ⟨mem_univ _, hRdom z hz⟩).comp_of_eq (analyticAt_const.prod
        (analyticAt_id.prod analyticAt_const)) rfl).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn hRc
  have hleft : TendstoUniformlyOn
      (fun N z => continuedRegCarlsonResolvent n b (pair r s) z * (P N).eval z)
      (fun z => continuedRegCarlsonResolvent n b (pair r s) z * f z) atTop Γ.range := by
    rw [Metric.tendstoUniformlyOn_iff] at hunifP ⊢
    intro ε hε
    obtain ⟨δ, hδ, hBδ⟩ : ∃ δ > 0, (|B| + 1) * δ < ε :=
      ⟨ε / (2 * (|B| + 1)), by positivity, by field_simp; linarith⟩
    filter_upwards [hunifP δ hδ] with N hN z hz
    have h1 := hN z (show jacobiEllipseRadius r s z ≤ ρ by rw [hΓσ z hz]; exact hσρ.le)
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    rw [dist_eq_norm] at h1
    calc _ ≤ (|B| + 1) * δ := mul_le_mul ((hB z hz).trans (by linarith [le_abs_self B]))
          h1.le (norm_nonneg _) (by positivity)
      _ < ε := hBδ
  have hlimL := (tendsto_cycle_integral_of_tendstoUniformlyOn Γ hΓ
    (fun N => hRc.mul (Polynomial.continuous _).continuousOn) hleft).const_mul
      ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹)
  -- the right side
  have hO' : IsOpen (jacobiEllipseDisk r s ρ) :=
    isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const
  have hloc0 : TendstoLocallyUniformlyOn (fun N x => (P N).eval x) f atTop
      (jacobiEllipseDisk r s ρ) :=
    (hunifP.mono (fun x (hx : jacobiEllipseRadius r s x < ρ) => hx.le)).tendstoLocallyUniformlyOn
  have hlock : ∀ k, TendstoLocallyUniformlyOn (fun N x => (derivative^[k] (P N)).eval x)
      (iteratedDeriv k f) atTop (jacobiEllipseDisk r s ρ) := by
    intro k
    induction k with
    | zero => simpa using hloc0
    | succ k ih =>
      have h := ih.deriv (Eventually.of_forall fun N =>
        (derivative^[k] (P N)).differentiable.differentiableOn) hO'
      rw [iteratedDeriv_succ]
      refine h.congr (fun N x _ => ?_)
      simp only [Function.comp_apply, Polynomial.deriv, Function.iterate_succ_apply']
  have hsegO : segment ℝ r s ⊆ jacobiEllipseDisk r s ρ := segment_subset_jacobiEllipseDisk r s hρ
  have hsegc : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]; exact (finite_range (pair r s)).isCompact_convexHull ℝ
  have hunifSeg := (tendstoLocallyUniformlyOn_iff_forall_isCompact hO').mp (hlock n) _ hsegO hsegc
  have hanf : AnalyticOnNhd ℂ (iteratedDeriv n f) (jacobiEllipseDisk r s τ) := by
    simpa [iteratedDeriv_eq_iterate] using (hf.analyticOnNhd hO).iterated_deriv n
  have hsegτ : segment ℝ r s ⊆ jacobiEllipseDisk r s τ :=
    segment_subset_jacobiEllipseDisk r s (hσ.trans hστ)
  have hlimR := tendsto_regCarlsonDirichletAverage_pair hb
    (fun N => (Polynomial.continuous _).continuousOn) (hanf.continuousOn.mono hsegτ) hunifSeg
  -- the two sides agree for polynomials
  have heq (N : ℕ) : (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ * Γ.integral (fun z =>
      toSpanSingleton ℂ (continuedRegCarlsonResolvent n b (pair r s) z * (P N).eval z)) =
      regCarlsonDirichletAverage b (pair r s) (fun x => (derivative^[n] (P N)).eval x) := by
    rw [cycleIntegral_continuedRegCarlsonResolvent_polynomial n hb (P N) Γ hΓ havoid, hind,
      one_mul]
  exact tendsto_nhds_unique (hlimL.congr heq) hlimR

/-- Carlson's formula (7.6-8) on elliptic disks, for all complex parameters: the Jacobi
coefficient of a function holomorphic on an open elliptic disk is the continued Dirichlet
average of its `n`-th derivative, `aₙ = F⁽ⁿ⁾(1+α+n, 1+β+n; r, s)/n!`, in regularized form. -/
theorem jacobiContourCoefficient_jacobiEllipseCycle_eq_continuation (α β r s : ℂ) (n : ℕ)
    {τ : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation (iteratedDeriv n f) (pair r s) G) :
    jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f =
      Gamma (α + n + 1 + (β + n + 1)) * G (pair (α + n + 1) (β + n + 1)) / n.factorial := by
  have hGe := congrFun (hG.eq (isRegCarlsonContinuation_jacobiEllipseCycle n hf hσ0 hσ hστ))
    (pair (α + n + 1) (β + n + 1))
  rw [hGe]
  unfold jacobiContourCoefficient
  have he : (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) =
      Gamma (α + n + 1 + (β + n + 1)) • (fun z => toSpanSingleton ℂ
        (continuedRegCarlsonResolvent n (pair (α + n + 1) (β + n + 1)) (pair r s) z * f z)) := by
    funext z; ext
    simp only [jacobiSecondKind, Pi.smul_apply, smul_apply, toSpanSingleton_apply, smul_eq_mul]
    ring
  rw [he, Cycle.integral_smul, smul_eq_mul]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Carlson's formula (7.6-8) in its native form: when `re(1+α+n), re(1+β+n) > 0`, the Jacobi
coefficient is the Dirichlet average of the `n`-th derivative over the focal segment divided by
`n!`. -/
theorem jacobiContourCoefficient_jacobiEllipseCycle_eq_average (α β r s : ℂ) (n : ℕ)
    (hα : 0 < (α + n + 1).re) (hβ : 0 < (β + n + 1).re)
    {τ : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) :
    jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f =
      carlsonDirichletAverage (pair (α + n + 1) (β + n + 1)) (pair r s) (iteratedDeriv n f) /
        n.factorial := by
  have hcont := isRegCarlsonContinuation_jacobiEllipseCycle n hf hσ0 hσ hστ
  have hnat := hcont.2 (show pair (α + n + 1) (β + n + 1) ∈ mvBetaConvergent by
      intro i; fin_cases i
      · exact hα
      · exact hβ)
  simp only at hnat
  rw [jacobiContourCoefficient_jacobiEllipseCycle_eq_continuation α β r s n hf hσ0 hσ hστ hcont,
    hnat, carlsonDirichletAverage, sum_pair]
  rfl

end Carlson.TwoVariable
