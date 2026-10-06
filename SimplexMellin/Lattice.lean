/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Image
public import StdSimplexMeasure.MomentProblem

/-!
# The simplex Mellin transform from its lattice values

For a kernel `g` continuous on the simplex, the simplex Mellin transform
`S_g(b) = ∫_Δ ∏ u^(b - 1) g` is holomorphic on `Re b > 0` and bounded by `‖g‖₁` on `Re b ≥ 1`.
By Carlson's theorem in several variables (`Complex.eqOn_zero_of_natCast_eq_zero_pi`) it is
therefore determined by its values at `b = n + 𝟙`, `n ∈ ℕ^ι`, the monomial moments
`∫_Δ uⁿ g`. This is an analytic counterpart of the moment determination of the kernel itself
(`StdSimplexMeasure.MomentDetermination`, `SimplexMellin.Uniqueness`): it concerns the transform
and not the kernel, and its proof uses no density argument.

## Main results

* `Dirichlet.differentiableOn_simplexMoment`: `S_g` is holomorphic on `Re b > 0`.
* `Dirichlet.norm_simplexMoment_le`: `‖S_g(b)‖ ≤ ‖g‖₁` for `Re b ≥ 1`.
* `Dirichlet.simplexMoment_eqOn_of_moments_eq`: kernels with the same monomial moments have the
  same transform on `Re b > 0`.
* `Dirichlet.exists_continuation_of_satisfiesSumShift`: nonnegative lattice data with the
  sum-shift equation, shifted by `𝟙`, have a continuation holomorphic on `Re b > -1` and bounded
  on `Re b ≥ 0`: the transform `b ↦ ∫ ∏ u^(b + 1) dμ` (`measureMellin`) of the measure solving
  the moment problem (`MeasureTheory.exists_measure_iff`).
* `Dirichlet.eqOn_of_natCast_eq_of_bounded`: such continuations are unique.

The shift by `𝟙` is needed. For the point mass at the vertex `e j`, the unshifted data in a
coordinate `i ≠ j` are `1` at `0` and `0` at every positive integer, and no function of
exponential type with imaginary type below `π` interpolates them.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology Real

namespace Dirichlet

open Measure

variable {ι : Type*} [Fintype ι]

open scoped Classical

omit [Fintype ι] in
/-- The region `Re b > 0` is convex. -/
theorem convex_mvBetaConvergent : Convex ℝ (mvBetaConvergent : Set (ι → ℂ)) := by
  intro x hx y hy a c ha hc hac i
  have hx' := hx i
  have hy' := hy i
  simp only [Pi.add_apply, Pi.smul_apply, add_re, smul_re, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hac; subst hac; simpa using hy'
  · nlinarith

/-- For a kernel continuous on the simplex, the simplex Mellin transform is holomorphic on
`Re b > 0`, where it equals `∏ Γ(b i) T_b[g]`. -/
theorem differentiableOn_simplexMoment {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    DifferentiableOn ℂ (fun b => simplexMoment b g) mvBetaConvergent := by
  have hdiv : divMonomial 0 g = g := funext fun u => by simp [divMonomial]
  have heq : ∀ b ∈ (mvBetaConvergent : Set (ι → ℂ)),
      simplexMoment b g = (∏ i, Gamma (b i)) * regDirichletIntegral b g := by
    intro b hb
    have := simplexMoment_eq_prod_Gamma_mul g 0 b fun i => by
      simpa using Gamma_ne_zero_of_re_pos (hb i)
    simpa [hdiv] using this
  refine DifferentiableOn.congr ?_ heq
  refine DifferentiableOn.mul ?_ (regDirichletIntegral_analyticOn hg).differentiableOn
  intro b hb
  have hGa : ∀ i, AnalyticAt ℂ Gamma (b i) := fun i =>
    DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re})
      (fun s hs => (differentiableAt_Gamma _ fun k h => by
        rw [h] at hs
        simp only [mem_ofPred_eq, neg_re, natCast_re] at hs
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]).differentiableWithinAt)
      ((isOpen_lt continuous_const continuous_re).mem_nhds (hb i))
  refine (Finset.analyticAt_fun_prod _ fun i _ => ?_).differentiableAt.differentiableWithinAt
  exact (hGa i).comp_of_eq
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b) rfl

/-- For a kernel continuous on the simplex and `Re b i ≥ 1`, `‖S_g(b)‖ ≤ ‖g‖₁`. -/
theorem norm_simplexMoment_le {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {b : ι → ℂ}
    (hb : ∀ i, 1 ≤ (b i).re) :
    ‖simplexMoment b g‖ ≤
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g u‖ ∂stdSimplexMeasure := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hgi : IntegrableOn (fun u => ‖g u‖) (Convexity.StdSimplex.coordinateSet ℝ ι)
      stdSimplexMeasure := by
    have h := hg.norm.integrableOn_compact (μ := stdSimplexMeasure.restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι))
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    rwa [IntegrableOn, Measure.restrict_restrict hS, inter_self] at h
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hgi ?_
  filter_upwards [ae_restrict_mem hS] with u hu
  rw [norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  have hu0 : 0 ≤ u i := (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).1
  have hu1 : u i ≤ 1 := (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
  rcases hu0.eq_or_lt with h0 | hpos
  · rw [← h0, ofReal_zero]
    by_cases hb1 : b i - 1 = 0
    · simp [hb1]
    · simp [zero_cpow hb1]
  · rw [norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_one hpos.le hu1 (by simp only [sub_re, one_re]; linarith [hb i])

/-- **The transform is determined by the monomial moments.** Two kernels continuous on the simplex
whose monomial moments agree, `S_g₁(n + 𝟙) = S_g₂(n + 𝟙)` for `n ∈ ℕ^ι`, have the same simplex
Mellin transform on `Re b > 0`. The proof applies Carlson's theorem in several variables on
`Re b ≥ 1` and the identity theorem; it uses no density of polynomials. -/
theorem simplexMoment_eqOn_of_moments_eq {g₁ g₂ : (ι → ℝ) → ℂ}
    (hg₁ : ContinuousOn g₁ (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hg₂ : ContinuousOn g₂ (Convexity.StdSimplex.coordinateSet ℝ ι))
    (h : ∀ n : ι → ℕ, simplexMoment (fun i => n i + 1) g₁ = simplexMoment (fun i => n i + 1) g₂) :
    EqOn (fun b => simplexMoment b g₁) (fun b => simplexMoment b g₂) mvBetaConvergent := by
  set D : (ι → ℂ) → ℂ := fun b => simplexMoment b g₁ - simplexMoment b g₂
  have hD : DifferentiableOn ℂ D mvBetaConvergent :=
    (differentiableOn_simplexMoment hg₁).sub (differentiableOn_simplexMoment hg₂)
  set A₁ := ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g₁ u‖ ∂stdSimplexMeasure
  set A₂ := ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g₂ u‖ ∂stdSimplexMeasure
  -- Carlson's theorem for `b ↦ D (b + 𝟙)` on `Re b ≥ 0`.
  have hshift : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → (fun i => b i + 1) ∈ mvBetaConvergent :=
    fun b hb i => by simp only [add_re, one_re]; linarith [hb i]
  have hC := Complex.eqOn_zero_of_natCast_eq_zero_pi (F := fun b => D fun i => b i + 1)
    (fun b hb => DifferentiableAt.comp (g := D) b ((hD _ (hshift b hb)).differentiableAt
      (isOpen_mvBetaConvergent.mem_nhds (hshift b hb)))
      (by fun_prop : DifferentiableAt ℂ (fun b : ι → ℂ => fun i => b i + 1) b))
    (C := A₁ + A₂) (τ := 0) (c := 0)
    (fun b hb => by
      simp only [zero_mul, add_zero, Finset.sum_const_zero, Real.exp_zero, mul_one]
      have hb1 : ∀ i, 1 ≤ ((fun i => b i + 1) i).re := fun i => by
        simp only [add_re, one_re]; linarith [hb i]
      exact (norm_sub_le _ _).trans (add_le_add (norm_simplexMoment_le hg₁ hb1)
        (norm_simplexMoment_le hg₂ hb1)))
    Real.pi_pos (fun n => by simp only [D, sub_eq_zero]; exact h n)
  -- The identity theorem on `Re b > 0`.
  have hDan : AnalyticOnNhd ℂ D mvBetaConvergent :=
    hD.analyticOnNhd_of_finiteDimensional isOpen_mvBetaConvergent
  set b₂ : ι → ℂ := fun _ => 2
  have hb₂ : b₂ ∈ mvBetaConvergent := fun i => by simp [b₂]
  have hW : IsOpen {b : ι → ℂ | ∀ i, 1 < (b i).re} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_re.comp (continuous_apply i))
  have hev : D =ᶠ[𝓝 b₂] 0 := by
    filter_upwards [hW.mem_nhds (fun i => by simp [b₂] : b₂ ∈ {b : ι → ℂ | ∀ i, 1 < (b i).re})]
      with b hb
    have := hC (fun i => b i - 1) fun i => by simp only [sub_re, one_re]; linarith [hb i]
    simpa using this
  have hz := hDan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_mvBetaConvergent.isPreconnected hb₂ hev
  intro b hb
  have := hz hb
  simpa [D, sub_eq_zero] using this

/-! ### Existence of continuations of lattice data -/

/-- The shifted Mellin transform `b ↦ ∫ ∏ u^(b + 1) dμ` of a measure on the simplex. -/
def measureMellin (μ : Measure (ι → ℝ)) (b : ι → ℂ) : ℂ :=
  ∫ u, ∏ i, ((u i : ℂ) ^ (b i + 1)) ∂μ

omit [Fintype ι] in
/-- On `[0, 1]`, complex powers with exponent of nonnegative real part are bounded by one. -/
theorem norm_ofReal_cpow_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(t : ℂ) ^ w‖ ≤ 1 := by
  rcases ht0.eq_or_lt with rfl | htp
  · rw [ofReal_zero]
    by_cases hw0 : w = 0
    · simp [hw0]
    · simp [zero_cpow hw0]
  · rw [norm_cpow_eq_rpow_re_of_pos htp]
    exact Real.rpow_le_one htp.le ht1 hw

omit [Fintype ι] in
/-- On `[0, 1]`, `‖t^w log t‖ ≤ 1 / σ` when `Re w ≥ σ > 0`. -/
theorem norm_ofReal_cpow_mul_log_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {w : ℂ} {σ : ℝ}
    (hσ : 0 < σ) (hw : σ ≤ w.re) : ‖(t : ℂ) ^ w * log t‖ ≤ 1 / σ := by
  rcases ht0.eq_or_lt with rfl | htp
  · simp [hσ.le]
  · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htp, ← ofReal_log htp.le, norm_real,
      Real.norm_eq_abs]
    calc t ^ w.re * |Real.log t| ≤ t ^ σ * |Real.log t| :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge htp ht1 hw) (abs_nonneg _)
      _ = |Real.log t * t ^ σ| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp σ), mul_comm]
      _ ≤ 1 / σ := (Real.abs_log_mul_self_rpow_lt t σ htp ht1 hσ).le

/-- The shifted Mellin transform of a finite measure on the simplex is holomorphic on
`Re b > -1`. -/
theorem differentiableOn_measureMellin {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = μ) :
    DifferentiableOn ℂ (measureMellin μ) {b | ∀ i, -1 < (b i).re} := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hae := ae_mem_of_restrict_eq_self hS hμ
  have hU : IsOpen {b : ι → ℂ | ∀ i, -1 < (b i).re} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_re.comp (continuous_apply i))
  refine (analyticOnNhd_integral_of_dominated_of_fderiv_le hU fun b₀ hb₀ => ?_).differentiableOn
  -- A uniform lower bound for `Re b i + 1` near `b₀`.
  set d : ι → ℝ := fun i => (b₀ i).re + 1
  have hd : ∀ i, 0 < d i := fun i => by simp only [d]; linarith [hb₀ i]
  set σ : ℝ := (∑ i, (d i)⁻¹ + 1)⁻¹ / 2
  have hσ0 : 0 < σ := div_pos (inv_pos.mpr (add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hd i)).le) one_pos)) two_pos
  have hσd : ∀ i, 2 * σ ≤ d i := by
    intro i
    have h1 : (d i)⁻¹ ≤ ∑ j, (d j)⁻¹ + 1 := by
      have := Finset.single_le_sum (f := fun j => (d j)⁻¹)
        (fun j _ => (inv_pos.mpr (hd j)).le) (Finset.mem_univ i)
      linarith
    have : (∑ j, (d j)⁻¹ + 1)⁻¹ ≤ d i := by
      calc (∑ j, (d j)⁻¹ + 1)⁻¹ ≤ ((d i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hd i)) h1
        _ = d i := inv_inv _
    simp only [σ]; linarith
  have hball : ∀ b ∈ Metric.ball b₀ σ, ∀ i, σ ≤ (b i + 1).re := by
    intro b hb i
    have h1 : |(b i).re - (b₀ i).re| < σ := by
      calc |(b i).re - (b₀ i).re| = |(b i - b₀ i).re| := by simp
        _ ≤ ‖b i - b₀ i‖ := abs_re_le_norm _
        _ ≤ ‖b - b₀‖ := norm_le_pi_norm (b - b₀) i
        _ < σ := by rwa [Metric.mem_ball, dist_eq_norm] at hb
    have := hσd i
    simp only [add_re, one_re, d] at this ⊢
    linarith [(abs_lt.mp h1).1]
  set F' : (ι → ℂ) → (ι → ℝ) → (ι → ℂ) →L[ℂ] ℂ := fun b u =>
    ∑ i, (∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j + 1)) •
      (((u i : ℂ) ^ (b i + 1) * log (u i)) • ContinuousLinearMap.proj i)
  have hmeasF : ∀ b : ι → ℂ, AEStronglyMeasurable
      (fun u : ι → ℝ => ∏ i, (u i : ℂ) ^ (b i + 1)) μ := fun b =>
    (Finset.measurable_prod _ fun i _ =>
      ((measurable_ofReal.comp (measurable_pi_apply i)).pow_const _)).aestronglyMeasurable
  refine ⟨Metric.ball b₀ σ, fun _ => Fintype.card ι * (1 / σ), F', Metric.ball_mem_nhds _ hσ0,
    Eventually.of_forall fun b => hmeasF b, ?_, ?_, ?_, integrable_const _, ?_⟩
  · refine Integrable.of_bound (hmeasF b₀) 1 ?_
    filter_upwards [hae] with u hu
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
    exact norm_ofReal_cpow_le_one (hu.1 i)
      (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
      (by simp only [add_re, one_re]; linarith [hb₀ i])
  · refine Measurable.aestronglyMeasurable ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    refine (Finset.measurable_prod _ fun j _ =>
      ((measurable_ofReal.comp (measurable_pi_apply j)).pow_const _)).smul ?_
    exact (((measurable_ofReal.comp (measurable_pi_apply i)).pow_const _).mul
      ((measurable_ofReal.comp (measurable_pi_apply i)).clog)).smul_const _
  · filter_upwards [hae] with u hu b hb
    have hu1 : ∀ i, u i ≤ 1 := fun i => (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
    refine (norm_sum_le _ _).trans ?_
    rw [show (Fintype.card ι : ℝ) * (1 / σ) = ∑ _i : ι, 1 / σ by simp]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, norm_smul]
    have h1 : ‖∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j + 1)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ =>
        norm_ofReal_cpow_le_one (hu.1 j) (hu1 j) (hσ0.le.trans (hball b hb j))
    have h2 := norm_ofReal_cpow_mul_log_le (hu.1 i) (hu1 i) hσ0 (hball b hb i)
    have h3 : ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        simpa using norm_le_pi_norm x i
    calc ‖∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j + 1)‖ *
          (‖(u i : ℂ) ^ (b i + 1) * log (u i)‖ * ‖ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : ι => ℂ) i‖)
        ≤ 1 * (1 / σ * 1) := by gcongr
      _ = 1 / σ := by ring
  · filter_upwards [hae] with u hu b hb
    refine HasFDerivAt.finsetProd fun i _ => ?_
    have hne : (u i : ℂ) ≠ 0 ∨ b i + 1 ≠ 0 := Or.inr fun h => by
      have := hball b hb i
      rw [h, zero_re] at this
      linarith
    have hd := (hasStrictDerivAt_const_cpow hne).hasDerivAt
    have hl : HasFDerivAt (fun b : ι → ℂ => b i + 1)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i) b :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.add_const 1
    exact hd.comp_hasFDerivAt b hl

/-- **Existence of continuations of lattice data.** A nonnegative sequence `a` on `ℕ^ι` with the
sum-shift equation has a continuation of the shifted data `n ↦ a (n + 𝟙)` that is holomorphic on
`Re b > -1` and bounded by `a 0` on `Re b ≥ 0`: the shifted Mellin transform of the measure
solving the moment problem (`MeasureTheory.exists_measure_of_satisfiesSumShift`). By Carlson's
theorem it is the only continuation of this kind (`Complex.eqOn_of_natCast_eq_pi`). -/
theorem exists_continuation_of_satisfiesSumShift {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (ha : MeasureTheory.SatisfiesSumShift a) :
    ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F {b | ∀ i, -1 < (b i).re} ∧
      (∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → ‖F b‖ ≤ a 0) ∧
      ∀ n : ι → ℕ, F (fun i => n i) = a (fun i => n i + 1) := by
  obtain ⟨μ, hμf, hμ, hm⟩ := MeasureTheory.exists_measure_of_satisfiesSumShift ha₀ ha
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hae := ae_mem_of_restrict_eq_self hS hμ
  refine ⟨measureMellin μ, differentiableOn_measureMellin hμ, fun b hb => ?_, fun n => ?_⟩
  · have hmass : (μ Set.univ).toReal = a 0 := by
      have := hm 0
      simpa [Measure.real] using this
    rw [← hmass]
    refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans (by simp [Measure.real])
    filter_upwards [hae] with u hu
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ =>
      norm_ofReal_cpow_le_one (hu.1 i) (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
        (by simp only [add_re, one_re]; linarith [hb i])
  · rw [measureMellin, ← hm (fun i => n i + 1), ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ofReal_prod, ofReal_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((n i : ℂ) + 1) = ((n i + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

/-- **Uniqueness of continuations of lattice data.** Two functions holomorphic on `Re b > -1` and
bounded on `Re b ≥ 0` that agree on `ℕ^ι` agree on `Re b ≥ 0` (Carlson's theorem). -/
theorem eqOn_of_natCast_eq_of_bounded {F₁ F₂ : (ι → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ {b | ∀ i, -1 < (b i).re})
    (hF₂ : DifferentiableOn ℂ F₂ {b | ∀ i, -1 < (b i).re}) {C : ℝ}
    (hb₁ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → ‖F₁ b‖ ≤ C)
    (hb₂ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → ‖F₂ b‖ ≤ C)
    (heq : ∀ n : ι → ℕ, F₁ (fun i => n i) = F₂ (fun i => n i)) :
    ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → F₁ b = F₂ b := by
  have hU : IsOpen {b : ι → ℂ | ∀ i, -1 < (b i).re} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_re.comp (continuous_apply i))
  have hmem : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → b ∈ {b : ι → ℂ | ∀ i, -1 < (b i).re} :=
    fun b hb i => by linarith [hb i]
  exact Complex.eqOn_of_natCast_eq_pi
    (fun b hb => (hF₁ b (hmem b hb)).differentiableAt (hU.mem_nhds (hmem b hb)))
    (fun b hb => (hF₂ b (hmem b hb)).differentiableAt (hU.mem_nhds (hmem b hb)))
    (C := C) (τ := 0) (c := 0) (fun b hb => by simpa using hb₁ b hb)
    (fun b hb => by simpa using hb₂ b hb) Real.pi_pos heq

end Dirichlet
