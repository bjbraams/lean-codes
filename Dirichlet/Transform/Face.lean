/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Laws
public import Pochhammer.IncompleteMellin

/-!
# Face formulas for the regularized Dirichlet transform

At a nonpositive integer parameter the regularized Dirichlet density `uᵢ^(bᵢ-1)/Γ(bᵢ)` becomes a
derivative of the Dirac measure on the face `uᵢ = 0`. For the entire transform of a smooth
kernel this gives face formulas:

* at `bᵢ = 0` the transform is the transform of the restriction of the kernel to the face
  `uᵢ = 0`, with the remaining parameters (Carlson's omission of a vanishing parameter, for
  general kernels);
* at `bᵢ = -m` it is a binomial combination of face transforms of tangential derivatives of the
  kernel, with lowered parameters.

The proof at `bᵢ = 0` splits off the coordinate `uᵢ` (`Dirichlet.regDirichletIntegral_split_at`)
and lets the exponent of the resulting regularized incomplete Mellin transform tend to zero. The
general case follows from tangential integration by parts (`IsRegDirichletContinuation.tangent`).

## Main results

* `Complex.tendsto_regIncompleteMellin_nhdsGT_zero`: the regularized incomplete Mellin transform
  of a continuous function tends to its value at zero as the exponent tends to zero.
* `Dirichlet.IsRegDirichletContinuation.face_zero`: the face formula at a zero parameter.
* `Dirichlet.regDirichletTransform_tangentDeriv`: integration by parts for the entire transform
  of a smooth kernel, for all complex parameters.
* `Dirichlet.regDirichletTransform_sub_single_eq_sum`: iterated integration by parts, a binomial
  expansion of a parameter shift by `-m`.
* `Dirichlet.regDirichletTransform_eq_sum_face`: the face formula at `bᵢ = -m`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.2
  (omission of a vanishing parameter).
* I. M. Gel'fand and G. E. Shilov, *Generalized Functions*, Vol. 1, Chapter I, §3 (the
  distributions `x₊^λ / Γ(λ + 1)`).
-/

open Complex MeasureTheory Set Filter
open scoped Topology

@[expose] public noncomputable section

namespace Complex

/-- The regularized incomplete Mellin transform of a function continuous on `[0, 1]` tends to the
value of the function at zero as the exponent tends to zero from the right. This is the statement
that `t₊^(ε-1)/Γ(ε)` tends to the Dirac measure at zero. -/
theorem tendsto_regIncompleteMellin_nhdsGT_zero {h : ℝ → ℂ} (hh : ContinuousOn h (Icc 0 1)) :
    Tendsto (fun ε : ℝ => regIncompleteMellin (ε : ℂ) 1 h) (𝓝[>] 0) (𝓝 (h 0)) := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hh.sub continuousOn_const : ContinuousOn (fun t => h t - h 0) (Icc 0 1))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0mem)
  -- The reciprocal of `Γ(ε + 1)` tends to one.
  have hrecip : Tendsto (fun ε : ℝ => (Gamma ((ε : ℂ) + 1))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => (Gamma ((ε : ℂ) + 1))⁻¹) := by
      have := differentiable_one_div_Gamma.continuous.comp
        (continuous_ofReal.add (continuous_const (y := (1 : ℂ))))
      simpa [Function.comp_def, one_div] using this
    have := hc.tendsto 0
    simp only [ofReal_zero, zero_add, Gamma_one, inv_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- Split off the value at zero.
  have hsplit : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), regIncompleteMellin (ε : ℂ) 1 h =
      (Gamma ((ε : ℂ) + 1))⁻¹ * h 0 +
        (ε : ℂ) * (Gamma ((ε : ℂ) + 1))⁻¹ *
          ∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hεre : 0 < ((ε : ℂ)).re := by simpa using hε
    have hε0 : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
    have hG : Gamma ((ε : ℂ) + 1) = ε * Gamma ε := Gamma_add_one _ hε0
    have hint1 := integrableOn_cpow_mul_Icc hεre zero_le_one (K := fun _ => h 0)
      continuousOn_const
    have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0)) (Icc 0 1) :=
      integrableOn_cpow_mul_Icc hεre zero_le_one (K := fun t => h t - h 0)
        (hh.sub continuousOn_const)
    have hpow : (∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ ((ε : ℂ) - 1) * h 0) = h 0 / ε := by
      rw [integral_mul_const, integral_Icc_cpow hεre one_pos]
      simp [div_eq_mul_inv, mul_comm]
    unfold regIncompleteMellin
    have hsum : (fun t : ℝ => (t : ℂ) ^ ((ε : ℂ) - 1) * h t) =
        fun t : ℝ => (t : ℂ) ^ ((ε : ℂ) - 1) * h 0 + (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0) := by
      funext t; ring
    rw [hsum, integral_add hint1 hint2, hpow, hG]
    have hΓ : Gamma (ε : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hεre
    field_simp
  -- The remainder tends to zero.
  have hrem : Tendsto (fun ε : ℝ => (ε : ℂ) * (Gamma ((ε : ℂ) + 1))⁻¹ *
      ∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    -- Choose `δ` such that `‖h t - h 0‖ ≤ η / 8` on `[0, δ]`.
    have hc0 : ContinuousWithinAt h (Icc 0 1) 0 := hh 0 h0mem
    obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousWithinAt_iff.mp hc0 (η / 8) (by positivity)
    set δ := min (δ₀ / 2) (1 / 2) with hδ_def
    have hδpos : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
    have hnear : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ δ → ‖h t - h 0‖ ≤ η / 8 := by
      intro t ht htδ
      have := hδ ht (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact lt_of_le_of_lt htδ (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
      rw [dist_eq_norm] at this
      exact this.le
    have hev1 := hrecip.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1))
    have hev2 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < min 1 (η * δ / (8 * (M + 1))) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (η * δ / (8 * (M + 1))) by
        positivity)] with ε hε using hε.2
    filter_upwards [hev1, hev2, self_mem_nhdsWithin] with ε h1 h2 (hε : 0 < ε)
    have hεre : 0 < ((ε : ℂ)).re := by simpa using hε
    have hε1 : ε < 1 := lt_of_lt_of_le h2 (min_le_left _ _)
    have hΓbound : ‖(Gamma ((ε : ℂ) + 1))⁻¹‖ ≤ 2 := by
      have := mem_ball_iff_norm.mp h1
      calc ‖(Gamma ((ε : ℂ) + 1))⁻¹‖ ≤ ‖(Gamma ((ε : ℂ) + 1))⁻¹ - 1‖ + ‖(1 : ℂ)‖ :=
            norm_le_norm_sub_add ((Gamma ((ε : ℂ) + 1))⁻¹) 1
        _ ≤ 2 := by rw [norm_one]; linarith
    -- Pointwise bound for the integrand.
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0)‖ ≤
          η / 8 * ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ + M / δ := by
      intro t ht
      rw [norm_mul]
      by_cases htδ : t ≤ δ
      · have := hnear t ht htδ
        nlinarith [norm_nonneg ((t : ℂ) ^ ((ε : ℂ) - 1)), div_nonneg hM0 hδpos.le]
      · push Not at htδ
        have htpos : 0 < t := hδpos.trans htδ
        have hnorm : ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ = t ^ (ε - 1) := by
          rw [show ((ε : ℂ) - 1) = ((ε - 1 : ℝ) : ℂ) by push_cast; ring,
            ← ofReal_cpow htpos.le, norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.rpow_pos_of_pos htpos _)]
        have hle : t ^ (ε - 1) ≤ 1 / δ := by
          calc t ^ (ε - 1) ≤ δ ^ (ε - 1) :=
                Real.rpow_le_rpow_of_nonpos hδpos htδ.le (by linarith)
            _ ≤ δ ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδpos (by linarith) (by linarith)
            _ = 1 / δ := by rw [Real.rpow_neg_one, one_div]
        have := hM t ht
        calc ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ * ‖h t - h 0‖ ≤ (1 / δ) * M := by
              rw [hnorm]
              exact mul_le_mul hle this (norm_nonneg _) (by positivity)
          _ = M / δ := by ring
          _ ≤ η / 8 * ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ + M / δ := le_add_of_nonneg_left (by positivity)
    have hintb : IntegrableOn (fun t : ℝ => η / 8 * ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ + M / δ)
        (Icc 0 1) := by
      refine Integrable.add ?_ (integrableOn_const (by simp) (by simp))
      exact ((integrableOn_cpow_Icc hεre zero_le_one).norm.const_mul _)
    have hnormint : ∫ t in Icc (0 : ℝ) 1, ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ = 1 / ε := by
      have : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ = t ^ (ε - 1) := by
        intro t ht
        rw [show ((ε : ℂ) - 1) = ((ε - 1 : ℝ) : ℂ) by push_cast; ring,
          ← ofReal_cpow ht.1, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
      rw [setIntegral_congr_fun measurableSet_Icc this, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
      simp [Real.zero_rpow hε.ne']
    have hI : ‖∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0)‖ ≤
        η / 8 * (1 / ε) + M / δ := by
      calc _ ≤ ∫ t in Icc (0 : ℝ) 1, (η / 8 * ‖(t : ℂ) ^ ((ε : ℂ) - 1)‖ + M / δ) :=
            MeasureTheory.norm_integral_le_of_norm_le hintb
              ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hbound))
        _ = η / 8 * (1 / ε) + M / δ := by
          rw [integral_add ((integrableOn_cpow_Icc hεre zero_le_one).norm.const_mul _)
            (integrableOn_const (by simp) (by simp)), integral_const_mul, hnormint,
            setIntegral_const]
          simp
    rw [dist_zero_right, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖(Gamma ((ε : ℂ) + 1))⁻¹‖ *
          ‖∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ ((ε : ℂ) - 1) * (h t - h 0)‖
        ≤ ε * 2 * (η / 8 * (1 / ε) + M / δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΓbound hε.le) hI (norm_nonneg _)
            (by positivity)
      _ = η / 4 + 2 * ε * (M / δ) := by field_simp; ring
      _ < η := by
          have hε' : ε < η * δ / (8 * (M + 1)) := lt_of_lt_of_le h2 (min_le_right _ _)
          have : 2 * ε * (M / δ) < η / 4 + η / 4 := by
            have hMδ : M / δ ≤ (M + 1) / δ := by gcongr; linarith
            calc 2 * ε * (M / δ) ≤ 2 * ε * ((M + 1) / δ) := by gcongr
              _ < 2 * (η * δ / (8 * (M + 1))) * ((M + 1) / δ) := by gcongr
              _ = η / 4 := by field_simp; ring
              _ < η / 4 + η / 4 := by linarith
          linarith
  have hlim := (hrecip.mul_const (h 0)).add hrem
  rw [one_mul, add_zero] at hlim
  exact hlim.congr' (hsplit.mono fun ε h => h.symm)

end Complex


namespace Dirichlet

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Slices of a continuous simplex kernel stay in the simplex. -/
theorem stdSimplexCoordMap_scale_mem (i : ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ}
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    stdSimplexCoordMap i (fun j => (1 - t) * v j) ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  rw [stdSimplexCoordMap_mem_stdSimplex_iff]
  refine ⟨fun j => mul_nonneg (sub_nonneg.mpr ht.2) (hv.1 j), ?_⟩
  rw [← Finset.mul_sum, hv.2, mul_one]
  exact sub_le_self _ ht.1

open scoped Classical in
/-- The regularized transform of the slices of a continuous kernel depends continuously on the
height of the slice. -/
theorem continuousOn_regDirichletIntegral_slice (i : ι) {b : {j : ι // j ≠ i} → ℂ}
    (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ContinuousOn (fun t => regDirichletIntegral b (stdSimplexSlice i t g)) (Icc 0 1) := by
  obtain ⟨C, hC⟩ := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).exists_bound_of_continuousOn
    hg
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ {j : ι // j ≠ i}).measurableSet
  have hden : IntegrableOn (fun v => regDirichletDensity b v)
      (Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) Measure.stdSimplexMeasure := by
    simpa using integrableOn_regDirichletDensity_mul b hb (f := fun _ => (1 : ℂ))
      continuousOn_const
  unfold regDirichletIntegral
  apply continuousOn_of_dominated (bound := fun v => ‖regDirichletDensity b v‖ * C)
  · intro t ht
    exact (integrableOn_regDirichletDensity_mul b hb
      (continuousOn_stdSimplexSlice i ht hg)).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem hS] with v hv
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ (stdSimplexCoordMap_scale_mem i ht hv))
      (norm_nonneg _)
  · exact hden.norm.mul_const C
  · filter_upwards [ae_restrict_mem hS] with v hv
    refine continuousOn_const.mul ?_
    have hmap : Continuous (fun t : ℝ => stdSimplexCoordMap i (fun j => (1 - t) * v j)) := by
      apply continuous_pi
      intro k
      by_cases hk : k = i
      · subst k; simp_rw [stdSimplexCoordMap_apply_self]; fun_prop
      · simp_rw [stdSimplexCoordMap_apply_of_ne i k hk]; fun_prop
    exact hg.comp hmap.continuousOn fun t ht => stdSimplexCoordMap_scale_mem i ht hv

open scoped Classical in
/-- **The face formula at a zero parameter.** If the `i`-th Dirichlet parameter vanishes, the
entire transform of a continuous kernel is the entire transform, with the remaining parameters,
of its restriction to the face `uᵢ = 0`. This is Carlson's omission of a vanishing parameter for
an arbitrary kernel. -/
theorem IsRegDirichletContinuation.face_zero [Nontrivial ι] {g : (ι → ℝ) → ℂ}
    {F : (ι → ℂ) → ℂ} (hF : IsRegDirichletContinuation g F) (i : ι)
    {F' : ({j : ι // j ≠ i} → ℂ) → ℂ}
    (hF' : IsRegDirichletContinuation (stdSimplexFaceRestriction i g) F')
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {b : ι → ℂ}
    (hb : b i = 0) : F b = F' (fun j => b j) := by
  -- The hyperplane `bᵢ = 0`, parametrized by the remaining parameters.
  let E : ({j : ι // j ≠ i} → ℂ) → ι → ℂ := fun c k => if h : k = i then 0 else c ⟨k, h⟩
  have hEb : E (fun j => b j) = b := by
    funext k; by_cases h : k = i
    · subst h; simp [E, hb]
    · simp [E, h]
  have hE : AnalyticOnNhd ℂ (fun c => F (E c)) univ := by
    intro c _
    refine (hF.1 _ (mem_univ _)).comp_of_eq ?_ rfl
    refine analyticAt_pi_iff.mpr fun k => ?_
    by_cases h : k = i
    · simp only [h, dite_true]; exact analyticAt_const
    · simp only [h, dite_false]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : {j : ι // j ≠ i} => ℂ)
        ⟨k, h⟩).analyticAt c
  -- Agreement where all remaining parameters have real part greater than one.
  have hW : ∀ c : {j : ι // j ≠ i} → ℂ, (∀ j, 1 < (c j).re) → F (E c) = F' c := by
    intro c hc
    have hc0 : c ∈ mvBetaConvergent := fun j => lt_trans one_pos (hc j)
    obtain ⟨j₀⟩ : Nonempty {j : ι // j ≠ i} := by
      obtain ⟨k, hk⟩ := exists_ne i
      exact ⟨⟨k, hk⟩⟩
    have hsum : 0 < (∑ q, c q - 1).re := by
      rw [sub_re, one_re, re_sum]
      have : (c j₀).re ≤ ∑ q, (c q).re := Finset.single_le_sum
        (fun q _ => (lt_trans one_pos (hc q)).le) (Finset.mem_univ j₀)
      linarith [hc j₀]
    set h : ℝ → ℂ := fun t => (1 - (t : ℂ)) ^ (∑ q, c q - 1) *
      regDirichletIntegral c (stdSimplexSlice i t g) with hh_def
    have hcont : ContinuousOn h (Icc 0 1) := by
      refine ContinuousOn.mul ?_ (continuousOn_regDirichletIntegral_slice i hc0 hg)
      intro t ht
      have hbase : 0 ≤ (1 - (t : ℂ)).re := by simp [ht.2]
      exact ((continuousAt_cpow_const_of_re_pos (Or.inl hbase) hsum).comp
        (f := fun t : ℝ => 1 - (t : ℂ)) (by fun_prop)).continuousWithinAt
    -- Approach the hyperplane from the convergence region.
    let bε : ℝ → ι → ℂ := fun ε => Function.update (E c) i (ε : ℂ)
    have hbε0 : bε 0 = E c := by
      funext k; by_cases hk : k = i
      · subst hk; simp [bε, E]
      · simp [bε, Function.update_of_ne hk]
    have hlimF : Tendsto (fun ε : ℝ => F (bε ε)) (𝓝[>] 0) (𝓝 (F (E c))) := by
      have hcb : Continuous bε := by
        apply continuous_pi; intro k
        by_cases hk : k = i
        · subst hk; simp only [bε, Function.update_self]; fun_prop
        · simp only [bε, Function.update_of_ne hk]; fun_prop
      have := ((hF.1 _ (mem_univ _)).continuousAt.tendsto.comp (hcb.tendsto 0))
      rw [hbε0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F (bε ε) = regIncompleteMellin (ε : ℂ) 1 h := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hmem : bε ε ∈ mvBetaConvergent := by
        intro k; by_cases hk : k = i
        · subst hk; simpa [bε] using hε
        · simpa [bε, Function.update_of_ne hk, E, hk] using hc0 ⟨k, hk⟩
      have hrest : (fun q : {j : ι // j ≠ i} => bε ε q) = c := by
        funext q; simp [bε, E, q.2]
      rw [hF.eq_native hmem, regDirichletIntegral_split_at i hmem hg, hrest]
      simp only [bε, Function.update_self]
      rfl
    have hlimM := Complex.tendsto_regIncompleteMellin_nhdsGT_zero hcont
    have hh0 : h 0 = F' c := by
      simp only [hh_def, ofReal_zero, sub_zero, one_cpow, one_mul, stdSimplexSlice_zero]
      exact (hF'.eq_native hc0).symm
    rw [← hh0]
    exact tendsto_nhds_unique hlimF (hlimM.congr' (heq.mono fun ε h => h.symm))
  -- The identity theorem.
  have hall : (fun c => F (E c)) = F' := by
    apply hE.eq_of_eventuallyEq hF'.1 (z₀ := fun _ => (2 : ℂ))
    have hopen : IsOpen {c : {j : ι // j ≠ i} → ℂ | ∀ j, 1 < (c j).re} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt continuous_const (continuous_re.comp (continuous_apply j))
    filter_upwards [hopen.mem_nhds (fun j => by norm_num)] with c hc
    exact hW c hc
  rw [← congrFun hall (fun j => b j), hEb]

/-! ### Tangential derivatives and the face formula at `bᵢ = -m` -/

/-- A kernel smooth near the simplex is differentiable at every point of the simplex. -/
theorem SmoothNearStdSimplex.differentiableAt {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) : DifferentiableAt ℝ g u := by
  obtain ⟨U, hU, hsub, hgU⟩ := hg 1
  exact (hgU.contDiffAt (hU.mem_nhds (hsub hu))).differentiableAt one_ne_zero

open scoped Classical in
/-- Restricting to a boundary face preserves smoothness near the simplex. -/
theorem SmoothNearStdSimplex.faceRestriction {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (i : ι) : SmoothNearStdSimplex (stdSimplexFaceRestriction i g) :=
  fun N => (hg N).faceRestriction i

/-- Iterated tangential derivatives of a smooth kernel are smooth. -/
theorem SmoothNearStdSimplex.iterate_tangentDeriv {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (j i : ι) (k : ℕ) :
    SmoothNearStdSimplex ((stdSimplexTangentDeriv j i)^[k] g) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tangentDeriv j i

open scoped Classical in
/-- **Integration by parts for the entire transform.** The transform of the tangential
derivative `∂ⱼᵢ g` (transferring mass from `i` to `j`) is a difference of unit parameter shifts
of the transform of `g`, for all complex parameters. -/
theorem regDirichletTransform_tangentDeriv {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (i : ι) (j : {j : ι // j ≠ i}) (b : ι → ℂ) :
    regDirichletTransform (stdSimplexTangentDeriv (j : ι) i g) (hg.tangentDeriv j i) b =
      regDirichletTransform g hg (b - Pi.single i 1) -
        regDirichletTransform g hg (b - Pi.single (j : ι) 1) :=
  (isRegDirichletContinuation_transform hg).tangent i j
    (isRegDirichletContinuation_transform (hg.tangentDeriv j i))
    (fun _ hu => hg.differentiableAt hu) ((hg.tangentDeriv j i) 0).continuousOn b

open scoped Classical in
/-- Iterated integration by parts: lowering the `i`-th parameter by `m` expands binomially into
the transforms of the tangential derivatives `∂ⱼᵢᵃ g` with the `j`-th parameter lowered by
`m - a`. -/
theorem regDirichletTransform_sub_single_eq_sum {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (i : ι) (j : {j : ι // j ≠ i}) (m : ℕ) (b : ι → ℂ) :
    regDirichletTransform g hg (b - Pi.single i (m : ℂ)) =
      ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℂ) *
        regDirichletTransform ((stdSimplexTangentDeriv (j : ι) i)^[p.1] g)
          (hg.iterate_tangentDeriv j i p.1) (b - Pi.single (j : ι) (p.2 : ℂ)) := by
  set D := stdSimplexTangentDeriv (j : ι) i
  let T : ℕ → (ι → ℂ) → ℂ := fun k => regDirichletTransform (D^[k] g)
    (hg.iterate_tangentDeriv j i k)
  -- The one-step recursion `T k (c - eᵢ) = T (k + 1) c + T k (c - eⱼ)`.
  have hstep (k : ℕ) (c : ι → ℂ) : T k (c - Pi.single i 1) =
      T (k + 1) c + T k (c - Pi.single (j : ι) 1) := by
    have h := regDirichletTransform_tangentDeriv (hg.iterate_tangentDeriv j i k) i j c
    simp only [T, Function.iterate_succ_apply']
    rw [h]; ring
  have hsingle (c : ι → ℂ) (l : ι) (x y : ℂ) :
      c - Pi.single l x - Pi.single l y = c - Pi.single l (x + y) := by
    ext q; by_cases hq : q = l
    · subst hq; simp; ring
    · simp [hq]
  suffices H : ∀ (m k : ℕ) (c : ι → ℂ), T k (c - Pi.single i (m : ℂ)) =
      ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℂ) *
        T (k + p.1) (c - Pi.single (j : ι) (p.2 : ℂ)) by
    simpa [T] using H m 0 b
  intro m
  induction m with
  | zero => intro k c; simp
  | succ m ih =>
    intro k c
    have hc : c - Pi.single i ((m + 1 : ℕ) : ℂ) = (c - Pi.single i (m : ℂ)) - Pi.single i 1 := by
      rw [hsingle]; push_cast; rfl
    have hP := Finset.sum_antidiagonal_choose_succ_mul (R := ℂ)
      (fun a l : ℕ => T (k + a) (c - Pi.single (j : ι) (l : ℂ))) m
    rw [hc, hstep, ih, sub_right_comm c (Pi.single i _) (Pi.single (j : ι) 1), ih, hP, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [hsingle]; push_cast; ring_nf
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [Nat.choose_symm_of_eq_add hp.symm, add_assoc, add_comm 1 p.1]

open scoped Classical in
/-- **The face formula at `bᵢ = -m`.** If the `i`-th parameter is a nonpositive integer `-m`,
the entire transform of a smooth kernel is a binomial combination of face transforms: for any
`j ≠ i`, of the restrictions to the face `uᵢ = 0` of the tangential derivatives `∂ⱼᵢᵃ g`, with
the `j`-th parameter lowered by `m - a`. For `m = 0` this is the face formula at a zero
parameter. -/
theorem regDirichletTransform_eq_sum_face {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (i : ι) (j : {j : ι // j ≠ i}) (m : ℕ) {b : ι → ℂ} (hb : b i = -m) :
    regDirichletTransform g hg b =
      ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℂ) *
        regDirichletTransform
          (stdSimplexFaceRestriction i ((stdSimplexTangentDeriv (j : ι) i)^[p.1] g))
          ((hg.iterate_tangentDeriv j i p.1).faceRestriction i)
          (fun q => b q - (Pi.single j (p.2 : ℂ) : {j : ι // j ≠ i} → ℂ) q) := by
  have : Nontrivial ι := ⟨⟨j, i, j.2⟩⟩
  have hb' : b = (b + Pi.single i (m : ℂ)) - Pi.single i (m : ℂ) := by simp
  rw [hb', regDirichletTransform_sub_single_eq_sum hg i j m]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hgk := hg.iterate_tangentDeriv j i p.1
  rw [(isRegDirichletContinuation_transform hgk).face_zero i
    (isRegDirichletContinuation_transform (hgk.faceRestriction i)) hgk.continuousOn]
  · congr 1
    funext q
    have hq : (q : ι) ≠ i := q.2
    by_cases hqj : q = j
    · subst hqj; simp [hq]
    · have : (q : ι) ≠ j := fun h => hqj (Subtype.ext h)
      simp [hq, this, Pi.single_eq_of_ne hqj]
  · simp [Pi.single_eq_of_ne' j.2, hb]

end Dirichlet

end
