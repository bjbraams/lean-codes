/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Integral
public import Carlson.S

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Confluence of Carlson's R-function to the S-function

This file formalizes the confluence limit of [Carl77, Section 5.10].  Natural exponents are
used first: this is the branch-independent form of Carlson's limit and is directly supported by
Mathlib's theorem `Complex.tendsto_one_add_div_pow_exp`. The exponent then tends to infinity in
the complex plane, with principal powers, as in Carlson's statement; the variables may also be
perturbed, `1 + ζ(t)/t` with `ζ(t) → z` (Carlson (5.10-9)). The proof bounds
`t log(1 + y/t) - y` by the logarithm estimate and applies dominated convergence along the
cobounded filter.


## Main results

* `Carlson.carlsonAffineForm_confluentVariables`: Carlson's affine form turns confluent
  variables into the corresponding scalar confluent variable.
* `Carlson.tendsto_carlsonAffineForm_confluentVariables_pow`: Pointwise confluence of the
  natural-power Carlson kernel to the exponential kernel.
* `Carlson.norm_carlsonAffineForm_confluentVariables_pow_le`: A uniform bound for the
  natural-power kernels occurring in Carlson's confluence limit.
* `Carlson.tendsto_regCarlsonRIntegral_confluent`: Carlson's confluence theorem 5.10-1 for the
  native regularized integrals: natural-power `R` functions with variables coalescing at `1`
  converge to the `S` function.
* `Carlson.tendsto_carlsonRIntegral_confluent`: Carlson's confluence theorem 5.10-1 for the
  native unregularized integrals.
* `Carlson.tendsto_one_add_div_cpow_cobounded`: `(1 + y(t)/t)^t → e^Y` as `t → ∞` in `ℂ`
  (5.10-1), (5.10-8).
* `Carlson.tendsto_regCarlsonRIntegral_confluent_cobounded`,
  `Carlson.tendsto_carlsonRIntegral_confluent_cobounded`: Theorem 5.10-1 with complex exponent,
  with the refinement (5.10-9).

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.10,
  Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Bornology
open scoped Topology
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The Carlson variables which coalesce at `1` in the confluence limit `R → S`. -/
def carlsonConfluentVariables (n : ℕ) (z : ι → ℂ) : ι → ℂ :=
  fun i ↦ 1 + z i / n

/-- Carlson's affine form turns confluent variables into the corresponding scalar confluent
variable. -/
theorem carlsonAffineForm_confluentVariables {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (n : ℕ) (z : ι → ℂ) :
    carlsonAffineForm (carlsonConfluentVariables n z) u =
      1 + carlsonAffineForm z u / n := by
  simp only [carlsonAffineForm, carlsonConfluentVariables, mul_add, Finset.sum_add_distrib]
  rw [show ∑ i, (u i : ℂ) * 1 = 1 by simpa using congrArg Complex.ofReal hu.2]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pointwise confluence of the natural-power Carlson kernel to the exponential kernel. -/
theorem tendsto_carlsonAffineForm_confluentVariables_pow (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    Tendsto (fun n : ℕ ↦ carlsonAffineForm (carlsonConfluentVariables n z) u ^ n)
      atTop (𝓝 (exp (carlsonAffineForm z u))) := by
  apply (Complex.tendsto_one_add_div_pow_exp (carlsonAffineForm z u)).congr'
  filter_upwards with n
  rw [carlsonAffineForm_confluentVariables hu]

/-- A uniform bound for the natural-power kernels occurring in Carlson's confluence limit. -/
theorem norm_carlsonAffineForm_confluentVariables_pow_le (n : ℕ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖carlsonAffineForm (carlsonConfluentVariables n z) u ^ n‖ ≤
      Real.exp (∑ i, ‖z i‖) := by
  let C : ℝ := ∑ i, ‖z i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [carlsonAffineForm_confluentVariables hu, norm_pow]
  calc
    ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ^ n ≤
        (1 + C / n) ^ n := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ≤
            1 + ‖carlsonAffineForm z u‖ / n := by
          calc
            ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ≤
                ‖(1 : ℂ)‖ + ‖carlsonAffineForm z u / (n : ℂ)‖ := norm_add_le _ _
            _ = 1 + ‖carlsonAffineForm z u‖ / n := by simp
        _ ≤ 1 + C / n := by
          gcongr
          exact norm_carlsonAffineForm_le_sum_norm z hu
    _ ≤ Real.exp C := by
      by_cases hn : n = 0
      · subst n
        simp [hC]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        calc
          (1 + C / n) ^ n ≤ (Real.exp (C / n)) ^ n := by
            gcongr
            simpa [add_comm] using Real.add_one_le_exp (C / n)
          _ = Real.exp C := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp

/-- Carlson's confluence theorem 5.10-1 for the native regularized integrals: natural-power
`R` functions with variables coalescing at `1` converge to the `S` function. -/
theorem tendsto_regCarlsonRIntegral_confluent (b z : ι → ℂ)
    (hb : b ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ regCarlsonRIntegral (n : ℂ) b
        (carlsonConfluentVariables n z)) atTop
      (𝓝 (regCarlsonSIntegral b z)) := by
  let μ := (stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let C : ℝ := Real.exp (∑ i, ‖z i‖)
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * carlsonAffineForm (carlsonConfluentVariables n z) u ^ n
  let f : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * exp (carlsonAffineForm z u)
  have hdens : IntegrableOn (fun u ↦ regDirichletDensity b u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure :=
    integrableOn_regDirichletDensity b hb
  have hbound : Integrable (fun u ↦ C * ‖regDirichletDensity b u‖) μ :=
    hdens.norm.const_mul C
  have hmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (integrableOn_regDirichletDensity_mul b hb
      ((continuous_carlsonAffineForm (carlsonConfluentVariables n z)).continuousOn.pow n)).1
  have hdom : ∀ n, ∀ᵐ u ∂μ, ‖F n u‖ ≤ C * ‖regDirichletDensity b u‖ := by
    intro n
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (norm_carlsonAffineForm_confluentVariables_pow_le n z hu) (norm_nonneg _)
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun n ↦ F n u) atTop (𝓝 (f u)) := by
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact tendsto_const_nhds.mul (tendsto_carlsonAffineForm_confluentVariables_pow z hu)
  have h := tendsto_integral_of_dominated_convergence
    (fun u ↦ C * ‖regDirichletDensity b u‖) hmeas hbound hdom hlim
  simpa [F, f, μ, regCarlsonRIntegral, regCarlsonSIntegral,
    regCarlsonDirichletAverage, regDirichletIntegral, cpow_natCast] using h

/-- Carlson's confluence theorem 5.10-1 for the native unregularized integrals. -/
theorem tendsto_carlsonRIntegral_confluent (b z : ι → ℂ)
    (hb : b ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ carlsonRIntegral (n : ℂ) b
        (carlsonConfluentVariables n z)) atTop
      (𝓝 (carlsonSIntegral b z)) := by
  simpa [carlsonRIntegral, carlsonSIntegral] using
    tendsto_const_nhds.mul (tendsto_regCarlsonRIntegral_confluent b z hb)

/-- The bound `‖(1 + y/t)^t‖ ≤ e^{2‖y‖}` for `2‖y‖ ≤ ‖t‖`, `t ≠ 0` (Carlson (5.10-6)). -/
theorem norm_one_add_div_cpow_le {y t : ℂ} (ht : t ≠ 0) (h : 2 * ‖y‖ ≤ ‖t‖) :
    ‖(1 + y / t) ^ t‖ ≤ Real.exp (2 * ‖y‖) := by
  have hw : ‖y / t‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr ht)]; linarith
  have h1 : (1 + y / t) ≠ 0 := by
    intro h0
    have : ‖y / t‖ = 1 := by rw [show y / t = -1 by linear_combination h0]; simp
    linarith
  rw [cpow_def_of_ne_zero h1, norm_exp]
  refine Real.exp_le_exp.mpr ((re_le_norm _).trans ?_)
  rw [norm_mul]
  have hl := norm_log_one_add_half_le_self hw
  calc ‖log (1 + y / t)‖ * ‖t‖ ≤ 3 / 2 * ‖y / t‖ * ‖t‖ :=
        mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    _ = 3 / 2 * ‖y‖ := by
        rw [norm_div]; field_simp [norm_ne_zero_iff.mpr ht]
    _ ≤ 2 * ‖y‖ := by linarith [norm_nonneg y]

/-- **The confluence of the power to the exponential** (Carlson (5.10-1), (5.10-8)):
`(1 + y(t)/t)^t → e^Y` as `t → ∞` in `ℂ`, whenever `y(t) → Y`. -/
theorem tendsto_one_add_div_cpow_cobounded {y : ℂ → ℂ} {Y : ℂ}
    (hy : Tendsto y (cobounded ℂ) (𝓝 Y)) :
    Tendsto (fun t => (1 + y t / t) ^ t) (cobounded ℂ) (𝓝 (exp Y)) := by
  have hinv := tendsto_inv₀_cobounded (α := ℂ)
  have hw : Tendsto (fun t => y t / t) (cobounded ℂ) (𝓝 0) := by
    simpa [div_eq_mul_inv] using hy.mul hinv
  have hsmall : ∀ᶠ t in cobounded ℂ, ‖y t / t‖ < 1 / 2 ∧ t ≠ 0 := by
    have h1 := hw.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 / 2 by norm_num))
    have h2 : ∀ᶠ t : ℂ in cobounded ℂ, t ≠ 0 := by
      simpa using (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0
    filter_upwards [h1, h2] with t a b using ⟨a, b⟩
  -- the exponent tends to `Y`
  have hE : Tendsto (fun t => log (1 + y t / t) * t) (cobounded ℂ) (𝓝 Y) := by
    have hrem : Tendsto (fun t => (log (1 + y t / t) - y t / t) * t) (cobounded ℂ) (𝓝 0) := by
      have hbd : Tendsto (fun t => ‖y t‖ ^ 2 * ‖t⁻¹‖) (cobounded ℂ) (𝓝 0) := by
        simpa using (hy.norm.pow 2).mul hinv.norm
      refine squeeze_zero_norm' ?_ hbd
      filter_upwards [hsmall] with t ⟨ht, ht0⟩
      have hl := norm_log_one_add_sub_self_le (show ‖y t / t‖ < 1 by linarith)
      have hq : (1 - ‖y t / t‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]; linarith
      rw [norm_mul]
      calc ‖log (1 + y t / t) - y t / t‖ * ‖t‖
          ≤ ‖y t / t‖ ^ 2 * (1 - ‖y t / t‖)⁻¹ / 2 * ‖t‖ :=
            mul_le_mul_of_nonneg_right hl (norm_nonneg _)
        _ ≤ ‖y t / t‖ ^ 2 * 2 / 2 * ‖t‖ := by gcongr
        _ = ‖y t‖ ^ 2 * ‖t⁻¹‖ := by
            rw [norm_div, norm_inv]; field_simp [norm_ne_zero_iff.mpr ht0]
    have := hy.add hrem
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hsmall] with t ⟨_, ht0⟩
    field_simp
    ring
  refine ((continuous_exp.tendsto Y).comp hE).congr' ?_
  filter_upwards [hsmall] with t ⟨ht, ht0⟩
  have h1 : (1 + y t / t) ≠ 0 := by
    intro h0
    have : ‖y t / t‖ = 1 := by rw [show y t / t = -1 by linear_combination h0]; simp
    linarith
  simp only [Function.comp_apply]
  rw [cpow_def_of_ne_zero h1]

/-- **Theorem 5.10-1** with complex exponent, and its refinement (5.10-9): for convergent
parameters, `R_t(b, 1 + ζ(t)/t) → S(b, z)` as `t → ∞` in `ℂ`, whenever `ζ(t) → z`
(regularized native integrals). -/
theorem tendsto_regCarlsonRIntegral_confluent_cobounded (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {ζ : ℂ → ι → ℂ} {z : ι → ℂ} (hζ : Tendsto ζ (cobounded ℂ) (𝓝 z)) :
    Tendsto (fun t : ℂ => regCarlsonRIntegral t b (fun i => 1 + ζ t i / t)) (cobounded ℂ)
      (𝓝 (regCarlsonSIntegral b z)) := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := (stdSimplexMeasure (ι := ι)).restrict K
  set M : ℝ := ∑ i, ‖z i‖ + 1
  have hdens : IntegrableOn (fun u ↦ regDirichletDensity b u) K stdSimplexMeasure :=
    integrableOn_regDirichletDensity b hb
  have hbound : Integrable (fun u ↦ Real.exp (2 * M) * ‖regDirichletDensity b u‖) μ :=
    hdens.norm.const_mul _
  -- eventually the nodes are bounded
  have hζM : ∀ᶠ t in cobounded ℂ, ∑ i, ‖ζ t i‖ ≤ M := by
    have hc : Tendsto (fun t => ∑ i, ‖ζ t i‖) (cobounded ℂ) (𝓝 (∑ i, ‖z i‖)) :=
      tendsto_finsetSum _ fun i _ => ((continuous_apply i).tendsto z |>.comp hζ).norm
    exact hc.eventually (ge_mem_nhds (by simp [M]))
  have hbig : ∀ᶠ t : ℂ in cobounded ℂ, 2 * M ≤ ‖t‖ ∧ t ≠ 0 := by
    have h1 := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_ge_atTop (2 * M)
    have h2 : ∀ᶠ t : ℂ in cobounded ℂ, t ≠ 0 := by
      simpa using (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0
    filter_upwards [h1, h2] with t a b using ⟨a, b⟩
  have haff : ∀ t : ℂ, ∀ u ∈ K,
      carlsonAffineForm (fun i => 1 + ζ t i / t) u = 1 + carlsonAffineForm (ζ t) u / t := by
    intro t u hu
    simp only [carlsonAffineForm, mul_add, Finset.sum_add_distrib]
    rw [show ∑ i, (u i : ℂ) * 1 = 1 by simpa using congrArg Complex.ofReal hu.2]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  let F : ℂ → (ι → ℝ) → ℂ := fun t u ↦
    regDirichletDensity b u * carlsonAffineForm (fun i => 1 + ζ t i / t) u ^ t
  let f : (ι → ℝ) → ℂ := fun u ↦ regDirichletDensity b u * exp (carlsonAffineForm z u)
  have hmeas : ∀ᶠ t in cobounded ℂ, AEStronglyMeasurable (F t) μ := by
    filter_upwards [hbig, hζM] with t ⟨ht, ht0⟩ hM
    refine (integrableOn_regDirichletDensity_mul b hb ?_).1
    refine ContinuousOn.cpow_const ((continuous_carlsonAffineForm _).continuousOn) fun u hu => ?_
    rw [haff t u hu]
    left
    have hn : ‖carlsonAffineForm (ζ t) u / t‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr ht0)]
      have := norm_carlsonAffineForm_le_sum_norm (ζ t) hu
      nlinarith
    have := re_le_norm (-(carlsonAffineForm (ζ t) u / t))
    simp only [norm_neg] at this
    simp only [add_re, one_re]
    have h2 := neg_re (carlsonAffineForm (ζ t) u / t)
    linarith
  have hdom : ∀ᶠ t in cobounded ℂ, ∀ᵐ u ∂μ, ‖F t u‖ ≤ Real.exp (2 * M) * ‖regDirichletDensity b u‖ := by
    filter_upwards [hbig, hζM] with t ⟨ht, ht0⟩ hM
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, norm_mul]
    rw [mul_comm, haff t u hu]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hy : ‖carlsonAffineForm (ζ t) u‖ ≤ M :=
      (norm_carlsonAffineForm_le_sum_norm (ζ t) hu).trans hM
    refine (norm_one_add_div_cpow_le ht0 (by linarith)).trans ?_
    exact Real.exp_le_exp.mpr (by linarith)
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun t ↦ F t u) (cobounded ℂ) (𝓝 (f u)) := by
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    refine tendsto_const_nhds.mul ?_
    have hy : Tendsto (fun t => carlsonAffineForm (ζ t) u) (cobounded ℂ)
        (𝓝 (carlsonAffineForm z u)) := by
      have := ((carlsonAffineFormCLM u).continuous.tendsto z).comp hζ
      simpa [Function.comp_def, carlsonAffineFormCLM_apply] using this
    refine (tendsto_one_add_div_cpow_cobounded hy).congr' (Eventually.of_forall fun t => ?_)
    simp only [haff t u hu]
  have : (cobounded ℂ).IsCountablyGenerated := by
    rw [← comap_norm_atTop]; infer_instance
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ Real.exp (2 * M) * ‖regDirichletDensity b u‖) hmeas hdom hbound hlim
  simpa [F, f, μ, K, regCarlsonRIntegral, regCarlsonSIntegral,
    regCarlsonDirichletAverage, regDirichletIntegral] using h

/-- **Theorem 5.10-1** with complex exponent for the native unregularized integrals:
`R_t(b, 1 + ζ(t)/t) → S(b, z)` as `t → ∞` in `ℂ`, whenever `ζ(t) → z`. -/
theorem tendsto_carlsonRIntegral_confluent_cobounded (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {ζ : ℂ → ι → ℂ} {z : ι → ℂ} (hζ : Tendsto ζ (cobounded ℂ) (𝓝 z)) :
    Tendsto (fun t : ℂ => carlsonRIntegral t b (fun i => 1 + ζ t i / t)) (cobounded ℂ)
      (𝓝 (carlsonSIntegral b z)) := by
  simpa [carlsonRIntegral, carlsonSIntegral] using
    tendsto_const_nhds.mul (tendsto_regCarlsonRIntegral_confluent_cobounded b hb hζ)

end Carlson
end CarlsonR
