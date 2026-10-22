/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Weights
public import Carlson.Mean.Properties
public import ToMathlib.Analysis.Calculus.HomogeneousMeanAsymptotic
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Large translates of hypergeometric means

The real positive mean is smooth at every real order, including order zero.
Its real derivative weights are the normalized parameters, so the general
Brenner–Carlson (1987) Hoehn–Niven theorem applies without exceptional orders.
-/

open Complex Dirichlet ProbabilityTheory Filter Set Asymptotics
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The real hypergeometric mean is smooth in its positive nodes at every real order. -/
theorem contDiffAt_carlsonMeanReal_nodes (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (carlsonMeanReal t b) x := by
  let B := fun i => (b i : ℂ)
  let X := fun i => (x i : ℂ)
  have ha : AnalyticAt ℂ (carlsonMean t B) X := by
    apply analyticAt_carlsonMean_comp t analyticAt_const analyticAt_id
      (fun i => ofReal_mem_slitPlane.mpr (hx i)) (sum_ofReal_parameters_ne_neg_nat hb)
    intro _
    change carlsonR (t : ℂ) (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) ∈ slitPlane
    rw [← ofReal_carlsonRReal t hb hx]
    exact ofReal_mem_slitPlane.mpr (carlsonRReal_pos t hb hx)
  have hmap : ContDiffAt ℝ n (fun y : ι → ℝ => fun i => (y i : ℂ)) x := by
    apply contDiffAt_pi.mpr
    intro i
    exact ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_apply ℝ (fun _ : ι => ℝ) i x)
  have hcomp := (ha.contDiffAt.restrict_scalars ℝ).comp x hmap
  have hr := reCLM.contDiff.contDiffAt.comp x hcomp
  apply hr.congr_of_eventuallyEq
  have hpos : ∀ᶠ y : ι → ℝ in 𝓝 x, ∀ i, 0 < y i := by
    apply eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (lt_mem_nhds (hx i))
  filter_upwards [hpos] with y hy
  simpa only [B, Function.comp_def, ContinuousLinearMap.coe_coe,
    Complex.reCLM_apply, Complex.ofReal_re] using
    (congrArg Complex.re (ofReal_carlsonMeanReal t hb hy))

variable [DecidableEq ι]

/-- The real derivative-defined hypergeometric weights are the normalized parameters. -/
theorem meanWeight_carlsonMeanReal (t : ℝ) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (i : ι) :
    Function.meanWeight ℝ (carlsonMeanReal t b) i = b i / ∑ j, b j := by
  have hc := sum_ofReal_parameters_ne_neg_nat hb
  have hd := (hasDerivAt_carlsonMean_update_one t hc i).real_of_complex
  have hcoef : (((b i : ℂ) / ∑ j, (b j : ℂ))).re = b i / ∑ j, b j := by
    rw [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hcoef] at hd
  have hreal : HasDerivAt (fun w => carlsonMeanReal t b (Function.update 1 i w))
      (b i / ∑ j, b j) 1 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with w hw
    have hu : ∀ j, 0 < Function.update (1 : ι → ℝ) i w j := by
      intro j
      by_cases hji : j = i <;> simp [hji, hw]
    calc
      carlsonMeanReal t b (Function.update 1 i w) =
          (carlsonMean t (fun j => (b j : ℂ))
            (fun j => (Function.update (1 : ι → ℝ) i w j : ℂ))).re := by
        simpa only [Complex.ofReal_re] using
          congrArg Complex.re (ofReal_carlsonMeanReal t hb hu)
      _ = _ := by
        apply congrArg (fun z : ι → ℂ => (carlsonMean t (fun j => (b j : ℂ)) z).re)
        ext j
        by_cases hji : j = i <;> simp [hji]
  exact (SeveralComplexVariables.hasDerivAt_update_of_differentiableAt
    ((contDiffAt_carlsonMeanReal_nodes t hb (fun _ => zero_lt_one) 2).differentiableAt
      (by norm_num)) i).unique hreal

/-- **Brenner–Carlson Theorem 1**, for every real-order hypergeometric mean. -/
theorem isBigO_carlsonMeanReal_translate (t : ℝ) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (a : ι → ℝ) :
    (fun x : ℝ => carlsonMeanReal t b (fun i => x + a i) - x -
      ∑ i, (b i / ∑ j, b j) * a i) =O[atTop] (fun x : ℝ => x⁻¹) := by
  have h := Function.isBigO_homogeneous_mean_translate
    (contDiffAt_carlsonMeanReal_nodes t hb (fun _ => zero_lt_one) 2)
    (carlsonMeanReal_const t zero_lt_one hb)
    (fun r hr z hz => carlsonMeanReal_mul t hb hz hr) a
  simpa only [meanWeight_carlsonMeanReal t hb] using h

end Carlson
