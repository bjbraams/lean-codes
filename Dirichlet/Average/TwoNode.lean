/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Chart
public import Dirichlet.Average.IntegralDomain
public import Dirichlet.Transform.Euler
public import ToMathlib.Analysis.Integral.EndpointDeformation
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Two-node Dirichlet averages on simply connected domains

Let `g` be holomorphic on a simply connected open set `D`, possibly depending holomorphically on
auxiliary parameters. The regularized two-node Dirichlet average of `g` with nodes `x, y` is
defined natively when the segment joining `x` and `y` lies in `D`. We construct a continuation
that is entire in the two Dirichlet parameters and holomorphic in both nodes throughout `D` and
in the auxiliary parameters.

The construction pulls the average back by a convex chart `φ : V → D` (the Riemann mapping
theorem of the Tau Ceti contributors). With `ξ = ψ x`, `η = ψ y` and `s = t ξ + (1 - t) η`, the
substitution `w = φ s` turns the average into the regularized Euler integral, over the straight
segment from `η` to `ξ` in `V`, of the kernel

`g (φ s) φ'(s) Q(s, η)^(b₀ - 1) Q(ξ, s)^(b₁ - 1) Q(ξ, η)^(1 - b₀ - b₁)`,

where `Q` is the difference quotient of `φ` and the powers use a holomorphic logarithm of `Q`
on `V × V`. The kernel is holomorphic in all variables, so the joint Euler continuation applies.

Agreement with the native average near a diagonal point is the statement that the Euler
integral over the straight segment from `y` to `x` equals the integral over its curved
deformation through `φ`; it is proved with a primitive on a convex strip and explicit endpoint
estimates (`Complex.intervalIntegral_mul_comp_eq_of_endpoint`). The identity theorem on the
connected open set of node pairs whose segment lies in `D` then gives agreement everywhere.

## Main definitions

* `Dirichlet.IsConvexChart`: a holomorphic chart from a convex open set with holomorphic
  inverse.
* `Dirichlet.twoNodeKernel`: the pulled-back kernel.

## Main results

* `Dirichlet.regEulerIntegral_twoNodeKernel_eventually_eq`: agreement near the diagonal.
* `Dirichlet.exists_twoNode_continuation_of_chart`: the parametric two-node continuation on the
  target of a given convex chart.
* `Dirichlet.exists_twoNode_continuation`: the parametric two-node continuation.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, Theorem 8.
-/

open Complex Set Filter Function MeasureTheory intervalIntegral
open scoped Topology Real

@[expose] public noncomputable section

namespace Dirichlet

/-- A holomorphic chart of `D` from a convex open set `V`, with holomorphic inverse `ψ`. -/
structure IsConvexChart (D V : Set ℂ) (φ ψ : ℂ → ℂ) : Prop where
  isOpen_source : IsOpen V
  convex_source : Convex ℝ V
  nonempty_source : V.Nonempty
  isOpen_target : IsOpen D
  analyticOnNhd : AnalyticOnNhd ℂ φ V
  analyticOnNhd_inv : AnalyticOnNhd ℂ ψ D
  mapsTo : MapsTo φ V D
  mapsTo_inv : MapsTo ψ D V
  left_inv : ∀ s ∈ V, ψ (φ s) = s
  right_inv : ∀ w ∈ D, φ (ψ w) = w

namespace IsConvexChart

variable {D V : Set ℂ} {φ ψ : ℂ → ℂ}

/-- A simply connected open set has a convex chart. -/
theorem exists_of_isSimplyConnected (hDo : IsOpen D) (hDs : IsSimplyConnected D) :
    ∃ (V : Set ℂ) (φ ψ : ℂ → ℂ), IsConvexChart D V φ ψ := by
  obtain ⟨V, φ, ψ, hVo, hVc, hVn, hφ, hψ, hm, hm', hl, hr⟩ := exists_convex_chart hDo hDs
  exact ⟨V, φ, ψ, ⟨hVo, hVc, hVn, hDo, hφ, hψ, hm, hm', hl, hr⟩⟩

/-- A chart is injective on its source. -/
theorem injOn (hC : IsConvexChart D V φ ψ) : InjOn φ V := by
  intro s hs t ht hst
  rw [← hC.left_inv s hs, ← hC.left_inv t ht, hst]

/-- The inverse of a chart is injective on the target. -/
theorem injOn_inv (hC : IsConvexChart D V φ ψ) : InjOn ψ D := by
  intro x hx y hy hxy
  rw [← hC.right_inv x hx, ← hC.right_inv y hy, hxy]

/-- A chart has nonvanishing derivative. -/
theorem deriv_ne_zero (hC : IsConvexChart D V φ ψ) {s : ℂ} (hs : s ∈ V) : deriv φ s ≠ 0 :=
  deriv_ne_zero_of_leftInv hC.isOpen_source hC.analyticOnNhd hC.analyticOnNhd_inv hC.mapsTo
    hC.left_inv hs

/-- A chart has a logarithm of its difference quotient. -/
theorem exists_log (hC : IsConvexChart D V φ ψ) :
    ∃ L : (Fin 2 → ℂ) → ℂ, AnalyticOnNhd ℂ L (pairDomain V) ∧
      ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v :=
  exists_chartLog hC.isOpen_source hC.convex_source hC.nonempty_source hC.analyticOnNhd
    hC.injOn (fun _ hs => hC.deriv_ne_zero hs)

end IsConvexChart

/-- The point `t ξ + (1 - t) η` of the segment from `η = c 1` to `ξ = c 0`. -/
def chartPoint (c : Fin 2 → ℂ) (t : ℂ) : ℂ := t * c 0 + (1 - t) * c 1

/-- The pulled-back two-node kernel. With `s = t ξ + (1 - t) η` it is
`g (φ s) φ'(s) Q(s, η)^(b₀ - 1) Q(ξ, η)^(b₁ - 1) Q(ξ, η)^(1 - b₀ - b₁)`, the powers taken with the
logarithm `L` of the difference quotient. -/
def twoNodeKernel (φ : ℂ → ℂ) (L : (Fin 2 → ℂ) → ℂ) (g : ℂ → ℂ) (b c : Fin 2 → ℂ) (t : ℂ) :
    ℂ :=
  g (φ (chartPoint c t)) * deriv φ (chartPoint c t) *
    exp ((b 0 - 1) * L ![chartPoint c t, c 1] + (b 1 - 1) * L ![c 0, chartPoint c t] -
      (b 0 + b 1 - 1) * L ![c 0, c 1])

/-! ### Estimates for powers near an endpoint -/

/-- A power of a point in a sector near zero is bounded by the corresponding real power of the
radius. -/
theorem norm_cpow_le_of_re_ge (e : ℂ) {w : ℂ} {t : ℝ} (ht : 0 < t) (hre : t / 2 ≤ w.re)
    (hn : ‖w‖ ≤ 2 * t) :
    ‖w ^ e‖ ≤ 2 ^ |e.re| * Real.exp (π * |e.im|) * t ^ e.re := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hre; linarith
  have hnw : t / 2 ≤ ‖w‖ := hre.trans (re_le_norm w)
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [norm_cpow_of_ne_zero hw0]
  have harg : Real.exp (-(π * |e.im|)) ≤ Real.exp (arg w * e.im) := by
    apply Real.exp_le_exp.mpr
    have h1 : |arg w * e.im| ≤ π * |e.im| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_arg_le_pi w) (abs_nonneg _)
    linarith [neg_abs_le (arg w * e.im)]
  have hpow : ‖w‖ ^ e.re ≤ 2 ^ |e.re| * t ^ e.re := by
    rcases le_total 0 e.re with he | he
    · calc ‖w‖ ^ e.re ≤ (2 * t) ^ e.re := Real.rpow_le_rpow hpos.le hn he
        _ = 2 ^ e.re * t ^ e.re := Real.mul_rpow (by norm_num) ht.le
        _ = 2 ^ |e.re| * t ^ e.re := by rw [abs_of_nonneg he]
    · calc ‖w‖ ^ e.re ≤ (t / 2) ^ e.re := Real.rpow_le_rpow_of_nonpos (by positivity)
            hnw he
        _ = 2 ^ |e.re| * t ^ e.re := by
          rw [Real.div_rpow ht.le (by norm_num), abs_of_nonpos he, Real.rpow_neg (by norm_num),
            div_eq_mul_inv, mul_comm]
  calc ‖w‖ ^ e.re / Real.exp (arg w * e.im)
      ≤ ‖w‖ ^ e.re / Real.exp (-(π * |e.im|)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) harg
    _ = ‖w‖ ^ e.re * Real.exp (π * |e.im|) := by rw [Real.exp_neg, div_inv_eq_mul]
    _ ≤ 2 ^ |e.re| * t ^ e.re * Real.exp (π * |e.im|) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by ring

/-- The constant in the endpoint estimate for the Euler weight. -/
def eulerWeightConst (e e' : ℂ) : ℝ :=
  2 ^ |e.re| * Real.exp (π * |e.im|) * (2 ^ |e'.re| * Real.exp (π * |e'.im|))

/-- The Euler weight near the endpoint `0`. -/
theorem norm_cpow_mul_one_sub_cpow_le (e e' : ℂ) {w : ℂ} {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4)
    (hre : t / 2 ≤ w.re) (hn : ‖w‖ ≤ 2 * t) :
    ‖w ^ e * (1 - w) ^ e'‖ ≤ eulerWeightConst e e' * t ^ e.re := by
  have h1 : ‖(1 - w) ^ e'‖ ≤ 2 ^ |e'.re| * Real.exp (π * |e'.im|) * (1 : ℝ) ^ e'.re := by
    apply norm_cpow_le_of_re_ge e' one_pos
    · have := (abs_re_le_norm w).trans hn
      rw [sub_re, one_re]
      linarith [le_abs_self w.re]
    · calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 * 1 := by rw [norm_one]; linarith
  rw [Real.one_rpow, mul_one] at h1
  rw [norm_mul, eulerWeightConst]
  calc ‖w ^ e‖ * ‖(1 - w) ^ e'‖
      ≤ (2 ^ |e.re| * Real.exp (π * |e.im|) * t ^ e.re) *
          (2 ^ |e'.re| * Real.exp (π * |e'.im|)) :=
        mul_le_mul (norm_cpow_le_of_re_ge e ht hre hn) h1 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Points of the segment from `t` to `t r`, with `r` close to one, lie in the sector used for the
endpoint estimates. -/
theorem mem_sector_of_mem_segment {t : ℝ} (ht : 0 < t) {r w : ℂ} (hr : ‖r - 1‖ < 1 / 2)
    (hw : w ∈ segment ℝ (t : ℂ) (t * r)) : t / 2 ≤ w.re ∧ ‖w‖ ≤ 2 * t := by
  have hrre : 1 / 2 ≤ r.re := by
    have := (abs_re_le_norm (r - 1)).trans hr.le
    rw [sub_re, one_re] at this
    linarith [neg_abs_le (r.re - 1)]
  have hrn : ‖r‖ ≤ 3 / 2 := by
    calc ‖r‖ = ‖(r - 1) + 1‖ := by ring_nf
      _ ≤ ‖r - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [norm_one]; linarith
  constructor
  · have hc : Convex ℝ {w : ℂ | t / 2 ≤ w.re} := convex_halfSpace_re_ge _
    refine hc.segment_subset ?_ ?_ hw
    · simp only [mem_ofPred_eq, ofReal_re]; linarith
    · simp only [mem_ofPred_eq, re_ofReal_mul]; nlinarith
  · have hc : Convex ℝ (Metric.closedBall (0 : ℂ) (2 * t)) := convex_closedBall _ _
    have := hc.segment_subset ?_ ?_ hw
    · simpa using this
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs,
        abs_of_pos ht]
      linarith
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos ht]
      nlinarith

/-! ### The deformed path -/

/-- The ratio `Q(s, η) / Q(ξ, η)` along the chart segment, with `c = ![ξ, η]`. -/
def chartRatio (φ : ℂ → ℂ) (c : Fin 2 → ℂ) (t : ℂ) : ℂ :=
  chartQuot φ ![chartPoint c t, c 1] / chartQuot φ c

/-- The ratio `Q(ξ, s) / Q(ξ, η)` along the chart segment, with `c = ![ξ, η]`. -/
def chartRatio' (φ : ℂ → ℂ) (c : Fin 2 → ℂ) (t : ℂ) : ℂ :=
  chartQuot φ ![c 0, chartPoint c t] / chartQuot φ c

/-- The image `φ s` of the chart segment, in the affine coordinate of the segment from `y` to
`x`. -/
def chartCurve (φ : ℂ → ℂ) (c : Fin 2 → ℂ) (x y : ℂ) (t : ℂ) : ℂ :=
  (φ (chartPoint c t) - y) / (x - y)

/-- The chart segment starts at `η = c 1`. -/
@[simp] theorem chartPoint_zero (c : Fin 2 → ℂ) : chartPoint c 0 = c 1 := by
  simp [chartPoint]

/-- The chart segment ends at `ξ = c 0`. -/
@[simp] theorem chartPoint_one (c : Fin 2 → ℂ) : chartPoint c 1 = c 0 := by
  simp [chartPoint]

/-- The chart segment from `η` to `ξ` is affine in the parameter. -/
theorem hasDerivAt_chartPoint (c : Fin 2 → ℂ) (t : ℂ) :
    HasDerivAt (chartPoint c) (c 0 - c 1) t := by
  have h := ((hasDerivAt_id t).mul_const (c 0)).add
    (((hasDerivAt_const t (1 : ℂ)).sub (hasDerivAt_id t)).mul_const (c 1))
  convert h using 1
  · funext τ; simp [chartPoint]
  · simp; ring

/-- The deformed path is the parameter times the first ratio. -/
theorem chartCurve_eq_mul (φ : ℂ → ℂ) {c : Fin 2 → ℂ} (hc : c 0 ≠ c 1)
    (hQ : chartQuot φ c ≠ 0) (t : ℂ) :
    chartCurve φ c (φ (c 0)) (φ (c 1)) t = t * chartRatio φ c t := by
  have h1 := sub_mul_chartQuot φ ![chartPoint c t, c 1]
  have h0 := sub_mul_chartQuot φ c
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
  have hs : chartPoint c t - c 1 = t * (c 0 - c 1) := by simp [chartPoint]; ring
  have hd : φ (c 0) - φ (c 1) ≠ 0 := by
    rw [← h0]; exact mul_ne_zero (sub_ne_zero.mpr hc) hQ
  rw [chartCurve, chartRatio, ← h1, hs, ← h0]
  have hc' : c 0 - c 1 ≠ 0 := sub_ne_zero.mpr hc
  field_simp

/-- One minus the deformed path is one minus the parameter, times the second ratio. -/
theorem one_sub_chartCurve_eq_mul (φ : ℂ → ℂ) {c : Fin 2 → ℂ} (hc : c 0 ≠ c 1)
    (hQ : chartQuot φ c ≠ 0) (t : ℂ) :
    1 - chartCurve φ c (φ (c 0)) (φ (c 1)) t = (1 - t) * chartRatio' φ c t := by
  have h2 := sub_mul_chartQuot φ ![c 0, chartPoint c t]
  have h0 := sub_mul_chartQuot φ c
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h2
  have hs : c 0 - chartPoint c t = (1 - t) * (c 0 - c 1) := by simp [chartPoint]; ring
  have hd : φ (c 0) - φ (c 1) ≠ 0 := by
    rw [← h0]; exact mul_ne_zero (sub_ne_zero.mpr hc) hQ
  have hc' : c 0 - c 1 ≠ 0 := sub_ne_zero.mpr hc
  rw [chartCurve, chartRatio', one_sub_div hd]
  rw [show φ (c 0) - φ (c 1) - (φ (chartPoint c t) - φ (c 1)) =
    φ (c 0) - φ (chartPoint c t) by ring, ← h2, hs, ← h0]
  field_simp

/-- The deformed path has derivative `φ'(s) / Q(ξ, η)`. -/
theorem hasDerivAt_chartCurve {V : Set ℂ} {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V)
    {c : Fin 2 → ℂ} (hc : c 0 ≠ c 1) (hQ : chartQuot φ c ≠ 0) {t : ℂ}
    (ht : chartPoint c t ∈ V) :
    HasDerivAt (chartCurve φ c (φ (c 0)) (φ (c 1)))
      (deriv φ (chartPoint c t) / chartQuot φ c) t := by
  have h0 := sub_mul_chartQuot φ c
  have hd : φ (c 0) - φ (c 1) ≠ 0 := by
    rw [← h0]; exact mul_ne_zero (sub_ne_zero.mpr hc) hQ
  have h := (((hφ _ ht).differentiableAt.hasDerivAt.comp t (hasDerivAt_chartPoint c t)).sub_const
    (φ (c 1))).div_const (φ (c 0) - φ (c 1))
  have hc' : c 0 - c 1 ≠ 0 := sub_ne_zero.mpr hc
  convert h using 1
  · rfl
  · rw [← h0]
    field_simp

/-- **The pointwise substitution identity.** Along the chart segment, the Euler integrand of the
pulled-back kernel is the Euler integrand of `g` along the deformed path, times its derivative,
provided the logarithm `L` matches the principal logarithms of the two ratios. -/
theorem eulerIntegrand_twoNodeKernel_eq {V : Set ℂ} {φ : ℂ → ℂ}
    {L : (Fin 2 → ℂ) → ℂ} (hLexp : ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v)
    (g : ℂ → ℂ) (b₀ b₁ : ℂ) {c : Fin 2 → ℂ} (hcV : c ∈ pairDomain V) (hc : c 0 ≠ c 1)
    (hQ : chartQuot φ c ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < (chartRatio φ c t).re) (hr' : 0 < (chartRatio' φ c t).re)
    (hlog : log (chartRatio φ c t) = L ![chartPoint c t, c 1] - L c)
    (hlog' : log (chartRatio' φ c t) = L ![c 0, chartPoint c t] - L c) :
    (t : ℂ) ^ (b₀ - 1) * (1 - t : ℂ) ^ (b₁ - 1) *
        twoNodeKernel φ L g ![b₀, b₁] c t =
      chartCurve φ c (φ (c 0)) (φ (c 1)) t ^ (b₀ - 1) *
        (1 - chartCurve φ c (φ (c 0)) (φ (c 1)) t) ^ (b₁ - 1) *
          g (φ (c 1) + chartCurve φ c (φ (c 0)) (φ (c 1)) t * (φ (c 0) - φ (c 1))) *
        (deriv φ (chartPoint c t) / chartQuot φ c) := by
  have h0 := sub_mul_chartQuot φ c
  have hd : φ (c 0) - φ (c 1) ≠ 0 := by
    rw [← h0]; exact mul_ne_zero (sub_ne_zero.mpr hc) hQ
  have hpt : φ (c 1) + chartCurve φ c (φ (c 0)) (φ (c 1)) t * (φ (c 0) - φ (c 1)) =
      φ (chartPoint c t) := by
    rw [chartCurve]; field_simp; ring
  have hr0 : chartRatio φ c t ≠ 0 := fun h => by simp [h] at hr
  have hr0' : chartRatio' φ c t ≠ 0 := fun h => by simp [h] at hr'
  have hc_eq : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
  have hQexp : chartQuot φ c = exp (L c) := (hLexp c hcV).symm
  rw [hpt, one_sub_chartCurve_eq_mul φ hc hQ, chartCurve_eq_mul φ hc hQ,
    TauCeti.ofReal_mul_cpow ht.1.le, show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    TauCeti.ofReal_mul_cpow (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t),
    cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hr0', hlog, hlog', hQexp]
  rw [twoNodeKernel]
  conv_rhs => rw [div_eq_mul_inv, ← exp_neg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← hc_eq]
  push_cast
  have key : exp ((b₀ - 1) * L ![chartPoint c t, c 1] + (b₁ - 1) * L ![c 0, chartPoint c t] -
      (b₀ + b₁ - 1) * L c) =
      exp ((L ![chartPoint c t, c 1] - L c) * (b₀ - 1)) *
        exp ((L ![c 0, chartPoint c t] - L c) * (b₁ - 1)) * exp (-L c) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [key]
  ring

/-- Points of the chart segment lie in the convex chart source. -/
theorem chartPoint_mem {V : Set ℂ} (hVc : Convex ℝ V) {c : Fin 2 → ℂ} (hc : c ∈ pairDomain V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chartPoint c t ∈ V := by
  have h := hVc hc.1 hc.2 ht.1 (sub_nonneg.mpr ht.2) (by ring)
  simpa [chartPoint, real_smul] using h

/-- The chart segment varies continuously with its parameter. -/
theorem continuous_chartPoint (c : Fin 2 → ℂ) :
    Continuous (fun t : ℝ => chartPoint c t) := by
  unfold chartPoint; fun_prop

/-- **Matching of logarithm branches**, first ratio. If the ratio `Q(s, η) / Q(ξ, η)` has
positive real part along the whole segment, its principal logarithm is `L(s, η) - L(ξ, η)`:
both are continuous logarithms agreeing at `s = ξ`. -/
theorem log_chartRatio_eq {V : Set ℂ} (hVo : IsOpen V) (hVc : Convex ℝ V) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ V) {L : (Fin 2 → ℂ) → ℂ} (hL : AnalyticOnNhd ℂ L (pairDomain V))
    (hLexp : ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v) {c : Fin 2 → ℂ}
    (hcV : c ∈ pairDomain V) (hQ : chartQuot φ c ≠ 0)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (chartRatio φ c t).re) :
    ∀ t ∈ Icc (0 : ℝ) 1, log (chartRatio φ c t) = L ![chartPoint c t, c 1] - L c := by
  have hc_eq : ![c 0, c 1] = c := by funext i; fin_cases i <;> rfl
  have hpair : ∀ t ∈ Icc (0 : ℝ) 1, ![chartPoint c t, c 1] ∈ pairDomain V := fun t ht =>
    ⟨by simpa using chartPoint_mem hVc hcV ht, by simpa using hcV.2⟩
  have hcont : ContinuousOn (fun t : ℝ => ![chartPoint c t, c 1]) (Icc 0 1) := by
    refine Continuous.continuousOn (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using continuous_chartPoint c
    · simpa using continuous_const
  have hQc := (analyticOnNhd_chartQuot hVo hφ).continuousOn.comp hcont hpair
  have hLc := hL.continuousOn.comp hcont hpair
  have hrc : ContinuousOn (fun t : ℝ => chartRatio φ c t) (Icc 0 1) :=
    hQc.div_const _
  apply Complex.eqOn_logBranch_of_continuousOn isPreconnected_Icc
    (g := fun t : ℝ => chartRatio φ c t)
  · exact fun t ht => ContinuousAt.comp_continuousWithinAt (f := fun t : ℝ => chartRatio φ c t)
      (continuousAt_clog (mem_slitPlane_iff.mpr (Or.inl (hr t ht)))) (hrc t ht)
  · exact hLc.sub continuousOn_const
  · intro t ht
    simp only [Function.comp_apply]
    exact exp_log fun h => by simpa [h] using hr t ht
  · intro t ht
    simp only [Function.comp_apply, exp_sub, hLexp _ (hpair t ht), hLexp c hcV, chartRatio]
  · exact ⟨zero_le_one, le_rfl⟩
  · simp [chartRatio, hc_eq, div_self hQ]

/-- **Matching of logarithm branches**, second ratio, normalized at `s = η`. -/
theorem log_chartRatio'_eq {V : Set ℂ} (hVo : IsOpen V) (hVc : Convex ℝ V) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ V) {L : (Fin 2 → ℂ) → ℂ} (hL : AnalyticOnNhd ℂ L (pairDomain V))
    (hLexp : ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v) {c : Fin 2 → ℂ}
    (hcV : c ∈ pairDomain V) (hQ : chartQuot φ c ≠ 0)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (chartRatio' φ c t).re) :
    ∀ t ∈ Icc (0 : ℝ) 1, log (chartRatio' φ c t) = L ![c 0, chartPoint c t] - L c := by
  have hc_eq : ![c 0, c 1] = c := by funext i; fin_cases i <;> rfl
  have hpair : ∀ t ∈ Icc (0 : ℝ) 1, ![c 0, chartPoint c t] ∈ pairDomain V := fun t ht =>
    ⟨by simpa using hcV.1, by simpa using chartPoint_mem hVc hcV ht⟩
  have hcont : ContinuousOn (fun t : ℝ => ![c 0, chartPoint c t]) (Icc 0 1) := by
    refine Continuous.continuousOn (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using continuous_const
    · simpa using continuous_chartPoint c
  have hQc := (analyticOnNhd_chartQuot hVo hφ).continuousOn.comp hcont hpair
  have hLc := hL.continuousOn.comp hcont hpair
  have hrc : ContinuousOn (fun t : ℝ => chartRatio' φ c t) (Icc 0 1) :=
    hQc.div_const _
  apply Complex.eqOn_logBranch_of_continuousOn isPreconnected_Icc
    (g := fun t : ℝ => chartRatio' φ c t)
  · exact fun t ht => ContinuousAt.comp_continuousWithinAt (f := fun t : ℝ => chartRatio' φ c t)
      (continuousAt_clog (mem_slitPlane_iff.mpr (Or.inl (hr t ht)))) (hrc t ht)
  · exact hLc.sub continuousOn_const
  · intro t ht
    simp only [Function.comp_apply]
    exact exp_log fun h => by simpa [h] using hr t ht
  · intro t ht
    simp only [Function.comp_apply, exp_sub, hLexp _ (hpair t ht), hLexp c hcV, chartRatio']
  · exact ⟨le_rfl, zero_le_one⟩
  · simp [chartRatio', hc_eq, div_self hQ]

/-- The pulled-back kernel is holomorphic in the segment parameter. -/
theorem analyticAt_twoNodeKernel {D V : Set ℂ} {φ ψ : ℂ → ℂ} (hC : IsConvexChart D V φ ψ)
    {L : (Fin 2 → ℂ) → ℂ} (hL : AnalyticOnNhd ℂ L (pairDomain V)) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g D) (b : Fin 2 → ℂ) {c : Fin 2 → ℂ} (hcV : c ∈ pairDomain V)
    {t : ℂ} (ht : chartPoint c t ∈ V) : AnalyticAt ℂ (twoNodeKernel φ L g b c) t := by
  have hs : AnalyticAt ℂ (chartPoint c) t := by
    unfold chartPoint; fun_prop
  have hφs := (hC.analyticOnNhd _ ht).comp_of_eq hs rfl
  have hg' := (hg _ (hC.mapsTo ht)).comp_of_eq hφs rfl
  have hd := (hC.analyticOnNhd.deriv _ ht).comp_of_eq hs rfl
  have hp1 : AnalyticAt ℂ (fun τ => (![chartPoint c τ, c 1] : Fin 2 → ℂ)) t := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · simpa using hs
    · simpa using analyticAt_const
  have hp2 : AnalyticAt ℂ (fun τ => (![c 0, chartPoint c τ] : Fin 2 → ℂ)) t := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · simpa using analyticAt_const
    · simpa using hs
  have hL1 := (hL _ ⟨by simpa using ht, by simpa using hcV.2⟩).comp_of_eq hp1 rfl
  have hL2 := (hL _ ⟨by simpa using hcV.1, by simpa using ht⟩).comp_of_eq hp2 rfl
  unfold twoNodeKernel
  exact (hg'.mul hd).mul ((((analyticAt_const.mul hL1).add (analyticAt_const.mul hL2)).sub
    analyticAt_const).cexp)

/-- **Uniform control near a diagonal point.** For node pairs near `(x₀, x₀)`, along the whole
chart segment both ratios stay within `1/2` of one and `φ s` stays in a prescribed open
neighborhood of `x₀`. -/
theorem eventually_chart_near_diag {D V : Set ℂ} {φ ψ : ℂ → ℂ} (hC : IsConvexChart D V φ ψ)
    {x₀ : ℂ} (hx₀ : x₀ ∈ D) {B : Set ℂ} (hBo : IsOpen B) (hx₀B : x₀ ∈ B) :
    ∀ᶠ z in 𝓝 (![x₀, x₀] : Fin 2 → ℂ), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖chartRatio φ ![ψ (z 0), ψ (z 1)] t - 1‖ < 1 / 2 ∧
      ‖chartRatio' φ ![ψ (z 0), ψ (z 1)] t - 1‖ < 1 / 2 ∧
      φ (chartPoint ![ψ (z 0), ψ (z 1)] t) ∈ B := by
  have hη₀ : ψ x₀ ∈ V := hC.mapsTo_inv hx₀
  have hφη₀ : φ (ψ x₀) = x₀ := hC.right_inv x₀ hx₀
  have hQ₀ : chartQuot φ ![ψ x₀, ψ x₀] ≠ 0 := by
    rw [chartQuot_self]; exact hC.deriv_ne_zero hη₀
  have hpd : (![ψ x₀, ψ x₀] : Fin 2 → ℂ) ∈ pairDomain V :=
    ⟨by simpa using hη₀, by simpa using hη₀⟩
  have hQc : ContinuousAt (chartQuot φ) ![ψ x₀, ψ x₀] :=
    (analyticOnNhd_chartQuot hC.isOpen_source hC.analyticOnNhd _ hpd).continuousAt
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have hψc : ContinuousAt ψ x₀ := (hC.analyticOnNhd_inv x₀ hx₀).continuousAt
  have hc0 : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ => ψ (p.1 0)) (![x₀, x₀], t) :=
    hψc.comp_of_eq (by fun_prop) (by simp)
  have hc1 : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ => ψ (p.1 1)) (![x₀, x₀], t) :=
    hψc.comp_of_eq (by fun_prop) (by simp)
  have hpt : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      chartPoint ![ψ (p.1 0), ψ (p.1 1)] p.2) (![x₀, x₀], t) := by
    unfold chartPoint
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ((continuous_ofReal.continuousAt.comp continuousAt_snd).mul hc0).add
      ((continuousAt_const.sub (continuous_ofReal.continuousAt.comp continuousAt_snd)).mul hc1)
  have hpt0 : chartPoint ![ψ x₀, ψ x₀] (t : ℂ) = ψ x₀ := by
    simp [chartPoint]; ring
  have hcv : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      (![ψ (p.1 0), ψ (p.1 1)] : Fin 2 → ℂ)) (![x₀, x₀], t) := by
    refine continuousAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hc0
    · simpa using hc1
  have hv1 : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      (![chartPoint ![ψ (p.1 0), ψ (p.1 1)] p.2, ψ (p.1 1)] : Fin 2 → ℂ)) (![x₀, x₀], t) := by
    refine continuousAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hpt
    · simpa using hc1
  have hv2 : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      (![ψ (p.1 0), chartPoint ![ψ (p.1 0), ψ (p.1 1)] p.2] : Fin 2 → ℂ)) (![x₀, x₀], t) := by
    refine continuousAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hc0
    · simpa using hpt
  have hden : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      chartQuot φ ![ψ (p.1 0), ψ (p.1 1)]) (![x₀, x₀], t) :=
    hQc.comp_of_eq hcv (by funext i; fin_cases i <;> simp)
  have hden0 : chartQuot φ ![ψ ((![x₀, x₀] : Fin 2 → ℂ) 0), ψ ((![x₀, x₀] : Fin 2 → ℂ) 1)] ≠ 0 := by
    simpa using hQ₀
  have hr : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      chartRatio φ ![ψ (p.1 0), ψ (p.1 1)] p.2) (![x₀, x₀], t) := by
    unfold chartRatio
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (hQc.comp_of_eq hv1 (by funext i; fin_cases i <;> simp [hpt0])).div hden hden0
  have hr' : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      chartRatio' φ ![ψ (p.1 0), ψ (p.1 1)] p.2) (![x₀, x₀], t) := by
    unfold chartRatio'
    simp only [Matrix.cons_val_zero]
    exact (hQc.comp_of_eq hv2 (by funext i; fin_cases i <;> simp [hpt0])).div hden hden0
  have hφc : ContinuousAt (fun p : (Fin 2 → ℂ) × ℝ =>
      φ (chartPoint ![ψ (p.1 0), ψ (p.1 1)] p.2)) (![x₀, x₀], t) :=
    (hC.analyticOnNhd (ψ x₀) hη₀).continuousAt.comp_of_eq hpt (by simpa using hpt0)
  have hr1 : chartRatio φ ![ψ x₀, ψ x₀] t = 1 := by
    rw [chartRatio]; simp [hpt0, div_self hQ₀]
  have hr1' : chartRatio' φ ![ψ x₀, ψ x₀] t = 1 := by
    rw [chartRatio']; simp [hpt0, div_self hQ₀]
  have t1 : Tendsto (fun p : (Fin 2 → ℂ) × ℝ => chartRatio φ ![ψ (p.1 0), ψ (p.1 1)] p.2)
      (𝓝 (![x₀, x₀], t)) (𝓝 1) := by
    convert hr.tendsto using 2; simpa using hr1.symm
  have t2 : Tendsto (fun p : (Fin 2 → ℂ) × ℝ => chartRatio' φ ![ψ (p.1 0), ψ (p.1 1)] p.2)
      (𝓝 (![x₀, x₀], t)) (𝓝 1) := by
    convert hr'.tendsto using 2; simpa using hr1'.symm
  have t3 : Tendsto (fun p : (Fin 2 → ℂ) × ℝ => φ (chartPoint ![ψ (p.1 0), ψ (p.1 1)] p.2))
      (𝓝 (![x₀, x₀], t)) (𝓝 x₀) := by
    convert hφc.tendsto using 2; simpa [hpt0] using hφη₀.symm
  have e1 := t1.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  have e2 := t2.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  have e3 := t3.eventually (hBo.mem_nhds hx₀B)
  filter_upwards [e1, e2, e3] with p h1 h2 h3
  exact ⟨by simpa [dist_eq_norm] using h1, by simpa [dist_eq_norm] using h2, h3⟩

/-- The Euler weight is bounded by a power near the endpoint, times a bound for `g`. -/
private theorem norm_eulerOmega_le {g : ℂ → ℂ} {x y : ℂ} {B : Set ℂ} {Cg : ℝ}
    (hCg : ∀ w ∈ B, ‖g w‖ ≤ Cg) (e e' : ℂ) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) {w : ℂ}
    (hre : t / 2 ≤ w.re) (hn : ‖w‖ ≤ 2 * t) (hB : y + w * (x - y) ∈ B) :
    ‖w ^ e * (1 - w) ^ e' * g (y + w * (x - y))‖ ≤ eulerWeightConst e e' * t ^ e.re * Cg := by
  rw [norm_mul]
  exact mul_le_mul (norm_cpow_mul_one_sub_cpow_le e e' ht ht' hre hn) (hCg _ hB)
    (norm_nonneg _) (by unfold eulerWeightConst; positivity)

/-- A power with positive exponent tends to zero at zero from the right. -/
private theorem tendsto_rpow_nhdsGT_zero_of_pos {q : ℝ} (hq : 0 < q) :
    Tendsto (fun t : ℝ => t ^ q) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
  rw [Real.zero_rpow hq.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Agreement near the diagonal.** For node pairs near a diagonal point of `D`, the regularized
Euler integral of the pulled-back kernel is the regularized Euler integral of `g` along the
segment, for Dirichlet parameters with positive real parts. -/
theorem regEulerIntegral_twoNodeKernel_eventually_eq {D V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hC : IsConvexChart D V φ ψ) {L : (Fin 2 → ℂ) → ℂ} (hL : AnalyticOnNhd ℂ L (pairDomain V))
    (hLexp : ∀ v ∈ pairDomain V, exp (L v) = chartQuot φ v)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g D) {b₀ b₁ : ℂ} (hb₀ : 0 < b₀.re) (hb₁ : 0 < b₁.re)
    {x₀ : ℂ} (hx₀ : x₀ ∈ D) :
    ∀ᶠ z in 𝓝 (![x₀, x₀] : Fin 2 → ℂ), z 0 ≠ z 1 →
      regEulerIntegral b₀ b₁
          (fun t : ℝ => twoNodeKernel φ L g ![b₀, b₁] ![ψ (z 0), ψ (z 1)] t) =
        regEulerIntegral b₀ b₁ (fun t : ℝ => g (t * z 0 + (1 - t) * z 1)) := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hC.isOpen_target x₀ hx₀
  have hR : (0 : ℝ) < ε / 2 := by positivity
  have hRD : Metric.closedBall x₀ (ε / 2) ⊆ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεD
  set B := Metric.ball x₀ (ε / 2) with hB_def
  have hBD : B ⊆ D := Metric.ball_subset_closedBall.trans hRD
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall x₀ (ε / 2)).exists_bound_of_continuousOn
    (hg.continuousOn.mono hRD)
  have hCgB : ∀ w ∈ B, ‖g w‖ ≤ Cg := fun w hw => hCg w (Metric.ball_subset_closedBall hw)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg x₀ (Metric.mem_closedBall_self hR.le))
  have hnear := eventually_chart_near_diag hC hx₀ Metric.isOpen_ball (Metric.mem_ball_self hR)
  have hzB : ∀ᶠ z in 𝓝 (![x₀, x₀] : Fin 2 → ℂ), z 0 ∈ B ∧ z 1 ∈ B := by
    have h0 : ∀ᶠ z in 𝓝 (![x₀, x₀] : Fin 2 → ℂ), z 0 ∈ B :=
      (continuous_apply 0).continuousAt.preimage_mem_nhds (by
        simpa using Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    have h1 : ∀ᶠ z in 𝓝 (![x₀, x₀] : Fin 2 → ℂ), z 1 ∈ B :=
      (continuous_apply 1).continuousAt.preimage_mem_nhds (by
        simpa using Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    filter_upwards [h0, h1] with z h0 h1 using ⟨h0, h1⟩
  filter_upwards [hnear, hzB] with z hz hzB' hne
  -- Notation for the nodes and their chart preimages.
  set c : Fin 2 → ℂ := ![ψ (z 0), ψ (z 1)] with hc_def
  have hxD : z 0 ∈ D := hBD hzB'.1
  have hyD : z 1 ∈ D := hBD hzB'.2
  have hcV : c ∈ pairDomain V :=
    ⟨by simpa [c] using hC.mapsTo_inv hxD, by simpa [c] using hC.mapsTo_inv hyD⟩
  have hx : φ (c 0) = z 0 := by simpa [c] using hC.right_inv _ hxD
  have hy : φ (c 1) = z 1 := by simpa [c] using hC.right_inv _ hyD
  have hc : c 0 ≠ c 1 := fun h => hne (by rw [← hx, ← hy, h])
  have hQ : chartQuot φ c ≠ 0 :=
    chartQuot_ne_zero hC.injOn (fun _ hs => hC.deriv_ne_zero hs) hcV
  have hre_of {r : ℂ} (h : ‖r - 1‖ < 1 / 2) : 0 < r.re := by
    have := (abs_re_le_norm (r - 1)).trans h.le
    rw [sub_re, one_re] at this
    linarith [neg_abs_le (r.re - 1)]
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (chartRatio φ c t).re := fun t ht => hre_of (hz t ht).1
  have hr' : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (chartRatio' φ c t).re := fun t ht => hre_of (hz t ht).2.1
  have hlog := log_chartRatio_eq hC.isOpen_source hC.convex_source hC.analyticOnNhd hL hLexp
    hcV hQ hr
  have hlog' := log_chartRatio'_eq hC.isOpen_source hC.convex_source hC.analyticOnNhd hL hLexp
    hcV hQ hr'
  -- The strip in which the deformation takes place.
  set x := φ (c 0)
  set y := φ (c 1)
  set U : Set ℂ := {τ | 0 < τ.re ∧ 0 < (1 - τ).re ∧ y + τ * (x - y) ∈ B} with hU_def
  have hUo : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_const (continuous_re.comp (continuous_const.sub continuous_id))).inter
        (Metric.isOpen_ball.preimage (by fun_prop)))
  have hUc : Convex ℝ U := by
    intro a ha a' ha' p q hp hq hpq
    refine ⟨?_, ?_, ?_⟩
    · have hre : (p • a + q • a').re = p * a.re + q * a'.re := by simp
      rw [hre]
      rcases eq_or_lt_of_le hp with h | h
      · subst h; simp only [zero_add] at hpq; subst hpq; simpa using ha'.1
      · have := mul_pos h ha.1; have := mul_nonneg hq ha'.1.le; linarith
    · have : (1 - (p • a + q • a')) = p • (1 - a) + q • (1 - a') := by
        simp only [real_smul]; rw [show q = 1 - p by linarith]; push_cast; ring
      rw [this]
      have hre : (p • (1 - a) + q • (1 - a')).re = p * (1 - a).re + q * (1 - a').re := by
        simp
      rw [hre]
      rcases eq_or_lt_of_le hp with h | h
      · subst h; simp only [zero_add] at hpq; subst hpq; simpa using ha'.2.1
      · have := mul_pos h ha.2.1; have := mul_nonneg hq ha'.2.1.le; linarith
    · have : y + (p • a + q • a') * (x - y) = p • (y + a * (x - y)) + q • (y + a' * (x - y)) := by
        simp only [real_smul]; rw [show q = 1 - p by linarith]; push_cast; ring
      rw [this]
      exact (convex_ball x₀ (ε / 2)) ha.2.2 ha'.2.2 hp hq hpq
  set ω : ℂ → ℂ := fun τ => τ ^ (b₀ - 1) * (1 - τ) ^ (b₁ - 1) * g (y + τ * (x - y)) with hω_def
  have hω : DifferentiableOn ℂ ω U := by
    intro τ hτ
    have h1 : DifferentiableAt ℂ (fun τ : ℂ => τ ^ (b₀ - 1)) τ :=
      differentiableAt_id.cpow_const (mem_slitPlane_iff.mpr (Or.inl hτ.1))
    have h2 : DifferentiableAt ℂ (fun τ : ℂ => (1 - τ) ^ (b₁ - 1)) τ :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).cpow_const
        (mem_slitPlane_iff.mpr (Or.inl hτ.2.1))
    have h3 : DifferentiableAt ℂ (fun τ : ℂ => g (y + τ * (x - y))) τ :=
      (hg _ (hBD hτ.2.2)).differentiableAt.comp τ (by fun_prop)
    exact ((h1.mul h2).mul h3).differentiableWithinAt
  set γ : ℂ → ℂ := chartCurve φ c x y with hγ_def
  have hγ_eq : ∀ τ : ℂ, γ τ = τ * chartRatio φ c τ := chartCurve_eq_mul φ hc hQ
  have hγ_eq' : ∀ τ : ℂ, 1 - γ τ = (1 - τ) * chartRatio' φ c τ :=
    one_sub_chartCurve_eq_mul φ hc hQ
  have hγpt : ∀ τ : ℂ, y + γ τ * (x - y) = φ (chartPoint c τ) := by
    intro τ
    have hd : x - y ≠ 0 := by
      rw [← sub_mul_chartQuot φ c]; exact mul_ne_zero (sub_ne_zero.mpr hc) hQ
    simp only [hγ_def, chartCurve]; field_simp; ring
  have hIoo_Icc : ∀ t ∈ Ioo (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => Ioo_subset_Icc_self ht
  have hU₁ : ∀ t ∈ Ioo (0 : ℝ) 1, ((t : ℝ) : ℂ) ∈ U := by
    intro t ht
    refine ⟨by simpa using ht.1, by simpa using ht.2, ?_⟩
    have := (convex_ball x₀ (ε / 2)) hzB'.1 hzB'.2 ht.1.le (sub_nonneg.mpr ht.2.le)
      (by ring : t + (1 - t) = 1)
    rw [← hx, ← hy] at this
    convert this using 1
    simp only [real_smul]; push_cast; ring
  have hU₂ : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ U := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hγ_eq, re_ofReal_mul]; exact mul_pos ht.1 (hr t (hIoo_Icc t ht))
    · rw [hγ_eq', show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
      exact mul_pos (by linarith [ht.2]) (hr' t (hIoo_Icc t ht))
    · rw [hγpt]; exact (hz t (hIoo_Icc t ht)).2.2
  have hγd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => γ t)
      (deriv φ (chartPoint c t) / chartQuot φ c) t := by
    intro t ht
    exact (hasDerivAt_chartCurve hC.analyticOnNhd hc hQ
      (chartPoint_mem hC.convex_source hcV (hIoo_Icc t ht))).comp_ofReal
  have hid : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t _ =>
    (hasDerivAt_id (t : ℂ)).comp_ofReal
  -- The pointwise substitution identity on the open interval.
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) 1,
      (t : ℂ) ^ (b₀ - 1) * (1 - t : ℂ) ^ (b₁ - 1) *
          twoNodeKernel φ L g ![b₀, b₁] c t =
        ω (γ t) * (deriv φ (chartPoint c t) / chartQuot φ c) := by
    intro t ht
    exact eulerIntegrand_twoNodeKernel_eq hLexp g b₀ b₁ hcV hc hQ ht
      (hr t (hIoo_Icc t ht)) (hr' t (hIoo_Icc t ht)) (hlog t (hIoo_Icc t ht))
      (hlog' t (hIoo_Icc t ht))
  -- Integrability.
  have hKc : ContinuousOn (fun t : ℝ => twoNodeKernel φ L g ![b₀, b₁] c t) (Icc 0 1) := by
    intro t ht
    exact ((analyticAt_twoNodeKernel hC hL hg ![b₀, b₁] hcV
      (chartPoint_mem hC.convex_source hcV ht)).continuousAt.comp
        continuous_ofReal.continuousAt).continuousWithinAt
  have hK_int := integrableOn_eulerKernel_mul hb₀ hb₁ hKc
  have hgc : ContinuousOn (fun t : ℝ => g (y + (t : ℂ) * (x - y))) (Icc 0 1) := by
    intro t ht
    have hmem : y + (t : ℂ) * (x - y) ∈ B := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simpa [hy] using hzB'.2
      rcases eq_or_lt_of_le ht.2 with h' | h'
      · subst h'; simpa [hx] using hzB'.1
      · exact (hU₁ t ⟨h, h'⟩).2.2
    exact ((hg _ (hBD hmem)).continuousAt.comp (f := fun t : ℝ => y + (t : ℂ) * (x - y))
      (by fun_prop)).continuousWithinAt
  have hg_int := integrableOn_eulerKernel_mul hb₀ hb₁ hgc
  have hi₁ : IntervalIntegrable (fun t : ℝ => ω t * 1) volume 0 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_
    simpa [hω_def] using hg_int
  have hi₂ : IntervalIntegrable (fun t : ℝ => ω (γ t) *
      (deriv φ (chartPoint c t) / chartQuot φ c)) volume 0 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_
    exact hK_int.congr_fun (fun t ht => hpoint t ht) measurableSet_Ioo
  -- Endpoint conditions.
  set e₀ := b₀ - 1
  set e₁ := b₁ - 1
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) (1 / 4) :=
    Ioo_mem_nhdsGT (by norm_num)
  have h₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), segment ℝ ((t : ℝ) : ℂ) (γ t) ⊆ U ∧
      ∀ w ∈ segment ℝ ((t : ℝ) : ℂ) (γ t), ‖ω w‖ ≤ eulerWeightConst e₀ e₁ * t ^ e₀.re * Cg := by
    filter_upwards [hsmall] with t ht
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
    have hseg : segment ℝ ((t : ℝ) : ℂ) (γ t) ⊆ U := hUc.segment_subset (hU₁ t ht01) (hU₂ t ht01)
    refine ⟨hseg, fun w hw => ?_⟩
    have hw' := hw
    rw [hγ_eq] at hw'
    obtain ⟨hre, hn⟩ := mem_sector_of_mem_segment ht.1 (hz t (hIoo_Icc t ht01)).1 hw'
    exact norm_eulerOmega_le hCgB e₀ e₁ ht.1 ht.2.le hre hn (hseg hw).2.2
  have h₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), segment ℝ (((1 - t : ℝ)) : ℂ) (γ (1 - t : ℝ)) ⊆ U ∧
      ∀ w ∈ segment ℝ (((1 - t : ℝ)) : ℂ) (γ (1 - t : ℝ)),
        ‖ω w‖ ≤ eulerWeightConst e₁ e₀ * t ^ e₁.re * Cg := by
    filter_upwards [hsmall] with t ht
    have ht01 : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hseg : segment ℝ (((1 - t : ℝ)) : ℂ) (γ (1 - t : ℝ)) ⊆ U :=
      hUc.segment_subset (hU₁ _ ht01) (hU₂ _ ht01)
    refine ⟨hseg, fun w hw => ?_⟩
    have hw' : 1 - w ∈ segment ℝ (t : ℂ) (t * chartRatio' φ c (1 - t : ℝ)) := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw
      refine ⟨p, q, hp, hq, hpq, ?_⟩
      have h1 : 1 - γ (1 - t : ℝ) = (t : ℂ) * chartRatio' φ c (1 - t : ℝ) := by
        rw [hγ_eq']; push_cast; ring
      rw [← h1]
      simp only [real_smul]; rw [show q = 1 - p by linarith]; push_cast; ring
    obtain ⟨hre, hn⟩ := mem_sector_of_mem_segment ht.1 (hz _ (hIoo_Icc _ ht01)).2.1 hw'
    have h := norm_cpow_mul_one_sub_cpow_le e₁ e₀ ht.1 ht.2.le hre hn
    simp only [sub_sub_cancel] at h
    rw [hω_def]
    simp only
    rw [norm_mul, mul_comm (w ^ e₀)]
    exact mul_le_mul h (hCgB _ (hseg hw).2.2) (norm_nonneg _)
      (mul_nonneg (by unfold eulerWeightConst; positivity) (Real.rpow_nonneg ht.1.le _))
  have hK₀ : 0 ≤ eulerWeightConst e₀ e₁ * Cg := by unfold eulerWeightConst; positivity
  have hK₁ : 0 ≤ eulerWeightConst e₁ e₀ * Cg := by unfold eulerWeightConst; positivity
  have ht₀ : Tendsto (fun t => eulerWeightConst e₀ e₁ * t ^ e₀.re * Cg *
      ‖γ (t : ℝ) - ((t : ℝ) : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
    have hlim := (tendsto_rpow_nhdsGT_zero_of_pos hb₀).const_mul (eulerWeightConst e₀ e₁ * Cg)
    rw [mul_zero] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hsmall] with t ht
      have : 0 ≤ t ^ e₀.re := Real.rpow_nonneg ht.1.le _
      unfold eulerWeightConst; positivity
    · filter_upwards [hsmall] with t ht
      have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
      have hd : ‖γ (t : ℝ) - ((t : ℝ) : ℂ)‖ ≤ t := by
        rw [hγ_eq, show (t : ℂ) * chartRatio φ c t - t = t * (chartRatio φ c t - 1) by ring,
          norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        exact mul_le_of_le_one_right ht.1.le (by linarith [(hz t (hIoo_Icc t ht01)).1])
      have hpow : t ^ e₀.re * t = t ^ b₀.re := by
        rw [← Real.rpow_add_one ht.1.ne']; congr 1; simp [e₀]
      calc eulerWeightConst e₀ e₁ * t ^ e₀.re * Cg * ‖γ (t : ℝ) - ((t : ℝ) : ℂ)‖
          ≤ eulerWeightConst e₀ e₁ * t ^ e₀.re * Cg * t := by
            apply mul_le_mul_of_nonneg_left hd
            have : 0 ≤ t ^ e₀.re := Real.rpow_nonneg ht.1.le _
            unfold eulerWeightConst; positivity
        _ = eulerWeightConst e₀ e₁ * Cg * t ^ b₀.re := by rw [← hpow]; ring
  have ht₁ : Tendsto (fun t => eulerWeightConst e₁ e₀ * t ^ e₁.re * Cg *
      ‖γ (1 - t : ℝ) - (((1 - t : ℝ)) : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
    have hlim := (tendsto_rpow_nhdsGT_zero_of_pos hb₁).const_mul (eulerWeightConst e₁ e₀ * Cg)
    rw [mul_zero] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hsmall] with t ht
      have : 0 ≤ t ^ e₁.re := Real.rpow_nonneg ht.1.le _
      unfold eulerWeightConst; positivity
    · filter_upwards [hsmall] with t ht
      have ht01 : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hd : ‖γ (1 - t : ℝ) - (((1 - t : ℝ)) : ℂ)‖ ≤ t := by
        have h1 : γ (1 - t : ℝ) - (((1 - t : ℝ)) : ℂ) =
            -((t : ℂ) * (chartRatio' φ c (1 - t : ℝ) - 1)) := by
          have := hγ_eq' (1 - t : ℝ)
          push_cast at this ⊢
          linear_combination -this
        rw [h1, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        exact mul_le_of_le_one_right ht.1.le (by linarith [(hz _ (hIoo_Icc _ ht01)).2.1])
      have hpow : t ^ e₁.re * t = t ^ b₁.re := by
        rw [← Real.rpow_add_one ht.1.ne']; congr 1; simp [e₁]
      calc eulerWeightConst e₁ e₀ * t ^ e₁.re * Cg * ‖γ (1 - t : ℝ) - (((1 - t : ℝ)) : ℂ)‖
          ≤ eulerWeightConst e₁ e₀ * t ^ e₁.re * Cg * t := by
            apply mul_le_mul_of_nonneg_left hd
            have : 0 ≤ t ^ e₁.re := Real.rpow_nonneg ht.1.le _
            unfold eulerWeightConst; positivity
        _ = eulerWeightConst e₁ e₀ * Cg * t ^ b₁.re := by rw [← hpow]; ring
  have hdef := Complex.intervalIntegral_mul_comp_eq_of_endpoint hUo hUc hω hid hγd hU₁ hU₂
    hi₁ hi₂ h₀ h₁ ht₀ ht₁
  -- Assemble.
  unfold regEulerIntegral
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioo hpoint, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← hdef, intervalIntegral.integral_of_le
    zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  simp only [hω_def, mul_one]
  rw [← hx, ← hy]
  congr 2
  ring

/-- A two-node regularized Dirichlet average is a regularized Euler integral along the segment. -/
theorem regCarlsonDirichletAverage_fin_two (b z : Fin 2 → ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage b z f =
      regEulerIntegral (b 0) (b 1) (fun t : ℝ => f (t * z 0 + (1 - t) * z 1)) := by
  have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
  unfold regCarlsonDirichletAverage
  rw [regDirichletIntegral_congr b (g := fun u => (fun t : ℝ => f (t * z 0 + (1 - t) * z 1)) (u 0))]
  · have h := regDirichletIntegral_fin_two (b 0) (b 1)
      (fun t : ℝ => f (t * z 0 + (1 - t) * z 1))
    rwa [← hb] at h
  · intro u hu
    have h1 : u 1 = 1 - u 0 := by
      have := hu.2; simp only [Fin.sum_univ_two] at this; linarith
    simp [carlsonAffineForm, Fin.sum_univ_two, h1]

/-- The auxiliary parameters of the two-node construction: Dirichlet parameters, chart nodes and
external parameters. -/
abbrev TwoNodeAux (σ : Type*) := Fin 2 ⊕ (Fin 2 ⊕ σ)

/-- Packing of the auxiliary parameters. -/
def twoNodeEnc {σ : Type*} (b c : Fin 2 → ℂ) (p : σ → ℂ) : TwoNodeAux σ → ℂ :=
  Sum.elim b (Sum.elim c p)

/-- The target of a convex chart is connected. -/
theorem IsConvexChart.isConnected_target {D V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hC : IsConvexChart D V φ ψ) : IsConnected D := by
  have hD : φ '' V = D := by
    refine Subset.antisymm (hC.mapsTo.image_subset) fun w hw => ⟨ψ w, hC.mapsTo_inv hw, ?_⟩
    exact hC.right_inv w hw
  rw [← hD]
  exact (hC.convex_source.isConnected hC.nonempty_source).image φ
    hC.analyticOnNhd.continuousOn

/-- **The parametric two-node continuation, from a convex chart.** Let `D` carry a convex chart
and `g (w, p)` be holomorphic for `w ∈ D` and `p` in an open parameter set `P`. There is a
function of the Dirichlet parameters, the two nodes and the parameter that is holomorphic for
all Dirichlet parameters, both nodes in `D` and `p ∈ P`, and that agrees with the regularized
two-node average of `g (·, p)` whenever the segment of the nodes lies in `D` and the Dirichlet
parameters have positive real parts. -/
theorem exists_twoNode_continuation_of_chart {D V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hC : IsConvexChart D V φ ψ)
    {σ : Type*} [Fintype σ] {P : Set (σ → ℂ)} (hP : IsOpen P)
    {g : ℂ × (σ → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g (D ×ˢ P)) :
    ∃ G : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) → ℂ,
      AnalyticOnNhd ℂ G ((univ ×ˢ pairDomain D) ×ˢ P) ∧
      ∀ p ∈ P, ∀ z : Fin 2 → ℂ, convexHull ℝ (range z) ⊆ D → ∀ b ∈ mvBetaConvergent,
        G ((b, z), p) = regCarlsonDirichletAverage b z (fun w => g (w, p)) := by
  have hDo : IsOpen D := hC.isOpen_target
  obtain ⟨L, hL, hLexp⟩ := hC.exists_log
  -- Accessors of the auxiliary parameters.
  let bOf : (TwoNodeAux σ → ℂ) → Fin 2 → ℂ := fun a i => a (Sum.inl i)
  let cOf : (TwoNodeAux σ → ℂ) → Fin 2 → ℂ := fun a i => a (Sum.inr (Sum.inl i))
  let pOf : (TwoNodeAux σ → ℂ) → σ → ℂ := fun a j => a (Sum.inr (Sum.inr j))
  have hbOf : AnalyticOnNhd ℂ bOf univ := fun a _ =>
    analyticAt_pi_iff.mpr fun i => (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : TwoNodeAux σ => ℂ) (Sum.inl i)).analyticAt a
  have hcOf : AnalyticOnNhd ℂ cOf univ := fun a _ =>
    analyticAt_pi_iff.mpr fun i => (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : TwoNodeAux σ => ℂ) (Sum.inr (Sum.inl i))).analyticAt a
  have hpOf : AnalyticOnNhd ℂ pOf univ := fun a _ =>
    analyticAt_pi_iff.mpr fun j => (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : TwoNodeAux σ => ℂ) (Sum.inr (Sum.inr j))).analyticAt a
  let H : (TwoNodeAux σ → ℂ) × ℂ → ℂ := fun q =>
    twoNodeKernel φ L (fun w => g (w, pOf q.1)) (bOf q.1) (cOf q.1) q.2
  let U : Set (TwoNodeAux σ → ℂ) := {a | cOf a ∈ pairDomain V ∧ pOf a ∈ P}
  let W : Set ((TwoNodeAux σ → ℂ) × ℂ) :=
    {q | chartPoint (cOf q.1) q.2 ∈ V ∧ cOf q.1 ∈ pairDomain V ∧ pOf q.1 ∈ P}
  have hcOfc : Continuous cOf := continuous_pi fun i => continuous_apply _
  have hpOfc : Continuous pOf := continuous_pi fun j => continuous_apply _
  have hUo : IsOpen U :=
    ((isOpen_pairDomain hC.isOpen_source).preimage hcOfc).inter (hP.preimage hpOfc)
  have hWo : IsOpen W := by
    refine (hC.isOpen_source.preimage ?_).inter
      (((isOpen_pairDomain hC.isOpen_source).preimage (hcOfc.comp continuous_fst)).inter
        (hP.preimage (hpOfc.comp continuous_fst)))
    unfold chartPoint
    exact ((continuous_snd.mul ((continuous_apply 0).comp (hcOfc.comp continuous_fst))).add
      ((continuous_const.sub continuous_snd).mul ((continuous_apply 1).comp
        (hcOfc.comp continuous_fst))))
  have hH : AnalyticOnNhd ℂ H W := by
    rintro ⟨a, t⟩ ⟨hs, hc, hp⟩
    have hca : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => cOf q.1) (a, t) :=
      (hcOf a (mem_univ a)).comp (analyticAt_fst (p := (a, t)))
    have hpa : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => pOf q.1) (a, t) :=
      (hpOf a (mem_univ a)).comp (analyticAt_fst (p := (a, t)))
    have hba : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => bOf q.1) (a, t) :=
      (hbOf a (mem_univ a)).comp (analyticAt_fst (p := (a, t)))
    have hc0 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => cOf q.1 0) (a, t) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp hca
    have hc1 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => cOf q.1 1) (a, t) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _).comp hca
    have hb0 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => bOf q.1 0) (a, t) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp hba
    have hb1 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => bOf q.1 1) (a, t) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _).comp hba
    have hs' : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ => chartPoint (cOf q.1) q.2)
        (a, t) := by
      unfold chartPoint
      exact (analyticAt_snd.mul hc0).add ((analyticAt_const.sub analyticAt_snd).mul hc1)
    have hφs := (hC.analyticOnNhd _ hs).comp_of_eq hs' rfl
    have hgs : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ =>
        g (φ (chartPoint (cOf q.1) q.2), pOf q.1)) (a, t) :=
      (hg _ ⟨hC.mapsTo hs, hp⟩).comp_of_eq (hφs.prod hpa) rfl
    have hds := (hC.analyticOnNhd.deriv _ hs).comp_of_eq hs' rfl
    have hp1 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ =>
        (![chartPoint (cOf q.1) q.2, cOf q.1 1] : Fin 2 → ℂ)) (a, t) := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i
      · simpa using hs'
      · simpa using hc1
    have hp2 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ =>
        (![cOf q.1 0, chartPoint (cOf q.1) q.2] : Fin 2 → ℂ)) (a, t) := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i
      · simpa using hc0
      · simpa using hs'
    have hp0 : AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ =>
        (![cOf q.1 0, cOf q.1 1] : Fin 2 → ℂ)) (a, t) := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i
      · simpa using hc0
      · simpa using hc1
    have hL1 := (hL _ ⟨by simpa using hs, by simpa using hc.2⟩).comp_of_eq hp1 rfl
    have hL2 := (hL _ ⟨by simpa using hc.1, by simpa using hs⟩).comp_of_eq hp2 rfl
    have hL0 := (hL _ ⟨by simpa using hc.1, by simpa using hc.2⟩).comp_of_eq hp0 rfl
    change AnalyticAt ℂ (fun q : (TwoNodeAux σ → ℂ) × ℂ =>
      g (φ (chartPoint (cOf q.1) q.2), pOf q.1) * deriv φ (chartPoint (cOf q.1) q.2) *
        exp ((bOf q.1 0 - 1) * L ![chartPoint (cOf q.1) q.2, cOf q.1 1] +
          (bOf q.1 1 - 1) * L ![cOf q.1 0, chartPoint (cOf q.1) q.2] -
            (bOf q.1 0 + bOf q.1 1 - 1) * L ![cOf q.1 0, cOf q.1 1])) (a, t)
    exact (hgs.mul hds).mul ((((hb0.sub analyticAt_const).mul hL1).add
      ((hb1.sub analyticAt_const).mul hL2)).sub (((hb0.add hb1).sub analyticAt_const).mul
        hL0)).cexp
  have hWU : ∀ a ∈ U, ∀ u ∈ Icc (0 : ℝ) 1, (a, (u : ℂ)) ∈ W := fun a ha u hu =>
    ⟨chartPoint_mem hC.convex_source ha.1 hu, ha.1, ha.2⟩
  obtain ⟨F, hF, hFeq⟩ := exists_joint_regEulerContinuation hUo hWo hH hWU
  let enc : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) → TwoNodeAux σ → ℂ := fun q =>
    twoNodeEnc q.1.1 ![ψ (q.1.2 0), ψ (q.1.2 1)] q.2
  have hGall : AnalyticOnNhd ℂ (fun q => F (q.1.1, enc q)) ((univ ×ˢ pairDomain D) ×ˢ P) := by
    rintro ⟨⟨b, z⟩, p⟩ ⟨⟨-, hz⟩, hp⟩
    have hz0 : AnalyticAt ℂ (fun q : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) => ψ (q.1.2 0))
        ((b, z), p) :=
      (hC.analyticOnNhd_inv _ hz.1).comp_of_eq (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp (analyticAt_snd.comp analyticAt_fst)) rfl
    have hz1 : AnalyticAt ℂ (fun q : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) => ψ (q.1.2 1))
        ((b, z), p) :=
      (hC.analyticOnNhd_inv _ hz.2).comp_of_eq (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _).comp (analyticAt_snd.comp analyticAt_fst)) rfl
    have henc : AnalyticAt ℂ enc ((b, z), p) := by
      refine analyticAt_pi_iff.mpr fun k => ?_
      rcases k with i | i | j
      · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).analyticAt _).comp
          (analyticAt_fst.comp analyticAt_fst)
      · fin_cases i
        · simpa [enc, twoNodeEnc] using hz0
        · simpa [enc, twoNodeEnc] using hz1
      · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) j).analyticAt _).comp
          analyticAt_snd
    have hmem : enc ((b, z), p) ∈ U := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [enc, twoNodeEnc, cOf] using hC.mapsTo_inv hz.1
      · simpa [enc, twoNodeEnc, cOf] using hC.mapsTo_inv hz.2
      · simpa [enc, twoNodeEnc, pOf] using hp
    exact (hF _ ⟨mem_univ _, hmem⟩).comp_of_eq ((analyticAt_fst.comp analyticAt_fst).prod henc) rfl
  refine ⟨_, hGall, ?_⟩
  · -- Agreement with the native average.
    intro p hp z hz b hb
    have hgp : AnalyticOnNhd ℂ (fun w => g (w, p)) D := fun w hw =>
      (hg _ ⟨hw, hp⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    obtain ⟨N, hN, hNeq⟩ := exists_joint_isRegCarlsonContinuation_on_integralDomain (ι := Fin 2)
      hDo hgp
    set S := carlsonIntegralNodeDomain (ι := Fin 2) D
    have hSo : IsOpen S := isOpen_carlsonIntegralNodeDomain hDo
    have hDc : IsConnected D := hC.isConnected_target
    have hSc : IsPreconnected S :=
      (isConnected_carlsonIntegralNodeDomain_of_isOpen hDo hDc).isPreconnected
    have hSsub : ∀ z ∈ S, z ∈ pairDomain D := fun z hz' =>
      ⟨hz' (subset_convexHull ℝ _ ⟨0, rfl⟩), hz' (subset_convexHull ℝ _ ⟨1, rfl⟩)⟩
    -- Both sides are holomorphic in the nodes on `S`.
    have hGa : AnalyticOnNhd ℂ (fun z => F (b, enc ((b, z), p))) S := fun z' hz' =>
      (hGall ((b, z'), p) ⟨⟨mem_univ _, hSsub z' hz'⟩, hp⟩).comp_of_eq
        ((analyticAt_const.prod analyticAt_id).prod analyticAt_const) rfl
    have hNa : AnalyticOnNhd ℂ (fun z => N (b, z)) S := fun z' hz' =>
      (hN (b, z') ⟨mem_univ _, hz'⟩).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    -- Agreement on an open set off the diagonal near a diagonal point.
    obtain ⟨x₀, hx₀⟩ := hDc.nonempty
    have hloc := regEulerIntegral_twoNodeKernel_eventually_eq hC hL hLexp hgp (hb 0) (hb 1) hx₀
    have hS0 : (![x₀, x₀] : Fin 2 → ℂ) ∈ S := by
      have hr : Set.range (![x₀, x₀] : Fin 2 → ℂ) = {x₀} := by
        ext w; simp [eq_comm]
      change convexHull ℝ (Set.range (![x₀, x₀] : Fin 2 → ℂ)) ⊆ D
      rw [hr, convexHull_singleton]
      exact singleton_subset_iff.mpr hx₀
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hloc (hSo.mem_nhds hS0))
    set z₁ : Fin 2 → ℂ := ![x₀ + (δ / 4 : ℝ), x₀]
    have hz₁ : dist z₁ ![x₀, x₀] < δ / 2 := by
      rw [dist_pi_lt_iff (by positivity)]
      intro i; fin_cases i
      · simp [z₁, dist_eq_norm, abs_of_pos hδ]; linarith
      · simpa [z₁] using by positivity
    have hz₁S : z₁ ∈ S := (hball (by rw [Metric.mem_ball]; linarith [hz₁])).2
    have hne_open : IsOpen {z : Fin 2 → ℂ | z 0 ≠ z 1} :=
      isOpen_ne_fun (continuous_apply 0) (continuous_apply 1)
    have hz₁ne : z₁ ∈ {z : Fin 2 → ℂ | z 0 ≠ z 1} := by
      simp only [mem_ofPred_eq, z₁, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, ne_eq, add_eq_left, ofReal_eq_zero]
      positivity
    have hbvec : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
    have heq : (fun z => F (b, enc ((b, z), p))) =ᶠ[𝓝 z₁] fun z => N (b, z) := by
      filter_upwards [Metric.ball_mem_nhds z₁ (half_pos hδ), hne_open.mem_nhds hz₁ne]
        with z hz1 hz2
      have hzz : z ∈ Metric.ball (![x₀, x₀] : Fin 2 → ℂ) δ := by
        rw [Metric.mem_ball]
        calc dist z ![x₀, x₀] ≤ dist z z₁ + dist z₁ ![x₀, x₀] := dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add (Metric.mem_ball.mp hz1) (by linarith [hz₁])
          _ = δ := by ring
      obtain ⟨hPz, hzS⟩ := hball hzz
      have hzD := hSsub z hzS
      have hmem : enc ((b, z), p) ∈ U := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa [enc, twoNodeEnc, cOf] using hC.mapsTo_inv hzD.1
        · simpa [enc, twoNodeEnc, cOf] using hC.mapsTo_inv hzD.2
        · simpa [enc, twoNodeEnc, pOf] using hp
      have h1 := hFeq _ hmem (b 0) (b 1) (hb 0) (hb 1)
      rw [← hbvec] at h1
      change F (b, enc ((b, z), p)) = N (b, z)
      rw [h1, (hNeq z hzS).eq_native hb, regCarlsonDirichletAverage_fin_two]
      have hk : (fun u : ℝ => H (enc ((b, z), p), (u : ℂ))) =
          fun u : ℝ => twoNodeKernel φ L (fun w => g (w, p)) ![b 0, b 1]
            ![ψ (z 0), ψ (z 1)] u := by
        funext u
        simp only [H, enc, twoNodeEnc, bOf, cOf, pOf, Sum.elim_inl, Sum.elim_inr]
        rw [← hbvec]
      rw [hk]
      exact hPz hz2
    have hfin := hGa.eqOn_of_preconnected_of_eventuallyEq hNa hSc hz₁S heq hz
    exact hfin.trans ((hNeq z hz).eq_native hb)

/-- **The parametric two-node continuation** (Carlson 1969, Theorem 8, two nodes). Let `D` be a
simply connected open set and `g (w, p)` be holomorphic for `w ∈ D` and `p` in an open parameter
set `P`. There is a function of the Dirichlet parameters, the two nodes and the parameter that is
holomorphic for all Dirichlet parameters, both nodes in `D` and `p ∈ P`, and that agrees with the
regularized two-node average of `g (·, p)` whenever the segment of the nodes lies in `D` and the
Dirichlet parameters have positive real parts. -/
theorem exists_twoNode_continuation {D : Set ℂ} (hDo : IsOpen D) (hDs : IsSimplyConnected D)
    {σ : Type*} [Fintype σ] {P : Set (σ → ℂ)} (hP : IsOpen P)
    {g : ℂ × (σ → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g (D ×ˢ P)) :
    ∃ G : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) → ℂ,
      AnalyticOnNhd ℂ G ((univ ×ˢ pairDomain D) ×ˢ P) ∧
      ∀ p ∈ P, ∀ z : Fin 2 → ℂ, convexHull ℝ (range z) ⊆ D → ∀ b ∈ mvBetaConvergent,
        G ((b, z), p) = regCarlsonDirichletAverage b z (fun w => g (w, p)) := by
  obtain ⟨V, φ, ψ, hC⟩ := IsConvexChart.exists_of_isSimplyConnected hDo hDs
  exact exists_twoNode_continuation_of_chart hC hP hg

end Dirichlet

end
