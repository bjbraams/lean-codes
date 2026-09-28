/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.Basic
public import Carlson.T.TwoF0
public import Carlson.R.ContourRepresentation

/-!
# The two-variable T-function with a zero node

Carlson's (5.12-2) defines `T(β, β'; x, 0)` as the limit of `T(β, β'; x, y)` as `y → 0`; it is
the Euler integral `B(β, β')⁻¹ ∫₀¹ e^{1/(ux)} u^{β-1} (1-u)^{β'-1} du`. The limit holds by
dominated convergence for nodes in the open left half-plane, where `|e^{1/w}| ≤ 1`. The
substitution `1/u = 1 - t x` turns the integral into (5.12-3), an integral against the Euler
measure `dλ_{β'}`, which is Carlson's `₂F₀` by (5.12-7).

## Main results

* `Carlson.tendsto_regCarlsonT_pair_zero`: the limit (5.12-2).
* `Carlson.regCarlsonTIntegral_pair_zero_eq`: formula (5.12-3).
* `Carlson.regCarlsonTIntegral_pair_zero_eq_carlson2F0`: (5.12-3) in terms of `₂F₀`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

open Complex MeasureTheory Filter Set Dirichlet
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson

open TwoVariable

/-- In the open left half-plane the T-kernel `e^{1/w}` has modulus at most one. -/
theorem norm_carlsonTKernel_le_one {w : ℂ} (hw : w.re < 0) : ‖carlsonTKernel w‖ ≤ 1 := by
  rw [carlsonTKernel, norm_exp, Real.exp_le_one_iff, inv_re]
  exact div_nonpos_of_nonpos_of_nonneg hw.le (normSq_nonneg _)

/-- **The zero-node limit (5.12-2)**: for `re β, re β' > 0` and `re x < 0`,
`T(β, β'; x, y) → T(β, β'; x, 0)` as `y → 0` in the left half-plane, where the limit is the
native average `B(β, β')⁻¹ ∫₀¹ e^{1/(ux)} u^{β-1} (1-u)^{β'-1} du`, here regularized. -/
theorem tendsto_regCarlsonT_pair_zero {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) {x : ℂ}
    (hx : x.re < 0) :
    Tendsto (fun y => regCarlsonT (pair β β') (pair x y)) (𝓝[{y | y.re < 0}] 0)
      (𝓝 (regCarlsonTIntegral (pair β β') (pair x 0))) := by
  have hb : pair β β' ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · exact hβ
    · exact hβ'
  have hH : Convex ℝ {w : ℂ | w.re < 0} := convex_halfSpace_re_lt 0
  have h0 : (0 : ℂ) ∉ {w : ℂ | w.re < 0} := by simp
  have hT : ∀ y : ℂ, y.re < 0 → regCarlsonT (pair β β') (pair x y) =
      regCarlsonTIntegral (pair β β') (pair x y) := fun y hy =>
    regCarlsonT_eq_integral hb (mem_carlsonTVariableDomain_of_range_subset hH h0 (by
      rintro _ ⟨i, rfl⟩; fin_cases i
      · exact hx
      · exact hy))
  have hre : ∀ y : ℂ, y.re ≤ 0 → ∀ u ∈ Ioo (0 : ℝ) 1, ((u : ℂ) * x + (1 - u : ℂ) * y).re < 0 := by
    intro y hy u hu
    have : ((u : ℂ) * x + (1 - u : ℂ) * y).re = u * x.re + (1 - u) * y.re := by simp
    rw [this]; nlinarith [hu.1, hu.2]
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun y hy => (hT y hy).symm) ?_
  simp only [regCarlsonTIntegral, regCarlsonDirichletAverage_pair_eq, regEulerIntegral]
  refine Tendsto.const_mul _ ?_
  set K : ℝ → ℂ := fun u => (u : ℂ) ^ (β - 1) * (1 - u : ℂ) ^ (β' - 1)
  have hK : IntegrableOn K (Ioo 0 1) := by
    simpa [K] using integrableOn_eulerKernel_mul hβ hβ' (f := fun _ => 1) continuousOn_const
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖K u‖) ?_ ?_ hK.norm ?_
  · refine eventually_nhdsWithin_of_forall fun y hy => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro u hu
    have hK' : ContinuousWithinAt K (Ioo 0 1) u := by
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : (u : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hu.1
      have h2 : (1 - u : ℂ) ∈ slitPlane := by
        rw [show (1 - u : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring]
        exact ofReal_mem_slitPlane.mpr (by linarith [hu.2])
      exact ((continuousAt_cpow_const h1).comp continuous_ofReal.continuousAt).mul
        ((continuousAt_cpow_const h2).comp (f := fun v : ℝ => (1 - v : ℂ))
          (by fun_prop : Continuous fun v : ℝ => (1 - v : ℂ)).continuousAt)
    refine hK'.mul (ContinuousAt.continuousWithinAt ?_)
    have hne : (u : ℂ) * x + (1 - u : ℂ) * y ≠ 0 := fun h => by
      have := hre y hy.le u hu; rw [h] at this; simp at this
    unfold carlsonTKernel
    exact (continuous_exp.continuousAt).comp (((by fun_prop : Continuous fun u : ℝ =>
      (u : ℂ) * x + (1 - u : ℂ) * y).continuousAt).inv₀ hne)
  · refine eventually_nhdsWithin_of_forall fun y hy => ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_carlsonTKernel_le_one (hre y hy.le u hu))
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
    refine Tendsto.const_mul _ (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have hne : (u : ℂ) * x + (1 - u : ℂ) * 0 ≠ 0 := by
      have := hre 0 le_rfl u hu; intro h; rw [h] at this; simp at this
    unfold carlsonTKernel
    exact ((continuous_exp.continuousAt).comp ((by fun_prop : Continuous fun y : ℂ =>
      (u : ℂ) * x + (1 - u : ℂ) * y).continuousAt.inv₀ hne))

/-- A positive real base to a complex power, as an exponential. -/
private theorem ofReal_cpow_eq_exp' {q : ℝ} (hq : 0 < q) (c : ℂ) :
    ((q : ℝ) : ℂ) ^ c = exp (Real.log q * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← ofReal_log hq.le]

/-- **Formula (5.12-3)**: for `re β, re β' > 0` and real `x < 0`,
`T(β, β'; x, 0)/Γ(β + β') = e^{1/x} (-x)^{β'}/Γ(β) ∫₀^∞ (1 - t x)^{-β-β'} dλ_{β'}(t)`. -/
theorem regCarlsonTIntegral_pair_zero_eq {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) {x : ℝ}
    (hx : x < 0) :
    regCarlsonTIntegral (pair β β') (pair (x : ℂ) 0) =
      exp (1 / x) * ((-x : ℝ) : ℂ) ^ β' / Gamma β *
        ∫ t in Ioi (0 : ℝ), eulerDensity β' t * ((1 - t * x : ℝ) : ℂ) ^ (-(β + β')) := by
  simp only [regCarlsonTIntegral, regCarlsonDirichletAverage_pair_eq, regEulerIntegral]
  set F : ℝ → ℂ := fun u => (u : ℂ) ^ (β - 1) * (1 - u : ℂ) ^ (β' - 1) *
    carlsonTKernel ((u : ℂ) * x + (1 - u : ℂ) * 0)
  set g : ℝ → ℝ := fun t => (1 - t * x)⁻¹
  have hV : ∀ t : ℝ, 0 < t → 1 < 1 - t * x := fun t ht => by nlinarith
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt g (x / (1 - t * x) ^ 2) (Ioi 0) t := by
    intro t ht
    have hne : 1 - t * x ≠ 0 := by linarith [hV t ht]
    have := ((hasDerivAt_id t).mul_const x).const_sub 1 |>.inv hne
    convert this.hasDerivWithinAt using 1
    · funext s; simp [g]
    · simp
  have hinj : InjOn g (Ioi 0) := by
    intro a ha b hb hab
    have h1 := hV a ha; have h2 := hV b hb
    simp only [g] at hab
    have := inv_injective hab
    have hx' : x ≠ 0 := hx.ne
    nlinarith [mul_left_cancel₀ hx' (show x * a = x * b by linarith)]
  have himg : g '' Ioi 0 = Ioo 0 1 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have := hV t ht
      exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ this⟩
    · rintro ⟨hu0, hu1⟩
      refine ⟨(u⁻¹ - 1) / (-x), div_pos (sub_pos.mpr ((one_lt_inv₀ hu0).mpr hu1))
        (by linarith), ?_⟩
      simp only [g]
      rw [show 1 - (u⁻¹ - 1) / -x * x = u⁻¹ by field_simp [hx.ne]; ring, inv_inv]
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
  rw [himg] at hsub
  rw [hsub, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  have hV1 := hV t ht'
  have hVpos : 0 < 1 - t * x := by linarith
  have hu : 0 < g t := inv_pos.mpr hVpos
  have h1u : 0 < 1 - g t := by simp only [g]; rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hV1
  have hgt : g t * x = x / (1 - t * x) := by simp only [g]; ring
  simp only [F, eulerDensity, carlsonTKernel, real_smul]
  rw [show (1 - (g t : ℂ)) = ((1 - g t : ℝ) : ℂ) by push_cast; ring, mul_zero, add_zero,
    show (g t : ℂ) * x = ((g t * x : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp' hu, ofReal_cpow_eq_exp' h1u, ofReal_cpow_eq_exp' ht',
    ofReal_cpow_eq_exp' (by linarith : (0 : ℝ) < -x), ofReal_cpow_eq_exp' hVpos]
  have hlogu : Real.log (g t) = -Real.log (1 - t * x) := by simp only [g]; rw [Real.log_inv]
  have hlog1u : Real.log (1 - g t) = Real.log t + Real.log (-x) - Real.log (1 - t * x) := by
    have : 1 - g t = t * (-x) / (1 - t * x) := by simp only [g]; field_simp; ring
    rw [this, Real.log_div (mul_pos ht' (by linarith)).ne' hVpos.ne',
      Real.log_mul ht'.ne' (by linarith)]
  have habs : |x / (1 - t * x) ^ 2| = (-x) / (1 - t * x) ^ 2 := by
    rw [abs_div, abs_of_neg hx, abs_of_pos (by positivity)]
  have hinvu : (g t * x)⁻¹ = 1 / x - t := by
    rw [hgt]; field_simp [hx.ne, hVpos.ne']
  rw [habs, hlogu, hlog1u, show ((g t * x : ℝ) : ℂ)⁻¹ = ((1 / x - t : ℝ) : ℂ) by
    rw [← ofReal_inv, hinvu]]
  have hqR : -x / (1 - t * x) ^ 2 = Real.exp (Real.log (-x) - 2 * Real.log (1 - t * x)) := by
    rw [Real.exp_sub, Real.exp_log (by linarith), show (2 : ℝ) * Real.log (1 - t * x)
      = Real.log ((1 - t * x) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hq : ((-x / (1 - t * x) ^ 2 : ℝ) : ℂ) =
      exp (Real.log (-x) - 2 * Real.log (1 - t * x)) := by
    rw [hqR, ofReal_exp]; push_cast; ring_nf
  rw [hq]
  simp only [ofReal_sub, ofReal_neg, ofReal_div, ofReal_one, ofReal_add]
  have hG : Gamma β ≠ 0 := Gamma_ne_zero_of_re_pos hβ
  have hG' : Gamma β' ≠ 0 := Gamma_ne_zero_of_re_pos hβ'
  field_simp
  simp only [← exp_add]
  congr 1
  ring

/-- Formula (5.12-3) with Carlson's `₂F₀`: for `re β, re β' > 0` and real `x < 0`,
`T(β, β'; x, 0)/Γ(β + β') = e^{1/x} (-x)^{β'} ₂F₀(β + β', β'; x)/Γ(β)`. -/
theorem regCarlsonTIntegral_pair_zero_eq_carlson2F0 {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re)
    {x : ℝ} (hx : x < 0) :
    regCarlsonTIntegral (pair β β') (pair (x : ℂ) 0) =
      exp (1 / x) * ((-x : ℝ) : ℂ) ^ β' / Gamma β * carlson2F0 (β + β') β' x := by
  rw [regCarlsonTIntegral_pair_zero_eq hβ hβ' hx,
    carlson2F0_eq_integral (by simp only [add_re]; linarith) hβ' (by simpa using hx.le)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; ring_nf

end Carlson
