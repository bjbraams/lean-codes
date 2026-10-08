/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.TwoF0Sector
public import Carlson.R.ContourRepresentation
public import Carlson.S.Continuation
public import Carlson.S.Properties
public import Dirichlet.Transform.Euler
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Connection formulas between `S` and `₂F₀`

Carlson's Theorem 5.12-8 expresses the two-variable S-function through two `₂F₀` functions,
formula (5.12-18):
`S(β, β'; x, y)/Γ(β + β') = e^x (x - y)^{-β'} ₂F₀(1 - β, β'; 1/(x - y))/Γ(β)
  + e^y (y - x)^{-β} ₂F₀(1 - β', β; 1/(y - x))/Γ(β')`,
and Theorem 5.12-9 inverts it, formula (5.12-20):
`₂F₀(α, β; -1/x) = Γ(β - α)/Γ(β) x^α S(α, 1 - β; x, 0) + Γ(α - β)/Γ(α) x^β S(β, 1 - α; x, 0)`.
Both involve multivalued functions; here `x - y = e^ξ` and `x = e^η` fix the branches, and the
`₂F₀` values are those of `carlson2F0Sector` on the sector `|ph(-x)| < 3π/2`.

Carlson's proof of (5.12-18) writes `S/Γ(β + β')` as the Euler integral over `[0, 1]` of
`K(u) = e^{u d} u^{β-1} (1-u)^{β'-1}`, `d = x - y`, and replaces `[0, 1]` by the ray from `0`
minus the parallel ray from `1` in the direction `v = -1/d`, by Cauchy's integral theorem. Here
this step is proved without contours: for `λ ≥ 0` let `Φ(λ) = ∫₀¹ K(s + λ v) ds`. Then
`Φ'(λ) = v (K(1 + λ v) - K(λ v))` by differentiation under the integral and the fundamental
theorem of calculus in `s`, `Φ` is continuous at `0` by dominated convergence, and `Φ(λ) → 0`
as `λ → ∞`; the improper fundamental theorem of calculus gives the contour identity. The two
ray integrals are single Euler integrals of `₂F₀`, formula (5.12-7), which is extended from the
half-plane to `|ph(-x)| < π` by the identity theorem. The result, first proved for
`0 < re β, re β' < 1`, extends to all parameters and to the full sector by the identity theorem
in `(β, β', ξ)`.

Formula (5.12-20) follows from (5.12-18), the symmetry of `₂F₀` and the reflection formula,
first as an identity of entire functions multiplied by `sin(π(β - α))`.

## Main results

* `Carlson.carlson2F0Sector_eq_integral`: formula (5.12-7) for `|ph(-x)| < π`.
* `Carlson.intervalIntegral_eulerContourKernel`: the contour step of Carlson's proof.
* `Carlson.regCarlsonS_pair_eq_twoF0`: Theorem 5.12-8, formula (5.12-18), for all `β, β'`.
* `Carlson.sin_mul_carlson2F0Sector`: Theorem 5.12-9 as an identity of entire functions.
* `Carlson.carlson2F0Sector_eq_carlsonS`: Theorem 5.12-9, formula (5.12-20), for `α - β ∉ ℤ`.

## References

* `TauCeti.Analysis.SpecialFunctions.Pow.Complex` and `TauCeti.Analysis.SpecialFunctions.Beta`:
  the Tau Ceti contributors' `TauCeti.ofReal_mul_cpow` and
  `TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow`.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

open Complex MeasureTheory Filter Set
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson

/-- A crude bound for complex powers: `‖u^c‖ ≤ ‖u‖^{re c} e^{π |im c|}`. -/
theorem norm_cpow_le_mul_exp (u c : ℂ) : ‖u ^ c‖ ≤ ‖u‖ ^ c.re * Real.exp (π * |c.im|) := by
  refine (norm_cpow_le u c).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  calc -(arg u * c.im) ≤ |arg u * c.im| := neg_le_abs _
    _ = |arg u| * |c.im| := abs_mul _ _
    _ ≤ π * |c.im| := mul_le_mul_of_nonneg_right (abs_arg_le_pi u) (abs_nonneg _)

/-- For `t ≥ 0` and `|im ζ| < π`, `1 + t e^ζ` lies in the slit plane. -/
theorem one_add_mul_exp_mem_slitPlane {t : ℝ} (ht : 0 ≤ t) {ζ : ℂ} (hζ : |ζ.im| < π) :
    1 + (t : ℂ) * exp ζ ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases ht.lt_or_eq with ht | ht
  swap
  · left; subst ht; simp
  by_cases hs : Real.sin ζ.im = 0
  · left
    have h0 : ζ.im = 0 := by
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
      have hk' : |(k : ℝ)| * π < π := by
        rw [← hk] at hζ; rwa [abs_mul, abs_of_pos Real.pi_pos] at hζ
      have : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
      have : k = 0 := by
        have := abs_lt.mp this
        have h1 : (-1 : ℝ) < k := this.1
        have h2 : (k : ℝ) < 1 := this.2
        exact_mod_cast (show k = 0 by
          have := Int.cast_lt.mp (show ((-1 : ℤ) : ℝ) < k by exact_mod_cast h1)
          have := Int.cast_lt.mp (show (k : ℝ) < ((1 : ℤ) : ℝ) by exact_mod_cast h2)
          omega)
      rw [← hk, this]; simp
    simp only [add_re, one_re, re_ofReal_mul, exp_re, h0, Real.cos_zero, mul_one]
    positivity
  · right
    simp only [add_im, one_im, zero_add, im_ofReal_mul, exp_im]
    intro h
    rcases mul_eq_zero.mp h with h | h
    · exact ht.ne' h
    · exact hs ((mul_eq_zero.mp h).resolve_left (Real.exp_pos _).ne')

/-- A lower bound for `‖1 + t e^ζ‖` when `ph(t e^ζ)` stays away from `±π`. -/
theorem sin_le_norm_one_add_mul_exp {t : ℝ} (ht : 0 ≤ t) {δ : ℝ} (hδ : 0 ≤ δ) {ζ : ℂ}
    (hζ : |ζ.im| ≤ π - δ) : Real.sin δ ≤ ‖1 + (t : ℂ) * exp ζ‖ := by
  set r := t * Real.exp ζ.re
  have hr : 0 ≤ r := mul_nonneg ht (Real.exp_pos _).le
  have hcos : -Real.cos δ ≤ Real.cos ζ.im := by
    rw [← Real.cos_abs ζ.im, ← Real.cos_pi_sub]
    have hle : π - δ ≤ π := by linarith [abs_nonneg ζ.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hle hζ
  have hre : (1 + (t : ℂ) * exp ζ).re = 1 + r * Real.cos ζ.im := by
    simp [r, exp_re, mul_assoc]
  have him : (1 + (t : ℂ) * exp ζ).im = r * Real.sin ζ.im := by
    simp [r, exp_im, mul_assoc]
  have hsq : ‖1 + (t : ℂ) * exp ζ‖ ^ 2 = (1 + r * Real.cos ζ.im) ^ 2 + (r * Real.sin ζ.im) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, hre, him]; ring
  have h1 : Real.sin δ ^ 2 ≤ ‖1 + (t : ℂ) * exp ζ‖ ^ 2 := by
    rw [hsq]
    have h1 := Real.sin_sq_add_cos_sq ζ.im
    have h2 := Real.sin_sq_add_cos_sq δ
    have e : (1 + r * Real.cos ζ.im) ^ 2 + (r * Real.sin ζ.im) ^ 2 =
        1 + 2 * (r * Real.cos ζ.im) + r ^ 2 := by linear_combination r ^ 2 * h1
    have h3 := mul_le_mul_of_nonneg_left hcos hr
    nlinarith [sq_nonneg (r - Real.cos δ)]
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  linarith

/-- The complexified integrand of the single Euler integral (5.12-7). -/
def twoF0SingleIntegrand (a b : ℂ) (v : ℂ × ℂ) : ℂ :=
  (Gamma b)⁻¹ * (v.2 ^ (b - 1) * exp (-v.2)) * (1 + v.2 * exp v.1) ^ (-a)

/-- The complexified single integrand is analytic at positive real `t` for `|im ζ| < π`. -/
theorem analyticAt_twoF0SingleIntegrand (a b : ℂ) {ζ : ℂ} (hζ : |ζ.im| < π) {t : ℝ}
    (ht : 0 < t) : AnalyticAt ℂ (twoF0SingleIntegrand a b) (ζ, (t : ℂ)) := by
  have hs : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have h1 : AnalyticAt ℂ (fun v : ℂ × ℂ => v.1) (ζ, (t : ℂ)) := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun v : ℂ × ℂ => v.2) (ζ, (t : ℂ)) := analyticAt_snd
  unfold twoF0SingleIntegrand
  exact (analyticAt_const.mul ((h2.cpow analyticAt_const hs).mul h2.neg.cexp)).mul
    ((analyticAt_const.add (h2.mul h1.cexp)).cpow analyticAt_const
      (one_add_mul_exp_mem_slitPlane ht.le hζ))

set_option maxHeartbeats 1000000 in
/-- The single Euler integral `∫ (1 + t e^ζ)^{-a} dλ_b(t)` is holomorphic in `ζ` on the strip
`|im ζ| < π`. -/
theorem analyticOnNhd_twoF0SingleIntegral {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => ∫ t in Ioi (0 : ℝ), eulerDensity b t * (1 + t * exp ζ) ^ (-a))
      {ζ | |ζ.im| < π} := by
  set F : ℂ → ℝ → ℂ := fun ζ t => twoF0SingleIntegrand a b (ζ, (t : ℂ))
  have hF : ∀ ζ, (fun t : ℝ => eulerDensity b t * (1 + t * exp ζ) ^ (-a)) = F ζ := fun ζ => by
    funext t; simp [F, twoF0SingleIntegrand, eulerDensity]
  have hfun : (fun ζ : ℂ => ∫ t in Ioi (0 : ℝ), eulerDensity b t * (1 + t * exp ζ) ^ (-a)) =
      fun ζ => ∫ t, F ζ t ∂(volume.restrict (Ioi 0)) := by
    funext ζ; rw [hF ζ]
  rw [hfun]
  have hU : IsOpen {ζ : ℂ | |ζ.im| < π} := isOpen_lt (by fun_prop) continuous_const
  apply analyticOnNhd_integral_of_locally_dominated hU
  · intro ζ hζ
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((analyticAt_twoF0SingleIntegrand a b hζ ht).continuousAt.comp_of_eq
      (show ContinuousAt (fun s : ℝ => (ζ, (s : ℂ))) t by fun_prop) rfl).continuousWithinAt
  · intro ζ hζ
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have heq : ∀ t ∈ Ioi (0 : ℝ), fderiv ℂ (fun q => F q t) ζ =
        (fderiv ℂ (twoF0SingleIntegrand a b) (ζ, (t : ℂ))).comp
          (ContinuousLinearMap.inl ℂ ℂ ℂ) := fun t ht => by
      show fderiv ℂ (twoF0SingleIntegrand a b ∘ fun e => (e, (t : ℂ))) ζ = _
      exact ((analyticAt_twoF0SingleIntegrand a b hζ ht).differentiableAt.hasFDerivAt.comp ζ
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) ζ (t : ℂ))).fderiv
    refine ContinuousOn.congr ?_ heq
    intro t ht
    exact (((analyticAt_twoF0SingleIntegrand a b hζ ht).fderiv.continuousAt.comp_of_eq
      (show ContinuousAt (fun s : ℝ => (ζ, (s : ℂ))) t by fun_prop) rfl).clm_comp
        continuousAt_const).continuousWithinAt
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    intro ζ hζ
    exact (analyticAt_twoF0SingleIntegrand a b hζ ht).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  · intro ζ hζ
    set δ := (π - |ζ.im|) / 2
    have hδ : 0 < δ := by simp only [δ, mem_ofPred_eq] at hζ ⊢; linarith
    have hδπ : δ ≤ π := by simp only [δ]; linarith [abs_nonneg ζ.im, Real.pi_pos]
    have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by
      simp only [δ]; linarith [abs_nonneg ζ.im, Real.pi_pos])
    have hc : Continuous fun q : ℂ => |q.im| := by fun_prop
    have hev : ∀ᶠ q in 𝓝 ζ, |q.im| < π - δ := hc.continuousAt.eventually_lt_const (by
      simp only [δ, mem_ofPred_eq] at hζ ⊢; linarith)
    set K := Real.sin δ ^ (-a.re) * Real.exp (π * |(-a).im|)
    refine ⟨{q | |q.im| < π - δ}, fun t => K * ‖eulerDensity b t‖, hev, ?_, ?_⟩
    · exact ((integrableOn_eulerDensity hb).norm.const_mul K)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht q hq
      rw [← hF q, norm_mul, mul_comm K]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_cpow_le_mul_exp _ _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      simp only [neg_re]
      exact Real.rpow_le_rpow_of_nonpos hsin
        (sin_le_norm_one_add_mul_exp (le_of_lt ht) hδ.le (le_of_lt hq)) (by linarith)

/-- **Formula (5.12-7) on the sector `|ph(-x)| < π`**: for `re a, re b > 0`,
`₂F₀(a, b; -e^ζ) = ∫ (1 + t e^ζ)^{-a} dλ_b(t)`. -/
theorem carlson2F0Sector_eq_integral {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {ζ : ℂ}
    (hζ : |ζ.im| < π) :
    carlson2F0Sector a b ζ = ∫ t in Ioi (0 : ℝ), eulerDensity b t * (1 + t * exp ζ) ^ (-a) := by
  have hS : IsPreconnected {ζ : ℂ | |ζ.im| < π} := by
    apply Convex.isPreconnected
    intro u hu w hw s r hs hr hsr
    simp only [mem_ofPred_eq, add_im, smul_im, smul_eq_mul] at hu hw ⊢
    calc |s * u.im + r * w.im| ≤ s * |u.im| + r * |w.im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hr]
      _ < π := by
          rcases hs.lt_or_eq with hs' | hs'
          · have e1 := mul_lt_mul_of_pos_left hu hs'
            have e2 := mul_le_mul_of_nonneg_left hw.le hr
            have e3 : s * π + r * π = π := by rw [← add_mul, hsr, one_mul]
            linarith
          · subst hs'; simp only [zero_mul, zero_add] at hsr ⊢; subst hsr; simpa using hw
  have hf : AnalyticOnNhd ℂ (fun ζ => carlson2F0Sector a b ζ) {ζ : ℂ | |ζ.im| < π} :=
    fun ζ hζ => (analyticOnNhd_carlson2F0Sector (a, b, ζ)
      (show |ζ.im| < 3 * π / 2 by
        simp only [mem_ofPred_eq] at hζ; linarith [Real.pi_pos])).comp_of_eq
      (analyticAt_const.prod (analyticAt_const.prod analyticAt_id)) rfl
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_twoF0SingleIntegral ha hb) hS
    (show (0 : ℂ) ∈ {ζ : ℂ | |ζ.im| < π} by simp [Real.pi_pos]) (by
      have hc : Continuous fun q : ℂ => |q.im| := by fun_prop
      filter_upwards [hc.continuousAt.eventually_lt_const (show |(0 : ℂ).im| < π / 2 by
        simp [Real.pi_pos])] with q hq
      rw [carlson2F0Sector_eq_carlson2F0 _ _ hq]
      have hx : (-exp q).re ≤ 0 := by
        rw [neg_re, exp_re, neg_nonpos]
        exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [(abs_lt.mp hq).1], by linarith [(abs_lt.mp hq).2]⟩)
      rw [carlson2F0_eq_integral ha hb hx]
      simp only [mul_neg, sub_neg_eq_add])
  exact heq hζ

/-! ### The contour step in Carlson's proof of Theorem 5.12-8 -/

/-- The Euler kernel `e^{u d} u^{β-1} (1-u)^{β'-1}` of the two-variable S-function. -/
def eulerContourKernel (β β' d : ℂ) (u : ℂ) : ℂ :=
  exp (u * d) * u ^ (β - 1) * (1 - u) ^ (β' - 1)

/-- A distance estimate for points on a line in direction `v`: `|a| |im v| ≤ ‖a + λ v‖ ‖v‖`. -/
theorem abs_mul_abs_im_le (a μ : ℝ) (v : ℂ) : |a| * |v.im| ≤ ‖(a : ℂ) + μ * v‖ * ‖v‖ := by
  have h : ((a : ℂ) + μ * v) * (starRingEnd ℂ) v = a * (starRingEnd ℂ) v + μ * normSq v := by
    rw [add_mul, mul_assoc, mul_conj]
  have him : (((a : ℂ) + μ * v) * (starRingEnd ℂ) v).im = -(a * v.im) := by
    rw [h]; simp
  calc |a| * |v.im| = |(((a : ℂ) + μ * v) * (starRingEnd ℂ) v).im| := by rw [him, abs_neg, abs_mul]
    _ ≤ ‖((a : ℂ) + μ * v) * (starRingEnd ℂ) v‖ := abs_im_le_norm _
    _ = ‖(a : ℂ) + μ * v‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

/-- The imaginary part bounds the distance from the real axis: `|μ| |im v| ≤ ‖a + μ v‖`. -/
theorem abs_mul_abs_im_le' (a μ : ℝ) (v : ℂ) : |μ| * |v.im| ≤ ‖(a : ℂ) + μ * v‖ := by
  have : ((a : ℂ) + μ * v).im = μ * v.im := by simp
  calc |μ| * |v.im| = |((a : ℂ) + μ * v).im| := by rw [this, abs_mul]
    _ ≤ _ := abs_im_le_norm _

/-- The domain of holomorphy of the Euler kernel. -/
def eulerContourDomain : Set ℂ := {u | u ∈ slitPlane ∧ 1 - u ∈ slitPlane}

/-- Points off the real axis lie in the domain of the Euler kernel. -/
theorem mem_eulerContourDomain_of_im_ne {u : ℂ} (hu : u.im ≠ 0) : u ∈ eulerContourDomain :=
  ⟨mem_slitPlane_iff.mpr (Or.inr hu), mem_slitPlane_iff.mpr (Or.inr (by simpa using hu))⟩

/-- Points of the open unit interval lie in the domain of the Euler kernel. -/
theorem mem_eulerContourDomain_of_mem_Ioo {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (s : ℂ) ∈ eulerContourDomain :=
  ⟨ofReal_mem_slitPlane.mpr hs.1, by
    rw [show (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith [hs.2])⟩

/-- The domain of the Euler kernel is open. -/
theorem isOpen_eulerContourDomain : IsOpen eulerContourDomain :=
  isOpen_slitPlane.inter (isOpen_slitPlane.preimage (by fun_prop))

/-- The Euler kernel is holomorphic on its domain. -/
theorem analyticOnNhd_eulerContourKernel (β β' d : ℂ) :
    AnalyticOnNhd ℂ (eulerContourKernel β β' d) eulerContourDomain := fun u hu => by
  unfold eulerContourKernel
  exact ((analyticAt_id.mul analyticAt_const).cexp.mul
      (analyticAt_id.cpow analyticAt_const hu.1)).mul
    ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hu.2)

/-- A pointwise bound for the Euler kernel. -/
theorem norm_eulerContourKernel_le (β β' d u : ℂ) :
    ‖eulerContourKernel β β' d u‖ ≤ Real.exp (u * d).re * ‖u‖ ^ (β.re - 1) *
      ‖1 - u‖ ^ (β'.re - 1) * Real.exp (π * (|β.im| + |β'.im|)) := by
  unfold eulerContourKernel
  rw [norm_mul, norm_mul, norm_exp]
  have h1 := norm_cpow_le_mul_exp u (β - 1)
  have h2 := norm_cpow_le_mul_exp (1 - u) (β' - 1)
  simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h1 h2
  have e := (Real.exp_pos (u * d).re).le
  calc Real.exp (u * d).re * ‖u ^ (β - 1)‖ * ‖(1 - u) ^ (β' - 1)‖
      ≤ Real.exp (u * d).re * (‖u‖ ^ (β.re - 1) * Real.exp (π * |β.im|)) *
          (‖1 - u‖ ^ (β'.re - 1) * Real.exp (π * |β'.im|)) := by
        gcongr
    _ = _ := by rw [mul_add, Real.exp_add]; ring

/-- The Euler kernel is measurable. -/
theorem measurable_eulerContourKernel (β β' d : ℂ) : Measurable (eulerContourKernel β β' d) := by
  unfold eulerContourKernel; fun_prop

/-- Bound on the ray from `0`: `‖K(μ v)‖ ≤ M μ^{re β - 1} e^{-μ}`. -/
theorem norm_eulerContourKernel_ray_le {β β' d v : ℂ} (hβ'1 : β'.re < 1) (hv : v.im ≠ 0)
    (hvd : v * d = -1) {μ : ℝ} (hμ : 0 < μ) :
    ‖eulerContourKernel β β' d (μ * v)‖ ≤
      (‖v‖ ^ (β.re - 1) * (|v.im| / ‖v‖) ^ (β'.re - 1) * Real.exp (π * (|β.im| + |β'.im|))) *
        (μ ^ (β.re - 1) * Real.exp (-μ)) := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hc0 : 0 < |v.im| / ‖v‖ := div_pos (abs_pos.mpr hv) hnv
  have h1 : |v.im| / ‖v‖ ≤ ‖1 - μ * v‖ := by
    have := abs_mul_abs_im_le 1 (-μ) v
    rw [abs_one, one_mul] at this
    rw [div_le_iff₀ hnv]
    simpa [sub_eq_add_neg] using this
  have h2 := Real.rpow_le_rpow_of_nonpos hc0 h1 (by linarith : β'.re - 1 ≤ 0)
  have := Real.exp_pos (-μ)
  have := Real.rpow_nonneg hμ.le (β.re - 1)
  have := Real.rpow_nonneg hnv.le (β.re - 1)
  have := Real.exp_pos (π * (|β.im| + |β'.im|))
  calc _ ≤ _ := norm_eulerContourKernel_le β β' d _
    _ = Real.exp (-μ) * (μ ^ (β.re - 1) * ‖v‖ ^ (β.re - 1)) * ‖1 - μ * v‖ ^ (β'.re - 1) *
          Real.exp (π * (|β.im| + |β'.im|)) := by
      rw [show (μ : ℂ) * v * d = -(μ : ℂ) by rw [mul_assoc, hvd]; ring, neg_re, ofReal_re,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ.le, Real.mul_rpow hμ.le hnv.le]
    _ ≤ Real.exp (-μ) * (μ ^ (β.re - 1) * ‖v‖ ^ (β.re - 1)) * (|v.im| / ‖v‖) ^ (β'.re - 1) *
          Real.exp (π * (|β.im| + |β'.im|)) := by gcongr
    _ = _ := by ring

/-- Bound on the ray from `1`: `‖K(1 + μ v)‖ ≤ M μ^{re β' - 1} e^{-μ}`. -/
theorem norm_eulerContourKernel_ray_one_le {β β' d v : ℂ} (hβ1 : β.re < 1) (hv : v.im ≠ 0)
    (hvd : v * d = -1) {μ : ℝ} (hμ : 0 < μ) :
    ‖eulerContourKernel β β' d (1 + μ * v)‖ ≤
      (Real.exp d.re * (|v.im| / ‖v‖) ^ (β.re - 1) * ‖v‖ ^ (β'.re - 1) *
        Real.exp (π * (|β.im| + |β'.im|))) * (μ ^ (β'.re - 1) * Real.exp (-μ)) := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hc0 : 0 < |v.im| / ‖v‖ := div_pos (abs_pos.mpr hv) hnv
  have h1 : |v.im| / ‖v‖ ≤ ‖1 + μ * v‖ := by
    have := abs_mul_abs_im_le 1 μ v
    rw [abs_one, one_mul] at this
    rw [div_le_iff₀ hnv]
    simpa using this
  have h2 := Real.rpow_le_rpow_of_nonpos hc0 h1 (by linarith : β.re - 1 ≤ 0)
  have := Real.exp_pos (-μ)
  have := Real.exp_pos d.re
  have := Real.rpow_nonneg hμ.le (β'.re - 1)
  have := Real.rpow_nonneg hnv.le (β'.re - 1)
  have := Real.exp_pos (π * (|β.im| + |β'.im|))
  calc _ ≤ _ := norm_eulerContourKernel_le β β' d _
    _ = Real.exp d.re * Real.exp (-μ) * ‖1 + μ * v‖ ^ (β.re - 1) *
          (μ ^ (β'.re - 1) * ‖v‖ ^ (β'.re - 1)) * Real.exp (π * (|β.im| + |β'.im|)) := by
      rw [show (1 + (μ : ℂ) * v) * d = d + -(μ : ℂ) by rw [add_mul, one_mul, mul_assoc, hvd]; ring,
        add_re, neg_re, ofReal_re, Real.exp_add, show (1 : ℂ) - (1 + μ * v) = -(μ * v) by ring,
        norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ.le,
        Real.mul_rpow hμ.le hnv.le]
    _ ≤ Real.exp d.re * Real.exp (-μ) * (|v.im| / ‖v‖) ^ (β.re - 1) *
          (μ ^ (β'.re - 1) * ‖v‖ ^ (β'.re - 1)) * Real.exp (π * (|β.im| + |β'.im|)) := by gcongr
    _ = _ := by ring

/-- The majorant `μ^{c-1} e^{-μ}` is integrable on `(0, ∞)` for `c > 0`. -/
theorem integrableOn_rpow_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun μ : ℝ => μ ^ (c - 1) * Real.exp (-μ)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c - 1) (b := 1) (by linarith)
    one_pos one_pos
  simpa using this

/-- The kernel along the ray from `0` is integrable. -/
theorem integrableOn_eulerContourKernel_ray {β β' d v : ℂ} (hβ0 : 0 < β.re) (hβ'1 : β'.re < 1)
    (hv : v.im ≠ 0) (hvd : v * d = -1) :
    IntegrableOn (fun μ : ℝ => eulerContourKernel β β' d (μ * v)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg hβ0).const_mul
    (‖v‖ ^ (β.re - 1) * (|v.im| / ‖v‖) ^ (β'.re - 1) * Real.exp (π * (|β.im| + |β'.im|))))
    ((measurable_eulerContourKernel β β' d).comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with μ hμ
  exact norm_eulerContourKernel_ray_le hβ'1 hv hvd hμ

/-- The kernel along the ray from `1` is integrable. -/
theorem integrableOn_eulerContourKernel_ray_one {β β' d v : ℂ} (hβ1 : β.re < 1) (hβ'0 : 0 < β'.re)
    (hv : v.im ≠ 0) (hvd : v * d = -1) :
    IntegrableOn (fun μ : ℝ => eulerContourKernel β β' d (1 + μ * v)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg hβ'0).const_mul
    (Real.exp d.re * (|v.im| / ‖v‖) ^ (β.re - 1) * ‖v‖ ^ (β'.re - 1) *
      Real.exp (π * (|β.im| + |β'.im|))))
    ((measurable_eulerContourKernel β β' d).comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with μ hμ
  exact norm_eulerContourKernel_ray_one_le hβ1 hv hvd hμ

/-- The function `λ ↦ ∫₀¹ K(s + λ v) ds` whose variation gives Carlson's contour step. -/
def eulerContourPhi (β β' d v : ℂ) (μ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, eulerContourKernel β β' d ((s : ℂ) + μ * v)

/-- `Φ` is continuous at `0`, where the segment touches the singular endpoints. -/
theorem continuousAt_eulerContourPhi {β β' d v : ℂ} (hβ0 : 0 < β.re) (hβ1 : β.re < 1)
    (hβ'0 : 0 < β'.re) (hβ'1 : β'.re < 1) (hv : v.im ≠ 0) :
    ContinuousAt (eulerContourPhi β β' d v) 0 := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set c₀ := |v.im| / ‖v‖
  have hc0 : 0 < c₀ := div_pos (abs_pos.mpr hv) hnv
  set C := Real.exp ((1 + ‖v‖) * ‖d‖) * Real.exp (π * (|β.im| + |β'.im|))
  set bound : ℝ → ℝ := fun s => C * (c₀ ^ (β.re - 1) * c₀ ^ (β'.re - 1)) *
    (s ^ (β.re - 1) * (1 - s) ^ (β'.re - 1))
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := bound)
  · exact Eventually.of_forall fun x =>
      ((measurable_eulerContourKernel β β' d).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with x hx
    filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hs
    have hs' : s ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1, lt_of_le_of_ne hs.2 (by simpa using hs1)⟩
    have hxv : ‖(x : ℂ) * v‖ ≤ ‖v‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    have hu : ‖(s : ℂ) + x * v‖ ≤ 1 + ‖v‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ hxv)
      rw [Complex.norm_real, Real.norm_of_nonneg hs'.1.le]; exact hs'.2.le
    have hl1 : c₀ * s ≤ ‖(s : ℂ) + x * v‖ := by
      have := abs_mul_abs_im_le s x v
      rw [abs_of_pos hs'.1] at this
      simp only [c₀, div_mul_eq_mul_div, div_le_iff₀ hnv]; linarith
    have hl2 : c₀ * (1 - s) ≤ ‖1 - ((s : ℂ) + x * v)‖ := by
      have := abs_mul_abs_im_le (1 - s) (-x) v
      rw [abs_of_pos (by linarith [hs'.2] : (0 : ℝ) < 1 - s)] at this
      rw [show (1 : ℂ) - ((s : ℂ) + x * v) = ((1 - s : ℝ) : ℂ) + (-x : ℝ) * v by push_cast; ring]
      simp only [c₀, div_mul_eq_mul_div, div_le_iff₀ hnv]; linarith
    have hp1 := Real.rpow_le_rpow_of_nonpos (mul_pos hc0 hs'.1) hl1 (by linarith : β.re - 1 ≤ 0)
    have hp2 := Real.rpow_le_rpow_of_nonpos (mul_pos hc0 (by linarith [hs'.2] : (0 : ℝ) < 1 - s))
      hl2 (by linarith : β'.re - 1 ≤ 0)
    have he : Real.exp (((s : ℂ) + x * v) * d).re ≤ Real.exp ((1 + ‖v‖) * ‖d‖) := by
      apply Real.exp_le_exp.mpr
      calc (((s : ℂ) + x * v) * d).re ≤ ‖((s : ℂ) + x * v) * d‖ := re_le_norm _
        _ = ‖(s : ℂ) + x * v‖ * ‖d‖ := norm_mul _ _
        _ ≤ (1 + ‖v‖) * ‖d‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    refine (norm_eulerContourKernel_le β β' d _).trans ?_
    simp only [bound, C]
    rw [Real.mul_rpow hc0.le hs'.1.le] at hp1
    rw [Real.mul_rpow hc0.le (by linarith [hs'.2])] at hp2
    have := Real.rpow_nonneg (norm_nonneg ((s : ℂ) + x * v)) (β.re - 1)
    have := Real.rpow_nonneg (norm_nonneg (1 - ((s : ℂ) + x * v))) (β'.re - 1)
    have := Real.exp_pos (((s : ℂ) + x * v) * d).re
    have := Real.exp_pos (π * (|β.im| + |β'.im|))
    have := Real.rpow_nonneg hc0.le (β.re - 1)
    have := Real.rpow_nonneg hs'.1.le (β.re - 1)
    have := Real.exp_pos ((1 + ‖v‖) * ‖d‖)
    calc _ ≤ Real.exp ((1 + ‖v‖) * ‖d‖) * (c₀ ^ (β.re - 1) * s ^ (β.re - 1)) *
          (c₀ ^ (β'.re - 1) * (1 - s) ^ (β'.re - 1)) * Real.exp (π * (|β.im| + |β'.im|)) := by
          gcongr
      _ = _ := by ring
  · exact (TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow hβ0 hβ'0 (by simp)
      (by simp)).const_mul _
  · filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hs
    have hs' : s ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1, lt_of_le_of_ne hs.2 (by simpa using hs1)⟩
    have hK := (analyticOnNhd_eulerContourKernel β β' d _
      (mem_eulerContourDomain_of_mem_Ioo hs')).continuousAt
    have hm : ContinuousAt (fun x : ℝ => (s : ℂ) + x * v) 0 := by fun_prop
    exact hK.comp_of_eq hm (by simp)

/-- Off the real axis the points `s + μ v` lie in the kernel's domain. -/
theorem mem_eulerContourDomain_add {v : ℂ} (hv : v.im ≠ 0) (s : ℝ) {μ : ℝ} (hμ : μ ≠ 0) :
    (s : ℂ) + μ * v ∈ eulerContourDomain :=
  mem_eulerContourDomain_of_im_ne (by simp [hμ, hv])

/-- The derivative of `Φ` for `μ ≠ 0`: `Φ'(μ) = v (K(1 + μ v) - K(μ v))`. -/
theorem hasDerivAt_eulerContourPhi {β β' d v : ℂ} (hv : v.im ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    HasDerivAt (eulerContourPhi β β' d v)
      (v * (eulerContourKernel β β' d (1 + μ * v) - eulerContourKernel β β' d (μ * v))) μ := by
  set K := eulerContourKernel β β' d
  have hKa := analyticOnNhd_eulerContourKernel β β' d
  set ε := |μ| / 2
  have hε : 0 < ε := by simp only [ε]; positivity
  have hne : ∀ x ∈ Metric.closedBall μ ε, x ≠ 0 := fun x hx h => by
    subst h
    rw [Metric.mem_closedBall, Real.dist_eq, zero_sub, abs_neg] at hx
    simp only [ε] at hx
    linarith [abs_pos.mpr hμ]
  -- a bound for `deriv K` on the compact image of `[0,1] × closedBall μ ε`
  set C : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * v) '' (Icc 0 1 ×ˢ Metric.closedBall μ ε)
  have hC : IsCompact C := (isCompact_Icc.prod (isCompact_closedBall μ ε)).image (by fun_prop)
  have hCsub : C ⊆ eulerContourDomain := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_eulerContourDomain_add hv p.1 (hne p.2 hp.2)
  have hdc : ContinuousOn (deriv K) C :=
    (hKa.deriv.continuousOn).mono hCsub
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hdc
  have hderivK : ∀ (s : ℝ) (x : ℝ), x ≠ 0 →
      HasDerivAt (fun y : ℝ => K ((s : ℂ) + y * v)) (deriv K ((s : ℂ) + x * v) * v) x := by
    intro s x hx
    have hK := (hKa _ (mem_eulerContourDomain_add hv s hx)).differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun z : ℂ => (s : ℂ) + z * v) v (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const v).const_add (s : ℂ)
    exact (hK.comp (x : ℂ) hl).comp_ofReal
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (a := 0) (b := 1) (x₀ := μ)
    (F := fun (x : ℝ) (s : ℝ) => K ((s : ℂ) + (x : ℂ) * v))
    (F' := fun (x : ℝ) (s : ℝ) => deriv K ((s : ℂ) + (x : ℂ) * v) * v)
    (bound := fun _ => M * ‖v‖) (s := Metric.ball μ ε) (Metric.ball_mem_nhds μ hε)
    (Eventually.of_forall fun x =>
      ((measurable_eulerContourKernel β β' d).comp (by fun_prop)).aestronglyMeasurable)
    (by
      refine ContinuousOn.intervalIntegrable fun s _ => ?_
      exact ((hKa _ (mem_eulerContourDomain_add hv s hμ)).continuousAt.comp_of_eq
        (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + μ * v) s) rfl).continuousWithinAt)
    (((measurable_deriv K).comp (by fun_prop)).mul_const v).aestronglyMeasurable
    (Eventually.of_forall fun s hs x hx => by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right (hM _ ⟨(s, x), ⟨?_, Metric.ball_subset_closedBall hx⟩, rfl⟩)
        (norm_nonneg _)
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun s _ x hx => hderivK s x (hne x (Metric.ball_subset_closedBall hx)))
  have hval : ∫ s in (0 : ℝ)..1, deriv K ((s : ℂ) + μ * v) * v =
      v * (K (1 + μ * v) - K (μ * v)) := by
    rw [intervalIntegral.integral_mul_const, mul_comm]
    congr 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => K ((s : ℂ) + μ * v)) (f' := fun s => deriv K ((s : ℂ) + μ * v))
      (a := 0) (b := 1) (fun s _ => by
        have hK := (hKa _ (mem_eulerContourDomain_add hv s hμ)).differentiableAt.hasDerivAt
        have hl : HasDerivAt (fun z : ℂ => z + μ * v) 1 (s : ℂ) := (hasDerivAt_id _).add_const _
        simpa using (hK.comp (s : ℂ) hl).comp_ofReal)
      (ContinuousOn.intervalIntegrable fun s _ =>
        ((hKa.deriv _ (mem_eulerContourDomain_add hv s hμ)).continuousAt.comp_of_eq
          (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + μ * v) s) rfl).continuousWithinAt)
    simpa using this
  rw [← hval]
  exact hmain.2

/-- `Φ(μ) → 0` as `μ → ∞`, when `v d = -1`. -/
theorem tendsto_eulerContourPhi_atTop {β β' d v : ℂ} (hβ1 : β.re < 1) (hβ'1 : β'.re < 1)
    (hv : v.im ≠ 0) (hvd : v * d = -1) :
    Tendsto (eulerContourPhi β β' d v) atTop (𝓝 0) := by
  set c := |v.im|
  have hc : 0 < c := abs_pos.mpr hv
  set C := Real.exp ‖d‖ * c ^ (β.re - 1) * c ^ (β'.re - 1) * Real.exp (π * (|β.im| + |β'.im|))
  have hbound : ∀ μ : ℝ, 1 ≤ μ → ‖eulerContourPhi β β' d v μ‖ ≤ C * Real.exp (-μ) := by
    intro μ hμ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := C * Real.exp (-μ)) (f := fun s : ℝ => eulerContourKernel β β' d ((s : ℂ) + μ * v))
      (fun s hs => by
        rw [uIoc_of_le zero_le_one] at hs
        refine (norm_eulerContourKernel_le β β' d _).trans ?_
        have hl1 : c ≤ ‖(s : ℂ) + μ * v‖ := by
          have := abs_mul_abs_im_le' s μ v
          rw [abs_of_pos (by linarith)] at this
          nlinarith
        have hl2 : c ≤ ‖1 - ((s : ℂ) + μ * v)‖ := by
          have := abs_mul_abs_im_le' (1 - s) (-μ) v
          rw [abs_neg, abs_of_pos (by linarith)] at this
          rw [show (1 : ℂ) - ((s : ℂ) + μ * v) = ((1 - s : ℝ) : ℂ) + (-μ : ℝ) * v by
            push_cast; ring]
          nlinarith
        have hp1 := Real.rpow_le_rpow_of_nonpos hc hl1 (by linarith : β.re - 1 ≤ 0)
        have hp2 := Real.rpow_le_rpow_of_nonpos hc hl2 (by linarith : β'.re - 1 ≤ 0)
        have he : Real.exp (((s : ℂ) + μ * v) * d).re ≤ Real.exp ‖d‖ * Real.exp (-μ) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [show ((s : ℂ) + μ * v) * d = s * d + -(μ : ℂ) by rw [add_mul, mul_assoc, hvd]; ring,
            add_re, neg_re, ofReal_re, re_ofReal_mul]
          have h1 := abs_re_le_norm d
          have h2 : s * d.re ≤ s * |d.re| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.1.le
          have h3 : s * |d.re| ≤ |d.re| := mul_le_of_le_one_left (abs_nonneg _) hs.2
          linarith
        have := Real.rpow_nonneg (norm_nonneg ((s : ℂ) + μ * v)) (β.re - 1)
        have := Real.rpow_nonneg (norm_nonneg (1 - ((s : ℂ) + μ * v))) (β'.re - 1)
        have := Real.exp_pos (((s : ℂ) + μ * v) * d).re
        have := Real.exp_pos (π * (|β.im| + |β'.im|))
        have := Real.rpow_nonneg hc.le (β.re - 1)
        have := Real.exp_pos ‖d‖
        have := Real.exp_pos (-μ)
        calc _ ≤ Real.exp ‖d‖ * Real.exp (-μ) * c ^ (β.re - 1) * c ^ (β'.re - 1) *
              Real.exp (π * (|β.im| + |β'.im|)) := by gcongr
          _ = _ := by simp only [C]; ring)
    simpa [eulerContourPhi] using h
  have hlim : Tendsto (fun μ : ℝ => C * Real.exp (-μ)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero_norm' (eventually_atTop.mpr ⟨1, hbound⟩) hlim

/-- **Carlson's contour step in Theorem 5.12-8**: for `0 < re β, re β' < 1`, `im v ≠ 0` and
`v d = -1`, the integral over `[0, 1]` of `e^{u d} u^{β-1} (1-u)^{β'-1}` equals the integral
along the ray from `0` in direction `v` minus the integral along the parallel ray from `1`. -/
theorem intervalIntegral_eulerContourKernel {β β' d v : ℂ} (hβ0 : 0 < β.re) (hβ1 : β.re < 1)
    (hβ'0 : 0 < β'.re) (hβ'1 : β'.re < 1) (hv : v.im ≠ 0) (hvd : v * d = -1) :
    ∫ s in (0 : ℝ)..1, eulerContourKernel β β' d s =
      v * (∫ μ in Ioi (0 : ℝ), eulerContourKernel β β' d (μ * v)) -
        v * ∫ μ in Ioi (0 : ℝ), eulerContourKernel β β' d (1 + μ * v) := by
  have I1 := integrableOn_eulerContourKernel_ray hβ0 hβ'1 hv hvd
  have I2 := integrableOn_eulerContourKernel_ray_one hβ1 hβ'0 hv hvd
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (f := eulerContourPhi β β' d v)
    (f' := fun μ : ℝ => v * (eulerContourKernel β β' d (1 + μ * v) -
      eulerContourKernel β β' d (μ * v)))
    (continuousAt_eulerContourPhi hβ0 hβ1 hβ'0 hβ'1 hv).continuousWithinAt
    (fun μ hμ => hasDerivAt_eulerContourPhi hv (ne_of_gt hμ))
    ((I2.sub I1).const_mul v) (tendsto_eulerContourPhi_atTop hβ1 hβ'1 hv hvd)
  rw [MeasureTheory.integral_const_mul, integral_sub I2 I1, zero_sub] at h
  have h0 : eulerContourPhi β β' d v 0 = ∫ s in (0 : ℝ)..1, eulerContourKernel β β' d s := by
    simp [eulerContourPhi]
  rw [← h0]
  linear_combination h

/-! ### Theorem 5.12-8 -/

/-- `e^{iεπ} = -1` for `ε = ±1`. -/
theorem exp_mul_pi_I_of_sign {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : exp ((ε * π : ℝ) * I) = -1 := by
  rcases hε with rfl | rfl
  · simp [exp_pi_mul_I]
  · simp [neg_mul, exp_neg, exp_pi_mul_I]

/-- The regularized S-function with two parameters as the Euler integral of the contour kernel. -/
theorem regCarlsonS_pair_eq_intervalIntegral {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) (d : ℂ) :
    regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair d 0) =
      (Gamma β * Gamma β')⁻¹ * ∫ s in (0 : ℝ)..1, eulerContourKernel β β' d s := by
  have hb : TwoVariable.pair β β' ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i
    · exact hβ
    · exact hβ'
  rw [regCarlsonS_eq_integral hb, regCarlsonSIntegral,
    TwoVariable.regCarlsonDirichletAverage_pair_eq, Dirichlet.regEulerIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
  simp only [eulerContourKernel, mul_zero, add_zero]
  ring_nf

/-- **Theorem 5.12-8, base case**: for `0 < re β, re β' < 1`, `x - y = e^ξ` with
`0 < ε im ξ < π` (`ε = ±1`), so that `ph(y - x) = im ξ - επ`, the two-variable S-function is
the sum of two `₂F₀` terms. -/
theorem regCarlsonS_pair_eq_twoF0_base {β β' : ℂ} (hβ0 : 0 < β.re) (hβ1 : β.re < 1)
    (hβ'0 : 0 < β'.re) (hβ'1 : β'.re < 1) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ξ : ℂ}
    (hξ0 : 0 < ε * ξ.im) (hξ1 : ε * ξ.im < π) :
    regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair (exp ξ) 0) =
      exp (exp ξ) * exp (-(β' * ξ)) * (Gamma β)⁻¹ *
          carlson2F0Sector (1 - β) β' (-ξ + (ε * π : ℝ) * I) +
        exp (-(β * (ξ - (ε * π : ℝ) * I))) * (Gamma β')⁻¹ * carlson2F0Sector (1 - β') β (-ξ) := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have habs : |ξ.im| < π ∧ 0 < |ξ.im| := by
    rcases hε with rfl | rfl
    · simp only [one_mul] at hξ0 hξ1; rw [abs_of_pos hξ0]; exact ⟨hξ1, hξ0⟩
    · simp only [neg_mul, one_mul] at hξ0 hξ1
      rw [abs_of_neg (by linarith)]; constructor <;> linarith
  set d := exp ξ
  set v := -exp (-ξ)
  set ζ₁ : ℂ := -ξ + (ε * π : ℝ) * I
  have hvexp : v = exp ζ₁ := by
    rw [show ζ₁ = -ξ + (ε * π : ℝ) * I from rfl, exp_add, exp_mul_pi_I_of_sign hε]; ring
  have hvd : v * d = -1 := by simp only [v, d]; rw [neg_mul, ← exp_add]; simp
  have hvim : v.im ≠ 0 := by
    simp only [v, neg_im, exp_im, neg_im, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    refine ⟨(Real.exp_pos _).ne', ?_⟩
    rw [Real.sin_neg, neg_eq_zero]
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hk' : |(k : ℝ)| * π < π ∧ 0 < |(k : ℝ)| * π := by
      rw [← abs_of_pos Real.pi_pos, ← abs_mul, hk, abs_of_pos Real.pi_pos]; exact habs
    have h1 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have h2 : 0 < |(k : ℝ)| := by nlinarith [Real.pi_pos]
    have : k = 0 := by
      have := abs_lt.mp h1
      have a1 := Int.cast_lt.mp (show ((-1 : ℤ) : ℝ) < k by exact_mod_cast this.1)
      have a2 := Int.cast_lt.mp (show (k : ℝ) < ((1 : ℤ) : ℝ) by exact_mod_cast this.2)
      omega
    subst this; simp at h2
  have hv0 : v ≠ 0 := fun h => hvim (by simp [h])
  have hζ₁ : |ζ₁.im| < π := by
    simp only [ζ₁, add_im, neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero]
    rcases hε with rfl | rfl
    · simp only [one_mul] at hξ0 hξ1 ⊢; rw [abs_lt]; constructor <;> linarith
    · simp only [neg_mul, one_mul] at hξ0 hξ1 ⊢; rw [abs_lt]; constructor <;> linarith
  have hζ₂ : |(-ξ).im| < π := by simpa using habs.1
  have hlogv : log v = ζ₁ := by
    rw [hvexp, log_exp]
    · linarith [(abs_lt.mp hζ₁).1]
    · exact (abs_lt.mp hζ₁).2.le
  have hlogξ : log (exp (-ξ)) = -ξ := log_exp (by linarith [(abs_lt.mp hζ₂).1]) (abs_lt.mp hζ₂).2.le
  have hΓ : Gamma β ≠ 0 := Gamma_ne_zero_of_re_pos hβ0
  have hΓ' : Gamma β' ≠ 0 := Gamma_ne_zero_of_re_pos hβ'0
  -- the ray from `0`
  have hray1 : ∫ μ in Ioi (0 : ℝ), eulerContourKernel β β' d (μ * v) =
      Gamma β * v ^ (β - 1) * carlson2F0Sector (1 - β') β (-ξ) := by
    rw [carlson2F0Sector_eq_integral (by simp; linarith) hβ0 hζ₂,
        ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun μ hμ => ?_
    simp only [eulerContourKernel, eulerDensity]
    rw [TauCeti.ofReal_mul_cpow hμ.le _,
      show (μ : ℂ) * v * d = -(μ : ℂ) by rw [mul_assoc, hvd]; ring,
      show (1 : ℂ) - μ * v = 1 + μ * exp (-ξ) by simp [v], show -(1 - β') = β' - 1 by ring]
    field_simp
  -- the ray from `1`
  have hray2 : ∫ μ in Ioi (0 : ℝ), eulerContourKernel β β' d (1 + μ * v) =
      exp d * Gamma β' * exp (-ξ) ^ (β' - 1) * carlson2F0Sector (1 - β) β' ζ₁ := by
    rw [carlson2F0Sector_eq_integral (by simp; linarith) hβ'0 hζ₁,
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun μ hμ => ?_
    simp only [eulerContourKernel, eulerDensity]
    rw [show (1 + (μ : ℂ) * v) * d = d + -(μ : ℂ) by rw [add_mul, one_mul, mul_assoc, hvd]; ring,
      show (1 : ℂ) - (1 + μ * v) = μ * exp (-ξ) by simp [v], TauCeti.ofReal_mul_cpow hμ.le _,
      ← hvexp, show -(1 - β) = β - 1 by ring, exp_add]
    field_simp
  have hmain := intervalIntegral_eulerContourKernel hβ0 hβ1 hβ'0 hβ'1 hvim hvd
  rw [hray1, hray2] at hmain
  rw [regCarlsonS_pair_eq_intervalIntegral hβ0 hβ'0, hmain]
  have hvβ : v * v ^ (β - 1) = exp (-(β * (ξ - (ε * π : ℝ) * I))) := by
    rw [cpow_sub _ _ hv0, cpow_one, mul_div_cancel₀ _ hv0, cpow_def_of_ne_zero hv0, hlogv]
    congr 1; simp only [ζ₁]; ring
  have hvξ : v * exp (-ξ) ^ (β' - 1) = -exp (-(β' * ξ)) := by
    rw [cpow_def_of_ne_zero (exp_ne_zero _), hlogξ]
    simp only [v, neg_mul, ← exp_add]; congr 1; ring_nf
  calc (Gamma β * Gamma β')⁻¹ * (v * (Gamma β * v ^ (β - 1) * carlson2F0Sector (1 - β') β (-ξ)) -
        v * (exp d * Gamma β' * exp (-ξ) ^ (β' - 1) * carlson2F0Sector (1 - β) β' ζ₁))
      = (Gamma β')⁻¹ * (v * v ^ (β - 1)) * carlson2F0Sector (1 - β') β (-ξ) -
          exp d * (Gamma β)⁻¹ * (v * exp (-ξ) ^ (β' - 1)) * carlson2F0Sector (1 - β) β' ζ₁ := by
        field_simp
    _ = _ := by rw [hvβ, hvξ]; ring

/-- A slab `a < im ζ < b` in the last coordinate of `ℂ × ℂ × ℂ` is convex. -/
theorem convex_im_slab (a b : ℝ) : Convex ℝ {p : ℂ × ℂ × ℂ | a < p.2.2.im ∧ p.2.2.im < b} := by
  intro p hp q hq s r hs hr hsr
  simp only [mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, add_im, smul_im, smul_eq_mul] at hp hq ⊢
  have e : s * a + r * a = a := by rw [← add_mul, hsr, one_mul]
  have e' : s * b + r * b = b := by rw [← add_mul, hsr, one_mul]
  rcases hs.lt_or_eq with hs' | hs'
  · constructor
    · nlinarith [mul_lt_mul_of_pos_left hp.1 hs', mul_le_mul_of_nonneg_left hq.1.le hr]
    · nlinarith [mul_lt_mul_of_pos_left hp.2 hs', mul_le_mul_of_nonneg_left hq.2.le hr]
  · subst hs'
    have : r = 1 := by linarith
    subst this
    simpa using hq

/-- The right side of (5.12-18) at `y = 0`, `x = e^ξ`. -/
def twoF0ConnectionRhs (ε : ℝ) (p : ℂ × ℂ × ℂ) : ℂ :=
  exp (exp p.2.2) * exp (-(p.2.1 * p.2.2)) * (Gamma p.1)⁻¹ *
      carlson2F0Sector (1 - p.1) p.2.1 (-p.2.2 + (ε * π : ℝ) * I) +
    exp (-(p.1 * (p.2.2 - (ε * π : ℝ) * I))) * (Gamma p.2.1)⁻¹ *
        carlson2F0Sector (1 - p.2.1) p.1 (-p.2.2)

/-- **Theorem 5.12-8** at `y = 0`: for all complex `β, β'`, and `x = e^ξ` with
`|ph(x)| = |im ξ| < 3π/2` and `|ph(-x)| = |im ξ - επ| < 3π/2`. -/
theorem regCarlsonS_pair_exp_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (β β' ξ : ℂ)
    (h1 : |ξ.im| < 3 * π / 2) (h2 : |ξ.im - ε * π| < 3 * π / 2) :
    regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair (exp ξ) 0) =
        twoF0ConnectionRhs ε (β, β', ξ) := by
  set T : Set (ℂ × ℂ × ℂ) := {p | -(3 * π / 2) < p.2.2.im ∧ p.2.2.im < 3 * π / 2} ∩
    {p | ε * π - 3 * π / 2 < p.2.2.im ∧ p.2.2.im < ε * π + 3 * π / 2}
  have hTc : IsPreconnected T := ((convex_im_slab _ _).inter (convex_im_slab _ _)).isPreconnected
  have hmemT : ∀ p : ℂ × ℂ × ℂ,
      p ∈ T ↔ |p.2.2.im| < 3 * π / 2 ∧ |p.2.2.im - ε * π| < 3 * π / 2 := by
    intro p
    simp only [T, mem_inter_iff, mem_ofPred_eq, abs_lt]
    constructor
    · rintro ⟨⟨a, b⟩, c, e⟩; exact ⟨⟨a, b⟩, by linarith, by linarith⟩
    · rintro ⟨⟨a, b⟩, c, e⟩; exact ⟨⟨a, b⟩, by linarith, by linarith⟩
  have hβ : ∀ p : ℂ × ℂ × ℂ, AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.1) p := fun p => analyticAt_fst
  have hβ' : ∀ p : ℂ × ℂ × ℂ, AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1) p := fun p =>
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p
  have hξ : ∀ p : ℂ × ℂ × ℂ, AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p := fun p =>
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p
  have hpair : ∀ {f g : ℂ × ℂ × ℂ → ℂ} {p}, AnalyticAt ℂ f p → AnalyticAt ℂ g p →
      AnalyticAt ℂ (fun q => TwoVariable.pair (f q) (g q)) p := fun hf hg => by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact hf
    · exact hg
  have hL : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ =>
      regCarlsonS (TwoVariable.pair p.1 p.2.1) (TwoVariable.pair (exp p.2.2) 0)) T := fun p _ =>
    analyticAt_regCarlsonS_comp (hpair (hβ p) (hβ' p)) (hpair (hξ p).cexp analyticAt_const)
  have hF : ∀ {a b ζ : ℂ × ℂ × ℂ → ℂ} {p}, AnalyticAt ℂ a p → AnalyticAt ℂ b p →
      AnalyticAt ℂ ζ p → |(ζ p).im| < 3 * π / 2 →
      AnalyticAt ℂ (fun q => carlson2F0Sector (a q) (b q) (ζ q)) p := fun ha hb hζ h =>
    (analyticOnNhd_carlson2F0Sector _ h).comp_of_eq (ha.prod (hb.prod hζ)) rfl
  have hG : ∀ {f : ℂ × ℂ × ℂ → ℂ} {p}, AnalyticAt ℂ f p →
      AnalyticAt ℂ (fun q => (Gamma (f q))⁻¹) p := fun hf =>
    (differentiable_one_div_Gamma.analyticAt _).comp_of_eq hf rfl
  have hR : AnalyticOnNhd ℂ (twoF0ConnectionRhs ε) T := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hmemT p).mp hp
    unfold twoF0ConnectionRhs
    refine (((((hξ p).cexp.cexp).mul ((hβ' p).mul (hξ p)).neg.cexp).mul (hG (hβ p))).mul
      (hF (analyticAt_const.sub (hβ p)) (hβ' p) ((hξ p).neg.add analyticAt_const) ?_)).add
      ((((((hβ p).mul ((hξ p).sub analyticAt_const)).neg.cexp).mul (hG (hβ' p))).mul
        (hF (analyticAt_const.sub (hβ' p)) (hβ p) (hξ p).neg ?_)))
    · show |(-p.2.2 + ((ε * π : ℝ) : ℂ) * I).im| < 3 * π / 2
      simp only [add_im, neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero]
      rw [show -p.2.2.im + ε * π = -(p.2.2.im - ε * π) by ring, abs_neg]; exact hp2
    · show |(-p.2.2).im| < 3 * π / 2
      rw [neg_im, abs_neg]; exact hp1
  -- the base point and neighbourhood
  set p₀ : ℂ × ℂ × ℂ := (1 / 2, 1 / 2, ((ε * (π / 2) : ℝ) : ℂ) * I)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hp₀im : p₀.2.2.im = ε * (π / 2) := by simp [p₀]
  have hp₀T : p₀ ∈ T := by
    rw [hmemT, hp₀im]
    rcases hε with rfl | rfl <;> constructor <;> rw [abs_lt] <;> constructor <;>
      linarith [Real.pi_pos]
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR hTc hp₀T (by
    have c1 : Continuous fun q : ℂ × ℂ × ℂ => q.1.re := by fun_prop
    have c2 : Continuous fun q : ℂ × ℂ × ℂ => q.2.1.re := by fun_prop
    have c3 : Continuous fun q : ℂ × ℂ × ℂ => ε * q.2.2.im := by fun_prop
    filter_upwards [c1.continuousAt.eventually_const_lt (show (0 : ℝ) < p₀.1.re by simp [p₀]),
      c1.continuousAt.eventually_lt_const (show p₀.1.re < 1 by simp [p₀]; norm_num),
      c2.continuousAt.eventually_const_lt (show (0 : ℝ) < p₀.2.1.re by simp [p₀]),
      c2.continuousAt.eventually_lt_const (show p₀.2.1.re < 1 by simp [p₀]; norm_num),
      c3.continuousAt.eventually_const_lt (show (0 : ℝ) < ε * p₀.2.2.im by
        rw [hp₀im, ← mul_assoc, hε2]; linarith [Real.pi_pos]),
      c3.continuousAt.eventually_lt_const (show ε * p₀.2.2.im < π by
        rw [hp₀im, ← mul_assoc, hε2]; linarith [Real.pi_pos])] with q a1 a2 a3 a4 a5 a6
    have hb := regCarlsonS_pair_eq_twoF0_base a1 a2 a3 a4 hε a5 a6
    rw [← twoF0ConnectionRhs] at hb
    exact hb)
  have h := heq ((hmemT (β, β', ξ)).mpr ⟨h1, h2⟩)
  simp only at h
  exact h

/-- **Theorem 5.12-8** (Carlson's formula (5.12-18)): for all complex `β, β'` and `x - y = e^ξ`,
`|ph(x - y)| = |im ξ| < 3π/2`, `|ph(y - x)| = |im ξ - επ| < 3π/2` (`ε = ±1`),
`S(β, β'; x, y)/Γ(β + β') = e^x (x - y)^{-β'} ₂F₀(1 - β, β'; 1/(x - y))/Γ(β)
  + e^y (y - x)^{-β} ₂F₀(1 - β', β; 1/(y - x))/Γ(β')`,
where `(x - y)^{-β'} = e^{-β' ξ}`, `(y - x)^{-β} = e^{-β (ξ - iεπ)}`, and the `₂F₀` values are
taken on the branches with `ph(-1/(x - y)) = -(im ξ - επ)` and `ph(-1/(y - x)) = -im ξ`. -/
theorem regCarlsonS_pair_eq_twoF0 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (β β' : ℂ) {x y ξ : ℂ}
    (hxy : x - y = exp ξ) (h1 : |ξ.im| < 3 * π / 2) (h2 : |ξ.im - ε * π| < 3 * π / 2) :
    regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair x y) =
      exp x * exp (-(β' * ξ)) * (Gamma β)⁻¹ *
          carlson2F0Sector (1 - β) β' (-ξ + (ε * π : ℝ) * I) +
        exp y * exp (-(β * (ξ - (ε * π : ℝ) * I))) * (Gamma β')⁻¹ *
          carlson2F0Sector (1 - β') β (-ξ) := by
  have ht := regCarlsonSSeries_add_const (TwoVariable.pair (exp ξ) 0) (TwoVariable.pair β β') y
  have hz : (fun i => TwoVariable.pair (exp ξ) 0 i + y) = TwoVariable.pair x y := by
    funext i; fin_cases i
    · simp [TwoVariable.pair, ← hxy]
    · simp [TwoVariable.pair]
  rw [hz] at ht
  change regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair x y) =
    exp y * regCarlsonS (TwoVariable.pair β β') (TwoVariable.pair (exp ξ) 0) at ht
  rw [ht, regCarlsonS_pair_exp_eq hε β β' ξ h1 h2, twoF0ConnectionRhs,
    show x = exp ξ + y by rw [← hxy]; ring, exp_add]
  ring

/-! ### Theorem 5.12-9 -/

/-- `e^{iεπa} sin(πb) - e^{iεπb} sin(πa) = sin(π(b - a))` for `ε = ±1`. -/
theorem exp_mul_sin_sub_exp_mul_sin {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (a b : ℂ) :
    exp ((ε * π : ℝ) * I * a) * sin (π * b) - exp ((ε * π : ℝ) * I * b) * sin (π * a) =
      sin (π * (b - a)) := by
  have key : ∀ c : ℂ, exp ((ε * π : ℝ) * I * c) = cos (π * c) + ε * sin (π * c) * I := by
    intro c
    rw [show ((ε * π : ℝ) : ℂ) * I * c = (ε * (π * c)) * I by push_cast; ring, exp_mul_I]
    rcases hε with rfl | rfl
    · simp
    · simp [cos_neg, sin_neg]
  rw [key, key, mul_sub, sin_sub]
  ring

/-- **Theorem 5.12-9, entire form**: for all complex `α, β` and `x = e^η` with `|ph x| < 3π/2`,
`sin(π(β - α)) ₂F₀(α, β; -1/x) = π (x^α S(α, 1-β; x, 0)/(Γ(α+1-β) Γ(β))
  - x^β S(β, 1-α; x, 0)/(Γ(β+1-α) Γ(α)))`, with the regularized S-functions. -/
theorem sin_mul_carlson2F0Sector (α β η : ℂ) (hη : |η.im| < 3 * π / 2) :
    sin (π * (β - α)) * carlson2F0Sector α β (-η) =
      π * (exp (α * η) * regCarlsonS (TwoVariable.pair α (1 - β)) (TwoVariable.pair (exp η) 0) *
          (Gamma β)⁻¹ -
        exp (β * η) * regCarlsonS (TwoVariable.pair β (1 - α)) (TwoVariable.pair (exp η) 0) *
          (Gamma α)⁻¹) := by
  obtain ⟨ε, hε, h2⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ |η.im - ε * π| < 3 * π / 2 := by
    rcases le_or_gt 0 η.im with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hη).2, Real.pi_pos]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hη).1, Real.pi_pos]
  have hA := regCarlsonS_pair_exp_eq hε α (1 - β) η hη h2
  have hB := regCarlsonS_pair_exp_eq hε β (1 - α) η hη h2
  simp only [twoF0ConnectionRhs, sub_sub_cancel] at hA hB
  set ζ₁ : ℂ := -η + (ε * π : ℝ) * I
  have hζ₁ : |ζ₁.im| < 3 * π / 2 := by
    simp only [ζ₁, add_im, neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero]
    rw [show -η.im + ε * π = -(η.im - ε * π) by ring, abs_neg]; exact h2
  have hη' : |(-η).im| < 3 * π / 2 := by rw [neg_im, abs_neg]; exact hη
  rw [hA, hB, carlson2F0Sector_comm (1 - β) (1 - α) ζ₁ hζ₁, carlson2F0Sector_comm β α (-η) hη']
  have hr : ∀ z : ℂ, (Gamma z)⁻¹ * (Gamma (1 - z))⁻¹ = sin (π * z) / π := fun z => by
    rw [← mul_inv, Gamma_mul_Gamma_one_sub, inv_div]
  have hs := exp_mul_sin_sub_exp_mul_sin hε α β
  have e1 : exp (α * η) * exp (-((1 - β) * η)) = exp (β * η) * exp (-((1 - α) * η)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e2 : exp (α * η) * exp (-(α * (η - (ε * π : ℝ) * I))) = exp ((ε * π : ℝ) * I * α) := by
    rw [← exp_add]; congr 1; ring
  have e3 : exp (β * η) * exp (-(β * (η - (ε * π : ℝ) * I))) = exp ((ε * π : ℝ) * I * β) := by
    rw [← exp_add]; congr 1; ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set F := carlson2F0Sector α β (-η)
  set Fc := carlson2F0Sector (1 - α) (1 - β) ζ₁
  have e1' : exp (α * η) * exp (-((1 - β) * η)) - exp (β * η) * exp (-((1 - α) * η)) = 0 :=
    sub_eq_zero.mpr e1
  calc sin (π * (β - α)) * F
      = F * (exp ((ε * π : ℝ) * I * α) * sin (π * β) - exp ((ε * π : ℝ) * I * β) *
          sin (π * α)) := by
        rw [hs]; ring
    _ = π * (exp (exp η) * Fc * (Gamma α)⁻¹ * (Gamma β)⁻¹ * 0 +
          F * (exp ((ε * π : ℝ) * I * α) * (sin (π * β) / π) -
            exp ((ε * π : ℝ) * I * β) * (sin (π * α) / π))) := by
        simp only [mul_zero, zero_add]
        field_simp
    _ = π * (exp (exp η) * Fc * (Gamma α)⁻¹ * (Gamma β)⁻¹ *
            (exp (α * η) * exp (-((1 - β) * η)) - exp (β * η) * exp (-((1 - α) * η))) +
          F * ((exp (α * η) * exp (-(α * (η - (ε * π : ℝ) * I)))) *
              ((Gamma β)⁻¹ * (Gamma (1 - β))⁻¹) -
            (exp (β * η) * exp (-(β * (η - (ε * π : ℝ) * I)))) *
              ((Gamma α)⁻¹ * (Gamma (1 - α))⁻¹))) := by
        rw [e1', e2, e3, hr β, hr α]
    _ = _ := by ring

/-- **Theorem 5.12-9** (Carlson's formula (5.12-20)): for `α - β ∉ ℤ` and `x = e^η` with
`|ph x| = |im η| < 3π/2`,
`₂F₀(α, β; -1/x) = Γ(β - α)/Γ(β) x^α S(α, 1 - β; x, 0) + Γ(α - β)/Γ(α) x^β S(β, 1 - α; x, 0)`,
with `x^α = e^{α η}`. -/
theorem carlson2F0Sector_eq_carlsonS {α β η : ℂ} (hη : |η.im| < 3 * π / 2)
    (hαβ : ∀ n : ℤ, α - β ≠ n) :
    carlson2F0Sector α β (-η) =
      Gamma (β - α) / Gamma β * exp (α * η) *
          carlsonS (TwoVariable.pair α (1 - β)) (TwoVariable.pair (exp η) 0) +
        Gamma (α - β) / Gamma α * exp (β * η) *
          carlsonS (TwoVariable.pair β (1 - α)) (TwoVariable.pair (exp η) 0) := by
  have hsin : sin (π * (β - α)) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : β - α = k := by
      have := hk; field_simp at this; linear_combination this
    exact hαβ (-k) (by push_cast; linear_combination -this)
  have h := sin_mul_carlson2F0Sector α β η hη
  have hr1 : Gamma (β - α) * Gamma (α + (1 - β)) = π / sin (π * (β - α)) := by
    rw [show α + (1 - β) = 1 - (β - α) by ring, Gamma_mul_Gamma_one_sub]
  have hr2 : Gamma (α - β) * Gamma (β + (1 - α)) = -(π / sin (π * (β - α))) := by
    rw [show β + (1 - α) = 1 - (α - β) by ring, Gamma_mul_Gamma_one_sub,
      show π * (α - β) = -(π * (β - α)) by ring, sin_neg, div_neg]
  simp only [carlsonS, TwoVariable.sum_pair]
  apply mul_left_cancel₀ hsin
  rw [h]
  calc (π : ℂ) * (exp (α * η) * regCarlsonS (TwoVariable.pair α (1 - β))
          (TwoVariable.pair (exp η) 0) * (Gamma β)⁻¹ -
        exp (β * η) * regCarlsonS (TwoVariable.pair β (1 - α)) (TwoVariable.pair (exp η) 0) *
          (Gamma α)⁻¹)
      = sin (π * (β - α)) * ((π / sin (π * (β - α))) / Gamma β * exp (α * η) *
          regCarlsonS (TwoVariable.pair α (1 - β)) (TwoVariable.pair (exp η) 0) +
        (-(π / sin (π * (β - α)))) / Gamma α * exp (β * η) *
          regCarlsonS (TwoVariable.pair β (1 - α)) (TwoVariable.pair (exp η) 0)) := by
        field_simp
        ring
    _ = _ := by rw [← hr2, ← hr1]; ring

end Carlson
