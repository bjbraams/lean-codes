/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Quantitative Laplace asymptotics with a complex quadratic phase

The phase is written `t² q(t)`, where the real part of `q` has a fixed positive
lower bound. Linear bounds on `q(t) - q(0)` and on the amplitude give a Gaussian
majorant for the error after rescaling. Constants independent of an auxiliary
parameter give uniform asymptotics. The amplitude and phase coefficient need only
be measurable. The finite-interval variant imposes the quantitative bounds only
on `[-δ, δ]`.

For `Re q(t) ≥ c > 0`, `‖A(0)‖ ≤ M`, `‖A(t)-A(0)‖ ≤ L |t|`, and
`‖q(t)-q(0)‖ ≤ B |t|`, the normalized integral satisfies

`‖sqrt n ∫ A(t) exp(-n t² q(t)) dt - A(0) (π/q(0))^(1/2)‖ ≤ (L/c + M B/c²)/sqrt n`.

The finite-interval estimate replaces `L` by `L + M/δ`. A nonzero amplitude at
the saddle gives an asymptotic equivalent. The square root is the principal
complex power; coercivity keeps its argument in the right half-plane.

## Main results

* `Complex.integrable_laplace`: absolute integrability under Gaussian coercivity.
* `Complex.norm_sqrt_mul_integral_laplace_sub_le`: quantitative whole-line estimate.
* `Complex.norm_sqrt_mul_integral_laplace_Icc_sub_le`: finite-interval estimate.
* `Complex.tendstoUniformlyOn_sqrt_mul_integral_laplace` and its `_Icc` version:
  uniform convergence over arbitrary parameter sets with common bounds.
* `Complex.isEquivalent_integral_laplace_Icc`: the leading asymptotic equivalent.

These are real-contour integrals with complex phases. The module does not
construct a saddle contour, derive the hypotheses from differentiability, or
verify them for particular special functions.
-/

open MeasureTheory Set Filter
open scoped Topology Real
@[expose] public noncomputable section

namespace Complex

/-- The exponential is Lipschitz on every left half-plane, with constant `exp b`. -/
theorem norm_exp_sub_exp_le_of_re_le {z w : ℂ} {b : ℝ} (hz : z.re ≤ b) (hw : w.re ≤ b) :
    ‖exp z - exp w‖ ≤ Real.exp b * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => by rw [norm_exp]; exact Real.exp_le_exp.mpr hu)
    (convex_halfSpace_re_le b) hw hz

end Complex

namespace MeasureTheory

/-- The absolute Gaussian moment of natural order `m` and real rate `c`. -/
def gaussianAbsMoment (c : ℝ) (m : ℕ) : ℝ :=
  ∫ t : ℝ, |t| ^ m * Real.exp (-c * t ^ 2)

/-- Every absolute Gaussian moment is integrable when its rate is positive. -/
theorem integrable_abs_pow_mul_gaussian {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Integrable (fun t : ℝ => |t| ^ m * Real.exp (-c * t ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hc (s := (m : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)] using h.norm

/-- Absolute Gaussian moments are nonnegative, also for totalized divergent integrals. -/
theorem gaussianAbsMoment_nonneg (c : ℝ) (m : ℕ) : 0 ≤ gaussianAbsMoment c m :=
  integral_nonneg (fun _ => by positivity)

/-- Absolute Gaussian moments evaluated by the Gamma integral. -/
theorem gaussianAbsMoment_eq_Gamma {c : ℝ} (hc : 0 < c) (m : ℕ) :
    gaussianAbsMoment c m = c ^ (-((m : ℝ) + 1) / 2) * Real.Gamma (((m : ℝ) + 1) / 2) := by
  let f : ℝ → ℝ := fun t => |t| ^ m * Real.exp (-c * t ^ 2)
  have hneg : (∫ t in Iic (0 : ℝ), f t) = ∫ t in Ioi (0 : ℝ), f t := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), f (-t) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := by simp [f]
  have hhalf : (∫ t in Ioi (0 : ℝ), f t) =
      c ^ (-((m : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((m : ℝ) + 1) / 2) := by
    rw [← integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (m : ℝ))
      (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) m; linarith) hc]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [f, abs_of_pos ht, Real.rpow_natCast, Real.rpow_two]
  change (∫ t, f t) = _
  rw [← integral_add_compl measurableSet_Ioi (integrable_abs_pow_mul_gaussian hc m),
    compl_Ioi, hneg, hhalf]
  ring

/-- The first absolute Gaussian moment is the reciprocal of the rate. -/
theorem gaussianAbsMoment_one {c : ℝ} (hc : 0 < c) : gaussianAbsMoment c 1 = c⁻¹ := by
  rw [gaussianAbsMoment_eq_Gamma hc]
  norm_num [Real.rpow_neg_one]

/-- The third absolute Gaussian moment is the reciprocal square of the rate. -/
theorem gaussianAbsMoment_three {c : ℝ} (hc : 0 < c) : gaussianAbsMoment c 3 = (c ^ 2)⁻¹ := by
  rw [gaussianAbsMoment_eq_Gamma hc]
  norm_num [Real.rpow_neg hc.le, Real.rpow_two]

end MeasureTheory

namespace Complex

/-- A pointwise Gaussian majorant for the error in a rescaled Laplace integrand.
The constants are independent of `t` and of any auxiliary parameters. -/
theorem norm_laplace_rescaled_sub_le {A q : ℝ → ℂ} {c L M B r : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hr : 0 < r)
    (hq : ∀ t, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ t, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t, ‖q t - q 0‖ ≤ B * |t|) (t : ℝ) :
    ‖A (t / r) * exp (-(t : ℂ) ^ 2 * q (t / r)) -
        A 0 * exp (-(t : ℂ) ^ 2 * q 0)‖ ≤
      ((L * |t| + M * B * |t| ^ 3) / r) * Real.exp (-c * t ^ 2) := by
  have hre (v : ℝ) : (-(t : ℂ) ^ 2 * q v).re ≤ -c * t ^ 2 := by
    simp only [← ofReal_pow, ← ofReal_neg, re_ofReal_mul]
    nlinarith [mul_le_mul_of_nonneg_right (hq v) (sq_nonneg t)]
  have he : ‖exp (-(t : ℂ) ^ 2 * q (t / r))‖ ≤ Real.exp (-c * t ^ 2) := by
    rw [norm_exp]; exact Real.exp_le_exp.mpr (hre _)
  have hd := norm_exp_sub_exp_le_of_re_le (hre (t / r)) (hre 0)
  rw [show -(t : ℂ) ^ 2 * q (t / r) - -(t : ℂ) ^ 2 * q 0 =
    -(t : ℂ) ^ 2 * (q (t / r) - q 0) by ring,
    norm_mul, norm_neg, norm_pow, norm_real, Real.norm_eq_abs] at hd
  have ha := hA (t / r)
  have hq' := hqt (t / r)
  rw [abs_div, abs_of_pos hr] at ha hq'
  calc
    _ = ‖(A (t / r) - A 0) * exp (-(t : ℂ) ^ 2 * q (t / r)) +
        A 0 * (exp (-(t : ℂ) ^ 2 * q (t / r)) - exp (-(t : ℂ) ^ 2 * q 0))‖ := by
      congr 1; ring
    _ ≤ ‖A (t / r) - A 0‖ * ‖exp (-(t : ℂ) ^ 2 * q (t / r))‖ +
        ‖A 0‖ * ‖exp (-(t : ℂ) ^ 2 * q (t / r)) - exp (-(t : ℂ) ^ 2 * q 0)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((A (t / r) - A 0) * exp (-(t : ℂ) ^ 2 * q (t / r)))
        (A 0 * (exp (-(t : ℂ) ^ 2 * q (t / r)) - exp (-(t : ℂ) ^ 2 * q 0)))
    _ ≤ (L * (|t| / r)) * Real.exp (-c * t ^ 2) +
        M * (Real.exp (-c * t ^ 2) * (|t| ^ 2 * (B * (|t| / r)))) := by
      gcongr
      exact hd.trans (by gcongr)
    _ = _ := by ring

/-- Gaussian coercivity and at most linear amplitude growth imply absolute integrability
of the Laplace integrand. No bound on the variation of `q` is needed here. -/
theorem integrable_laplace {A q : ℝ → ℂ} {c L M n : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hn : 0 < n)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t, c ≤ (q t).re) (hA : ∀ t, ‖A t‖ ≤ M + L * |t|) :
    Integrable (fun t : ℝ => A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t)) := by
  have hi : Integrable (fun t : ℝ => (M + L * |t|) * Real.exp (-(n * c) * t ^ 2)) := by
    have h := ((integrable_exp_neg_mul_sq (mul_pos hn hc)).const_mul M).add
      ((integrable_abs_pow_mul_gaussian (mul_pos hn hc) 1).const_mul L)
    convert h using 1
    funext t
    simp only [Pi.add_apply, pow_one]; ring
  apply hi.mono' (by fun_prop)
  filter_upwards with t
  rw [norm_mul, norm_exp]
  have he : (-(n : ℂ) * (t : ℂ) ^ 2 * q t).re ≤ -(n * c) * t ^ 2 := by
    rw [← ofReal_pow, ← ofReal_neg, ← ofReal_mul, re_ofReal_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hq t) (mul_nonneg hn.le (sq_nonneg t))]
  exact mul_le_mul (hA t) (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)

/-- A quantitative Laplace estimate after rescaling, for a complex quadratic coefficient
with positive real part. The error is bounded by absolute Gaussian moments. -/
theorem norm_integral_laplace_rescaled_sub_le {A q : ℝ → ℂ} {c L M B r : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hr : 0 < r)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ t, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t, ‖q t - q 0‖ ≤ B * |t|) :
    ‖(∫ t : ℝ, A (t / r) * exp (-(t : ℂ) ^ 2 * q (t / r))) -
        A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ)‖ ≤
      (L * gaussianAbsMoment c 1 + M * B * gaussianAbsMoment c 3) / r := by
  let F : ℝ → ℂ := fun t => A (t / r) * exp (-(t : ℂ) ^ 2 * q (t / r))
  let G : ℝ → ℂ := fun t => A 0 * exp (-(t : ℂ) ^ 2 * q 0)
  let H : ℝ → ℝ := fun t => ((L * |t| + M * B * |t| ^ 3) / r) * Real.exp (-c * t ^ 2)
  have hH : Integrable H := by
    have hi := ((integrable_abs_pow_mul_gaussian hc 1).const_mul L).add
      ((integrable_abs_pow_mul_gaussian hc 3).const_mul (M * B))
    convert hi.div_const r using 1
    funext t
    simp only [H, pow_one, Pi.add_apply]; ring
  have hbound : ∀ t, ‖F t - G t‖ ≤ H t :=
    norm_laplace_rescaled_sub_le hL hM hr hq hA0 hA hqt
  have hG : Integrable G := by
    convert (integrable_cexp_neg_mul_sq (hc.trans_le (hq 0))).const_mul (A 0) using 1
    funext t
    simp only [G]; congr 2; ring
  have hdiff : Integrable (fun t => F t - G t) :=
    hH.mono' (by dsimp [F, G]; fun_prop) (ae_of_all _ hbound)
  have hF : Integrable F := by
    have hi := hdiff.add hG
    change Integrable (fun t => (F t - G t) + G t) at hi
    simpa only [sub_add_cancel] using hi
  have hvalG : (∫ t, G t) = A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ) := by
    simp only [G, show ∀ t : ℝ, -(t : ℂ) ^ 2 * q 0 = -q 0 * (t : ℂ) ^ 2 by intro t; ring]
    rw [integral_const_mul, integral_gaussian_complex (hc.trans_le (hq 0))]
  have hvalH : (∫ t, H t) =
      (L * gaussianAbsMoment c 1 + M * B * gaussianAbsMoment c 3) / r := by
    have he : H = fun t => (L * (|t| ^ 1 * Real.exp (-c * t ^ 2)) +
      (M * B) * (|t| ^ 3 * Real.exp (-c * t ^ 2))) / r := by
      funext t; simp only [H, pow_one]; ring
    rw [he, integral_div, integral_add ((integrable_abs_pow_mul_gaussian hc 1).const_mul L)
      ((integrable_abs_pow_mul_gaussian hc 3).const_mul (M * B)), integral_const_mul,
      integral_const_mul]
    rfl
  rw [← hvalG, ← integral_sub hF hG, ← hvalH]
  exact norm_integral_le_of_norm_le hH (ae_of_all _ hbound)

/-- Quantitative Laplace asymptotics: after multiplying by `r`, the integral with
phase `-r² t² q(t)` differs from its complex Gaussian value by at most
`(L/c + M B/c²)/r`. -/
theorem norm_mul_integral_laplace_sub_le {A q : ℝ → ℂ} {c L M B r : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hr : 0 < r)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ t, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t, ‖q t - q 0‖ ≤ B * |t|) :
    ‖(r : ℂ) * (∫ t : ℝ, A t * exp (-(r : ℂ) ^ 2 * (t : ℂ) ^ 2 * q t)) -
        A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ)‖ ≤ (L / c + M * B / c ^ 2) / r := by
  have h := norm_integral_laplace_rescaled_sub_le hc hL hM hr hAc hqc hq hA0 hA hqt
  rw [gaussianAbsMoment_one hc, gaussianAbsMoment_three hc] at h
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have he : (∫ t : ℝ, A (t / r) * exp (-(t : ℂ) ^ 2 * q (t / r))) =
      (r : ℂ) * ∫ t : ℝ, A t * exp (-(r : ℂ) ^ 2 * (t : ℂ) ^ 2 * q t) := by
    calc
      _ = ∫ t : ℝ, A (t / r) * exp (-(r : ℂ) ^ 2 * ((t / r : ℝ) : ℂ) ^ 2 * q (t / r)) := by
        apply integral_congr_ae
        filter_upwards with t
        congr 2
        push_cast
        field_simp
      _ = _ := by
        simpa only [abs_of_pos hr, real_smul] using
          (Measure.integral_comp_div
            (fun t : ℝ => A t * exp (-(r : ℂ) ^ 2 * (t : ℂ) ^ 2 * q t)) r)
  rw [he] at h
  simpa only [div_eq_mul_inv] using h

/-- The usual `sqrt n` normalization of the Laplace estimate, valid for every positive real `n`.
The error constant is uniform whenever the hypotheses have common constants. -/
theorem norm_sqrt_mul_integral_laplace_sub_le {A q : ℝ → ℂ} {c L M B n : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hn : 0 < n)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ t, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t, ‖q t - q 0‖ ≤ B * |t|) :
    ‖(Real.sqrt n : ℂ) * (∫ t : ℝ, A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t)) -
        A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ)‖ ≤ (L / c + M * B / c ^ 2) / Real.sqrt n := by
  have h := norm_mul_integral_laplace_sub_le hc hL hM (Real.sqrt_pos.mpr hn)
    hAc hqc hq hA0 hA hqt
  simpa only [← ofReal_pow, Real.sq_sqrt hn.le] using h

/-- Uniform Laplace asymptotics on any parameter set with common coercivity and variation
bounds. No topology on the parameter type or nonemptiness of the set is required. -/
theorem tendstoUniformlyOn_sqrt_mul_integral_laplace {P : Type*} {S : Set P}
    {A q : P → ℝ → ℂ} {c L M B : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hAc : ∀ p ∈ S, Measurable (A p)) (hqc : ∀ p ∈ S, Measurable (q p))
    (hq : ∀ p ∈ S, ∀ t, c ≤ (q p t).re) (hA0 : ∀ p ∈ S, ‖A p 0‖ ≤ M)
    (hA : ∀ p ∈ S, ∀ t, ‖A p t - A p 0‖ ≤ L * |t|)
    (hqt : ∀ p ∈ S, ∀ t, ‖q p t - q p 0‖ ≤ B * |t|) :
    TendstoUniformlyOn
      (fun n : ℝ => fun p => (Real.sqrt n : ℂ) *
        ∫ t : ℝ, A p t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q p t))
      (fun p => A p 0 * (Real.pi / q p 0) ^ (1 / 2 : ℂ)) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℝ => (L / c + M * B / c ^ 2) / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hε)] with n hn hεn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (norm_sqrt_mul_integral_laplace_sub_le hc hL hM hn (hAc p hp) (hqc p hp)
    (hq p hp) (hA0 p hp) (hA p hp) (hqt p hp)).trans_lt hεn

/-- A finite-interval Laplace estimate requiring phase and amplitude bounds only on `[-δ, δ]`.
The cutoff costs `M/δ` in the amplitude variation constant. -/
theorem norm_sqrt_mul_integral_laplace_Icc_sub_le {A q : ℝ → ℂ} {c L M B δ n : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 < δ) (hn : 0 < n)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t ∈ Icc (-δ) δ, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ t ∈ Icc (-δ) δ, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t ∈ Icc (-δ) δ, ‖q t - q 0‖ ≤ B * |t|) :
    ‖(Real.sqrt n : ℂ) * (∫ t in Icc (-δ) δ, A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t)) -
        A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ)‖ ≤
      ((L + M / δ) / c + M * B / c ^ 2) / Real.sqrt n := by
  classical
  let A' := (Icc (-δ) δ).indicator A
  let q' := (Icc (-δ) δ).piecewise q (fun _ => q 0)
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hA'0 : A' 0 = A 0 := by simp [A', h0]
  have hq'0 : q' 0 = q 0 := by simp [q', h0]
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hqt δ ⟨by linarith, le_rfl⟩)
    rw [abs_of_pos hδ] at h
    exact nonneg_of_mul_nonneg_left h hδ
  have hA'm : Measurable A' := hAc.indicator measurableSet_Icc
  have hq'm : Measurable q' := hqc.piecewise measurableSet_Icc measurable_const
  have hq' : ∀ t, c ≤ (q' t).re := by
    intro t
    by_cases ht : t ∈ Icc (-δ) δ
    · simpa [q', ht] using hq t ht
    · simpa [q', ht] using hq 0 h0
  have hqt' : ∀ t, ‖q' t - q' 0‖ ≤ B * |t| := by
    intro t
    rw [hq'0]
    by_cases ht : t ∈ Icc (-δ) δ
    · simpa [q', ht] using hqt t ht
    · simp only [q', piecewise_eq_of_notMem _ _ _ ht, sub_self, norm_zero]
      positivity
  have hA' : ∀ t, ‖A' t - A' 0‖ ≤ (L + M / δ) * |t| := by
    intro t
    rw [hA'0]
    by_cases ht : t ∈ Icc (-δ) δ
    · simp only [A', indicator_of_mem ht]
      exact (hA t ht).trans (by gcongr; linarith [div_nonneg hM hδ.le])
    · have hab : δ ≤ |t| := by
        by_contra! h
        apply ht
        have ht' := abs_lt.mp h
        exact ⟨ht'.1.le, ht'.2.le⟩
      simp only [A', indicator_of_notMem ht, zero_sub, norm_neg]
      calc
        ‖A 0‖ ≤ M := hA0
        _ = (M / δ) * δ := by field_simp
        _ ≤ (M / δ) * |t| := mul_le_mul_of_nonneg_left hab (div_nonneg hM hδ.le)
        _ ≤ (L + M / δ) * |t| := by gcongr; linarith
  have H := norm_sqrt_mul_integral_laplace_sub_le hc (by positivity : 0 ≤ L + M / δ)
    hM hn hA'm hq'm hq' (by rwa [hA'0]) hA' hqt'
  have he : (fun t : ℝ => A' t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q' t)) =
      (Icc (-δ) δ).indicator (fun t => A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t)) := by
    funext t
    by_cases ht : t ∈ Icc (-δ) δ <;> simp [A', q', ht]
  rw [he, integral_indicator measurableSet_Icc, hA'0, hq'0] at H
  exact H

/-- Uniform finite-interval Laplace asymptotics under common local quadratic and amplitude
bounds. This applies in particular to compact parameter sets with such bounds. -/
theorem tendstoUniformlyOn_sqrt_mul_integral_laplace_Icc {P : Type*} {S : Set P}
    {A q : P → ℝ → ℂ} {c L M B δ : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hAc : ∀ p ∈ S, Measurable (A p)) (hqc : ∀ p ∈ S, Measurable (q p))
    (hq : ∀ p ∈ S, ∀ t ∈ Icc (-δ) δ, c ≤ (q p t).re)
    (hA0 : ∀ p ∈ S, ‖A p 0‖ ≤ M)
    (hA : ∀ p ∈ S, ∀ t ∈ Icc (-δ) δ, ‖A p t - A p 0‖ ≤ L * |t|)
    (hqt : ∀ p ∈ S, ∀ t ∈ Icc (-δ) δ, ‖q p t - q p 0‖ ≤ B * |t|) :
    TendstoUniformlyOn
      (fun n : ℝ => fun p => (Real.sqrt n : ℂ) *
        ∫ t in Icc (-δ) δ, A p t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q p t))
      (fun p => A p 0 * (Real.pi / q p 0) ^ (1 / 2 : ℂ)) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto
      (fun n : ℝ => ((L + M / δ) / c + M * B / c ^ 2) / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hε)] with n hn hεn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (norm_sqrt_mul_integral_laplace_Icc_sub_le hc hL hM hδ hn (hAc p hp) (hqc p hp)
    (hq p hp) (hA0 p hp) (hA p hp) (hqt p hp)).trans_lt hεn

/-- A nonzero saddle amplitude gives the usual asymptotic equivalent on a finite interval.
The square root in the Gaussian coefficient is the principal complex power. -/
theorem isEquivalent_integral_laplace_Icc {A q : ℝ → ℂ} {c L M B δ : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hAc : Measurable A) (hqc : Measurable q)
    (hq : ∀ t ∈ Icc (-δ) δ, c ≤ (q t).re) (hA0 : ‖A 0‖ ≤ M) (hAne : A 0 ≠ 0)
    (hA : ∀ t ∈ Icc (-δ) δ, ‖A t - A 0‖ ≤ L * |t|)
    (hqt : ∀ t ∈ Icc (-δ) δ, ‖q t - q 0‖ ≤ B * |t|) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℝ => ∫ t in Icc (-δ) δ, A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t))
      (fun n : ℝ => (A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ)) / (Real.sqrt n : ℂ)) := by
  have H := (tendstoUniformlyOn_sqrt_mul_integral_laplace_Icc
    (S := (univ : Set Unit)) (A := fun _ => A) (q := fun _ => q) hc hL hM hδ
    (fun _ _ => hAc) (fun _ _ => hqc) (fun _ _ => hq) (fun _ _ => hA0)
    (fun _ _ => hA) (fun _ _ => hqt)).tendsto_at (mem_univ ())
  have hq0 : q 0 ≠ 0 := by
    have hh := hc.trans_le (hq 0 ⟨by linarith, hδ.le⟩)
    intro he; simp [he] at hh
  have hC : A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero hAne (cpow_ne_zero_iff.mpr (Or.inl
      (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hq0)))
  have H' := H.div_const (A 0 * (Real.pi / q 0) ^ (1 / 2 : ℂ))
  rw [div_self hC] at H'
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert H' using 1
  funext n
  simp only [Pi.div_apply]
  field

end Complex
