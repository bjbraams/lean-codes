/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindSaddle
public import ToMathlib.Analysis.Integral.Laplace
public import ToMathlib.Analysis.SpecialFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Laplace estimates on the Jacobi saddle curve

Centering the Möbius saddle curve at `t = 1/2` gives the normalized kernel
`(1-u²)/(1-w u²)`, where `w = ((c-1)/(c+1))²` and `Re c > 0`.
The strict inequality `‖w‖ < 1` controls both the local Gaussian phase and
the part of the integral away from the saddle. The logarithmic quadratic
coefficient differs from `1-w` by at most `2u²` for `|u| ≤ 1/2`. The normalized
kernel satisfies `‖K(u)‖ ≤ 1-(1-‖w‖)u²` on the whole interval.

These estimates give a Gaussian limit with a nonzero coefficient for the actual
Möbius Euler integral. Comparing it with the beta integral at coincident endpoints
cancels the Gamma normalization exactly. A fixed degree shift controls both
endpoints for arbitrary complex Jacobi parameters, and can then be removed.
The result is the pointwise second-kind asymptotic with a nonzero coefficient
independent of degree. Uniformity on compact sets and the polynomial asymptotics
of §7.4 are not asserted here.

## Main results

* `norm_jacobiSaddlePhase_sub_le`: the explicit local phase remainder.
* `norm_sqrt_mul_integral_jacobiSaddleKernel_sub_le`: the central Laplace error.
* `norm_integral_jacobiSaddleKernel_tail_le`: geometric decay of the outer pieces.
* `tendsto_sqrt_mul_pow_mul_integral_jacobiMobius`: the full Euler integral limit.
* `isEquivalent_jacobiSecondKind_saddle_shift`: the equivalent with an explicitly
  defined ratio of Gaussian leading constants.
* `exists_isEquivalent_jacobiSecondKind_geometric`: the pointwise equivalent for
  every complex parameter pair, after removing the auxiliary degree shift.
* `norm_jacobiSaddleScale`: the saddle scale has modulus `4μ(z)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.4, the saddle-point argument for Theorem 7.4-3.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Set Filter MeasureTheory
open scoped Topology

/-- The centered shape parameter of the Jacobi saddle kernel. -/
def jacobiSaddleShape (c : ℂ) : ℂ := ((c - 1) / (c + 1)) ^ 2

/-- A right-half-plane saddle ratio gives a shape parameter strictly inside the unit disk. -/
theorem norm_jacobiSaddleShape_lt_one {c : ℂ} (hc : 0 < c.re) :
    ‖jacobiSaddleShape c‖ < 1 := by
  have hn : ‖c - 1‖ < ‖c + 1‖ := by
    have h1 := Complex.sq_norm (c - 1)
    have h2 := Complex.sq_norm (c + 1)
    simp only [normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero,
      add_re, add_im, add_zero] at h1 h2
    nlinarith [norm_nonneg (c - 1), norm_nonneg (c + 1)]
  have hp : 0 < ‖c + 1‖ := (norm_nonneg _).trans_lt hn
  have hdiv : ‖(c - 1) / (c + 1)‖ < 1 := by rwa [norm_div, div_lt_one hp]
  simpa only [jacobiSaddleShape, norm_pow] using pow_lt_one₀ (norm_nonneg _) hdiv (by decide : 2 ≠ 0)

/-- The normalized centered kernel on the Jacobi saddle curve. -/
def jacobiSaddleKernel (w : ℂ) (u : ℝ) : ℂ :=
  (1 - (u : ℂ) ^ 2) / (1 - w * (u : ℂ) ^ 2)

/-- The quadratic coefficient in minus the logarithm of the normalized saddle
kernel, with its removable value assigned at the saddle. -/
def jacobiSaddlePhase (w : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 1 - w else
    (log (1 - w * (u : ℂ) ^ 2) - log (1 - (u : ℂ) ^ 2)) / (u : ℂ) ^ 2

/-- The Gaussian coefficient at the centered saddle is `1-w`. -/
@[simp] theorem jacobiSaddlePhase_zero (w : ℂ) : jacobiSaddlePhase w 0 = 1 - w := by
  simp [jacobiSaddlePhase]

/-- The centered phase is measurable, including the assigned value at zero. -/
theorem measurable_jacobiSaddlePhase (w : ℂ) : Measurable (jacobiSaddlePhase w) := by
  unfold jacobiSaddlePhase
  apply Measurable.ite (by measurability) measurable_const
  exact ((Complex.measurable_log.comp (by fun_prop)).sub
    (Complex.measurable_log.comp (by fun_prop))).div (by fun_prop)

/-- A convenient quadratic remainder estimate for the complex logarithm. -/
private theorem norm_log_one_sub_add_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖log (1 - z) + z‖ ≤ ‖z‖ ^ 2 := by
  have h := norm_log_one_add_sub_self_le (z := -z) (by simpa using hz.trans_lt (by norm_num : (1:ℝ)/2 < 1))
  simp only [norm_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
  apply h.trans
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
  nlinarith [sq_nonneg ‖z‖, mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z‖)]

/-- The Jacobi logarithmic phase differs from its Gaussian coefficient by at
most `2u²` on the fixed interval `|u| ≤ 1/2`, uniformly for `‖w‖ ≤ 1`. -/
theorem norm_jacobiSaddlePhase_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) {u : ℝ}
    (hu : |u| ≤ 1 / 2) : ‖jacobiSaddlePhase w u - (1 - w)‖ ≤ 2 * u ^ 2 := by
  by_cases hu0 : u = 0
  · simp [hu0]
  have huC : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hu0)
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hnorm : ‖(u : ℂ) ^ 2‖ = u ^ 2 := by simp [norm_pow, Real.norm_eq_abs, sq_abs]
  have hwu : ‖w * (u : ℂ) ^ 2‖ ≤ u ^ 2 := by
    rw [norm_mul, hnorm]; nlinarith [sq_nonneg u]
  have h1 := norm_log_one_sub_add_le (hwu.trans (by linarith : u ^ 2 ≤ 1 / 2))
  have h2 := norm_log_one_sub_add_le (z := (u : ℂ) ^ 2) (by rw [hnorm]; linarith)
  have he : jacobiSaddlePhase w u - (1 - w) =
      ((log (1 - w * (u : ℂ) ^ 2) + w * (u : ℂ) ^ 2) -
        (log (1 - (u : ℂ) ^ 2) + (u : ℂ) ^ 2)) / (u : ℂ) ^ 2 := by
    simp only [jacobiSaddlePhase, ite_eq_right hu0]
    field_simp [ofReal_ne_zero.mpr hu0]
    ring
  rw [he, norm_div, hnorm]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hu0)).mpr
  have h := (norm_sub_le (log (1 - w * (u : ℂ) ^ 2) + w * (u : ℂ) ^ 2)
    (log (1 - (u : ℂ) ^ 2) + (u : ℂ) ^ 2)).trans (add_le_add h1 h2)
  rw [hnorm] at h
  have hs : ‖w * (u : ℂ) ^ 2‖ ^ 2 ≤ (u ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwu 2
  nlinarith

/-- On a sufficiently small symmetric interval the Jacobi phase has a positive
real part, with the coercivity constant explicitly controlled by `Re(1-w)`. -/
theorem re_jacobiSaddlePhase_ge {w : ℂ} (hw : ‖w‖ ≤ 1) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (hsmall : 4 * δ ^ 2 ≤ (1 - w).re) {u : ℝ}
    (hu : |u| ≤ δ) : (1 - w).re / 2 ≤ (jacobiSaddlePhase w u).re := by
  have hb := norm_jacobiSaddlePhase_sub_le hw (hu.trans hδ)
  have hr := (abs_le.mp (abs_re_le_norm (jacobiSaddlePhase w u - (1 - w)))).1
  simp only [sub_re, one_re] at hr hsmall ⊢
  have hs : u ^ 2 ≤ δ ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  linarith

/-- Exponentiating the centered quadratic phase recovers every natural power
of the normalized saddle kernel. -/
theorem exp_neg_mul_jacobiSaddlePhase {w : ℂ} (hw : ‖w‖ < 1) {u : ℝ}
    (hu : |u| < 1) (n : ℕ) :
    exp (-(n : ℂ) * (u : ℂ) ^ 2 * jacobiSaddlePhase w u) = jacobiSaddleKernel w u ^ n := by
  by_cases hu0 : u = 0
  · simp [hu0, jacobiSaddleKernel]
  have huC : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hu0)
  have hnorm : ‖(u : ℂ) ^ 2‖ < 1 := by
    simpa only [norm_pow, norm_real, Real.norm_eq_abs] using
      pow_lt_one₀ (abs_nonneg u) hu (by decide : 2 ≠ 0)
  have h1 : 1 - (u : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he; rw [← he, norm_one] at hnorm; exact lt_irrefl _ hnorm)
  have h2 : 1 - w * (u : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    have hn : ‖w * (u : ℂ) ^ 2‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg w, norm_nonneg ((u : ℂ)^2)]
    rw [← he, norm_one] at hn; exact lt_irrefl _ hn)
  rw [show -(n : ℂ) * (u : ℂ) ^ 2 * jacobiSaddlePhase w u =
      (n : ℂ) * (log (1 - (u : ℂ) ^ 2) - log (1 - w * (u : ℂ) ^ 2)) by
        simp only [jacobiSaddlePhase, ite_eq_right hu0]; field_simp [ofReal_ne_zero.mpr hu0]; ring,
    exp_nat_mul, exp_sub, exp_log h1, exp_log h2]
  rfl

/-- The normalized saddle kernel has no denominator zero on its whole real interval. -/
theorem jacobiSaddleKernel_den_ne_zero {w : ℂ} (hw : ‖w‖ < 1) {u : ℝ}
    (hu : |u| ≤ 1) : 1 - w * (u : ℂ) ^ 2 ≠ 0 := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
  have hn : ‖w * (u : ℂ) ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg w, sq_nonneg u]
  intro he
  rw [sub_eq_zero] at he
  rw [← he, norm_one] at hn
  exact lt_irrefl _ hn

/-- The normalized saddle kernel has a strict quadratic decrease in norm over
the entire centered interval. This supplies the estimate away from the saddle. -/
theorem norm_jacobiSaddleKernel_le {w : ℂ} (hw : ‖w‖ < 1) {u : ℝ}
    (hu : |u| ≤ 1) : ‖jacobiSaddleKernel w u‖ ≤ 1 - (1 - ‖w‖) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
  have hd : 0 < 1 - ‖w‖ * u ^ 2 := by nlinarith [norm_nonneg w, sq_nonneg u]
  have hden : 1 - ‖w‖ * u ^ 2 ≤ ‖1 - w * (u : ℂ) ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (w * (u : ℂ) ^ 2)
    rw [norm_one, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hnum : ‖1 - (u : ℂ) ^ 2‖ = 1 - u ^ 2 := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [jacobiSaddleKernel, norm_div, hnum]
  calc
    (1 - u ^ 2) / ‖1 - w * (u : ℂ) ^ 2‖ ≤ (1 - u ^ 2) / (1 - ‖w‖ * u ^ 2) :=
      div_le_div_of_nonneg_left (by linarith) hd hden
    _ ≤ 1 - (1 - ‖w‖) * u ^ 2 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hw.le)) (sq_nonneg (u ^ 2))]

/-- Centering the Möbius contour identifies its degree factor with the normalized
saddle kernel times its value at the saddle. -/
theorem jacobiMobiusKernel_eq_saddleKernel {A B c : ℂ} (hA : A ≠ 0)
    (hc : 0 < c.re) (hcAB : c ^ 2 * A = B) {u : ℝ} (hu : |u| ≤ 1) :
    jacobiMobiusKernel A B c ((u + 1) / 2) =
      (A * (c + 1) ^ 2)⁻¹ * jacobiSaddleKernel (jacobiSaddleShape c) u := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hcp : c + 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hd := jacobiSaddleKernel_den_ne_zero (norm_jacobiSaddleShape_lt_one hc) hu
  have ht : (u + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    have hh := abs_le.mp hu; constructor <;> linarith
  have hL := mobius_resolvent_ne_zero hA hc hcAB (by rw [div_self hc0]; simp) ht
  have hD : 1 - (((u + 1) / 2 : ℝ) : ℂ) + c * (((u + 1) / 2 : ℝ) : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg re he
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero, zero_re] at hh
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h] at hh; linarith
    · nlinarith [ht.1]
  simp only [jacobiMobiusKernel, jacobiSaddleKernel, jacobiSaddleShape] at *
  rw [← hcAB] at *
  push_cast at *
  field_simp
  ring

/-- The quantitative Laplace bound for the actual normalized Jacobi kernel on
a central interval. The only amplitude hypotheses are measurability and a local
linear variation bound. -/
theorem norm_sqrt_mul_integral_jacobiSaddleKernel_sub_le {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) {δ L M : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsmall : 4 * δ ^ 2 ≤ (1 - w).re) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hAc : Measurable A) (hA0 : ‖A 0‖ ≤ M)
    (hA : ∀ u ∈ Icc (-δ) δ, ‖A u - A 0‖ ≤ L * |u|) {n : ℕ} (hn : 0 < n) :
    ‖(Real.sqrt n : ℂ) * (∫ u in Icc (-δ) δ, A u * jacobiSaddleKernel w u ^ n) -
        A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ)‖ ≤
      ((L + M / δ) / ((1 - w).re / 2) + M / ((1 - w).re / 2) ^ 2) / Real.sqrt n := by
  have hu (u : ℝ) (hu : u ∈ Icc (-δ) δ) : |u| ≤ δ := abs_le.mpr hu
  have hq : ∀ u ∈ Icc (-δ) δ, (1 - w).re / 2 ≤ (jacobiSaddlePhase w u).re :=
    fun u h => re_jacobiSaddlePhase_ge hw.le hδhalf hsmall (hu u h)
  have hqt : ∀ u ∈ Icc (-δ) δ, ‖jacobiSaddlePhase w u - jacobiSaddlePhase w 0‖ ≤ 1 * |u| := by
    intro u h
    rw [jacobiSaddlePhase_zero]
    have hb := norm_jacobiSaddlePhase_sub_le hw.le ((hu u h).trans hδhalf)
    have hh := (hu u h).trans hδhalf
    nlinarith [sq_abs u, abs_nonneg u]
  have H := norm_sqrt_mul_integral_laplace_Icc_sub_le
    (half_pos (Complex.re_one_sub_pos hw)) hL hM hδ
    (Nat.cast_pos.mpr hn) hAc (measurable_jacobiSaddlePhase w) hq hA0 hA hqt
  simp only [jacobiSaddlePhase_zero, mul_one, ofReal_natCast] at H
  convert H using 2
  congr 2
  apply setIntegral_congr_fun measurableSet_Icc
  intro u h
  exact congrArg (A u * ·)
    (exp_neg_mul_jacobiSaddlePhase hw ((hu u h).trans_lt (by linarith)) n).symm

/-- Continuity of the normalized saddle kernel on the closed integration interval. -/
theorem continuousOn_jacobiSaddleKernel {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousOn (jacobiSaddleKernel w) (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  exact jacobiSaddleKernel_den_ne_zero hw (abs_le.mpr hu)

/-- Outside the central interval, the normalized kernel has a uniform geometric
bound strictly below one when `0 < δ < 1`. -/
theorem norm_integral_jacobiSaddleKernel_tail_le {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) (hAi : IntegrableOn A (Icc (-1 : ℝ) 1))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    ‖(∫ u in Icc (-1 : ℝ) 1, A u * jacobiSaddleKernel w u ^ n) -
      (∫ u in Icc (-δ) δ, A u * jacobiSaddleKernel w u ^ n)‖ ≤
      (∫ u in Icc (-1 : ℝ) 1, ‖A u‖) * (1 - (1 - ‖w‖) * δ ^ 2) ^ n := by
  have hsub : Icc (-δ) δ ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) hδ1
  have hi := hAi.mul_continuousOn ((continuousOn_jacobiSaddleKernel hw).pow n) isCompact_Icc
  change IntegrableOn (fun u => A u * jacobiSaddleKernel w u ^ n) (Icc (-1 : ℝ) 1) at hi
  rw [← setIntegral_sdiff measurableSet_Icc hi hsub]
  have hR : 0 ≤ 1 - (1 - ‖w‖) * δ ^ 2 := by
    have : δ ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) (sq_nonneg δ)]
  have hb : ∀ u ∈ Icc (-1 : ℝ) 1 \ Icc (-δ) δ,
      ‖A u * jacobiSaddleKernel w u ^ n‖ ≤ ‖A u‖ * (1 - (1 - ‖w‖) * δ ^ 2) ^ n := by
    intro u hu
    have hdu : δ ≤ |u| := by
      by_contra! h
      exact hu.2 (abs_le.mp h.le)
    have hs : δ ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
    rw [norm_mul, norm_pow]
    gcongr
    exact (norm_jacobiSaddleKernel_le hw (abs_le.mpr hu.1)).trans (by nlinarith)
  calc
    _ ≤ ∫ u in Icc (-1 : ℝ) 1 \ Icc (-δ) δ, ‖A u‖ * (1 - (1 - ‖w‖) * δ ^ 2) ^ n :=
      norm_integral_le_of_norm_le (((show IntegrableOn (fun u => ‖A u‖) (Icc (-1 : ℝ) 1) volume from hAi.norm).mono_set sdiff_subset).mul_const _)
        (ae_restrict_of_forall_mem (measurableSet_Icc.diff measurableSet_Icc) hb)
    _ = (∫ u in Icc (-1 : ℝ) 1 \ Icc (-δ) δ, ‖A u‖) * (1 - (1 - ‖w‖) * δ ^ 2) ^ n := by
      rw [integral_mul_const]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (setIntegral_mono_set hAi.norm (ae_of_all _ (fun u => norm_nonneg (A u)))
        (Eventually.of_forall (fun _ h => h.1))) (pow_nonneg hR n)

/-- A differentiable amplitude admits a central interval on which the quantitative
Jacobi Laplace estimate applies, with constants derived rather than assumed. -/
theorem exists_jacobiSaddle_local_bounds {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) (hAd : DifferentiableAt ℝ A 0) :
    ∃ δ L : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 4 * δ ^ 2 ≤ (1 - w).re ∧ 0 ≤ L ∧
      ∀ u ∈ Icc (-δ) δ, ‖A u - A 0‖ ≤ L * |u| := by
  obtain ⟨C, hC⟩ := hAd.isBigO_sub.bound
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hC
  let δ := min (ε / 2) (min (1 / 2) (Real.sqrt (1 - w).re / 2))
  have hq := Complex.re_one_sub_pos hw
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδq : δ ≤ Real.sqrt (1 - w).re / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, |C|, hδ, hδhalf, ?_, abs_nonneg _, ?_⟩
  · have hs := Real.sq_sqrt hq.le
    nlinarith [Real.sqrt_nonneg (1 - w).re]
  · intro u hu
    have huu := abs_le.mpr hu
    have h := hball (show u ∈ Metric.ball 0 ε by simpa [Real.dist_eq] using huu.trans_lt hδε)
    have h' : ‖A u - A 0‖ ≤ C * |u| := by simpa [Real.norm_eq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg u))

/-- The central part of a Jacobi saddle integral has the predicted Gaussian limit. -/
theorem tendsto_sqrt_mul_integral_jacobiSaddleKernel_central {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) {δ L : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsmall : 4 * δ ^ 2 ≤ (1 - w).re) (hL : 0 ≤ L) (hAc : Measurable A)
    (hA : ∀ u ∈ Icc (-δ) δ, ‖A u - A 0‖ ≤ L * |u|) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-δ) δ, A u * jacobiSaddleKernel w u ^ n) atTop
      (𝓝 (A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop 0).mono (fun n hn =>
      norm_sqrt_mul_integral_jacobiSaddleKernel_sub_le hw hδ hδhalf hsmall hL
        (norm_nonneg (A 0)) hAc le_rfl hA hn))
  exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Laplace asymptotics for the full centered Jacobi saddle kernel. Integrability
controls the endpoints, differentiability at zero controls the amplitude near the
saddle, and the complementary pieces decay geometrically. -/
theorem tendsto_sqrt_mul_integral_jacobiSaddleKernel {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) (hAc : Measurable A) (hAi : IntegrableOn A (Icc (-1 : ℝ) 1))
    (hAd : DifferentiableAt ℝ A 0) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-1 : ℝ) 1, A u * jacobiSaddleKernel w u ^ n) atTop
      (𝓝 (A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ))) := by
  obtain ⟨δ, L, hδ, hδhalf, hsmall, hL, hA⟩ := exists_jacobiSaddle_local_bounds hw hAd
  have hcentral := tendsto_sqrt_mul_integral_jacobiSaddleKernel_central hw hδ hδhalf hsmall hL hAc hA
  let R : ℝ := 1 - (1 - ‖w‖) * δ ^ 2
  let M : ℝ := ∫ u in Icc (-1 : ℝ) 1, ‖A u‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  have hR : 0 ≤ R := by dsimp [R]; nlinarith [norm_nonneg w, sq_nonneg δ]
  have hR1 : R < 1 := by dsimp [R]; nlinarith [sq_pos_of_pos hδ]
  have htail : Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
      ((∫ u in Icc (-1 : ℝ) 1, A u * jacobiSaddleKernel w u ^ n) -
       (∫ u in Icc (-δ) δ, A u * jacobiSaddleKernel w u ^ n))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => ((n : ℝ) * R ^ n) * M)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hbound := norm_integral_jacobiSaddleKernel_tail_le hw hAi hδ.le (by linarith) n
      have hs : Real.sqrt n ≤ (n : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn))
      exact (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)).trans
        (show Real.sqrt n * (M * R ^ n) ≤ ((n : ℝ) * R ^ n) * M by
          calc
            _ ≤ (n : ℝ) * (M * R ^ n) := mul_le_mul_of_nonneg_right hs (by positivity)
            _ = _ := by ring)
    · simpa using (tendsto_self_mul_const_pow_of_lt_one hR hR1).mul_const M
  convert htail.add hcentral using 1
  · funext n; ring
  · simp

/-- With a nonzero amplitude at the saddle, the centered Jacobi integral has a
nonzero leading asymptotic equivalent. -/
theorem isEquivalent_integral_jacobiSaddleKernel {A : ℝ → ℂ} {w : ℂ}
    (hw : ‖w‖ < 1) (hAc : Measurable A) (hAi : IntegrableOn A (Icc (-1 : ℝ) 1))
    (hAd : DifferentiableAt ℝ A 0) (hA0 : A 0 ≠ 0) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => ∫ u in Icc (-1 : ℝ) 1, A u * jacobiSaddleKernel w u ^ n)
      (fun n : ℕ => (A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ)) / (Real.sqrt n : ℂ)) := by
  have hC : A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ) ≠ 0 := by
    apply mul_ne_zero hA0
    apply cpow_ne_zero_iff.mpr
    left
    apply div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    intro h
    have hh := Complex.re_one_sub_pos hw
    simp [h] at hh
  have h := (tendsto_sqrt_mul_integral_jacobiSaddleKernel hw hAc hAi hAd).div_const
    (A 0 * (Real.pi / (1 - w)) ^ (1 / 2 : ℂ))
  rw [div_self hC] at h
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert h using 1
  funext n
  simp only [Pi.div_apply]
  field

/-- The fixed-degree amplitude on the centered Jacobi saddle curve. -/
def jacobiSaddleAmplitude (a b : ℂ) (m : ℕ) (r s z : ℂ) (u : ℝ) : ℂ :=
  jacobiMobiusIntegrand a b m (z - r) (z - s) (jacobiSaddleRatio r s z) ((u + 1) / 2)

/-- Composition of a measurable complex function with a fixed principal power
is measurable, including the totalized value at zero. -/
private theorem measurable_cpow_comp {f : ℝ → ℂ} (hf : Measurable f) (a : ℂ) :
    Measurable (fun u => f u ^ a) := by
  simp only [cpow_def]
  apply Measurable.ite (by measurability) measurable_const
  exact Complex.measurable_exp.comp ((Complex.measurable_log.comp hf).mul_const a)

/-- The centered Jacobi amplitude is measurable on the whole real line. -/
theorem measurable_jacobiSaddleAmplitude (a b : ℂ) (m : ℕ) (r s z : ℂ) :
    Measurable (jacobiSaddleAmplitude a b m r s z) := by
  unfold jacobiSaddleAmplitude jacobiMobiusIntegrand Polynomial.complexJacobiWeight
  apply Measurable.mul
  · apply Measurable.mul
    · exact measurable_const.mul ((measurable_cpow_comp (by fun_prop) a).mul
        (measurable_cpow_comp (by fun_prop) b))
    · exact measurable_cpow_comp (by fun_prop) _
  · fun_prop

/-- Positive real parts of the base exponents make the centered Jacobi amplitude
continuous and integrable up to both endpoints. -/
theorem continuousOn_jacobiSaddleAmplitude {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ContinuousOn (jacobiSaddleAmplitude a b m r s z) (Icc (-1 : ℝ) 1) := by
  intro u hu
  have ht : (u + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  have H := (continuousAt_jacobiMobiusIntegrand_saddle ha hb m hz ht).comp
    (f := fun v : ℝ => (z, (v + 1) / 2)) (by fun_prop)
  exact H.continuousWithinAt

/-- The Möbius amplitude is differentiable at every interior point of the
parameter interval, with no restrictions on its complex exponents. -/
theorem differentiableAt_jacobiMobiusIntegrand (a b : ℂ) (m : ℕ) {A B c : ℂ}
    (hA : A ≠ 0) (hc : 0 < c.re) (hcAB : c ^ 2 * A = B) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (jacobiMobiusIntegrand a b m A B c) t := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hD : 1 - (t : ℂ) + c * t ∈ slitPlane := by
    left
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
    nlinarith [ht.1, ht.2]
  have hL := mobius_resolvent_ne_zero hA hc hcAB (by rw [div_self hc0]; simp)
    (Ioo_subset_Icc_self ht)
  have hw : DifferentiableAt ℂ (Polynomial.complexJacobiWeight a b) (t : ℂ) := by
    simpa only [sub_add_cancel] using
      (Polynomial.hasDerivAt_complexJacobiWeight_succ (a - 1) (b - 1)
        (ofReal_mem_slitPlane.mpr ht.1)
        (by left; simp only [sub_re, one_re, ofReal_re]; linarith [ht.2])).differentiableAt
  have hd : DifferentiableAt ℂ (fun v : ℂ => c ^ (a + 1) *
      Polynomial.complexJacobiWeight a b v * (1 - v + c * v) ^ ((m : ℂ) - a - b - 2) *
        (c * v * A + (1 - v) * B) ^ (-(m : ℤ))) (t : ℂ) := by
    apply DifferentiableAt.mul
    · exact (differentiableAt_const _ |>.mul hw).mul
        (((differentiableAt_const _).sub differentiableAt_id |>.add
          (differentiableAt_const _ |>.mul differentiableAt_id)).cpow_const hD)
    · exact ((differentiableAt_const _ |>.mul differentiableAt_id |>.mul_const A).add
        ((differentiableAt_const _).sub differentiableAt_id |>.mul_const B)).zpow (Or.inl hL)
  exact hd.hasDerivAt.comp_ofReal.differentiableAt

/-- The centered Jacobi amplitude is differentiable at the saddle for all complex
exponents. A fixed degree shift is needed only to control the endpoints. -/
theorem differentiableAt_jacobiSaddleAmplitude (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) : DifferentiableAt ℝ (jacobiSaddleAmplitude a b m r s z) 0 := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hd := differentiableAt_jacobiMobiusIntegrand a b m (sub_ne_zero.mpr hzr)
    (re_jacobiSaddleRatio_pos hz) (jacobiSaddleRatio_sq_mul hzr)
    (show (0 + 1) / 2 ∈ Ioo (0 : ℝ) 1 by norm_num)
  exact hd.comp 0 (by fun_prop)

/-- The Jacobi amplitude at its saddle is nonzero, for all complex exponents. -/
theorem jacobiSaddleAmplitude_zero_ne_zero (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) : jacobiSaddleAmplitude a b m r s z 0 ≠ 0 := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hc := re_jacobiSaddleRatio_pos hz
  have hc0 : jacobiSaddleRatio r s z ≠ 0 := by intro h; simp [h] at hc
  have hL := mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc
    (jacobiSaddleRatio_sq_mul hzr) (by rw [div_self hc0]; simp)
    (show (0 + 1) / 2 ∈ Icc (0 : ℝ) 1 by norm_num)
  have hD : 1 - (((0 + 1) / 2 : ℝ) : ℂ) + jacobiSaddleRatio r s z * (((0 + 1) / 2 : ℝ) : ℂ) ≠ 0 := by
    intro he
    have h := congrArg re he
    norm_num at h
    linarith
  unfold jacobiSaddleAmplitude jacobiMobiusIntegrand Polynomial.complexJacobiWeight
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero ?_ ?_)) ?_) ?_
  · exact cpow_ne_zero_iff.mpr (Or.inl hc0)
  · exact cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact cpow_ne_zero_iff.mpr (Or.inl hD)
  · exact zpow_ne_zero _ hL

/-- The Gaussian limit for the full centered Jacobi amplitude on its actual
Möbius saddle curve, including both complementary pieces of the integral. -/
theorem tendsto_sqrt_mul_integral_jacobiSaddleAmplitude {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) * ∫ u in Icc (-1 : ℝ) 1,
      jacobiSaddleAmplitude a b m r s z u *
        jacobiSaddleKernel (jacobiSaddleShape (jacobiSaddleRatio r s z)) u ^ n) atTop
      (𝓝 (jacobiSaddleAmplitude a b m r s z 0 *
        (Real.pi / (1 - jacobiSaddleShape (jacobiSaddleRatio r s z))) ^ (1 / 2 : ℂ))) :=
  tendsto_sqrt_mul_integral_jacobiSaddleKernel
    (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos hz))
    (measurable_jacobiSaddleAmplitude a b m r s z)
    ((continuousOn_jacobiSaddleAmplitude ha hb m hz).integrableOn_Icc)
    (differentiableAt_jacobiSaddleAmplitude a b m hz)

/-- The reciprocal of the degree factor at the Jacobi saddle. -/
def jacobiSaddleScale (r s z : ℂ) : ℂ :=
  (z - r) * (jacobiSaddleRatio r s z + 1) ^ 2

/-- The saddle scale is nonzero off the focal segment, also for coincident endpoints. -/
theorem jacobiSaddleScale_ne_zero {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    jacobiSaddleScale r s z ≠ 0 := by
  unfold jacobiSaddleScale
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  apply mul_ne_zero (sub_ne_zero.mpr hzr)
  apply pow_ne_zero
  intro h
  have hc := re_jacobiSaddleRatio_pos hz
  have he := congrArg re h
  simp only [add_re, one_re, zero_re] at he
  linarith

/-- The Gaussian leading constant for the unnormalized Jacobi Euler integral.
The factor `1/2` is the Jacobian of the centered parameter. -/
def jacobiSaddleLeading (a b : ℂ) (m : ℕ) (r s z : ℂ) : ℂ :=
  jacobiSaddleAmplitude a b m r s z 0 *
    (Real.pi / (1 - jacobiSaddleShape (jacobiSaddleRatio r s z))) ^ (1 / 2 : ℂ) / 2

/-- The leading Gaussian constant of the Jacobi Euler integral is nonzero. -/
theorem jacobiSaddleLeading_ne_zero (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) : jacobiSaddleLeading a b m r s z ≠ 0 := by
  apply div_ne_zero _ (by norm_num)
  apply mul_ne_zero (jacobiSaddleAmplitude_zero_ne_zero a b m hz)
  apply cpow_ne_zero_iff.mpr
  left
  apply div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  intro h
  have hh := Complex.re_one_sub_pos (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos hz))
  simp [h] at hh

/-- The centered saddle integral is exactly the shifted-degree Möbius integral,
after extracting the saddle scale and the centering Jacobian. -/
theorem integral_jacobiSaddleAmplitude_mul_kernel_pow (a b : ℂ) (m k : ℕ)
    {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    (∫ u in Icc (-1 : ℝ) 1, jacobiSaddleAmplitude a b m r s z u *
      jacobiSaddleKernel (jacobiSaddleShape (jacobiSaddleRatio r s z)) u ^ k) =
      jacobiSaddleScale r s z ^ k * 2 * ∫ t in (0 : ℝ)..1,
        jacobiMobiusIntegrand (a + k) (b + k) (m + k) (z - r) (z - s)
          (jacobiSaddleRatio r s z) t := by
  let F := jacobiMobiusIntegrand (a + k) (b + k) (m + k) (z - r) (z - s)
    (jacobiSaddleRatio r s z)
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hc := re_jacobiSaddleRatio_pos hz
  have hc0 : jacobiSaddleRatio r s z ≠ 0 := by intro h; simp [h] at hc
  have hscale := jacobiSaddleScale_ne_zero hz
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  calc
    _ = ∫ u in (-1 : ℝ)..1, jacobiSaddleScale r s z ^ k * F ((u + 1) / 2) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (1 : ℝ)] with u hu huint
      simp only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Ioc] at huint
      have ht : (u + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [lt_of_le_of_ne huint.2 hu]
      have hL := mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc (jacobiSaddleRatio_sq_mul hzr)
        (by rw [div_self hc0]; simp) (Ioo_subset_Icc_self ht)
      dsimp only [F, jacobiSaddleAmplitude]
      rw [jacobiMobiusIntegrand_add_nat a b m k _ _ _ hc ht hL,
        jacobiMobiusKernel_eq_saddleKernel (sub_ne_zero.mpr hzr) hc (jacobiSaddleRatio_sq_mul hzr)
          (abs_le.mpr ⟨huint.1.le, huint.2⟩)]
      change _ = jacobiSaddleScale r s z ^ k *
        (_ * ((jacobiSaddleScale r s z)⁻¹ * _) ^ k)
      rw [mul_pow, inv_pow]
      field_simp
    _ = jacobiSaddleScale r s z ^ k * (2 * ∫ t in (0 : ℝ)..1, F t) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have he := intervalIntegral.integral_comp_add_div (a := (-1 : ℝ)) (b := 1) F
        (by norm_num : (2 : ℝ) ≠ 0) (1 / 2)
      calc
        _ = ∫ u in (-1 : ℝ)..1, F (1 / 2 + u / 2) := by
          apply intervalIntegral.integral_congr
          intro u _
          exact congrArg F (by ring : (u + 1) / 2 = 1 / 2 + u / 2)
        _ = _ := by convert he using 1; norm_num [real_smul]
    _ = _ := by ring

/-- The Laplace limit of the original Möbius Euler integral, after removing
its geometric saddle factor. The base exponents can always be made positive by
a fixed degree shift. -/
theorem tendsto_sqrt_mul_pow_mul_integral_jacobiMobius {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) :
    Tendsto (fun k : ℕ => (Real.sqrt k : ℂ) * jacobiSaddleScale r s z ^ k *
      ∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (a + k) (b + k) (m + k)
        (z - r) (z - s) (jacobiSaddleRatio r s z) t) atTop
      (𝓝 (jacobiSaddleLeading a b m r s z)) := by
  have h := (tendsto_sqrt_mul_integral_jacobiSaddleAmplitude ha hb m hz).div_const 2
  convert h using 1
  · funext k
    rw [integral_jacobiSaddleAmplitude_mul_kernel_pow a b m k hz]
    ring
  · rfl

/-- The unnormalized shifted-degree Euler integral has an asymptotic equivalent
with an explicitly defined, nonzero Gaussian coefficient. -/
theorem isEquivalent_integral_jacobiMobius {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    Asymptotics.IsEquivalent atTop
      (fun k : ℕ => ∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (a + k) (b + k) (m + k)
        (z - r) (z - s) (jacobiSaddleRatio r s z) t)
      (fun k : ℕ => jacobiSaddleLeading a b m r s z /
        ((Real.sqrt k : ℂ) * jacobiSaddleScale r s z ^ k)) := by
  have h := (tendsto_sqrt_mul_pow_mul_integral_jacobiMobius ha hb m hz).div_const
    (jacobiSaddleLeading a b m r s z)
  rw [div_self (jacobiSaddleLeading_ne_zero a b m hz)] at h
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert h using 1
  funext k
  simp only [Pi.div_apply]
  field

/-- At coincident reference endpoints, the Möbius integrand is just the beta weight. -/
theorem jacobiMobiusIntegrand_reference (a b : ℂ) (m : ℕ) (t : ℝ) :
    jacobiMobiusIntegrand a b m (1 - 0) (1 - 0) (jacobiSaddleRatio 0 0 1) t =
      Polynomial.complexJacobiWeight a b t := by
  simp [jacobiSaddleRatio, jacobiMobiusIntegrand]

/-- The reference saddle scale for the beta integral is four. -/
@[simp] theorem jacobiSaddleScale_reference : jacobiSaddleScale 0 0 1 = 4 := by
  norm_num [jacobiSaddleScale, jacobiSaddleRatio]

/-- Dividing the deformed Euler integral by the reference beta integral gives the
second-kind Jacobi function. This cancels the Gamma normalization exactly. -/
theorem jacobiSecondKind_eq_saddle_integral_div_reference (α β r s : ℂ) (N k : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {z : ℂ}
    (hz : z ∉ segment ℝ r s) :
    jacobiSecondKind α β r s (N + k) z =
      (∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (α + N + k) (β + N + k) (N + 1 + k)
        (z - r) (z - s) (jacobiSaddleRatio r s z) t) /
      (∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (α + N + k) (β + N + k) (N + 1 + k)
        (1 - 0) (1 - 0) (jacobiSaddleRatio 0 0 1) t) := by
  have ha : 0 < (α + (N + k : ℕ)).re := by
    simp only [Nat.cast_add, ← add_assoc, add_re, natCast_re] at *
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hb : 0 < (β + (N + k : ℕ)).re := by
    simp only [Nat.cast_add, ← add_assoc, add_re, natCast_re] at *
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  rw [jacobiSecondKind_eq_integral_mobius α β r s (N + k) ha hb hz]
  simp only [jacobiMobiusIntegrand_reference]
  have he : (∫ t in (0 : ℝ)..1, Polynomial.complexJacobiWeight (α + N + k) (β + N + k) t) =
      betaIntegral (α + (N + k : ℕ) + 1) (β + (N + k : ℕ) + 1) := by
    simp only [betaIntegral, Polynomial.complexJacobiWeight, Nat.cast_add, ← add_assoc, add_sub_cancel_right]
  rw [he, betaIntegral_eq_Gamma_mul_div _ _ (by simpa using (by linarith : 0 < (α + (N + k : ℕ)).re + 1))
    (by simpa using (by linarith : 0 < (β + (N + k : ℕ)).re + 1))]
  simp only [Nat.cast_add, ← add_assoc, show N + k + 1 = N + 1 + k by omega]
  field

/-- The ratio of the actual and reference Gaussian constants for a fixed base degree. -/
def jacobiSecondKindSaddleCoefficient (α β : ℂ) (N : ℕ) (r s z : ℂ) : ℂ :=
  jacobiSaddleLeading (α + N) (β + N) (N + 1) r s z /
    jacobiSaddleLeading (α + N) (β + N) (N + 1) 0 0 1

/-- The Jacobi asymptotic coefficient is nonzero off the segment. -/
theorem jacobiSecondKindSaddleCoefficient_ne_zero (α β : ℂ) (N : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) : jacobiSecondKindSaddleCoefficient α β N r s z ≠ 0 :=
  div_ne_zero (jacobiSaddleLeading_ne_zero _ _ _ hz)
    (jacobiSaddleLeading_ne_zero _ _ _ (by simp))

/-- Pointwise second-kind Jacobi asymptotics after a fixed degree shift, for all
complex parameters whose shifted base exponents have positive real parts.
The Gamma factor is removed by comparison with the beta integral, so the leading
coefficient is independent of the growing degree. -/
theorem isEquivalent_jacobiSecondKind_saddle_shift (α β r s : ℂ) (N : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {z : ℂ}
    (hz : z ∉ segment ℝ r s) :
    Asymptotics.IsEquivalent atTop (fun k : ℕ => jacobiSecondKind α β r s (N + k) z)
      (fun k : ℕ => jacobiSecondKindSaddleCoefficient α β N r s z *
        (4 / jacobiSaddleScale r s z) ^ k) := by
  have h := (isEquivalent_integral_jacobiMobius hα hβ (N + 1) hz).div
    (isEquivalent_integral_jacobiMobius hα hβ (N + 1)
      (r := 0) (s := 0) (z := 1) (by simp))
  apply (h.congr_left (Eventually.of_forall (fun k =>
    (jacobiSecondKind_eq_saddle_integral_div_reference α β r s N k hα hβ hz).symm))).congr_right
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hs : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)).ne'
  have hscale := jacobiSaddleScale_ne_zero hz
  have hC := jacobiSaddleLeading_ne_zero (α + N) (β + N) (N + 1) (r := 0) (s := 0) (z := 1) (by simp)
  simp only [Pi.div_apply, jacobiSaddleScale_reference, jacobiSecondKindSaddleCoefficient, div_pow]
  field_simp

/-- The pointwise second-kind asymptotic of Carlson §7.4: for every complex
parameter pair and every point off the focal segment, a nonzero degree-independent
coefficient multiplies the sharp geometric saddle factor. This theorem does not
assert uniformity on compact sets. -/
theorem exists_isEquivalent_jacobiSecondKind_geometric (α β r s : ℂ) {z : ℂ}
    (hz : z ∉ segment ℝ r s) :
    ∃ C : ℂ, C ≠ 0 ∧ Asymptotics.IsEquivalent atTop
      (fun n : ℕ => jacobiSecondKind α β r s n z)
      (fun n : ℕ => C * (4 / jacobiSaddleScale r s z) ^ n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-α.re) (-β.re))
  have hα : 0 < (α + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_left (-α.re) (-β.re)]
  have hβ : 0 < (β + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_right (-α.re) (-β.re)]
  let G := 4 / jacobiSaddleScale r s z
  have hG : G ≠ 0 := div_ne_zero (by norm_num) (jacobiSaddleScale_ne_zero hz)
  refine ⟨jacobiSecondKindSaddleCoefficient α β N r s z / G ^ N,
    div_ne_zero (jacobiSecondKindSaddleCoefficient_ne_zero α β N hz) (pow_ne_zero _ hG), ?_⟩
  have h := (isEquivalent_jacobiSecondKind_saddle_shift α β r s N hα hβ hz).comp_tendsto
    (tendsto_sub_atTop_nat N)
  have he : ((fun k => jacobiSecondKind α β r s (N + k) z) ∘ fun n => n - N) =ᶠ[atTop]
      (fun n => jacobiSecondKind α β r s n z) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Function.comp_apply]
    congr 1
    omega
  apply (h.congr_left he).congr_right
  filter_upwards [eventually_ge_atTop N] with n hn
  change jacobiSecondKindSaddleCoefficient α β N r s z * G ^ (n - N) =
    jacobiSecondKindSaddleCoefficient α β N r s z / G ^ N * G ^ n
  have hpow : G ^ (n - N) * G ^ N = G ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [← hpow]
  field_simp

/-- The modulus of the complex saddle scale is four times Carlson's elliptic
mean radius. Thus the geometric asymptotic has norm ratio `1/μ(z)`. -/
theorem norm_jacobiSaddleScale {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ‖jacobiSaddleScale r s z‖ = 4 * jacobiEllipseRadius r s z := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  let c := jacobiSaddleRatio r s z
  have hc : 0 < c.re := re_jacobiSaddleRatio_pos hz
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (z - r) (by norm_num : 0 < (2 : ℕ))
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ha
    exact sub_ne_zero.mpr hzr ha.symm
  let b := a * c
  have hb : b ^ 2 = z - s := by
    dsimp [b]
    rw [mul_pow, ha, mul_comm]
    exact jacobiSaddleRatio_sq_mul hzr
  have hab : 0 ≤ (a * starRingEnd ℂ b).re := by
    have he : (a * starRingEnd ℂ b).re = normSq a * c.re := by
      simp only [b, map_mul, mul_re, mul_im, conj_re, conj_im, normSq_apply]
      ring
    rw [he]
    exact (mul_pos (normSq_pos.mpr ha0) hc).le
  rw [jacobiEllipseRadius_eq_sq_of_re_mul_conj_nonneg r s z a b ha hb hab]
  have he : jacobiSaddleScale r s z = (a + b) ^ 2 := by
    dsimp [jacobiSaddleScale, b, c]
    rw [← ha]
    ring
  rw [he, norm_pow]
  ring

end Carlson.TwoVariable
