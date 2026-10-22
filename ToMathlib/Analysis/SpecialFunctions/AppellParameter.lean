/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.AppellF2F3
public import ToMathlib.Analysis.SpecialFunctions.GammaShiftBounds
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Entire denominator dependence of regularized Appell F₃

The double series converges locally uniformly in its denominator parameter on
the whole complex plane. Compact uniform reciprocal-Gamma bounds and two scalar
Gauss-series majorants preserve the full argument bidisk, including Gamma poles.
Mathlib's Weierstrass theorem gives entire dependence on the denominator parameter.
-/

open Complex Set Polynomial Filter
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- Gauss-type coefficient series are summable throughout the unit disk. -/
private theorem summable_HG_unit {A C : Multiset ℂ} (hcard : A.card = C.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => regularizedHGFunCoeff A C n * z ^ n) := by
  apply (hasSum_regularizedHGFun_of_mem_eball ?_).summable
  rw [Metric.mem_eball, edist_zero_right]
  apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one hcard)
  rw [← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

/-- The total-degree Gauss coefficient is a factorial times reciprocal Gamma. -/
private theorem regularizedHGFunCoeff_one_one (c : ℂ) (N : ℕ) :
    regularizedHGFunCoeff {1, 1} {c} N = (N.factorial : ℂ) * (Gamma (c + N))⁻¹ := by
  simp [regularizedHGFunCoeff, ascPochhammer_eval_one, div_eq_mul_inv, mul_inv_rev,
    mul_left_comm, mul_comm, Nat.cast_ne_zero.mpr N.factorial_ne_zero]

/-- A compact uniform majorant for the `F₃` double series with variable denominator. -/
private theorem exists_summable_norm_regularizedAppellF3_denominator
    (a a' b b' : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ M : ℕ × ℕ → ℝ, Summable M ∧ ∀ p c, c ∈ K →
      ‖regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2‖ ≤ M p := by
  obtain ⟨r, hr, hr1⟩ := exists_between (max_lt hx hy)
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let B := fun n => regularizedHGFunCoeff {a, b} {1} n * (x / (r : ℂ)) ^ n
  let D := fun n => regularizedHGFunCoeff {a', b'} {1} n * (y / (r : ℂ)) ^ n
  have hBs : Summable B := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_left _ _).trans_lt hr))
  have hDs : Summable D := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_right _ _).trans_lt hr))
  obtain ⟨C, hC0, hC⟩ := exists_uniform_norm_factorial_mul_inv_Gamma_mul_pow hK hr0.le hr1
  have hA (c : ℂ) (hc : c ∈ K) (N : ℕ) :
      ‖regularizedHGFunCoeff {1, 1} {c} N * (r : ℂ) ^ N‖ ≤ C := by
    simpa only [regularizedHGFunCoeff_one_one, norm_mul, norm_pow, norm_natCast,
      norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hC c hc N
  have hM := (hBs.norm.mul_of_nonneg hDs.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)).mul_left C
  refine ⟨fun p => C * (‖B p.1‖ * ‖D p.2‖), hM, fun p c hc => ?_⟩
  have he : regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2 =
      (regularizedHGFunCoeff {1, 1} {c} (p.1 + p.2) * (r : ℂ) ^ (p.1 + p.2)) *
        B p.1 * D p.2 / ((p.1 + p.2).choose p.1 : ℂ) := by
    dsimp [B, D, regularizedAppellF3Coeff]
    rw [pow_add, div_pow, div_pow]
    field_simp
  rw [he, norm_div, norm_mul, norm_mul, norm_natCast]
  have hchoose : (1 : ℝ) ≤ ((p.1 + p.2).choose p.1 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
  calc
    _ ≤ ‖regularizedHGFunCoeff {1, 1} {c} (p.1 + p.2) * (r : ℂ) ^ (p.1 + p.2)‖ *
        ‖B p.1‖ * ‖D p.2‖ := div_le_self (by positivity) hchoose
    _ ≤ C * ‖B p.1‖ * ‖D p.2‖ := by gcongr; exact hA c hc _
    _ = _ := by ring

/-- The regularized `F₃` series converges locally uniformly in every denominator parameter,
including at nonpositive integers, on the full argument bidisk. -/
theorem summableLocallyUniformlyOn_regularizedAppellF3_denominator
    (a a' b b' : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    SummableLocallyUniformlyOn
      (fun (p : ℕ × ℕ) (c : ℂ) => regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2)
      univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _ hK
  exact exists_summable_norm_regularizedAppellF3_denominator a a' b b' hx hy hK

/-- Regularized `F₃` is entire in its denominator parameter, on the full argument bidisk. -/
theorem analyticOnNhd_regularizedAppellF3_denominator (a a' b b' : ℂ)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    AnalyticOnNhd ℂ (fun c => regularizedAppellF3 a a' b b' c x y) univ := by
  have hterm (p : ℕ × ℕ) : AnalyticOnNhd ℂ (fun c =>
      regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2) univ := by
    have he : (fun c => regularizedAppellF3Coeff a a' b b' c p * x ^ p.1 * y ^ p.2) =
        fun c => ((ascPochhammer ℂ p.1).eval a * (ascPochhammer ℂ p.2).eval a' *
          (ascPochhammer ℂ p.1).eval b * (ascPochhammer ℂ p.2).eval b' /
          ((p.1.factorial : ℂ) * p.2.factorial) * x ^ p.1 * y ^ p.2) *
          (Gamma (c + (p.1 + p.2 : ℕ)))⁻¹ := by
      funext c
      rw [regularizedAppellF3Coeff_eq]
      ring
    rw [he]
    intro c _
    apply AnalyticAt.mul analyticAt_const
    exact (differentiable_one_div_Gamma.analyticAt _).comp
      (f := fun c : ℂ => c + (p.1 + p.2 : ℕ)) (analyticAt_id.add analyticAt_const)
  have hs := summableLocallyUniformlyOn_regularizedAppellF3_denominator a a' b b' hx hy
  have hsum := hs.hasSumLocallyUniformlyOn
  exact (hsum.differentiableOn (Eventually.of_forall (fun s =>
    DifferentiableOn.fun_sum (fun p _ => (hterm p).differentiableOn)))
    isOpen_univ).analyticOnNhd isOpen_univ

end Complex
