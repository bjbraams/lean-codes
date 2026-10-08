/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import ToMathlib.Analysis.Integral.FunSplitAt
public import ToMathlib.Analysis.Integral.Tail
public import ToMathlib.Analysis.MellinBarnes
public import ToMathlib.Analysis.SchwartzExpExp
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The Paley–Wiener theorem

Let `F` be an entire function on `ℂ^ι` with

`‖F ζ‖ ≤ C_N (1 + ‖ζ‖)^(-N) exp (2π ∑ i, ρ i |Im ζ i|)`.

Then the inverse Fourier transform `f` of the restriction of `F` to `ℝ^ι` vanishes outside the
box `|x i| ≤ ρ i`, and `F` is the Fourier–Laplace transform of `f`.

The support statement reduces to one variable. For `|x j| > ρ j`, Fubini isolates the `j`-th
frequency, and in that variable the line of integration is shifted to `ℝ + iη` by Cauchy's
theorem on rectangles (`Complex.integral_add_mul_I_eq_of_bound`). The shifted integral is bounded
by a multiple of `exp (2π (ρ j - |x j|) |η|)`, which tends to zero as `|η| → ∞` in the right
direction.

## Main results

* `Complex.integral_add_mul_I_eq_of_bound`: shifting a line of integration for an entire
  function that decays like `(1 + |x|)^(-2)` uniformly in a horizontal strip.
* `PaleyWiener.fourierInv_eq_zero_of_bound`: the support statement, from one bound with
  `N = card ι + 2`.
* `PaleyWiener.fourierInv_of_bound`: under the bounds for every `N`, `f = 𝓕⁻ (F|ℝ^ι)` is smooth,
  vanishes outside the box, has compact support, and `𝓕 f = F|ℝ^ι`.
* `PaleyWiener.norm_fourierLaplace_le_of_contDiff`: the converse bounds for smooth `ψ` supported
  in the box `Function.support ψ ⊆ Set.univ.pi fun j ↦ Icc (-ρ j) (ρ j)`.
* `PaleyWiener.fourierLaplace_lineDeriv`: integration by parts for `lineDeriv`.
* `PaleyWiener.fourier_eq_fourierLaplace`, `PaleyWiener.eq_zero_of_fourierLaplace_eq_zero`: the
  Fourier–Laplace transform on real frequencies and its injectivity.

Conversely (`norm_fourierLaplace_le_of_contDiff`), the Fourier–Laplace transform
`FL ψ(ζ) = ∫ e^(-2πi ⟨ζ, w⟩) ψ(w) dw` of a smooth function vanishing outside the box satisfies
these bounds: `‖FL ψ(ζ)‖ ≤ ‖ψ‖₁ exp (2π ∑ ρ j |Im ζ j|)`, and integration by parts gives
`FL (∂_j ψ) = 2πi ζ_j FL ψ`. A continuous compactly supported `ψ` whose transform vanishes at the
real points is zero (`eq_zero_of_fourierLaplace_eq_zero`, by Fourier inversion).

The identification of `F` at complex points with the Fourier–Laplace transform of `f` follows
from uniqueness of entire functions agreeing on `ℝ^ι`; it is not stated here, because the
several-variable uniqueness theorem lives in a layer above `ToMathlib`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983,
  Theorem 7.3.1.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Topology FourierTransform Real ContDiff

/-- **Shifting a horizontal line of integration.** If `f` is entire and
`‖f (x + y I)‖ ≤ C (1 + |x|)^(-2)` whenever `|y| ≤ |η|`, then
`∫ f (x + η I) dx = ∫ f x dx`. This is `Complex.integral_vertical_eq_of_bound` for
`s ↦ f (I s)`. -/
theorem Complex.integral_add_mul_I_eq_of_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {η C : ℝ}
    (hC : ∀ x y : ℝ, |y| ≤ |η| → ‖f (x + y * I)‖ ≤ C * (1 + |x|) ^ (-2 : ℝ)) :
    ∫ x : ℝ, f (x + η * I) = ∫ x : ℝ, f x := by
  have hrot (σ t : ℝ) : I * ((σ : ℂ) + t * I) = ((-t : ℝ) : ℂ) + σ * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hline (σ : ℝ) : ∫ t : ℝ, f (I * ((σ : ℂ) + t * I)) = ∫ x : ℝ, f (x + σ * I) := by
    simp_rw [hrot]
    exact integral_neg_eq_self (fun x : ℝ ↦ f (x + σ * I)) volume
  have key : ∀ a b : ℝ, a ≤ b → (∀ σ, a ≤ σ → σ ≤ b → |σ| ≤ |η|) →
      ∫ x : ℝ, f (x + a * I) = ∫ x : ℝ, f (x + b * I) := by
    intro a b hab hσ
    rw [← hline, ← hline]
    refine Complex.integral_vertical_eq_of_bound (C := C) hab
      (fun s _ _ ↦ (hf _).comp s (differentiableAt_id.const_mul I)) fun σ t h1 h2 ↦ ?_
    simpa [hrot] using hC (-t) σ (hσ σ h1 h2)
  have h0 := key (min 0 η) (max 0 η) (min_le_max) fun σ h1 h2 ↦ by
    rcases le_total 0 η with h | h
    · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
      rw [abs_of_nonneg h1, abs_of_nonneg h]; exact h2
    · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
      rw [abs_of_nonpos h2, abs_of_nonpos h]; linarith
  rcases le_total 0 η with h | h
  · simpa [min_eq_left h, max_eq_right h] using h0.symm
  · simpa [min_eq_right h, max_eq_left h] using h0

namespace PaleyWiener

section Support

variable {ι : Type*} [Fintype ι]

/-- The real points of `ℂ^ι` corresponding to a vector of `EuclideanSpace ℝ ι`. -/
def realPoint (ξ : EuclideanSpace ℝ ι) : ι → ℂ := fun i ↦ (ξ i : ℂ)

/-- The real coordinate vector has norm at most that of any complex vector with the same real
parts. -/
theorem norm_le_norm_of_re {v : ι → ℝ} {ζ : ι → ℂ} (h : ∀ i, (ζ i).re = v i) : ‖v‖ ≤ ‖ζ‖ :=
  pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun i ↦ by
    rw [Real.norm_eq_abs, ← h i]
    exact (abs_re_le_norm _).trans (norm_le_pi_norm ζ i)

/-- **Paley–Wiener, support.** Let `F` be entire on `ℂ^ι` with
`‖F ζ‖ ≤ C (1 + ‖ζ‖)^(-(card ι + 2)) exp (2π ∑ i, ρ i |Im ζ i|)` and `ρ ≥ 0`. Then the inverse
Fourier transform of the restriction of `F` to `ℝ^ι` vanishes at every `x` with `|x j| > ρ j`
for some `j`. -/
theorem fourierInv_eq_zero_of_bound {F : (ι → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {C : ℝ}
    (hbd : ∀ ζ, ‖F ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(Fintype.card ι + 2 : ℝ)) *
      Real.exp (2 * π * ∑ i, ρ i * |(ζ i).im|))
    {x : EuclideanSpace ℝ ι} {j : ι} (hj : ρ j < |x j|) :
    𝓕⁻ (fun ξ ↦ F (realPoint ξ)) x = 0 := by
  classical
  set N : ℝ := Fintype.card ι + 2
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hbd 0)
    have hpos : 0 < (1 + ‖(0 : ι → ℂ)‖) ^ (-N) *
        Real.exp (2 * π * ∑ i, ρ i * |((0 : ι → ℂ) i).im|) := by positivity
    nlinarith [mul_assoc C ((1 + ‖(0 : ι → ℂ)‖) ^ (-N))
      (Real.exp (2 * π * ∑ i, ρ i * |((0 : ι → ℂ) i).im|))]
  have hxj : x j ≠ 0 := fun h ↦ by rw [h, abs_zero] at hj; linarith [hρ j]
  -- The integrand on `ι → ℝ`.
  set Φ : (ι → ℝ) → ℂ := fun v ↦
    Complex.exp (↑(2 * π * ∑ i, v i * x i) * I) * F (fun i ↦ (v i : ℂ)) with hΦ
  have hΦeq : 𝓕⁻ (fun ξ ↦ F (realPoint ξ)) x = ∫ v : ι → ℝ, Φ v := by
    rw [Real.fourierInv_eq', ← (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    simp only [Φ, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul]
    rw [show (∑ i, x.ofLp i * v i) = ∑ i, v i * x.ofLp i from
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _]
    rfl
  -- Integrability of `Φ`.
  have hFc : Continuous F := hF.continuous
  have hΦc : Continuous Φ := by
    simp only [Φ]
    refine Continuous.mul (by fun_prop) (hFc.comp (continuous_pi fun i ↦
      continuous_ofReal.comp (continuous_apply i)))
  have hΦi : Integrable Φ := by
    have hN : ((Module.finrank ℝ (ι → ℝ) : ℕ) : ℝ) < N := by
      simp [N, Module.finrank_fintype_fun_eq_card]
    refine ((integrable_one_add_norm hN).const_mul C).mono' hΦc.aestronglyMeasurable
      (Eventually.of_forall fun v ↦ ?_)
    simp only [Φ, norm_mul, Complex.norm_exp]
    have hre : (↑(2 * π * ∑ i, v i * x i) * I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    refine (hbd _).trans ?_
    have him : ∑ i, ρ i * |((fun i ↦ (v i : ℂ)) i).im| = 0 := by simp
    rw [him, mul_zero, Real.exp_zero, mul_one, Real.rpow_neg (by positivity),
      Real.rpow_neg (by positivity)]
    gcongr
    exact norm_le_norm_of_re fun i ↦ by simp
  -- Split off the `j`-th coordinate.
  have hsplit := volume_preserving_funSplitAt (ι := ι) j
  set e := Homeomorph.funSplitAt ℝ j
  have hΦ' : Integrable (Φ ∘ e.symm) ((volume : Measure ℝ).prod volume) := by
    rw [← hsplit.integrable_comp_emb e.measurableEmbedding]
    simpa [Function.comp_def] using hΦi
  have hsp : ∫ v : ι → ℝ, Φ v = ∫ p, (Φ ∘ e.symm) p ∂((volume : Measure ℝ).prod volume) := by
    rw [← hsplit.integral_comp e.measurableEmbedding]
    simp
  rw [hΦeq, hsp, integral_prod_symm _ hΦ']
  -- Each one-dimensional slice integral vanishes.
  suffices hslice : ∀ ξ' : {i // i ≠ j} → ℝ, ∫ t : ℝ, Φ (e.symm (t, ξ')) = 0 by
    simp only [Function.comp_apply, hslice, integral_zero]
  intro ξ'
  set ζ₀ : ι → ℂ := fun i ↦ ((e.symm (0, ξ') i : ℝ) : ℂ)
  set S₀ : ℝ := ∑ i, e.symm (0, ξ') i * x i
  have hsymm : ∀ t : ℝ, e.symm (t, ξ') = e.symm (0, ξ') + t • Pi.single j (1 : ℝ) := by
    intro t
    funext i
    by_cases hi : i = j
    · subst hi; simp [e]
    · simp [e, hi]
  set ψ : ℂ → ℂ := fun z ↦
    Complex.exp (2 * π * I * (S₀ + z * x j)) * F (ζ₀ + z • Pi.single j (1 : ℂ))
  have hψ : Differentiable ℂ ψ := by
    refine Differentiable.mul (by fun_prop) (hF.comp ?_)
    exact (differentiable_const _).add (differentiable_id.smul_const _)
  have hψt : ∀ t : ℝ, Φ (e.symm (t, ξ')) = ψ t := by
    intro t
    simp only [Φ, ψ, hsymm t]
    congr 1
    · congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, S₀]
      push_cast
      ring
    · congr 1
      funext i
      by_cases hi : i = j
      · subst hi; simp [ζ₀]
      · simp [ζ₀, hi]
  -- The pointwise bound on horizontal lines.
  have hζ₀ : ∀ i, (ζ₀ i).im = 0 := fun i ↦ by simp [ζ₀]
  have hbound : ∀ t y : ℝ, ‖ψ (t + y * I)‖ ≤
      C * Real.exp (-(2 * π * y * x j)) * Real.exp (2 * π * ρ j * |y|) *
        (1 + |t|) ^ (-2 : ℝ) := by
    intro t y
    simp only [ψ, norm_mul, Complex.norm_exp]
    have hre : (2 * π * I * (S₀ + (t + y * I) * x j)).re = -(2 * π * y * x j) := by
      simp; ring
    rw [hre]
    have hF' := hbd (ζ₀ + (t + y * I) • Pi.single j (1 : ℂ))
    have him : ∑ i, ρ i * |((ζ₀ + (t + y * I) • Pi.single j (1 : ℂ) : ι → ℂ) i).im| =
        ρ j * |y| := by
      rw [Finset.sum_eq_single j]
      · simp [hζ₀]
      · intro i _ hi
        simp [hζ₀, hi]
      · simp
    rw [him] at hF'
    have hnorm : 1 + |t| ≤ 1 + ‖ζ₀ + (t + y * I) • Pi.single j (1 : ℂ)‖ := by
      have := norm_le_pi_norm (ζ₀ + (t + y * I) • Pi.single j (1 : ℂ)) j
      have hj' : (ζ₀ + (t + y * I) • Pi.single j (1 : ℂ) : ι → ℂ) j = ζ₀ j + (t + y * I) := by
        simp
      rw [hj'] at this
      have hz : |t| ≤ ‖ζ₀ j + (t + y * I)‖ := by
        have hre' : (ζ₀ j + (t + y * I)).re = t := by simp [ζ₀, e]
        calc |t| = |(ζ₀ j + (t + y * I)).re| := by rw [hre']
          _ ≤ ‖ζ₀ j + (t + y * I)‖ := abs_re_le_norm _
      linarith
    have hpow : (1 + ‖ζ₀ + (t + y * I) • Pi.single j (1 : ℂ)‖) ^ (-N) ≤ (1 + |t|) ^ (-2 : ℝ) := by
      calc (1 + ‖ζ₀ + (t + y * I) • Pi.single j (1 : ℂ)‖) ^ (-N) ≤ (1 + |t|) ^ (-N) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hnorm
              (by simp only [N, neg_nonpos]; positivity)
        _ ≤ (1 + |t|) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t])
              (by simp [N])
    calc Real.exp (-(2 * π * y * x j)) * ‖F (ζ₀ + (t + y * I) • Pi.single j (1 : ℂ))‖
        ≤ Real.exp (-(2 * π * y * x j)) * (C * (1 + |t|) ^ (-2 : ℝ) *
            Real.exp (2 * π * (ρ j * |y|))) := by
          gcongr
          exact hF'.trans (by gcongr)
      _ = _ := by ring_nf
  -- Shift to `ℝ + iη` and let `|η| → ∞`.
  set a : ℝ := |x j| - ρ j
  have ha : 0 < a := by simp [a]; linarith
  set K : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hshift : ∀ s : ℝ, 0 < s →
      ‖∫ t : ℝ, ψ t‖ ≤ C * K * Real.exp (-(2 * π * a * s)) := by
    intro s hs
    set η : ℝ := if 0 < x j then s else -s
    have hsgn : η * x j = s * |x j| := by
      simp only [η]
      split_ifs with h
      · rw [abs_of_pos h]
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hxj)]; ring
    have habsη : |η| = s := by
      simp only [η]
      split_ifs <;> simp [abs_of_pos hs]
    have hstrip : ∀ t y : ℝ, |y| ≤ |η| → ‖ψ (t + y * I)‖ ≤
        (C * Real.exp (2 * π * |x j| * |η|) * Real.exp (2 * π * ρ j * |η|)) *
          (1 + |t|) ^ (-2 : ℝ) := by
      intro t y hy
      refine (hbound t y).trans ?_
      have h1 : -(2 * π * y * x j) ≤ 2 * π * |x j| * |η| := by
        have : |y * x j| ≤ |x j| * |η| := by
          rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
        nlinarith [neg_abs_le (y * x j), Real.pi_pos]
      have h2 : 2 * π * ρ j * |y| ≤ 2 * π * ρ j * |η| := by
        have := hρ j
        gcongr
      gcongr
    have heq := integral_add_mul_I_eq_of_bound hψ hstrip
    rw [← heq]
    calc ‖∫ t : ℝ, ψ (t + η * I)‖
        ≤ ∫ t : ℝ, C * Real.exp (-(2 * π * η * x j)) * Real.exp (2 * π * ρ j * |η|) *
            (1 + |t|) ^ (-2 : ℝ) :=
          norm_integral_le_of_norm_le
            (integrable_one_add_abs_rpow_neg_two.const_mul _)
            (Eventually.of_forall fun t ↦ hbound t η)
      _ = C * K * Real.exp (-(2 * π * a * s)) := by
          rw [MeasureTheory.integral_const_mul,
            show -(2 * π * η * x j) = -(2 * π * (η * x j)) by ring, hsgn, habsη]
          rw [show C * Real.exp (-(2 * π * (s * |x j|))) * Real.exp (2 * π * ρ j * s) * K =
              C * K * (Real.exp (-(2 * π * (s * |x j|))) * Real.exp (2 * π * ρ j * s)) by ring,
            ← Real.exp_add]
          congr 2
          simp only [a]
          ring
  -- Conclude.
  have hlim : Tendsto (fun s : ℝ ↦ C * K * Real.exp (-(2 * π * a * s))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ -(2 * π * a * s)) atTop atBot := by
      refine tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (by positivity) tendsto_id)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (C * K)
  have hle : ‖∫ t : ℝ, ψ t‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun s hs ↦ hshift s hs)
  simp only [hψt]
  exact norm_le_zero_iff.mp hle

/-- On real points the bound in terms of `‖ζ‖` gives a bound in terms of the Euclidean norm. -/
theorem one_add_norm_rpow_neg_le (ξ : EuclideanSpace ℝ ι) {N : ℝ} (hN : 0 ≤ N) :
    (1 + ‖realPoint ξ‖) ^ (-N) ≤ (1 + Fintype.card ι) ^ N * (1 + ‖ξ‖) ^ (-N) := by
  have hξ : ‖ξ‖ ≤ Fintype.card ι * ‖realPoint ξ‖ := by
    refine (EuclideanSpace.norm_le_sum_abs ξ).trans ?_
    calc ∑ i, |ξ i| ≤ ∑ _i : ι, ‖realPoint ξ‖ := Finset.sum_le_sum fun i _ ↦ by
          simpa [realPoint, Real.norm_eq_abs] using norm_le_pi_norm (realPoint ξ) i
      _ = Fintype.card ι * ‖realPoint ξ‖ := by simp
  have h1 : 1 + ‖ξ‖ ≤ (1 + Fintype.card ι) * (1 + ‖realPoint ξ‖) := by
    nlinarith [norm_nonneg (realPoint ξ), (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]
  set A := 1 + ‖realPoint ξ‖
  set B : ℝ := 1 + Fintype.card ι
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  calc A ^ (-N) = B ^ N * (B * A) ^ (-N) := by
        rw [Real.mul_rpow hB.le hA.le, ← mul_assoc, ← Real.rpow_add hB, add_neg_cancel,
          Real.rpow_zero, one_mul]
    _ ≤ B ^ N * (1 + ‖ξ‖) ^ (-N) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) h1 (neg_nonpos.mpr hN)) (by positivity)

/-- **The Paley–Wiener theorem.** Let `F` be entire on `ℂ^ι`, `ρ ≥ 0`, and suppose that for every
`N` there is `C` with `‖F ζ‖ ≤ C (1 + ‖ζ‖)^(-N) exp (2π ∑ i, ρ i |Im ζ i|)`. Then
`f = 𝓕⁻ (F|ℝ^ι)` is smooth, vanishes outside the box `|x i| ≤ ρ i`, and `𝓕 f = F|ℝ^ι`. -/
theorem fourierInv_of_bound {F : (ι → ℂ) → ℂ} (hF : Differentiable ℂ F) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i)
    (hbd : ∀ N : ℕ, ∃ C, ∀ ζ, ‖F ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ)) *
      Real.exp (2 * π * ∑ i, ρ i * |(ζ i).im|)) :
    ContDiff ℝ ∞ (𝓕⁻ fun ξ ↦ F (realPoint ξ)) ∧
      (∀ x : EuclideanSpace ℝ ι, ∀ j, ρ j < |x j| → 𝓕⁻ (fun ξ ↦ F (realPoint ξ)) x = 0) ∧
      HasCompactSupport (𝓕⁻ fun ξ ↦ F (realPoint ξ)) ∧
      𝓕 (𝓕⁻ fun ξ ↦ F (realPoint ξ)) = fun ξ ↦ F (realPoint ξ) := by
  set g : EuclideanSpace ℝ ι → ℂ := fun ξ ↦ F (realPoint ξ)
  have hgc : Continuous g :=
    hF.continuous.comp (continuous_pi fun i ↦ continuous_ofReal.comp
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)))
  -- Polynomially weighted integrability on the real space.
  have hdecay : ∀ n : ℕ, Integrable fun v : EuclideanSpace ℝ ι ↦ ‖v‖ ^ n * ‖g v‖ := by
    intro n
    set d : ℕ := Fintype.card ι
    obtain ⟨C, hC⟩ := hbd (n + d + 1)
    have hfr : ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℕ) : ℝ) < (d + 1 : ℝ) := by
      simp [d]
    refine ((integrable_one_add_norm hfr).const_mul (C * (1 + d) ^ ((n + d + 1 : ℕ) : ℝ))).mono'
      (by fun_prop) (Eventually.of_forall fun v ↦ ?_)
    have hv := hC (realPoint v)
    have him : ∑ i, ρ i * |(realPoint v i).im| = 0 := by simp [realPoint]
    rw [him, mul_zero, Real.exp_zero, mul_one] at hv
    have hC0 : 0 ≤ C := by
      by_contra h
      have : C * (1 + ‖realPoint v‖) ^ (-((n + d + 1 : ℕ) : ℝ)) < 0 :=
        mul_neg_of_neg_of_pos (not_le.mp h) (by positivity)
      linarith [norm_nonneg (F (realPoint v))]
    have hcmp := one_add_norm_rpow_neg_le v (N := ((n + d + 1 : ℕ) : ℝ)) (by positivity)
    rw [norm_mul, norm_norm, norm_pow, norm_norm]
    calc ‖v‖ ^ n * ‖g v‖ ≤ (1 + ‖v‖) ^ (n : ℝ) *
          (C * ((1 + d) ^ ((n + d + 1 : ℕ) : ℝ) * (1 + ‖v‖) ^ (-((n + d + 1 : ℕ) : ℝ)))) := by
          gcongr
          · rw [Real.rpow_natCast]; gcongr; linarith
          · exact hv.trans (by gcongr)
      _ = C * (1 + d) ^ ((n + d + 1 : ℕ) : ℝ) * (1 + ‖v‖) ^ (-((d : ℝ) + 1)) := by
          rw [show -(((n + d + 1 : ℕ) : ℝ)) = -((d : ℝ) + 1) + -(n : ℝ) by push_cast; ring,
            Real.rpow_add (by positivity), Real.rpow_neg (by positivity) (n : ℝ)]
          field_simp
  have hgi : Integrable g :=
    (integrable_norm_iff hgc.aestronglyMeasurable).mp (by simpa using hdecay 0)
  -- Smoothness.
  have hsmooth : ContDiff ℝ ∞ (𝓕⁻ g) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    refine Real.contDiff_fourier fun n _ ↦ ?_
    have := (hdecay n).comp_neg
    simpa [Function.comp_def, norm_neg] using this
  -- Support.
  obtain ⟨C, hC⟩ := hbd (Fintype.card ι + 2)
  have hsupp : ∀ x : EuclideanSpace ℝ ι, ∀ j, ρ j < |x j| → 𝓕⁻ g x = 0 := fun x j hj ↦
    fourierInv_eq_zero_of_bound hF hρ (C := C) (by exact_mod_cast hC) hj
  have hcpt : HasCompactSupport (𝓕⁻ g) := by
    set K : Set (EuclideanSpace ℝ ι) := WithLp.toLp 2 '' (univ.pi fun i ↦ Icc (-ρ i) (ρ i))
    have hK : IsCompact K :=
      (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    refine HasCompactSupport.intro hK fun x hx ↦ ?_
    by_contra hne
    apply hx
    refine ⟨x.ofLp, fun i _ ↦ ?_, rfl⟩
    by_contra hi
    exact hne (hsupp x i (by
      simp only [mem_Icc, not_and_or, not_le] at hi
      rcases hi with h | h
      · rw [abs_of_neg (by linarith [hρ i])]; linarith
      · rw [abs_of_pos (by linarith [hρ i])]; exact h))
  refine ⟨hsmooth, hsupp, hcpt, ?_⟩
  have hfi : Integrable (𝓕⁻ g) := hsmooth.continuous.integrable_of_hasCompactSupport hcpt
  have hFg : Integrable (𝓕 g) := by
    refine hfi.comp_neg.congr (Eventually.of_forall fun w ↦ ?_)
    simp [Real.fourierInv_eq_fourier_neg]
  funext ξ
  exact hgi.fourier_fourierInv_eq hFg hgc.continuousAt

end Support

section Necessity

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Fourier–Laplace transform `ζ ↦ ∫ e^(-2πi ∑ j, ζ j w j) ψ(w) dw` on `m → ℝ`. -/
def fourierLaplace (ψ : (m → ℝ) → ℂ) (ζ : m → ℂ) : ℂ :=
  ∫ w, Complex.exp (-(2 * π * I) * ∑ j, ζ j * w j) * ψ w

omit [Fintype m] [DecidableEq m] in
/-- A function vanishing outside a box, in the pointwise form, has compact support. -/
private theorem hasCompactSupport_of_forall_abs_le {ψ : (m → ℝ) → ℂ} {ρ : m → ℝ}
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) : HasCompactSupport ψ := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun j ↦ isCompact_Icc (a := -ρ j)
    (b := ρ j)) fun w hw ↦ ?_
  by_contra hne
  exact hw fun j _ ↦ abs_le.mp (hψ w hne j)

omit [DecidableEq m] in
/-- The exponential kernel is bounded on the box by `exp (2π ∑ ρ j |Im ζ j|)`. -/
theorem norm_cexp_fourierLaplace_le {ρ : m → ℝ} {w : m → ℝ} (hw : ∀ j, |w j| ≤ ρ j)
    (ζ : m → ℂ) :
    ‖Complex.exp (-(2 * π * I) * ∑ j, ζ j * w j)‖ ≤ Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-(2 * π * I) * ∑ j, ζ j * w j).re = 2 * π * ∑ j, (ζ j).im * w j := by
    simp [Complex.mul_re, Finset.mul_sum, re_sum]
  rw [hre]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ ?_) (by positivity)
  calc (ζ j).im * w j ≤ |(ζ j).im * w j| := le_abs_self _
    _ = |(ζ j).im| * |w j| := abs_mul _ _
    _ ≤ |(ζ j).im| * ρ j := mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _)
    _ = ρ j * |(ζ j).im| := mul_comm _ _

omit [DecidableEq m] in
/-- `norm_fourierLaplace_le` with the box condition in pointwise form. -/
private theorem norm_fourierLaplace_le_aux {ψ : (m → ℝ) → ℂ} (hψc : Continuous ψ) {ρ : m → ℝ}
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) (ζ : m → ℂ) :
    ‖fourierLaplace ψ ζ‖ ≤ (∫ w, ‖ψ w‖) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) := by
  have hint : Integrable fun w ↦ ‖ψ w‖ :=
    (hψc.norm.integrable_of_hasCompactSupport (hasCompactSupport_of_forall_abs_le hψ).norm)
  rw [← MeasureTheory.integral_mul_const]
  refine norm_integral_le_of_norm_le (hint.mul_const _) (Eventually.of_forall fun w ↦ ?_)
  by_cases h : ψ w = 0
  · simp [h]
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_fourierLaplace_le (hψ w h) ζ) (norm_nonneg _)

/-- The derivative of `ψ` in the `j`-th coordinate direction. -/
private def coordDeriv (j : m) (ψ : (m → ℝ) → ℂ) (w : m → ℝ) : ℂ := fderiv ℝ ψ w (Pi.single j 1)

/-- Coordinate derivatives of smooth functions are smooth. -/
private theorem contDiff_coordDeriv (j : m) {ψ : (m → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (coordDeriv j ψ) :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

omit [Fintype m] in
/-- Coordinate derivatives keep a box support. -/
private theorem coordDeriv_box (j : m) {ψ : (m → ℝ) → ℂ} {ρ : m → ℝ}
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) :
    ∀ w, coordDeriv j ψ w ≠ 0 → ∀ i, |w i| ≤ ρ i := by
  intro w hw i
  have hsupp : w ∈ tsupport ψ := by
    by_contra h
    exact hw (by simp [coordDeriv, fderiv_of_notMem_tsupport ℝ h])
  have hclosed : IsClosed {w : m → ℝ | ∀ i, |w i| ≤ ρ i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le (continuous_abs.comp (continuous_apply i))
      continuous_const
  exact (closure_minimal (fun w hw ↦ hψ w hw) hclosed) hsupp i

/-- Integration by parts for the Fréchet coordinate derivative, with the box condition in
pointwise form. -/
private theorem fourierLaplace_coordDeriv (j : m) {ψ : (m → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {ρ : m → ℝ} (hbox : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) (ζ : m → ℂ) :
    fourierLaplace (coordDeriv j ψ) ζ = 2 * π * I * ζ j * fourierLaplace ψ ζ := by
  set e : (m → ℝ) → ℂ := fun w ↦ Complex.exp (-(2 * π * I) * ∑ j, ζ j * w j)
  set L : (m → ℝ) →L[ℝ] ℂ := ∑ i, (-(2 * π * I) * ζ i) • (Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj i))
  have hL : ∀ w, L w = -(2 * π * I) * ∑ i, ζ i * w i := fun w ↦ by
    simp [L, Finset.mul_sum, mul_assoc]
  have he : ∀ w, HasFDerivAt e (e w • L) w := by
    intro w
    have h : HasFDerivAt (fun w : m → ℝ ↦ -(2 * π * I) * ∑ i, ζ i * w i) L w := by
      have : (fun w : m → ℝ ↦ -(2 * π * I) * ∑ i, ζ i * w i) = L := funext fun w ↦ (hL w).symm
      rw [this]; exact L.hasFDerivAt
    exact h.cexp
  have hsing : ∑ i, ζ i * (((Pi.single j (1 : ℝ) : m → ℝ) i : ℝ) : ℂ) = ζ j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  have hde' : ∀ w, fderiv ℝ e w (Pi.single j 1) = -(2 * π * I) * ζ j * e w := by
    intro w
    rw [(he w).fderiv, smul_apply, hL, smul_eq_mul, hsing]
    ring
  have hcpt := hasCompactSupport_of_forall_abs_le hbox
  have hec : Continuous e := by fun_prop
  have hψ1 : ∀ w, DifferentiableAt ℝ ψ w := fun w ↦ hψ.differentiable (by simp) w
  have hD : Continuous (coordDeriv j ψ) := (contDiff_coordDeriv j hψ).continuous
  have hDcpt : HasCompactSupport (coordDeriv j ψ) :=
    hasCompactSupport_of_forall_abs_le (coordDeriv_box j hbox)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := e) (g := ψ)
    (v := Pi.single j 1) ?_ ?_ ?_ (fun w _ ↦ (he w).differentiableAt) (fun w _ ↦ hψ1 w)
  · have hde := hde'
    simp only [fourierLaplace]
    change ∫ w, e w * coordDeriv j ψ w = _
    simp only [coordDeriv]
    rw [hibp]
    simp_rw [hde]
    rw [← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
    simp only [e]
    ring
  · simp_rw [hde']
    exact (Continuous.mul (by fun_prop) hψ.continuous).integrable_of_hasCompactSupport
      hcpt.mul_left
  · exact (hec.mul hD).integrable_of_hasCompactSupport hDcpt.mul_left
  · exact (hec.mul hψ.continuous).integrable_of_hasCompactSupport hcpt.mul_left

omit [DecidableEq m] in
/-- `norm_fourierLaplace_le_of_contDiff` with the box condition in pointwise form. -/
private theorem norm_fourierLaplace_le_of_contDiff_aux {ψ : (m → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {ρ : m → ℝ} (hbox : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) (N : ℕ) :
    ∃ C, ∀ ζ : m → ℂ, ‖fourierLaplace ψ ζ‖ ≤
      C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) := by
  classical
  -- Iterated coordinate derivatives.
  have hiter : ∀ (j : m) (n : ℕ), ContDiff ℝ ∞ ((coordDeriv j)^[n] ψ) ∧
      (∀ w, (coordDeriv j)^[n] ψ w ≠ 0 → ∀ i, |w i| ≤ ρ i) := by
    intro j n
    induction n with
    | zero => exact ⟨hψ, hbox⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨contDiff_coordDeriv j ih.1, coordDeriv_box j ih.2⟩
  have hFL : ∀ (j : m) (n : ℕ) (ζ : m → ℂ),
      fourierLaplace ((coordDeriv j)^[n] ψ) ζ = (2 * π * I * ζ j) ^ n * fourierLaplace ψ ζ := by
    intro j n ζ
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', fourierLaplace_coordDeriv j (hiter j n).1 (hiter j n).2,
        ih, pow_succ]
      ring
  set A : m → ℝ := fun j ↦ ∫ w, ‖(coordDeriv j)^[N] ψ w‖
  set A₀ : ℝ := ∫ w, ‖ψ w‖
  have hA₀ : 0 ≤ A₀ := integral_nonneg fun _ ↦ norm_nonneg _
  have hA : ∀ j, 0 ≤ A j := fun j ↦ integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨2 ^ N * (A₀ + ∑ j, A j), fun ζ ↦ ?_⟩
  set H := Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|)
  have hH : 0 < H := Real.exp_pos _
  -- Bounds for `FL ψ` alone and with the factor `(2π ζ j)^N`.
  have h0 : ‖fourierLaplace ψ ζ‖ ≤ A₀ * H := norm_fourierLaplace_le_aux hψ.continuous hbox ζ
  have hj : ∀ j, ‖ζ j‖ ^ N * ‖fourierLaplace ψ ζ‖ ≤ A j * H := by
    intro j
    have h := norm_fourierLaplace_le_aux (hiter j N).1.continuous (hiter j N).2 ζ
    rw [hFL, norm_mul, norm_pow] at h
    have h2π : 1 ≤ ‖2 * π * I * ζ j‖ / ‖ζ j‖ ∨ ζ j = 0 := by
      by_cases hz : ζ j = 0
      · exact Or.inr hz
      · left
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_div_assoc,
          div_self (norm_ne_zero_iff.mpr hz), mul_one]
        simp only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        nlinarith [Real.two_le_pi]
    calc ‖ζ j‖ ^ N * ‖fourierLaplace ψ ζ‖ ≤ ‖2 * π * I * ζ j‖ ^ N * ‖fourierLaplace ψ ζ‖ := by
          gcongr
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
          simp only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          nlinarith [Real.two_le_pi, norm_nonneg (ζ j)]
      _ ≤ A j * H := h
  -- The largest coordinate controls the norm.
  have hmain : (1 + ‖ζ‖) ^ N * ‖fourierLaplace ψ ζ‖ ≤ 2 ^ N * (A₀ + ∑ j, A j) * H := by
    cases isEmpty_or_nonempty m with
    | inl _ =>
      have : ‖ζ‖ = 0 := by simp [Subsingleton.elim ζ 0]
      rw [this, add_zero, one_pow, one_mul]
      calc ‖fourierLaplace ψ ζ‖ ≤ A₀ * H := h0
        _ ≤ 2 ^ N * (A₀ + ∑ j, A j) * H := by
          have : A₀ ≤ 2 ^ N * (A₀ + ∑ j, A j) := by
            have hs : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ ↦ hA j
            have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
            nlinarith
          gcongr
    | inr _ =>
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖ζ j‖)
        Finset.univ_nonempty
      have hζ : ‖ζ‖ ≤ ‖ζ j₀‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j ↦ hj₀ j (Finset.mem_univ j)
      have hpow : (1 + ‖ζ‖) ^ N ≤ 2 ^ N * (1 + ‖ζ j₀‖ ^ N) := by
        calc (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ j₀‖) ^ N := by gcongr
          _ ≤ (2 * max 1 ‖ζ j₀‖) ^ N := by
              gcongr; linarith [le_max_left 1 ‖ζ j₀‖, le_max_right 1 ‖ζ j₀‖]
          _ = 2 ^ N * max 1 ‖ζ j₀‖ ^ N := mul_pow _ _ _
          _ ≤ 2 ^ N * (1 + ‖ζ j₀‖ ^ N) := by
              gcongr
              rcases le_total 1 ‖ζ j₀‖ with h | h
              · rw [max_eq_right h]; linarith [one_le_pow₀ h (n := N)]
              · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (norm_nonneg (ζ j₀)) N]
      have hsum : A j₀ ≤ ∑ j, A j :=
        Finset.single_le_sum (fun j _ ↦ hA j) (Finset.mem_univ j₀)
      calc (1 + ‖ζ‖) ^ N * ‖fourierLaplace ψ ζ‖
          ≤ 2 ^ N * (1 + ‖ζ j₀‖ ^ N) * ‖fourierLaplace ψ ζ‖ := by gcongr
        _ = 2 ^ N * (‖fourierLaplace ψ ζ‖ + ‖ζ j₀‖ ^ N * ‖fourierLaplace ψ ζ‖) := by ring
        _ ≤ 2 ^ N * (A₀ * H + A j₀ * H) :=
            mul_le_mul_of_nonneg_left (add_le_add h0 (hj j₀)) (by positivity)
        _ ≤ 2 ^ N * ((A₀ + ∑ j, A j) * H) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [hsum, hH]
        _ = 2 ^ N * (A₀ + ∑ j, A j) * H := by ring
  have hpos : 0 < (1 + ‖ζ‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast,
    show 2 ^ N * (A₀ + ∑ j, A j) * ((1 + ‖ζ‖) ^ N)⁻¹ * H =
      2 ^ N * (A₀ + ∑ j, A j) * H / (1 + ‖ζ‖) ^ N by ring, le_div_iff₀ hpos]
  linarith [hmain]

omit [DecidableEq m] in
/-- On real frequencies, the Fourier–Laplace transform is the Fourier transform on the Euclidean
space. -/
theorem fourier_eq_fourierLaplace (ψ : (m → ℝ) → ℂ) (ξ : EuclideanSpace ℝ m) :
    𝓕 (fun v : EuclideanSpace ℝ m ↦ ψ v.ofLp) ξ = fourierLaplace ψ (realPoint ξ) := by
  rw [Real.fourier_eq', ← (PiLp.volume_preserving_toLp _).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding, fourierLaplace]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul, realPoint]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  push_cast
  ring_nf

omit [DecidableEq m] in
/-- **Injectivity.** A continuous function with compact support whose Fourier–Laplace transform
vanishes at all real frequencies is zero. -/
theorem eq_zero_of_fourierLaplace_eq_zero {ψ : (m → ℝ) → ℂ} (hψ : Continuous ψ)
    (hcpt : HasCompactSupport ψ) (h : ∀ ξ : m → ℝ, fourierLaplace ψ (fun j ↦ (ξ j : ℂ)) = 0) :
    ψ = 0 := by
  set f : EuclideanSpace ℝ m → ℂ := fun v ↦ ψ v.ofLp
  have hfc : Continuous f := hψ.comp (PiLp.continuous_ofLp 2 _)
  have hfcpt : HasCompactSupport f :=
    hcpt.comp_homeomorph (PiLp.homeomorph 2 fun _ : m ↦ ℝ)
  have hf : Integrable f := hfc.integrable_of_hasCompactSupport hfcpt
  have hF : 𝓕 f = 0 := by
    funext ξ
    rw [fourier_eq_fourierLaplace]
    exact h ξ.ofLp
  funext w
  have hinv := hf.fourierInv_fourier_eq (by rw [hF]; exact integrable_zero _ _ _)
    hfc.continuousAt (v := WithLp.toLp 2 w)
  rw [hF] at hinv
  simpa [f, Real.fourierInv_eq'] using hinv.symm

omit [Fintype m] [DecidableEq m] in
/-- Support in the box `∏ⱼ [-ρ j, ρ j]` means vanishing wherever some `|w j| > ρ j`. -/
theorem support_subset_pi_Icc_iff {E : Type*} [Zero E] {ψ : (m → ℝ) → E} {ρ : m → ℝ} :
    Function.support ψ ⊆ Set.univ.pi (fun j ↦ Icc (-ρ j) (ρ j)) ↔
      ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j := by
  simp only [Set.subset_def, Function.mem_support, Set.mem_univ_pi, Set.mem_Icc, abs_le]

omit [Fintype m] [DecidableEq m] in
/-- A function supported in a box has compact support. -/
theorem hasCompactSupport_of_box {ψ : (m → ℝ) → ℂ} {ρ : m → ℝ}
    (hsupp : Function.support ψ ⊆ Set.univ.pi fun j ↦ Icc (-ρ j) (ρ j)) :
    HasCompactSupport ψ :=
  hasCompactSupport_of_forall_abs_le (support_subset_pi_Icc_iff.mp hsupp)

omit [DecidableEq m] in
/-- **The basic bound.** For `ψ` continuous and supported in the box `∏ⱼ [-ρ j, ρ j]`,
`‖FL ψ (ζ)‖ ≤ ‖ψ‖₁ exp (2π ∑ ρ j |Im ζ j|)`. -/
theorem norm_fourierLaplace_le {ψ : (m → ℝ) → ℂ} (hψc : Continuous ψ) {ρ : m → ℝ}
    (hsupp : Function.support ψ ⊆ Set.univ.pi fun j ↦ Icc (-ρ j) (ρ j)) (ζ : m → ℂ) :
    ‖fourierLaplace ψ ζ‖ ≤ (∫ w, ‖ψ w‖) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) :=
  norm_fourierLaplace_le_aux hψc (support_subset_pi_Icc_iff.mp hsupp) ζ

/-- **Integration by parts.** For `ψ` smooth and supported in a box, the partial derivative
`∂ⱼ ψ = lineDeriv ℝ ψ · (Pi.single j 1)` satisfies `FL (∂ⱼ ψ)(ζ) = 2πi ζ j FL ψ(ζ)`. -/
theorem fourierLaplace_lineDeriv (j : m) {ψ : (m → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) {ρ : m → ℝ}
    (hsupp : Function.support ψ ⊆ Set.univ.pi fun j ↦ Icc (-ρ j) (ρ j)) (ζ : m → ℂ) :
    fourierLaplace (fun w ↦ lineDeriv ℝ ψ w (Pi.single j 1)) ζ =
      2 * π * I * ζ j * fourierLaplace ψ ζ := by
  have he : (fun w ↦ lineDeriv ℝ ψ w (Pi.single j 1)) = coordDeriv j ψ :=
    funext fun w ↦ ((hψ.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv
  rw [he]
  exact fourierLaplace_coordDeriv j hψ (support_subset_pi_Icc_iff.mp hsupp) ζ

omit [DecidableEq m] in
/-- **Paley–Wiener, necessity.** The Fourier–Laplace transform of a smooth function supported in
the box `∏ⱼ [-ρ j, ρ j]` satisfies, for every `N`,
`‖FL ψ(ζ)‖ ≤ C (1 + ‖ζ‖)^(-N) exp (2π ∑ j, ρ j |Im ζ j|)`. -/
theorem norm_fourierLaplace_le_of_contDiff {ψ : (m → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {ρ : m → ℝ} (hsupp : Function.support ψ ⊆ Set.univ.pi fun j ↦ Icc (-ρ j) (ρ j)) (N : ℕ) :
    ∃ C, ∀ ζ : m → ℂ, ‖fourierLaplace ψ ζ‖ ≤
      C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) :=
  norm_fourierLaplace_le_of_contDiff_aux hψ (support_subset_pi_Icc_iff.mp hsupp) N

end Necessity

end PaleyWiener
