/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Fourier integrability under finite regularity

Mathlib's derivative estimates for Fourier transforms give integrability when a function
has `N` integrable derivatives and `N` exceeds the real dimension of the domain.
A finite smooth multiplier with bounded derivatives preserves integrability of the
corresponding derivatives of a Schwartz function. Together these statements give a
finite-regularity replacement for the usual Schwartz-space Fourier integrability argument.

## Main results

* `Real.exists_norm_pow_mul_norm_fourier_le_of_integrable_iteratedFDeriv`.
* `Real.integrable_fourier_of_integrable_iteratedFDeriv`.
* `SchwartzMap.integrable_iteratedFDeriv_smul_of_bounded`.
-/

open MeasureTheory Set
open scoped ContDiff FourierTransform

@[expose] public noncomputable section

namespace Real
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Integrable derivatives through order `N` give polynomial Fourier decay of order `N`.
This is Mathlib's Fourier derivative estimate with zeroth-order frequency derivatives. -/
theorem exists_norm_pow_mul_norm_fourier_le_of_integrable_iteratedFDeriv
    {N : ℕ} {f : V → F} (hf : ContDiff ℝ N f)
    (hd : ∀ n ≤ N, Integrable (iteratedFDeriv ℝ n f)) :
    ∃ C, ∀ w : V, ‖w‖ ^ N * ‖𝓕 f w‖ ≤ C := by
  have hdec := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := (N : ℕ∞)) hf
    (fun k n hk hn => by
      have hk0 : k = 0 := by simpa using hk
      subst k
      simpa only [pow_zero, one_mul] using (hd n (by exact_mod_cast hn)).norm)
    (k := 0) (n := N) (by simp) (by simp)
  simp only [norm_iteratedFDeriv_zero] at hdec
  exact ⟨_, hdec⟩

/-- More than dimension many integrable derivatives suffice for Fourier integrability. -/
theorem integrable_fourier_of_integrable_iteratedFDeriv {N : ℕ} {f : V → F}
    (hN : Module.finrank ℝ V < N) (hf : ContDiff ℝ N f)
    (hd : ∀ n ≤ N, Integrable (iteratedFDeriv ℝ n f)) : Integrable (𝓕 f) := by
  have h0 : Integrable f := by
    apply (integrable_norm_iff hf.continuous.aestronglyMeasurable).mp
    simpa only [norm_iteratedFDeriv_zero] using (hd 0 (Nat.zero_le N)).norm
  obtain ⟨C, hbound⟩ := exists_norm_pow_mul_norm_fourier_le_of_integrable_iteratedFDeriv hf hd
  have hInt : Integrable (fun w : V => (1 + ‖w‖) ^ (-(N : ℝ))) :=
    integrable_one_add_norm (by exact_mod_cast hN)
  have hcont : Continuous (𝓕 f) := by
    change Continuous (fun w : V => 𝓕 f w)
    simp_rw [Real.fourier_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h0
  apply (hInt.const_mul (2 ^ N * ((∫ v, ‖f v‖) + C))).mono' hcont.aestronglyMeasurable
  filter_upwards with w
  simpa only [pow_zero, one_mul, zero_add] using
    (pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := N) (norm_nonneg w)
      (norm_nonneg (𝓕 f w)) (norm_fourier_le_integral_norm f w) (by simpa using hbound w))
end Real

namespace SchwartzMap
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Finite smooth multipliers with bounded derivatives preserve integrability of derivatives
of a Schwartz function, up to the multiplier's differentiability order. -/
theorem integrable_iteratedFDeriv_smul_of_bounded {N : ℕ} (S : SchwartzMap V F)
    {g : V → ℂ} (hg : ContDiff ℝ N g)
    (hb : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {n : ℕ} (hn : n ≤ N) :
    Integrable (iteratedFDeriv ℝ n (fun x => g x • S x)) := by
  classical
  let C (i : ℕ) : ℝ := if h : i ≤ N then (hb i h).choose else 0
  have hC (i : ℕ) (hi : i ≤ N) (x : V) : ‖iteratedFDeriv ℝ i g x‖ ≤ C i := by
    simpa only [C, dite_eq_left hi] using (hb i hi).choose_spec x
  have hsum : Integrable (fun x : V => ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (n - i) S x‖) := by
    apply integrable_finsetSum
    intro i hi
    have h := S.integrable_pow_mul_iteratedFDeriv (μ := volume) 0 (n - i)
    simpa only [pow_zero, one_mul] using h.const_mul ((n.choose i : ℝ) * C i)
  apply hsum.mono' ((hg.smul (S.smooth N)).continuous_iteratedFDeriv
    (by exact_mod_cast hn)).aestronglyMeasurable
  filter_upwards with x
  refine (norm_iteratedFDeriv_smul_le hg (S.smooth N) x
    (by exact_mod_cast hn)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  gcongr
  exact hC i (by simp only [Finset.mem_range] at hi; omega) x
end SchwartzMap

end
