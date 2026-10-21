/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Fourier.FiniteRegularity
public import ToMathlib.Analysis.Fourier.Plancherel
public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Fourier integrability from square-integrable derivatives

Classical `C^N` functions whose derivatives through order `N` belong to `L²` lie
in the Bessel-potential space `H^N`. The proof uses Tau Ceti's identification of
weak and distributional derivatives and its first-derivative characterization of
Bessel-potential regularity. Mathlib's `MemSobolev.fourier_memL1` then gives
Fourier integrability when `2N > dim V`. On `L¹ ∩ L²`, the distributional Fourier
transform agrees with the classical Fourier integral by the local Plancherel bridge.

These are sufficient conditions; no endpoint or optimality claim is made.
-/

open MeasureTheory Set SchwartzMap
open scoped ContDiff FourierTransform LineDeriv

@[expose] public noncomputable section

namespace Real

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Square-integrable classical derivatives imply integer-order Bessel-potential
regularity. The derivative characterization and weak/distributional bridge are due to
the Tau Ceti contributors. -/
theorem memSobolev_toLp_of_memLp_iteratedFDeriv {N : ℕ} {f : V → H}
    (hf : ContDiff ℝ N f) (hd : ∀ n ≤ N, MemLp (iteratedFDeriv ℝ n f) 2)
    (h₂ : MemLp f 2) :
    TemperedDistribution.MemSobolev N 2 (Lp.toTemperedDistribution (h₂.toLp f)) := by
  induction N generalizing f with
  | zero =>
    rw [Nat.cast_zero, TemperedDistribution.memSobolev_zero_iff]
    exact ⟨h₂.toLp f, rfl⟩
  | succ N ih =>
    rw [Nat.cast_succ, TemperedDistribution.memSobolev_natCast_add_one_iff
      ENNReal.one_lt_two ENNReal.ofNat_ne_top]
    refine ⟨TemperedDistribution.memSobolev_zero_iff.mpr ⟨h₂.toLp f, rfl⟩, fun v => ?_⟩
    have hfd : ContDiff ℝ N (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hfv : ContDiff ℝ N (fun x => fderiv ℝ f x v) := hfd.clm_apply contDiff_const
    have hdv (n : ℕ) (hn : n ≤ N) :
        MemLp (iteratedFDeriv ℝ n (fun x => fderiv ℝ f x v)) 2 := by
      apply (hd (n + 1) (by omega)).of_le_mul
        (hfv.continuous_iteratedFDeriv (by exact_mod_cast hn)).aestronglyMeasurable
      filter_upwards with x
      simpa only [norm_iteratedFDeriv_fderiv] using
        norm_iteratedFDeriv_clm_apply_const hfd.contDiffAt (by exact_mod_cast hn)
    have h₂v : MemLp (fun x => fderiv ℝ f x v) 2 := by
      apply (hdv 0 (Nat.zero_le N)).of_le hfv.continuous.aestronglyMeasurable
      filter_upwards with x
      simp only [norm_iteratedFDeriv_zero, le_refl]
    have hweak : TauCeti.HasWeakLineDerivOn volume ⊤ f (fun x => fderiv ℝ f x v) v :=
      TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
        ((h₂.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
        ((h₂v.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
        (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v)
    have hweak' : TauCeti.HasWeakLineDerivOn volume ⊤ (h₂.toLp f)
        (h₂v.toLp (fun x => fderiv ℝ f x v)) v :=
      (hweak.congr_ae (by simpa using h₂.coeFn_toLp.symm)).congr_ae_deriv
        (by simpa using h₂v.coeFn_toLp.symm)
    rw [hweak'.lineDerivOp_toTemperedDistribution_eq]
    exact ih hfv hdv h₂v

/-- The classical Fourier integral of an integrable `H^s` function is integrable
when `2s > dim V`, for arbitrary real Sobolev order `s`. -/
theorem integrable_fourier_of_memSobolev {s : ℝ} {f : V → H}
    (hs : (Module.finrank ℝ V : ℝ) < 2 * s) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (hS : TemperedDistribution.MemSobolev s 2 (Lp.toTemperedDistribution (h₂.toLp f))) :
    Integrable (𝓕 f) := by
  obtain ⟨v, hv⟩ := hS.fourier_memL1 hs
  have hae := fourier_toLp_ae_eq h₁ h₂
  have hloc := (memLp_fourier_of_integrable_memLp h₁ h₂).locallyIntegrable (by norm_num)
  have hvf : v =ᵐ[volume] 𝓕 f := by
    apply Lp.ae_eq_of_toTemperedDistribution_apply_eq v hloc
    intro φ
    rw [← hv, Lp.fourier_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  exact (L1.integrable_coeFn v).congr hvf

/-- More than half the dimension many square-integrable classical derivatives give
an integrable classical Fourier transform, provided the original function is integrable. -/
theorem integrable_fourier_of_memLp_iteratedFDeriv {N : ℕ} {f : V → H}
    (hN : Module.finrank ℝ V < 2 * N) (hf : ContDiff ℝ N f)
    (h₁ : Integrable f) (hd : ∀ n ≤ N, MemLp (iteratedFDeriv ℝ n f) 2) :
    Integrable (𝓕 f) := by
  have h₂ : MemLp f 2 := by
    apply (hd 0 (Nat.zero_le N)).of_le hf.continuous.aestronglyMeasurable
    filter_upwards with x
    simp only [norm_iteratedFDeriv_zero, le_refl]
  exact integrable_fourier_of_memSobolev (by exact_mod_cast hN) h₁ h₂
    (memSobolev_toLp_of_memLp_iteratedFDeriv hf hd h₂)

/-- Bessel-potential regularity gives a square-integrable weighted classical Fourier
transform. This identifies Mathlib's distributional Sobolev weight with the native integral. -/
theorem memLp_weighted_fourier_of_memSobolev {s : ℝ} {f : V → H}
    (h₁ : Integrable f) (h₂ : MemLp f 2)
    (hS : TemperedDistribution.MemSobolev s 2 (Lp.toTemperedDistribution (h₂.toLp f))) :
    MemLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 := by
  let w : V → ℂ := fun ξ => ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hcont : Continuous (𝓕 f) := by
    change Continuous (fun ξ : V => 𝓕 f ξ)
    simp_rw [Real.fourier_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  obtain ⟨u, hu⟩ := TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp hS
  have hae : u =ᵐ[volume] fun ξ => w ξ • 𝓕 f ξ := by
    apply Lp.ae_eq_of_toTemperedDistribution_apply_eq u
      (hw.1.continuous.smul hcont).locallyIntegrable
    intro φ
    rw [← hu, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.fourier_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [fourier_toLp_ae_eq h₁ h₂] with ξ hξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw, hξ]
    change (w ξ * φ ξ) • 𝓕 f ξ = φ ξ • (w ξ • 𝓕 f ξ)
    rw [smul_smul, mul_comm]
  exact (Lp.memLp u).ae_eq hae

end Real

namespace SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every classical iterated derivative of a Schwartz function belongs to `L²`, even
when its continuous multilinear target carries its operator norm rather than a Hilbert norm. -/
theorem memLp_two_iteratedFDeriv (S : SchwartzMap V F) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n S) 2 := by
  have hcont : Continuous (iteratedFDeriv ℝ n S) :=
    (S.smooth ⊤).continuous_iteratedFDeriv (by simp)
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  have hInt : Integrable (fun x : V => ‖iteratedFDeriv ℝ n S x‖) := by
    simpa only [pow_zero, one_mul] using S.integrable_pow_mul_iteratedFDeriv (μ := volume) 0 n
  apply (hInt.const_mul ((SchwartzMap.seminorm ℂ 0 n) S)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (S.norm_iteratedFDeriv_le_seminorm ℂ n x) (norm_nonneg _)

/-- A finite smooth multiplier with bounded derivatives preserves square integrability
of Schwartz derivatives through its differentiability order. -/
theorem memLp_two_iteratedFDeriv_smul_of_bounded {N : ℕ} (S : SchwartzMap V F)
    {g : V → ℂ} (hg : ContDiff ℝ N g)
    (hb : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {n : ℕ} (hn : n ≤ N) :
    MemLp (iteratedFDeriv ℝ n (fun x => g x • S x)) 2 := by
  classical
  let C (i : ℕ) : ℝ := if h : i ≤ N then (hb i h).choose else 0
  have hC (i : ℕ) (hi : i ≤ N) (x : V) : ‖iteratedFDeriv ℝ i g x‖ ≤ C i := by
    simpa only [C, dite_eq_left hi] using (hb i hi).choose_spec x
  have hsum : MemLp (fun x : V => ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (n - i) S x‖) 2 := by
    apply memLp_finsetSum
    intro i _
    exact ((S.memLp_two_iteratedFDeriv (n - i)).norm).const_mul _
  apply hsum.of_le ((hg.smul (S.smooth N)).continuous_iteratedFDeriv
    (by exact_mod_cast hn)).aestronglyMeasurable
  filter_upwards with x
  apply le_trans ?_ (le_abs_self _)
  refine (norm_iteratedFDeriv_smul_le hg (S.smooth N) x
    (by exact_mod_cast hn)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  gcongr
  exact hC i (by simp only [Finset.mem_range] at hi; omega) x

end SchwartzMap
