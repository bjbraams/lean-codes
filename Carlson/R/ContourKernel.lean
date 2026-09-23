/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Euler
public import ComplexAnalysis.ExteriorPath
public import Carlson.R.Explicit

/-!
# Compactified exterior-path kernels for Carlson continuation

For the integer resolvent of order `n + 1`, write an exterior path as
`τ(u) = t + (1 - u) / u * q u`. Let `L i u` be logarithms of
`1 - u + u * (t - z i) / q u`, normalized to zero at `u = 0`.
The regular part of Carlson's exterior-path integrand is

`q(u)^(-n-2) * (q(u) - u*(1-u)*q'(u)) * exp(-∑ i, b i * L i u)`.

The two endpoint powers have exponents `n` and `sum b - n - 2`. Their Gamma
regularization is an instance of the general Euler/Dirichlet transform, so the kernel
admits joint analytic continuation without a separate parameter-raising construction.
The straight-path specialization recovers the existing slit-plane R-function.

The existence theorem below is conditional on an admissible path and analytic branches.
It does not yet assert independence of the exterior path or construct paths for arbitrary
Jordan domains. Those are necessary further steps toward Carlson (1969), Theorems 4–5.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A simply connected parameter neighborhood of an admissible exterior path supplies
holomorphic logarithms of all normalized node factors, vanishing at infinity.
Only avoidance of the individual nodes is required, not avoidance of their convex hull. -/
theorem exists_analyticOnNhd_exteriorPathLog
    {U : Set (κ → ℂ)} {V : Set ℂ} {W : Set ((κ → ℂ) × ℂ)}
    (hW : IsOpen W) (hWc : IsSimplyConnected W) (hWU : W ⊆ U ×ˢ V)
    (hsection : ∀ p ∈ W, (p.1, (0 : ℂ)) ∈ W)
    {t : (κ → ℂ) → ℂ} (ht : AnalyticOnNhd ℂ t U)
    {z : (κ → ℂ) → ι → ℂ} (hz : AnalyticOnNhd ℂ z U)
    {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q V) (hq0 : ∀ u ∈ V, q u ≠ 0)
    (havoid : ∀ p ∈ W, p.2 ≠ 0 → ∀ i, compactifiedRay q (t p.1) p.2 ≠ z p.1 i) :
    ∃ L : ι → ((κ → ℂ) × ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (L i) W) ∧
      (∀ i, ∀ p ∈ W, exp (L i p) = 1 - p.2 + p.2 * (t p.1 - z p.1 i) / q p.2) ∧
      ∀ i p, L i (p, 0) = 0 := by
  have hlogs (i : ι) : ∃ L : ((κ → ℂ) × ℂ) → ℂ,
      AnalyticOnNhd ℂ L W ∧
      EqOn (exp ∘ L) (fun p => 1 - p.2 + p.2 * (t p.1 - z p.1 i) / q p.2) W ∧
      ∀ p, L (p, 0) = 0 := by
    apply exists_analyticOnNhd_logBranch_zero_section hW hWc hsection
    · intro p hp
      apply (analyticAt_const.sub analyticAt_snd).add
      apply AnalyticAt.div
      · exact analyticAt_snd.mul (((ht p.1 (hWU hp).1).comp analyticAt_fst).sub
          (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt (z p.1)).comp_of_eq
            ((hz p.1 (hWU hp).1).comp_of_eq analyticAt_fst rfl) rfl))
      · exact (hq p.2 (hWU hp).2).comp analyticAt_snd
      · exact hq0 p.2 (hWU hp).2
    · intro p hp
      by_cases hu : p.2 = 0
      · simp [hu]
      · rw [compactifiedRay_sub_factor q (t p.1) (z p.1 i) hu (hq0 p.2 (hWU hp).2)]
        exact div_ne_zero (mul_ne_zero hu (sub_ne_zero.mpr (havoid p hp hu i)))
          (hq0 p.2 (hWU hp).2)
    · intro p _
      simp
  choose L hL he hzero using hlogs
  exact ⟨L, hL, fun i p hp => he i hp, hzero⟩

/-- The regular endpoint amplitude for an integer-order exterior-path resolvent. -/
def carlsonExteriorPathAmplitude (n : ℕ) (b : ι → ℂ) (q : ℂ → ℂ)
    (L : ι → ℂ → ℂ) (u : ℂ) : ℂ :=
  (q u ^ (n + 2))⁻¹ * compactifiedRayJacobian q u * exp (-∑ i, b i * L i u)

/-- The native compactified exterior-path integral, including both endpoint Gamma factors.
Analytic continuation, rather than this totalized integral, is needed beyond convergence. -/
def regCarlsonExteriorPathIntegral (n : ℕ) (b : ι → ℂ) (q : ℂ → ℂ)
    (L : ι → ℂ → ℂ) : ℂ :=
  regEulerIntegral (n + 1) ((∑ i, b i) - n - 1)
    (fun u => carlsonExteriorPathAmplitude n b q L (u : ℂ))

/-- Holomorphic branch data make the regular part of the exterior-path integrand holomorphic. -/
theorem analyticOnNhd_carlsonExteriorPathAmplitude (n : ℕ)
    {U : Set (κ → ℂ)} {V : Set ℂ} {W : Set ((κ → ℂ) × ℂ)}
    (hWU : W ⊆ U ×ˢ V) {b : (κ → ℂ) → ι → ℂ}
    (hb : AnalyticOnNhd ℂ b U) {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q V)
    (hq0 : ∀ u ∈ V, q u ≠ 0) {L : ι → ((κ → ℂ) × ℂ) → ℂ}
    (hL : ∀ i, AnalyticOnNhd ℂ (L i) W) :
    AnalyticOnNhd ℂ
      (fun p => carlsonExteriorPathAmplitude n (b p.1) q (fun i u => L i (p.1, u)) p.2) W := by
  intro p hp
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · exact (((hq p.2 (hWU hp).2).comp analyticAt_snd).pow (n + 2)).inv
        (pow_ne_zero _ (hq0 p.2 (hWU hp).2))
    · exact (analyticOnNhd_compactifiedRayJacobian hq p.2 (hWU hp).2).comp analyticAt_snd
  · apply AnalyticAt.cexp
    apply AnalyticAt.neg
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt (b p.1)).comp_of_eq
      ((hb p.1 (hWU hp).1).comp_of_eq analyticAt_fst rfl) rfl).mul (hL i p hp)

/-- Compactified exterior-path integrals admit joint continuation by the Euler transform.
No positivity of individual Dirichlet parameters is required for native agreement; only
the total-parameter endpoint must converge. -/
theorem exists_analyticOnNhd_regCarlsonExteriorPathIntegral (n : ℕ)
    {U : Set (κ → ℂ)} (hU : IsOpen U) {V : Set ℂ} {W : Set ((κ → ℂ) × ℂ)}
    (hW : IsOpen W) (hWU : W ⊆ U ×ˢ V)
    (hcover : ∀ p ∈ U, ∀ u ∈ Icc (0 : ℝ) 1, (p, (u : ℂ)) ∈ W)
    {b : (κ → ℂ) → ι → ℂ} (hb : AnalyticOnNhd ℂ b U)
    {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q V) (hq0 : ∀ u ∈ V, q u ≠ 0)
    {L : ι → ((κ → ℂ) × ℂ) → ℂ} (hL : ∀ i, AnalyticOnNhd ℂ (L i) W) :
    ∃ F : (κ → ℂ) → ℂ, AnalyticOnNhd ℂ F U ∧
      ∀ p ∈ U, (n : ℝ) + 1 < (∑ i, b p i).re →
        F p = regCarlsonExteriorPathIntegral n (b p) q (fun i u => L i (p, u)) := by
  have hsum : AnalyticOnNhd ℂ (fun p => ∑ i, b p i) U := by
    intro p hp
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt (b p)).comp (hb p hp)
  obtain ⟨F, hF, heq⟩ := exists_analyticOnNhd_regEulerIntegral hU hW
    (analyticOnNhd_carlsonExteriorPathAmplitude n hWU hb hq hq0 hL) hcover
    (analyticOnNhd_const (v := ((n : ℂ) + 1)))
    ((hsum.sub (analyticOnNhd_const (v := (n : ℂ)))).sub (analyticOnNhd_const (v := 1)))
  refine ⟨F, hF, fun p hp hc => ?_⟩
  exact heq p hp (by simp only [add_re, natCast_re, one_re]; positivity)
    (by simpa only [Pi.sub_apply, sub_re, natCast_re, one_re] using
      (show 0 < (∑ i, b p i).re - n - 1 by linarith))

/-- On a straight path, principal logarithms recover the familiar product of powers. -/
theorem carlsonExteriorPathAmplitude_one (n : ℕ) (b z : ι → ℂ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hz : z ∈ carlsonRSlitDomain) :
    carlsonExteriorPathAmplitude n b (fun _ => 1)
      (fun i v => log (1 - v + v * z i)) (u : ℂ) = singleIntegralKernel b z u := by
  simp only [carlsonExteriorPathAmplitude, compactifiedRayJacobian, deriv_const,
    mul_zero, sub_zero, one_pow, inv_one, one_mul]
  rw [← Finset.sum_neg_distrib, exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero (carlsonRSegment_mem_slitPlane hz hu i))]
  congr 1
  ring

/-- In its convergence strip, the straight exterior-path construction is the slit resolvent. -/
theorem regCarlsonExteriorPathIntegral_one (n : ℕ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    (hc : (n : ℝ) + 1 < (∑ i, b i).re) :
    regCarlsonExteriorPathIntegral n b (fun _ => 1)
      (fun i v => log (1 - v + v * z i)) = regCarlsonR (-(n + 1)) b z := by
  have ha : 0 < ((n : ℂ) + 1).re := by simp; positivity
  have hb : 0 < ((∑ i, b i) - n - 1).re := by
    simp only [sub_re, natCast_re, one_re]
    linarith
  unfold regCarlsonExteriorPathIntegral regEulerIntegral
  rw [show (∫ u in Ioo (0 : ℝ) 1,
      (u : ℂ) ^ ((n : ℂ) + 1 - 1) * (1 - u : ℂ) ^ ((∑ i, b i) - n - 1 - 1) *
        carlsonExteriorPathAmplitude n b (fun _ => 1)
          (fun i v => log (1 - v + v * z i)) (u : ℂ)) =
      carlsonRUnitIntervalIntegral (n + 1) ((∑ i, b i) - n - 1) b z by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp only
    rw [carlsonExteriorPathAmplitude_one n b z ⟨hu.1.le, hu.2.le⟩ hz]
    rfl]
  rw [carlsonRUnitIntervalIntegral_eq_gamma_mul_regCarlsonR ha hb (by ring) hz,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hb))]

/-- An entire continuation of the straight-path integral is the established slit resolvent
at every parameter, including outside the initial total-parameter convergence strip. -/
theorem eq_regCarlsonR_of_exteriorPath_one [Nonempty ι] (n : ℕ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F univ)
    (hFnative : ∀ b : ι → ℂ, (n : ℝ) + 1 < (∑ i, b i).re →
      F b = regCarlsonExteriorPathIntegral n b (fun _ => 1)
        (fun i v => log (1 - v + v * z i))) :
    F = fun b => regCarlsonR (-(n + 1)) b z := by
  classical
  let i : ι := Classical.choice inferInstance
  let b₀ : ι → ℂ := Pi.single i ((n : ℂ) + 2)
  have hb₀ : (n : ℝ) + 1 < (∑ j, b₀ j).re := by
    dsimp [b₀]
    rw [Fintype.sum_pi_single']
    change (n : ℝ) + 1 < (n : ℝ) + 2
    linarith
  have hopen : IsOpen {b : ι → ℂ | (n : ℝ) + 1 < (∑ i, b i).re} :=
    isOpen_lt continuous_const (by fun_prop)
  apply hF.eq_of_eventuallyEq
    (fun _ _ => analyticAt_regCarlsonR_comp
      analyticAt_const analyticAt_id analyticAt_const hz) (z₀ := b₀)
  filter_upwards [hopen.mem_nhds hb₀] with b hb
  exact (hFnative b hb).trans (regCarlsonExteriorPathIntegral_one n b hz hb)

end Carlson
