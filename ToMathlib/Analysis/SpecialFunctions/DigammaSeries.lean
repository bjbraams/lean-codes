/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.GammaAsymptotic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import TauCeti.Analysis.Complex.Conformal.Vitali

/-!
# The partial-fraction expansions of digamma

Carlson (1977), §3.6. The Euler approximants converge locally uniformly away
from the Gamma poles, by the Tau Ceti contributors' whole-domain convergence
theorem. Mathlib's convergence theorem for logarithmic derivatives then
justifies differentiating the Euler limit. Absolute convergence of the rational
series uses Mathlib's general summability lemma for two linear denominator factors.
-/

open Filter Set MeasureTheory Polynomial Finset
open scoped Topology

@[expose] public noncomputable section

namespace Complex

/-- A finite product controlling the cost of shifting an Euler approximant. -/
private def gammaSeqBound (N : ℕ) (z : ℂ) : ℝ :=
  Real.Gamma (z.re + N) * ∏ k ∈ range N, ((2 + ‖z + k‖) / ‖z + k‖)

/-- Gamma regularity excludes every linear denominator in an Euler approximant. -/
private theorem gamma_regular_of_ne_zero {z : ℂ} (hz : Gamma z ≠ 0) :
    ∀ k : ℕ, z ≠ -(k : ℂ) := by
  intro k hk
  exact hz (by rw [hk, Gamma_neg_nat_eq_zero])

/-- Holomorphy of every nonzero-index Euler approximant away from the Gamma poles. -/
private theorem differentiableOn_GammaSeq (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => GammaSeq z (n + 1)) {z | Gamma z ≠ 0} := by
  intro z hz
  have hr := gamma_regular_of_ne_zero hz
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hden : (∏ k ∈ range (n + 1 + 1), (z + k)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro k _ hk
    apply hr k
    linear_combination hk
  have he : (fun z : ℂ => GammaSeq z (n + 1)) = fun z : ℂ =>
      exp (log (n + 1 : ℂ) * z) * ((n + 1).factorial : ℂ) /
        ∏ k ∈ range (n + 1 + 1), (z + k) := by
    funext z
    rw [GammaSeq]
    push_cast only [Nat.cast_add, Nat.cast_one]
    rw [cpow_def_of_ne_zero hn]
  rw [he]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hden

/-- The beta-integral majorant bounds the Euler approximants in the right half-plane. -/
private theorem norm_GammaSeq_le_Gamma_re {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖GammaSeq z (n + 1)‖ ≤ Real.Gamma z.re := by
  rw [GammaSeq_eq_betaIntegral_of_re_pos hz]
  simpa only [Nat.cast_add, Nat.cast_one, ofReal_add, ofReal_natCast, ofReal_one] using
    (norm_cpow_mul_betaIntegral_le_Gamma_re hz (x := ((n + 1 : ℕ) : ℝ)) (by positivity))

/-- One downward parameter shift costs a bounded rational factor, uniformly in the index. -/
private theorem norm_GammaSeq_le_shift {z : ℂ} (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) (n : ℕ) :
    ‖GammaSeq z (n + 1)‖ ≤ (2 + ‖z‖) / ‖z‖ * ‖GammaSeq (z + 1) (n + 1)‖ := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hn0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hzn : (n + 1 : ℂ) + 1 + z ≠ 0 := by
    intro h
    apply hz (n + 2)
    push_cast
    linear_combination h
  have he := GammaSeq_add_one_left z (n := n + 1) (by omega)
  push_cast only [Nat.cast_add, Nat.cast_one] at he
  have heq : GammaSeq z (n + 1) =
      (((n + 1 : ℂ) + 1 + z) / ((n + 1 : ℂ) * z)) * GammaSeq (z + 1) (n + 1) := by
    field_simp [hz0, hn0, hzn] at he ⊢
    linear_combination -he
  have hnR : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hzR : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnum : ‖(n + 1 : ℂ) + 1 + z‖ ≤ (n + 1 : ℕ) + 1 + ‖z‖ := by
    apply (norm_add_le _ _).trans
    simp only [← Nat.cast_add_one, norm_natCast]
    push_cast
    rfl
  have hfactor : ‖((n + 1 : ℂ) + 1 + z) / ((n + 1 : ℂ) * z)‖ ≤ (2 + ‖z‖) / ‖z‖ := by
    rw [norm_div, norm_mul,
      show ‖(n + 1 : ℂ)‖ = ((n + 1 : ℕ) : ℝ) by rw [← Nat.cast_add_one, norm_natCast]]
    calc
      _ ≤ (((n + 1 : ℕ) : ℝ) * (2 + ‖z‖)) / (((n + 1 : ℕ) : ℝ) * ‖z‖) := by
        apply (div_le_div_iff_of_pos_right (by positivity)).mpr
        nlinarith [norm_nonneg z]
      _ = _ := by field_simp
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)

/-- Repeated shifts give a compact-uniform bound for all Euler approximants. -/
private theorem norm_GammaSeq_le_bound (N : ℕ) {z : ℂ}
    (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) (hpos : 0 < z.re + N) (n : ℕ) :
    ‖GammaSeq z (n + 1)‖ ≤ gammaSeqBound N z := by
  induction N generalizing z with
  | zero => simpa [gammaSeqBound] using norm_GammaSeq_le_Gamma_re (by simpa using hpos) n
  | succ N ih =>
    have hz1 : ∀ k : ℕ, z + 1 ≠ -(k : ℂ) := by
      intro k hk
      apply hz (k + 1)
      push_cast
      linear_combination hk
    have hp1 : 0 < (z + 1).re + N := by
      simp only [add_re, one_re, Nat.cast_succ] at hpos ⊢
      linarith
    have hstep := norm_GammaSeq_le_shift hz n
    have hbound := ih hz1 hp1
    have he : gammaSeqBound (N + 1) z = (2 + ‖z‖) / ‖z‖ * gammaSeqBound N (z + 1) := by
      unfold gammaSeqBound
      rw [prod_range_succ']
      simp only [Nat.cast_zero, add_zero, Nat.cast_succ, add_re, one_re]
      have hp : (∏ k ∈ range N, (2 + ‖z + ((k : ℂ) + 1)‖) / ‖z + ((k : ℂ) + 1)‖) =
          ∏ k ∈ range N, (2 + ‖z + 1 + k‖) / ‖z + 1 + k‖ := by
        apply prod_congr rfl
        intro k _
        rw [show z + ((k : ℂ) + 1) = z + 1 + k by ring]
      rw [hp, show z.re + ((N : ℝ) + 1) = z.re + 1 + N by ring]
      ring
    rw [he]
    exact hstep.trans (mul_le_mul_of_nonneg_left hbound (by positivity))

/-- Euler's limit is locally uniform throughout the complement of its poles. -/
theorem tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => GammaSeq z (n + 1)) Gamma atTop
      {z | Gamma z ≠ 0} := by
  let U : Set ℂ := {z | Gamma z ≠ 0}
  have hU : IsOpen U := by
    have he : U = {z : ℂ | (Gamma z)⁻¹ ≠ 0} := by ext z; simp [U]
    rw [he]
    have hc : Continuous (fun z : ℂ => (Gamma z)⁻¹) := by
      simpa only [one_div] using differentiable_one_div_Gamma.continuous
    exact isOpen_ne.preimage hc
  have hbound : TauCeti.IsLocallyBoundedOn (fun n : ℕ => fun z : ℂ => GammaSeq z (n + 1)) U := by
    rw [TauCeti.isLocallyBoundedOn_def]
    intro K hKU hK
    obtain ⟨A, hA⟩ := hK.bddBelow_image continuous_re.continuousOn
    obtain ⟨N, hN⟩ := exists_nat_gt (-A)
    have hpos (z : ℂ) (hz : z ∈ K) : 0 < z.re + N := by
      have hzA : A ≤ z.re := hA (mem_image_of_mem _ hz)
      linarith
    have hc : ContinuousOn (gammaSeqBound N) K := by
      apply ContinuousOn.mul
      · intro z hz
        exact ((Real.differentiableAt_Gamma (fun k => by
          change z.re + (N : ℝ) ≠ -(k : ℝ)
          linarith [hpos z hz, Nat.cast_nonneg (α := ℝ) k])).continuousAt.comp
          (continuous_re.add continuous_const).continuousAt).continuousWithinAt
      · apply continuousOn_finsetProd
        intro k _
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro z hz hzero
          apply gamma_regular_of_ne_zero (hKU hz) k
          have he := norm_eq_zero.mp hzero
          linear_combination he
    obtain ⟨M, hM⟩ := hK.bddAbove_image hc
    refine ⟨M, fun n z hz => ?_⟩
    exact (norm_GammaSeq_le_bound N (gamma_regular_of_ne_zero (hKU hz)) (hpos z hz) n).trans
      (hM (mem_image_of_mem _ hz))
  exact TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto hU
    differentiableOn_GammaSeq hbound (fun z _ =>
      (GammaSeq_tendsto_Gamma z).comp (tendsto_add_atTop_nat 1))

/-- The logarithmic derivative of the finite Euler approximant. -/
private theorem logDeriv_GammaSeq {z : ℂ} (hz : ∀ k : ℕ, z ≠ -(k : ℂ))
    {n : ℕ} (hn : 0 < n) :
    logDeriv (fun z : ℂ => GammaSeq z n) z = log (n : ℂ) - ∑ k ∈ range (n + 1), (z + k)⁻¹ := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hzlin (k : ℕ) : z + k ≠ 0 := by
    intro hk
    apply hz k
    linear_combination hk
  have hden : (∏ k ∈ range (n + 1), (z + k)) ≠ 0 := prod_ne_zero_iff.mpr (fun k _ => hzlin k)
  have he : (fun z : ℂ => GammaSeq z n) = fun z : ℂ =>
      (exp (log (n : ℂ) * z) * (n.factorial : ℂ)) /
        ∏ k ∈ range (n + 1), (z + k) := by
    funext z
    rw [GammaSeq, cpow_def_of_ne_zero hnC]
  rw [he, logDeriv_fun_div
    (f := fun w : ℂ => exp (log (n : ℂ) * w) * (n.factorial : ℂ))
    (g := fun w : ℂ => ∏ k ∈ range (n + 1), (w + k))
    z (mul_ne_zero (exp_ne_zero _) hf) hden (by fun_prop) (by fun_prop),
    logDeriv_mul_const (f := fun w : ℂ => exp (log (n : ℂ) * w)) z _ hf,
    logDeriv_fun_prod (f := fun k : ℕ => fun w : ℂ => w + k)
      (fun k _ => hzlin k) (fun _ _ => by fun_prop)]
  have heexp : logDeriv (fun w : ℂ => exp (log (n : ℂ) * w)) z = log (n : ℂ) := by
    have hd := ((hasDerivAt_id z).const_mul (log (n : ℂ))).cexp
    simp only [id] at hd
    rw [logDeriv_apply, hd.deriv]
    simp only [mul_one, mul_div_cancel_left₀ _ (exp_ne_zero _)]
  rw [heexp]
  congr 1
  apply sum_congr rfl
  intro k _
  have hd := (hasDerivAt_id z).add_const (k : ℂ)
  simp only [id] at hd
  rw [logDeriv_apply, hd.deriv]
  simp

/-- Absolute summability of the rational digamma terms, from Mathlib's quadratic
linear-denominator summability theorem. -/
theorem summable_digamma_series {z : ℂ} (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) :
    Summable (fun k : ℕ => (k + 1 : ℂ)⁻¹ - (z + k + 1)⁻¹) := by
  have h := (EisensteinSeries.summable_linear_right_add_one_mul_linear_right (z + 1) 0
    1).comp_injective
    (i := fun n : ℕ => (n : ℤ)) Nat.cast_injective
  simp only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, one_mul] at h
  refine (h.mul_left z).congr (fun k => ?_)
  dsimp only [Function.comp_def]
  simp only [Int.cast_natCast]
  have hkC : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
  have hzk : z + k + 1 ≠ 0 := by
    intro hk
    apply hz (k + 1)
    push_cast
    linear_combination hk
  rw [show z + 1 + k = z + k + 1 by ring]
  field_simp [hkC, hzk]
  ring

/-- **Carlson (3.6-12).** The partial-fraction series of digamma, on the full
complement of the nonpositive integers. -/
theorem hasSum_digamma_series {z : ℂ} (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) :
    HasSum (fun k : ℕ => (k + 1 : ℂ)⁻¹ - (z + k + 1)⁻¹)
      (digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹) := by
  have hΓ : Gamma z ≠ 0 := Gamma_ne_zero hz
  have hU : IsOpen {w : ℂ | Gamma w ≠ 0} := by
    let U : Set ℂ := {w | Gamma w ≠ 0}
    change IsOpen U
    have he : U = {w : ℂ | (Gamma w)⁻¹ ≠ 0} := by ext w; simp [U]
    rw [he]
    have hc : Continuous (fun w : ℂ => (Gamma w)⁻¹) := by
      simpa only [one_div] using differentiable_one_div_Gamma.continuous
    exact isOpen_ne.preimage hc
  have hder := Complex.logDeriv_tendsto hU hΓ tendstoLocallyUniformlyOn_GammaSeq
    (Eventually.of_forall differentiableOn_GammaSeq) hΓ
  change Tendsto _ _ (𝓝 (digamma z)) at hder
  have hγ : Tendsto (fun n : ℕ => (((harmonic (n + 1) : ℝ) - Real.log (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have h := (continuous_ofReal.tendsto Real.eulerMascheroniConstant).comp
      (Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have H := (hder.add hγ).add_const z⁻¹
  apply ((summable_digamma_series hz).hasSum_iff_tendsto_nat).mpr
  rw [← tendsto_add_atTop_iff_nat 1]
  apply H.congr'
  filter_upwards with n
  rw [logDeriv_GammaSeq hz (by omega)]
  have hlog : log ((n + 1 : ℕ) : ℂ) = (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg (n + 1))]
  rw [hlog, sum_range_succ' (f := fun k : ℕ => (z + k)⁻¹)]
  simp only [Nat.cast_zero, add_zero]
  have hharm : ((harmonic (n + 1) : ℝ) : ℂ) =
      ∑ k ∈ range (n + 1), (k + 1 : ℂ)⁻¹ := by
    rw [harmonic]
    push_cast
    rfl
  push_cast only [ofReal_sub]
  rw [hharm, sum_sub_distrib]
  simp_rw [Nat.cast_add, Nat.cast_one, add_assoc]
  ring

/-- The usual partial-fraction expression for the digamma function. -/
theorem digamma_eq_neg_eulerMascheroni_sub_inv_add_tsum {z : ℂ}
    (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) :
    digamma z = -(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
      ∑' k : ℕ, ((k + 1 : ℂ)⁻¹ - (z + k + 1)⁻¹) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end Complex

namespace Real

/-- The logarithmic series for Euler's constant, obtained by telescoping the
logarithms in Mathlib's lower harmonic approximants. -/
theorem hasSum_eulerMascheroni_log_series :
    HasSum (fun k : ℕ => (k + 1 : ℝ)⁻¹ - log (1 + (k + 1 : ℝ)⁻¹))
      eulerMascheroniConstant := by
  have hnonneg (k : ℕ) : 0 ≤ (k + 1 : ℝ)⁻¹ - log (1 + (k + 1 : ℝ)⁻¹) := by
    have h := log_le_sub_one_of_pos (show 0 < 1 + (k + 1 : ℝ)⁻¹ by positivity)
    linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr
  have hsum (n : ℕ) :
      ∑ k ∈ range n, log (1 + (k + 1 : ℝ)⁻¹) = log (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, ← log_mul (by positivity : (n : ℝ) + 1 ≠ 0)
        (by positivity : 1 + (n + 1 : ℝ)⁻¹ ≠ 0)]
      congr 1
      push_cast
      field_simp
  convert tendsto_harmonic_sub_log_add_one using 1
  funext n
  rw [sum_sub_distrib, hsum, harmonic]
  push_cast
  rfl

end Real

namespace Complex

/-- **Carlson (3.6-9).** The logarithmic partial-fraction expansion of digamma,
with the principal complex logarithm and every nonpole parameter. -/
theorem hasSum_digamma_log_series {z : ℂ} (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) :
    HasSum (fun k : ℕ => log (1 + (k + 1 : ℂ)⁻¹) - (z + k + 1)⁻¹)
      (digamma z + z⁻¹) := by
  have hγ := Complex.hasSum_ofReal.mpr Real.hasSum_eulerMascheroni_log_series
  have he (k : ℕ) :
      (((k + 1 : ℝ)⁻¹ - Real.log (1 + (k + 1 : ℝ)⁻¹) : ℝ) : ℂ) =
        (k + 1 : ℂ)⁻¹ - log (1 + (k + 1 : ℂ)⁻¹) := by
    rw [ofReal_sub, ofReal_log (by positivity)]
    push_cast
    rfl
  simp_rw [he] at hγ
  convert (hasSum_digamma_series hz).sub hγ using 1 <;> first | (funext k; ring) | ring

/-- The logarithmic series expression for digamma. -/
theorem digamma_eq_neg_inv_add_log_tsum {z : ℂ}
    (hz : ∀ k : ℕ, z ≠ -(k : ℂ)) :
    digamma z = -z⁻¹ +
      ∑' k : ℕ, (log (1 + (k + 1 : ℂ)⁻¹) - (z + k + 1)⁻¹) := by
  rw [(hasSum_digamma_log_series hz).tsum_eq]
  ring

end Complex
