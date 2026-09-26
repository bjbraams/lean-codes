/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.Gamma
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Ordinary normalization and exceptional total parameters

Multiplication of an analytic regularized function by `Gamma c` restores Carlson's
ordinary normalization. At `c = -m` it has a local analytic numerator divided by `c + m`.
The numerator gives the residue; vanishing of the regularized germ at that point is
exactly the condition for a removable singularity in this one complex variable.
These statements concern punctured germs, not Gamma's totalized center value.

## Main results

* `Complex.Gamma_eq_gammaPoleFactor_div`: a local-pole form valid as a totalized identity.
* `Complex.analyticAt_gammaPoleFactor`: the pole factor is analytic at each exceptional point.
* `Complex.tendsto_mul_Gamma_mul`: the residue of a Gamma-normalized analytic germ.
* `Complex.exists_analyticAt_Gamma_mul_iff`: the one-variable removability criterion.
* `Complex.tendsto_Gamma_mul_of_eq_zero`: the finite value at a removable singularity.
* `Complex.exists_analyticAt_Gamma_mul_comp_of_factor`: joint removal from local divisibility.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 6.
* `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`: reciprocal-Gamma continuation.
-/

open Filter Set Polynomial
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- The analytic factor left after removing Gamma's pole at the nonpositive integer `-m`.
Only its germ at `-m` is asserted to be analytic. -/
def gammaPoleFactor (m : ℕ) (c : ℂ) : ℂ :=
  ((ascPochhammer ℂ m).eval c * (Gamma (c + m + 1))⁻¹)⁻¹

/-- Gamma is the pole factor divided by the local total-parameter coordinate.
The equality includes Lean's totalized values at zeros of the denominator. -/
theorem Gamma_eq_gammaPoleFactor_div (m : ℕ) (c : ℂ) :
    Gamma c = gammaPoleFactor m c / (c + m) := by
  apply inv_injective
  rw [one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat c (m + 1)]
  simp only [gammaPoleFactor, inv_div, ascPochhammer_succ_eval,
    Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring_nf

/-- The Gamma pole factor at `-m` is the classical residue `(-1)^m / m!`. -/
@[simp] theorem gammaPoleFactor_neg_nat (m : ℕ) :
    gammaPoleFactor m (-m) = (-1 : ℂ) ^ m / m.factorial := by
  have hpow : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by rw [← inv_pow]; norm_num
  simp [gammaPoleFactor, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self, div_eq_mul_inv, hpow, mul_comm]

/-- The Gamma pole factor does not vanish at its distinguished point. -/
theorem gammaPoleFactor_neg_nat_ne_zero (m : ℕ) : gammaPoleFactor m (-m) ≠ 0 := by
  rw [gammaPoleFactor_neg_nat]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)

/-- The Gamma pole factor is analytic at its distinguished point. -/
theorem analyticAt_gammaPoleFactor (m : ℕ) : AnalyticAt ℂ (gammaPoleFactor m) (-m) := by
  have hp : AnalyticAt ℂ (fun c : ℂ => (ascPochhammer ℂ m).eval c) (-m) :=
    (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ m)) _ (mem_univ _)
  have hg : AnalyticAt ℂ (fun c : ℂ => (Gamma (c + m + 1))⁻¹) (-m) :=
    (differentiable_one_div_Gamma.analyticAt _).comp_of_eq
      ((analyticAt_id.add analyticAt_const).add analyticAt_const) rfl
  apply (hp.mul hg).inv
  change (ascPochhammer ℂ m).eval (-(m : ℂ)) * (Gamma (-(m : ℂ) + m + 1))⁻¹ ≠ 0
  intro h
  exact gammaPoleFactor_neg_nat_ne_zero m (by unfold gammaPoleFactor; rw [h, inv_zero])

/-- Analytic dependence of an ordinary Gamma normalization away from the exceptional
nonpositive integral total parameters. -/
theorem analyticAt_Gamma_mul_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c F : E → ℂ} {p : E} (hc : AnalyticAt ℂ c p) (hF : AnalyticAt ℂ F p)
    (hreg : ∀ m : ℕ, c p ≠ -m) : AnalyticAt ℂ (fun q => Gamma (c q) * F q) p := by
  have hrecip := (differentiable_one_div_Gamma.analyticAt (c p)).comp_of_eq hc rfl
  have hg := hrecip.inv (inv_ne_zero (Gamma_ne_zero hreg))
  change AnalyticAt ℂ (fun q => ((Gamma (c q))⁻¹)⁻¹) p at hg
  simpa only [inv_inv] using (show AnalyticAt ℂ
    (fun q => ((Gamma (c q))⁻¹)⁻¹ * F q) p from hg.mul hF)

/-- Every one-complex-variable analytic specialization of a Gamma normalization is
meromorphic, including specializations meeting exceptional total parameters. -/
theorem meromorphicAt_Gamma_mul_comp {c F : ℂ → ℂ} {p : ℂ}
    (hc : AnalyticAt ℂ c p) (hF : AnalyticAt ℂ F p) :
    MeromorphicAt (fun q => Gamma (c q) * F q) p :=
  ((Meromorphic.Gamma (c p)).comp_analyticAt hc).mul hF.meromorphicAt

/-- After multiplication by the local coordinate, a Gamma-normalized continuous germ
has limit `(-1)^m / m!` times its regularized value. -/
theorem tendsto_mul_Gamma_mul (m : ℕ) {F : ℂ → ℂ} (hF : ContinuousAt F (-m)) :
    Tendsto (fun c => (c + m) * (Gamma c * F c)) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) * F (-m))) := by
  have h : Tendsto (fun c => gammaPoleFactor m c * F c) (𝓝[≠] (-m : ℂ))
      (𝓝 (gammaPoleFactor m (-m) * F (-m))) :=
    ((analyticAt_gammaPoleFactor m).continuousAt.mul hF).continuousWithinAt.tendsto
  rw [gammaPoleFactor_neg_nat] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hne : c + (m : ℂ) ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hc
  rw [Gamma_eq_gammaPoleFactor_div m c]
  field_simp

/-- A Gamma-normalized analytic germ has a removable singularity at `-m` exactly when
its regularized value vanishes. The extension need not equal the totalized product there. -/
theorem exists_analyticAt_Gamma_mul_iff (m : ℕ) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F (-m)) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => Gamma c * F c) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔ F (-m) = 0 := by
  constructor
  · rintro ⟨H, hH, he⟩
    have hzero : Tendsto (fun c => (c + m) * H c) (𝓝[≠] (-m : ℂ)) (𝓝 0) := by
      have hc : ContinuousAt (fun c : ℂ => (c + (m : ℂ)) * H c) (-m) :=
        (continuousAt_id.add continuousAt_const).mul hH.continuousAt
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {-(m : ℂ)}ᶜ))
    have hlim := tendsto_mul_Gamma_mul m hF.continuousAt
    have he' : (fun c => (c + m) * (Gamma c * F c)) =ᶠ[𝓝[≠] (-m : ℂ)]
        (fun c => (c + m) * H c) := he.mono fun c hc => congrArg (fun a => (c + m) * a) hc
    have hval := tendsto_nhds_unique hlim (hzero.congr' he'.symm)
    exact (mul_eq_zero.mp hval).resolve_left (by
      simpa only [gammaPoleFactor_neg_nat] using gammaPoleFactor_neg_nat_ne_zero m)
  · intro hzero
    have hd : AnalyticAt ℂ (dslope F (-m)) (-m) := by
      obtain ⟨r, hr, ha⟩ := hF.exists_ball_analyticOnNhd
      exact ((differentiableOn_dslope (Metric.ball_mem_nhds _ hr)).mpr
        ha.differentiableOn).analyticAt (Metric.ball_mem_nhds _ hr)
    refine ⟨fun c => gammaPoleFactor m c * dslope F (-m) c,
      (analyticAt_gammaPoleFactor m).mul hd, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hne : c ≠ -(m : ℂ) := hc
    rw [Gamma_eq_gammaPoleFactor_div m c, dslope_of_ne _ hne, slope_def_field, hzero]
    simp only [sub_zero, sub_neg_eq_add]
    ring

/-- The analytic numerator of an ordinary normalization at an exceptional total parameter.
This is a joint statement for arbitrary complex normed parameter spaces. -/
theorem analyticAt_gammaPoleFactor_mul_comp (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c F : E → ℂ} {p : E} (hc : AnalyticAt ℂ c p) (hF : AnalyticAt ℂ F p)
    (hm : c p = -m) :
    AnalyticAt ℂ (fun q => gammaPoleFactor m (c q) * F q) p :=
  ((analyticAt_gammaPoleFactor m).comp_of_eq hc hm).mul hF

/-- The ordinary normalization is its pole numerator divided by the local total parameter.
This identity alone does not assert removability along the whole exceptional hypersurface. -/
theorem Gamma_mul_eq_poleNumerator_div (m : ℕ) (c v : ℂ) :
    Gamma c * v = (gammaPoleFactor m c * v) / (c + m) := by
  rw [Gamma_eq_gammaPoleFactor_div m c]
  ring

/-- At a removable Gamma-normalization singularity, the finite value is the Gamma residue
multiplied by the derivative of the regularized germ. -/
theorem tendsto_Gamma_mul_of_eq_zero (m : ℕ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (-m)) (hzero : F (-m) = 0) :
    Tendsto (fun c => Gamma c * F c) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) * deriv F (-m))) := by
  have hd : ContinuousAt (dslope F (-m)) (-m) := continuousAt_dslope_same.mpr hF
  have h : Tendsto (fun c => gammaPoleFactor m c * dslope F (-m) c)
      (𝓝[≠] (-m : ℂ)) (𝓝 (gammaPoleFactor m (-m) * dslope F (-m) (-m))) :=
    ((analyticAt_gammaPoleFactor m).continuousAt.mul hd).continuousWithinAt.tendsto
  rw [gammaPoleFactor_neg_nat, dslope_same] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hne : c ≠ -(m : ℂ) := hc
  rw [Gamma_eq_gammaPoleFactor_div m c, dslope_of_ne _ hne, slope_def_field, hzero]
  simp only [sub_zero, sub_neg_eq_add]
  ring

/-- A nonzero regularized value at an exceptional total parameter prevents any finite
limit of the ordinary one-variable normalization. -/
theorem not_tendsto_Gamma_mul_of_ne_zero (m : ℕ) {F : ℂ → ℂ}
    (hF : ContinuousAt F (-m)) (hne : F (-m) ≠ 0) (v : ℂ) :
    ¬ Tendsto (fun c => Gamma c * F c) (𝓝[≠] (-m : ℂ)) (𝓝 v) := by
  intro h
  have hc : Tendsto (fun c : ℂ => c + (m : ℂ)) (𝓝[≠] (-m : ℂ)) (𝓝 0) := by
    simpa using (continuousAt_id.add_const (m : ℂ)).tendsto.mono_left
      (nhdsWithin_le_nhds (a := -(m : ℂ)) (s := {-(m : ℂ)}ᶜ))
  have heq := tendsto_nhds_unique (tendsto_mul_Gamma_mul m hF) (hc.mul h)
  have hn : ((-1 : ℂ) ^ m / m.factorial) * F (-m) ≠ 0 :=
    mul_ne_zero (by simpa using gammaPoleFactor_neg_nat_ne_zero m) hne
  exact hn (by simpa using heq)

/-- Divisibility of the regularized family by the exceptional total-parameter factor
supplies a joint analytic extension of the ordinary normalization. Agreement is asserted
off that hypersurface; vanishing only at the base point is not sufficient. -/
theorem exists_analyticAt_Gamma_mul_comp_of_factor (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c F H : E → ℂ} {p : E} (hc : AnalyticAt ℂ c p) (hH : AnalyticAt ℂ H p)
    (hm : c p = -m) (hfactor : ∀ᶠ q in 𝓝 p, F q = (c q + m) * H q) :
    ∃ K : E → ℂ, AnalyticAt ℂ K p ∧ K p = ((-1 : ℂ) ^ m / m.factorial) * H p ∧
      (fun q => Gamma (c q) * F q) =ᶠ[𝓝 p ⊓ 𝓟 {q | c q ≠ -m}] K := by
  refine ⟨fun q => gammaPoleFactor m (c q) * H q,
    analyticAt_gammaPoleFactor_mul_comp m hc hH hm, ?_, ?_⟩
  · change gammaPoleFactor m (c p) * H p = _
    rw [hm, gammaPoleFactor_neg_nat]
  · filter_upwards [hfactor.filter_mono inf_le_left,
      (show ∀ᶠ q in 𝓟 {q | c q ≠ -m}, c q ≠ -m from eventually_mem_principal _).filter_mono
        inf_le_right] with q hq hne
    rw [Gamma_eq_gammaPoleFactor_div m (c q), hq]
    have hn : c q + (m : ℂ) ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    field_simp

end Complex
