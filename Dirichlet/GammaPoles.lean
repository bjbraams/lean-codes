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
public import SeveralComplexVariables.SeparateAnalytic

/-!
# Gamma poles of regularized functions

Multiplication of an analytic regularized function by `Gamma c` restores the ordinary
normalization. At `c = -m` it has a local analytic numerator divided by `c + m`. The numerator
gives the residue; vanishing of the regularized germ at that point is exactly the condition for
a removable singularity in this one complex variable. These statements concern punctured germs,
not Gamma's totalized center value.

When the regularized function vanishes along every exceptional hyperplane `p none = -m`, the
singularities are removable jointly in all variables: along each line in the exceptional
variable the singularity is removable, the filled-in value is the Gamma residue times the
derivative, and joint analyticity follows from Hartogs' theorem on separate analyticity.

These results were previously part of `Carlson.Normalization.Basic` and
`Carlson.Normalization.EqualParameter`; they are used by the Dirichlet-average continuation
theory as well as by the Carlson functions.

## Main definitions

* `Complex.GammaPoleFactor`: the analytic factor left after removing a Gamma pole.
* `Complex.GammaRemovedValue`: `Γ(p none) G(p)` with its removable singularities filled in.

## Main results

* `Complex.Gamma_eq_GammaPoleFactor_div`: a local-pole form valid as a totalized identity.
* `Complex.analyticAt_GammaPoleFactor`: the pole factor is analytic at each exceptional point.
* `Complex.tendsto_mul_Gamma_mul`: the residue of a Gamma-normalized analytic germ.
* `Complex.exists_analyticAt_Gamma_mul_iff`: the one-variable removability criterion.
* `Complex.tendsto_Gamma_mul_of_eq_zero`: the finite value at a removable singularity.
* `Complex.exists_analyticAt_Gamma_mul_comp_of_factor`: joint removal from local divisibility.
* `Complex.analyticOnNhd_GammaRemovedValue`: removal of Gamma poles in one variable, jointly
  analytic in the others, when the regularized function vanishes at the poles.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 6.
* `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`: reciprocal-Gamma continuation.
-/

open Filter Set Polynomial Function
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- The analytic factor left after removing Gamma's pole at the nonpositive integer `-m`.
Only its germ at `-m` is asserted to be analytic. -/
def GammaPoleFactor (m : ℕ) (c : ℂ) : ℂ :=
  ((ascPochhammer ℂ m).eval c * (Gamma (c + m + 1))⁻¹)⁻¹

/-- Gamma is the pole factor divided by the local total-parameter coordinate.
The equality includes Lean's totalized values at zeros of the denominator. -/
theorem Gamma_eq_GammaPoleFactor_div (m : ℕ) (c : ℂ) :
    Gamma c = GammaPoleFactor m c / (c + m) := by
  apply inv_injective
  rw [one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat c (m + 1)]
  simp only [GammaPoleFactor, inv_div, ascPochhammer_succ_eval,
    Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring_nf

/-- The Gamma pole factor at `-m` is the classical residue `(-1)^m / m!`. -/
@[simp] theorem GammaPoleFactor_neg_nat (m : ℕ) :
    GammaPoleFactor m (-m) = (-1 : ℂ) ^ m / m.factorial := by
  have hpow : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by rw [← inv_pow]; norm_num
  simp [GammaPoleFactor, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self, div_eq_mul_inv, hpow, mul_comm]

/-- The Gamma pole factor does not vanish at its distinguished point. -/
theorem GammaPoleFactor_neg_nat_ne_zero (m : ℕ) : GammaPoleFactor m (-m) ≠ 0 := by
  rw [GammaPoleFactor_neg_nat]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)

/-- The Gamma pole factor is analytic at its distinguished point. -/
theorem analyticAt_GammaPoleFactor (m : ℕ) : AnalyticAt ℂ (GammaPoleFactor m) (-m) := by
  have hp : AnalyticAt ℂ (fun c : ℂ => (ascPochhammer ℂ m).eval c) (-m) :=
    (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ m)) _ (mem_univ _)
  have hg : AnalyticAt ℂ (fun c : ℂ => (Gamma (c + m + 1))⁻¹) (-m) :=
    (differentiable_one_div_Gamma.analyticAt _).comp_of_eq
      ((analyticAt_id.add analyticAt_const).add analyticAt_const) rfl
  apply (hp.mul hg).inv
  change (ascPochhammer ℂ m).eval (-(m : ℂ)) * (Gamma (-(m : ℂ) + m + 1))⁻¹ ≠ 0
  intro h
  exact GammaPoleFactor_neg_nat_ne_zero m (by unfold GammaPoleFactor; rw [h, inv_zero])

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
  have h : Tendsto (fun c => GammaPoleFactor m c * F c) (𝓝[≠] (-m : ℂ))
      (𝓝 (GammaPoleFactor m (-m) * F (-m))) :=
    ((analyticAt_GammaPoleFactor m).continuousAt.mul hF).continuousWithinAt.tendsto
  rw [GammaPoleFactor_neg_nat] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hne : c + (m : ℂ) ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hc
  rw [Gamma_eq_GammaPoleFactor_div m c]
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
      simpa only [GammaPoleFactor_neg_nat] using GammaPoleFactor_neg_nat_ne_zero m)
  · intro hzero
    have hd : AnalyticAt ℂ (dslope F (-m)) (-m) := by
      obtain ⟨r, hr, ha⟩ := hF.exists_ball_analyticOnNhd
      exact ((differentiableOn_dslope (Metric.ball_mem_nhds _ hr)).mpr
        ha.differentiableOn).analyticAt (Metric.ball_mem_nhds _ hr)
    refine ⟨fun c => GammaPoleFactor m c * dslope F (-m) c,
      (analyticAt_GammaPoleFactor m).mul hd, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hne : c ≠ -(m : ℂ) := hc
    rw [Gamma_eq_GammaPoleFactor_div m c, dslope_of_ne _ hne, slope_def_field, hzero]
    simp only [sub_zero, sub_neg_eq_add]
    ring

/-- The analytic numerator of an ordinary normalization at an exceptional total parameter.
This is a joint statement for arbitrary complex normed parameter spaces. -/
theorem analyticAt_GammaPoleFactor_mul_comp (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c F : E → ℂ} {p : E} (hc : AnalyticAt ℂ c p) (hF : AnalyticAt ℂ F p)
    (hm : c p = -m) :
    AnalyticAt ℂ (fun q => GammaPoleFactor m (c q) * F q) p :=
  ((analyticAt_GammaPoleFactor m).comp_of_eq hc hm).mul hF

/-- The ordinary normalization is its pole numerator divided by the local total parameter.
This identity alone does not assert removability along the whole exceptional hypersurface. -/
theorem Gamma_mul_eq_poleNumerator_div (m : ℕ) (c v : ℂ) :
    Gamma c * v = (GammaPoleFactor m c * v) / (c + m) := by
  rw [Gamma_eq_GammaPoleFactor_div m c]
  ring

/-- At a removable Gamma-normalization singularity, the finite value is the Gamma residue
multiplied by the derivative of the regularized germ. -/
theorem tendsto_Gamma_mul_of_eq_zero (m : ℕ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (-m)) (hzero : F (-m) = 0) :
    Tendsto (fun c => Gamma c * F c) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) * deriv F (-m))) := by
  have hd : ContinuousAt (dslope F (-m)) (-m) := continuousAt_dslope_same.mpr hF
  have h : Tendsto (fun c => GammaPoleFactor m c * dslope F (-m) c)
      (𝓝[≠] (-m : ℂ)) (𝓝 (GammaPoleFactor m (-m) * dslope F (-m) (-m))) :=
    ((analyticAt_GammaPoleFactor m).continuousAt.mul hd).continuousWithinAt.tendsto
  rw [GammaPoleFactor_neg_nat, dslope_same] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hne : c ≠ -(m : ℂ) := hc
  rw [Gamma_eq_GammaPoleFactor_div m c, dslope_of_ne _ hne, slope_def_field, hzero]
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
    mul_ne_zero (by simpa using GammaPoleFactor_neg_nat_ne_zero m) hne
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
  refine ⟨fun q => GammaPoleFactor m (c q) * H q,
    analyticAt_GammaPoleFactor_mul_comp m hc hH hm, ?_, ?_⟩
  · change GammaPoleFactor m (c p) * H p = _
    rw [hm, GammaPoleFactor_neg_nat]
  · filter_upwards [hfactor.filter_mono inf_le_left,
      (show ∀ᶠ q in 𝓟 {q | c q ≠ -m}, c q ≠ -m from eventually_mem_principal _).filter_mono
        inf_le_right] with q hq hne
    rw [Gamma_eq_GammaPoleFactor_div m (c q), hq]
    have hn : c q + (m : ℂ) ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    field_simp

/-- The zeros of Gamma, which are its totalized values at the poles, are isolated. -/
theorem eventually_Gamma_ne_zero_nhdsNE (β₀ : ℂ) :
    ∀ᶠ β in 𝓝[≠] β₀, Gamma β ≠ 0 := by
  have ha : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) β₀ :=
    differentiable_one_div_Gamma.analyticAt β₀
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall := (differentiable_one_div_Gamma.differentiableOn.analyticOnNhd
      isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ β₀) h
    have := hall (mem_univ 1)
    simp at this
  · filter_upwards [h] with β hβ
    exact fun h' => hβ (by simp [h'])


/-- The index `m` of a Gamma pole `-m`, read off from the real part. -/
def GammaPoleIndex (β : ℂ) : ℕ := ⌊-β.re⌋₊

/-- The pole index of `-m` is `m`. -/
@[simp] theorem GammaPoleIndex_neg_nat (m : ℕ) : GammaPoleIndex (-m) = m := by
  simp [GammaPoleIndex]

/-- The residue-weighted derivative that removes a Gamma pole in the first coordinate. -/
def GammaRemovedValue {κ : Type*} [DecidableEq κ] (G : (Option κ → ℂ) → ℂ)
    (p : Option κ → ℂ) : ℂ :=
  if Gamma (p none) = 0 then
    ((-1 : ℂ) ^ GammaPoleIndex (p none) / (GammaPoleIndex (p none)).factorial) *
      fderiv ℂ G p (Pi.single none 1)
  else Gamma (p none) * G p

/-- Updating one coordinate of a finite complex vector is analytic in the new value. -/
theorem analyticAt_update_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → ℂ) (i : κ)
    (w : ℂ) :
    AnalyticAt ℂ (fun v : ℂ => update p i v) w := by
  refine analyticAt_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h; simp only [update_self]; exact analyticAt_id
  · simpa [update_of_ne h] using analyticAt_const

/-- **Removal of Gamma poles in one variable, jointly in the others.** Let `G` be analytic on
an open set of `Option κ → ℂ` and vanish wherever its `none` coordinate is a nonpositive
integer. Then `Γ(p none) G p` extends analytically across these points. -/
theorem analyticOnNhd_GammaRemovedValue {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Set (Option κ → ℂ)} (hU : IsOpen U) {G : (Option κ → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G U) (hzero : ∀ p ∈ U, Gamma (p none) = 0 → G p = 0) :
    AnalyticOnNhd ℂ (GammaRemovedValue G) U := by
  apply SeveralComplexVariables.analyticOnNhd_of_separately_analytic hU
  intro p hp i
  have hGline : ∀ j, AnalyticAt ℂ (fun w => G (update p j w)) (p j) := fun j =>
    (hG _ (by simpa using hp)).comp_of_eq (analyticAt_update_apply p j (p j)) (by simp)
  rcases i with _ | j
  · by_cases hpole : Gamma (p none) = 0
    · obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hpole
      set F : ℂ → ℂ := fun w => G (update p none w)
      have hF : AnalyticAt ℂ F (-m) := by rw [← hm]; exact hGline none
      have hF0 : F (-m) = 0 := by
        simp only [F, ← hm, update_eq_self]; exact hzero p hp hpole
      obtain ⟨H, hH, hHe⟩ := (exists_analyticAt_Gamma_mul_iff m hF).mpr hF0
      have hlim := tendsto_Gamma_mul_of_eq_zero m hF.differentiableAt hF0
      have hHval : H (-m) = ((-1 : ℂ) ^ m / m.factorial) * deriv F (-m) :=
        tendsto_nhds_unique (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (hlim.congr' hHe)
      have hderiv : deriv F (-m) = fderiv ℂ G p (Pi.single none 1) := by
        have h1 : HasFDerivAt G (fderiv ℂ G p) (update p none (-m)) := by
          rw [← hm, update_eq_self]; exact (hG p hp).differentiableAt.hasFDerivAt
        exact (h1.comp_hasDerivAt (-(m : ℂ)) (hasDerivAt_update p none _)).deriv
      rw [hm]
      apply hH.congr
      have hne := Complex.eventually_Gamma_ne_zero_nhdsNE (-(m : ℂ))
      have hHe' := eventually_nhdsWithin_iff.mp hHe
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hHe', hne] with w hw1 hw2
      by_cases hw : w = -m
      · subst hw
        rw [hHval, hderiv, GammaRemovedValue, update_self, GammaPoleIndex_neg_nat,
          Gamma_neg_nat_eq_zero m]
        simp only [↓reduceIte]
        rw [← hm, update_eq_self]
      · have hg := hw2 hw
        simp only [GammaRemovedValue, update_self, hg, ite_false]
        exact (hw1 hw).symm
    · have hev : ∀ᶠ w in 𝓝 (p none), Gamma w ≠ 0 :=
        (differentiable_one_div_Gamma.continuous.continuousAt.eventually_ne
          (inv_ne_zero hpole)).mono fun w hw h => hw (by simp [h])
      have ha : AnalyticAt ℂ (fun w => Gamma w * G (update p none w)) (p none) :=
        analyticAt_Gamma_mul_comp analyticAt_id (hGline none)
          (fun m h => hpole ((Gamma_eq_zero_iff _).mpr ⟨m, h⟩))
      apply ha.congr
      filter_upwards [hev] with w hw
      simp [GammaRemovedValue, hw]
  · by_cases hpole : Gamma (p none) = 0
    · have hd : AnalyticAt ℂ (fun w => fderiv ℂ G (update p (some j) w) (Pi.single none 1))
          (p (some j)) := by
        have h1 := (hG.fderiv p hp).comp_of_eq (analyticAt_update_apply p (some j) (p (some j)))
          (by simp)
        exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single none 1)).analyticAt _).comp h1
      refine ((analyticAt_const (v := (-1 : ℂ) ^ GammaPoleIndex (p none) /
        (GammaPoleIndex (p none)).factorial)).mul hd).congr (Eventually.of_forall fun w => ?_)
      simp [GammaRemovedValue, hpole]
    · refine ((analyticAt_const (v := Gamma (p none))).mul (hGline (some j))).congr
        (Eventually.of_forall fun w => ?_)
      simp [GammaRemovedValue, hpole]

/-- Off the Gamma poles the removed value is the product itself. -/
theorem GammaRemovedValue_of_ne {κ : Type*} [DecidableEq κ] (G : (Option κ → ℂ) → ℂ)
    {p : Option κ → ℂ} (hp : ∀ m : ℕ, p none ≠ -m) :
    GammaRemovedValue G p = Gamma (p none) * G p := by
  simp [GammaRemovedValue, Gamma_ne_zero hp]

/-- The removed value is the limit of the Gamma-normalized product along punctured
neighborhoods in the first coordinate. -/
theorem tendsto_GammaRemovedValue {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Set (Option κ → ℂ)} {G : (Option κ → ℂ) → ℂ}
    (hK : AnalyticOnNhd ℂ (GammaRemovedValue G) U) {p : Option κ → ℂ} (hp : p ∈ U) :
    Tendsto (fun β => Gamma β * G (update p none β)) (𝓝[≠] (p none))
      (𝓝 (GammaRemovedValue G p)) := by
  have hc : ContinuousAt (fun β => GammaRemovedValue G (update p none β)) (p none) :=
    ((hK p hp).comp_of_eq (analyticAt_update_apply p none (p none)) (by simp)).continuousAt
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p none}ᶜ))
  rw [update_eq_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_Gamma_ne_zero_nhdsNE (p none)] with β hβ
  rw [GammaRemovedValue_of_ne _ (fun m h => hβ ((Gamma_eq_zero_iff _).mpr ⟨m, by simpa using h⟩))]
  simp

end Complex
