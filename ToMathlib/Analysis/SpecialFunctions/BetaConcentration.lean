/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BetaDensity
public import ToMathlib.Analysis.SpecialFunctions.BetaKernel
public import ToMathlib.Analysis.Integral.TwoCrossings

/-!
# Strict convex comparison of beta distributions

Increasing both beta parameters by a common factor strictly decreases the
expectation of any continuous strictly convex function on the unit interval.
The proof uses the two crossings of the density ratio and cancellation of the
zeroth and first moments, following Carlson–Tobey (1968).
-/

open MeasureTheory Set
public noncomputable section
namespace ProbabilityTheory

/-- The restriction of Lebesgue measure to the open unit interval is nonzero. -/
private theorem volume_unitInterval_ne_zero :
    volume.restrict (Ioo (0 : ℝ) 1) ≠ 0 := by
  intro h
  have h := congrArg (fun μ : Measure ℝ => μ univ) h
  simp [Real.volume_Ioo] at h

/-- The density ratio for two different concentrations exceeds one at its mode. -/
private theorem beta_concentration_ratio_max {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcd : c < d) :
    let A := (d - c) * a
    let B := (d - c) * b
    let K := beta (c * a) (c * b) / beta (d * a) (d * b)
    1 < K * (A / (A + B)) ^ A * (1 - A / (A + B)) ^ B := by
  let A := (d - c) * a
  let B := (d - c) * b
  let K := beta (c * a) (c * b) / beta (d * a) (d * b)
  let m := A / (A + B)
  let F := fun u : ℝ => K * u ^ A * (1 - u) ^ B
  change 1 < F m
  have hd := hc.trans hcd
  have hA : 0 < A := mul_pos (sub_pos.mpr hcd) ha
  have hB : 0 < B := mul_pos (sub_pos.mpr hcd) hb
  have hK : 0 < K := div_pos (beta_pos (mul_pos hc ha) (mul_pos hc hb))
    (beta_pos (mul_pos hd ha) (mul_pos hd hb))
  have hm0 : 0 < m := div_pos hA (add_pos hA hB)
  have hm1 : m < 1 := (div_lt_one (add_pos hA hB)).mpr (by linarith)
  have hmono := Real.strictMonoOn_betaKernel hK hA hB
  have hanti := Real.strictAntiOn_betaKernel hK hA hB
  let : NeZero (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨volume_unitInterval_ne_zero⟩
  by_contra hn
  have hn : F m ≤ 1 := le_of_not_gt hn
  have hcmp : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      betaPDFReal (d * a) (d * b) u < betaPDFReal (c * a) (c * b) u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo,
      ae_restrict_of_ae (volume.ae_ne m)] with u hu hne
    have hF : F u < F m := by
      rcases lt_or_gt_of_ne hne with hum | hmu
      · exact hmono ⟨hu.1.le, hum.le⟩ ⟨hm0.le, le_rfl⟩ hum
      · exact hanti ⟨le_rfl, hm1.le⟩ ⟨hmu.le, hu.2.le⟩ hmu
    rw [betaPDFReal_concentration_ratio ha hb hc hu]
    change betaPDFReal (c * a) (c * b) u * F u < betaPDFReal (c * a) (c * b) u
    have hp := betaPDFReal_pos hu.1 hu.2 (mul_pos hc ha) (mul_pos hc hb)
    nlinarith [hF.trans_le hn]
  have h := integral_lt_integral_of_ae_lt
    (integrable_betaPDFReal (mul_pos hd ha) (mul_pos hd hb)).restrict
    (integrable_betaPDFReal (mul_pos hc ha) (mul_pos hc hb)).restrict hcmp
  have he (p q : ℝ) : (∫ u in Ioo (0 : ℝ) 1, betaPDFReal p q u) =
      ∫ u, betaPDFReal p q u := by
    simpa using integral_betaPDFReal_mul_Ioo p q (fun _ => 1)
  rw [he, he, integral_betaPDFReal (mul_pos hd ha) (mul_pos hd hb),
    integral_betaPDFReal (mul_pos hc ha) (mul_pos hc hb)] at h
  exact (lt_irrefl _ h)

/-- Increasing concentration strictly decreases a continuous strictly convex beta average. -/
theorem integral_betaMeasure_lt_of_concentration {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcd : c < d)
    {f : ℝ → ℝ} (hf : StrictConvexOn ℝ (Icc 0 1) f)
    (hfcont : ContinuousOn f (Icc 0 1)) :
    (∫ u, f u ∂betaMeasure (d * a) (d * b)) <
      ∫ u, f u ∂betaMeasure (c * a) (c * b) := by
  have hd := hc.trans hcd
  have hca := mul_pos hc ha
  have hcb := mul_pos hc hb
  have hda := mul_pos hd ha
  have hdb := mul_pos hd hb
  let pc := betaPDFReal (c * a) (c * b)
  let pd := betaPDFReal (d * a) (d * b)
  let g := fun u => pd u - pc u
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let : NeZero μ := ⟨volume_unitInterval_ne_zero⟩
  have hpc : Integrable pc := integrable_betaPDFReal hca hcb
  have hpd : Integrable pd := integrable_betaPDFReal hda hdb
  have hip (h : ℝ → ℝ) (hh : ContinuousOn h (Icc 0 1)) :
      Integrable (fun u => h u * g u) := by
    have h1 := integrable_betaPDFReal_mul_of_continuousOn hda hdb hh
    have h2 := integrable_betaPDFReal_mul_of_continuousOn hca hcb hh
    convert h1.sub h2 using 1
    ext u
    dsimp [g, pd, pc]
    ring
  have he (h : ℝ → ℝ) (hh : ContinuousOn h (Icc 0 1)) :
      (∫ u, h u * g u ∂μ) = (∫ u, pd u * h u) - ∫ u, pc u * h u := by
    have h1 := integrable_betaPDFReal_mul_of_continuousOn hda hdb hh
    have h2 := integrable_betaPDFReal_mul_of_continuousOn hca hcb hh
    have heq : (fun u => h u * g u) =
        (fun u => pd u * h u - pc u * h u) := by funext u; dsimp [g]; ring
    rw [heq, integral_sub h1.restrict h2.restrict]
    exact congrArg₂ (· - ·) (integral_betaPDFReal_mul_Ioo _ _ h)
      (integral_betaPDFReal_mul_Ioo _ _ h)
  have h0 : (∫ u, g u ∂μ) = 0 := by
    have h := he (fun _ => 1) continuousOn_const
    simpa only [one_mul, mul_one, pd, pc, integral_betaPDFReal hda hdb,
      integral_betaPDFReal hca hcb, sub_self] using h
  have h1 : (∫ u, u * g u ∂μ) = 0 := by
    rw [he (fun u => u) continuousOn_id]
    have hed : (∫ u, pd u * u) = a / (a + b) := by
      simpa only [pd, mul_comm] using integral_mul_betaPDFReal_concentration ha hb hd
    have hec : (∫ u, pc u * u) = a / (a + b) := by
      simpa only [pc, mul_comm] using integral_mul_betaPDFReal_concentration ha hb hc
    rw [hed, hec, sub_self]
  have hK := div_pos (beta_pos hca hcb) (beta_pos hda hdb)
  obtain ⟨l, r, hl, hlr, hr, hpos, hneg⟩ := Real.exists_betaKernel_crossings hK
    (mul_pos (sub_pos.mpr hcd) ha) (mul_pos (sub_pos.mpr hcd) hb)
    (beta_concentration_ratio_max ha hb hc hcd)
  have hs : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1 := self_mem_ae_restrict measurableSet_Ioo
  have hp : ∀ᵐ u ∂μ, u ∈ Ioo l r → 0 < g u := by
    filter_upwards [hs] with u hu hur
    have h := hpos u hur
    have hp := betaPDFReal_pos hu.1 hu.2 hca hcb
    dsimp only [g, pc, pd]
    rw [betaPDFReal_concentration_ratio ha hb hc hu]
    nlinarith
  have hn : ∀ᵐ u ∂μ, u < l ∨ r < u → g u < 0 := by
    filter_upwards [hs] with u hu hur
    have h := hneg u hu hur
    have hp := betaPDFReal_pos hu.1 hu.2 hca hcb
    dsimp only [g, pc, pd]
    rw [betaPDFReal_concentration_ratio ha hb hc hu]
    nlinarith
  have h := hf.integral_mul_neg_of_two_crossings
    ⟨hl.le, (hlr.trans hr).le⟩ ⟨(hl.trans hlr).le, hr.le⟩ hlr
    (hs.mono fun _ hu => ⟨hu.1.le, hu.2.le⟩)
    (by filter_upwards [ae_restrict_of_ae (volume.ae_ne l), ae_restrict_of_ae (volume.ae_ne r)]
        with u hu hv; exact ⟨hu, hv⟩)
    hp hn (hpd.sub hpc).restrict (hip _ continuousOn_id).restrict
    (hip _ hfcont).restrict h0 h1
  rw [he _ hfcont] at h
  rw [integral_betaMeasure hda hdb, integral_betaMeasure hca hcb]
  exact sub_neg.mp h

/-- Increasing concentration strictly increases a continuous strictly concave beta average. -/
theorem integral_betaMeasure_lt_of_concentration_concave {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcd : c < d)
    {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Icc 0 1) f)
    (hfcont : ContinuousOn f (Icc 0 1)) :
    (∫ u, f u ∂betaMeasure (c * a) (c * b)) <
      ∫ u, f u ∂betaMeasure (d * a) (d * b) := by
  have h := integral_betaMeasure_lt_of_concentration ha hb hc hcd hf.neg hfcont.neg
  simpa only [Pi.neg_apply, integral_neg, neg_lt_neg_iff] using h

end ProbabilityTheory
