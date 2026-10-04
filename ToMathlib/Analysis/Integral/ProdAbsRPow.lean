/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrability of products of powers with distinct real singularities

For distinct real nodes `xᵢ` and exponents `bᵢ < 1` with `∑ bᵢ > 1`, the function
`σ ↦ ∏ |σ - xᵢ|^{-bᵢ}` is integrable on the whole real line: each singularity is integrable
because `bᵢ < 1`, and the decay `|σ|^{-∑ bᵢ}` at infinity is integrable because `∑ bᵢ > 1`.
This is the integrability behind the boundary values of Schwarz–Christoffel integrals.

## Main results

* `intervalIntegrable_abs_sub_rpow`: `|σ - c|^r` is interval integrable for `r > -1`.
* `integrable_prod_abs_sub_rpow_neg`: integrability of `∏ |σ - xᵢ|^{-bᵢ}` on `ℝ`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Topology

/-- For `r > -1`, `σ ↦ |σ - c|^r` is interval integrable on every interval. -/
theorem intervalIntegrable_abs_sub_rpow {r : ℝ} (hr : -1 < r) (c a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ => |σ - c| ^ r) volume a b := by
  have h0 : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun σ : ℝ => |σ| ^ r) volume 0 t := by
    intro t ht
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hr).congr ?_
    intro σ hσ
    rw [uIoc_of_le ht] at hσ
    simp [abs_of_pos hσ.1]
  have h1 : ∀ t : ℝ, IntervalIntegrable (fun σ : ℝ => |σ| ^ r) volume 0 t := by
    intro t
    rcases le_total 0 t with ht | ht
    · exact h0 t ht
    · have := (h0 (-t) (by linarith)).comp_mul_left (c := -1)
      simpa [abs_neg] using this
  have h2 : IntervalIntegrable (fun σ : ℝ => |σ| ^ r) volume (a - c) (b - c) :=
    (h1 (a - c)).symm.trans (h1 (b - c))
  simpa using h2.comp_sub_right c

/-- **Integrability of `∏ |σ - xᵢ|^{-bᵢ}`**: for injective real nodes `xᵢ` and exponents
`bᵢ < 1` with `∑ bᵢ > 1`, the product is integrable on `ℝ`. -/
theorem integrable_prod_abs_sub_rpow_neg {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : Function.Injective x) {b : ι → ℝ} (hb1 : ∀ i, b i < 1)
    (hsum : 1 < ∑ i, b i) :
    Integrable (fun σ : ℝ => ∏ i, |σ - x i| ^ (-b i)) := by
  classical
  set f : ℝ → ℝ := fun σ => ∏ i, |σ - x i| ^ (-b i) with hf_def
  have hmeas : Measurable f :=
    Finset.measurable_prod _ fun i _ =>
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable.pow_const _
  have hf0 : ∀ σ, 0 ≤ f σ := fun σ =>
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  -- local integrability
  have hloc : LocallyIntegrable f := by
    intro y
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, x i ≠ y → 2 * δ ≤ |y - x i| := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : x i = y
      · exact Filter.Eventually.of_forall fun _ h => (h hi).elim
      · have hpos : 0 < |y - x i| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hi))
        have : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < |y - x i| / 2 :=
          eventually_lt_nhds (by linarith)
        filter_upwards [nhdsWithin_le_nhds this] with δ hδ _
        linarith
    obtain ⟨δ, hδ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδpos : 0 < δ := hδpos
    refine ⟨Ioo (y - δ) (y + δ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    -- the bound
    let C := fun i => max (δ ^ (-b i)) ((|y - x i| + δ) ^ (-b i))
    set g : ℝ → ℝ := fun σ => ∏ i, (if x i = y then |σ - y| ^ (-b i) else C i) with hg
    have hbound : ∀ σ ∈ Ioo (y - δ) (y + δ), f σ ≤ g σ := by
      intro σ hσ
      refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) fun i _ => ?_
      split_ifs with hi
      · rw [hi]
      · have hd : δ ≤ |σ - x i| := by
          have h2 := hδ i hi
          have : |y - x i| ≤ |y - σ| + |σ - x i| := by
            have := abs_sub_le y σ (x i); linarith
          have hyσ : |y - σ| < δ := by
            rw [abs_sub_lt_iff]; constructor <;> linarith [hσ.1, hσ.2]
          linarith
        by_cases hb : 0 ≤ b i
        · exact (Real.rpow_le_rpow_of_nonpos hδpos hd (neg_nonpos.mpr hb)).trans
            (le_max_left _ _)
        · have hu : |σ - x i| ≤ |y - x i| + δ := by
            have ht := abs_sub_le σ y (x i)
            have hyσ : |σ - y| < δ := by
              rw [abs_sub_lt_iff]; constructor <;> linarith [hσ.1, hσ.2]
            linarith
          exact (Real.rpow_le_rpow (abs_nonneg _) hu (by linarith)).trans
            (le_max_right _ _)
    have hgint : IntegrableOn g (Ioo (y - δ) (y + δ)) := by
      by_cases hj : ∃ j, x j = y
      · obtain ⟨j, hj⟩ := hj
        have hgeq : g = fun σ => (∏ i ∈ Finset.univ.erase j, C i) *
            |σ - y| ^ (-b j) := by
          funext σ
          simp only [hg]
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm]
          simp only [hj, ↓reduceIte]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          have : x i ≠ y := fun h => (Finset.mem_erase.mp hi).1 (hx (h.trans hj.symm))
          simp only [this, ↓reduceIte]
        rw [hgeq]
        refine Integrable.const_mul ?_ _
        have := intervalIntegrable_abs_sub_rpow (r := -b j) (by linarith [hb1 j]) y
          (y - δ) (y + δ)
        rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)] at this
        exact this
      · simp only [not_exists] at hj
        have hgeq : g = fun _ => ∏ i, C i := by
          funext σ
          exact Finset.prod_congr rfl fun i _ => by simp only [hj i, ↓reduceIte]
        rw [hgeq]
        exact integrableOn_const (by simp) (by simp)
    refine hgint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 σ)]
    exact hbound σ hσ
  -- decay at infinity
  set B := ∑ i, b i
  set M : ℝ := ∑ i, |x i| + 1 with hM
  have hM1 : ∀ i, |x i| + 1 ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg (x i))
      (Finset.mem_univ i)
    linarith
  have hMpos : 0 < M := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (x i)); linarith
  let C : ℝ := ∏ i, (2 : ℝ) ^ |b i|
  have hfar : ∀ σ, 2 * M ≤ |σ| → f σ ≤ C * |σ| ^ (-B) := by
    intro σ hσ
    have hσpos : 0 < |σ| := by linarith
    have hfac : ∀ i, |σ - x i| ^ (-b i) ≤ 2 ^ |b i| * |σ| ^ (-b i) := by
      intro i
      by_cases hb : 0 ≤ b i
      · have h1 : |σ| / 2 ≤ |σ - x i| := by
          have := abs_sub_abs_le_abs_sub σ (x i)
          linarith [hM1 i]
        calc
          _ ≤ (|σ| / 2) ^ (-b i) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 (neg_nonpos.mpr hb)
          _ = _ := by
            rw [abs_of_nonneg hb, Real.div_rpow hσpos.le (by norm_num),
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
      · have h1 : |σ - x i| ≤ 2 * |σ| := by
          have := abs_sub σ (x i)
          linarith [hM1 i]
        calc
          _ ≤ (2 * |σ|) ^ (-b i) :=
            Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
          _ = _ := by rw [Real.mul_rpow (by norm_num) hσpos.le, abs_of_neg (lt_of_not_ge hb)]
    calc
      f σ ≤ ∏ i, (2 ^ |b i| * |σ| ^ (-b i)) :=
        Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) fun i _ => hfac i
      _ = C * |σ| ^ (-B) := by
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hσpos, Finset.sum_neg_distrib]
  have hRight : IntegrableOn f (Ioi (2 * M)) := by
    have hI : IntegrableOn (fun σ : ℝ => C * σ ^ (-B)) (Ioi (2 * M)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul _
    refine hI.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    have hσ' : 2 * M < σ := hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 σ)]
    have := hfar σ (by rw [abs_of_pos (by linarith)]; exact hσ'.le)
    rwa [abs_of_pos (by linarith)] at this
  have hLeft : IntegrableOn f (Iio (-(2 * M))) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [neg_preimage, neg_Iio, neg_neg]
    have hI : IntegrableOn (fun σ : ℝ => C * σ ^ (-B)) (Ioi (2 * M)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul _
    refine hI.mono' (hmeas.comp measurable_neg).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    have hσ' : 2 * M < σ := hσ
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
    have := hfar (-σ) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hσ'.le)
    rwa [abs_neg, abs_of_pos (by linarith)] at this
  have hMid : IntegrableOn f (Icc (-(2 * M)) (2 * M)) :=
    hloc.integrableOn_isCompact isCompact_Icc
  have hcover : (univ : Set ℝ) ⊆ Iio (-(2 * M)) ∪ Icc (-(2 * M)) (2 * M) ∪ Ioi (2 * M) := by
    intro σ _
    by_cases h1 : σ < -(2 * M)
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : 2 * M < σ
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨not_lt.mp h1, not_lt.mp h2⟩)
  rw [← integrableOn_univ]
  exact ((hLeft.union hMid).union hRight).mono_set hcover

/-- A finite product of real powers at distinct nodes is integrable if every local exponent
exceeds `-1` and the sum of the exponents is less than `-1`. Positive exponents are allowed. -/
theorem integrable_prod_abs_sub_rpow {ι : Type*} [Fintype ι] {x r : ι → ℝ}
    (hx : Function.Injective x) (hr : ∀ i, -1 < r i) (hsum : ∑ i, r i < -1) :
    Integrable (fun t : ℝ => ∏ i, |t - x i| ^ r i) := by
  simpa only [neg_neg] using integrable_prod_abs_sub_rpow_neg (b := fun i => -r i) hx
    (fun i => by linarith [hr i]) (by simp only [Finset.sum_neg_distrib]; linarith)
