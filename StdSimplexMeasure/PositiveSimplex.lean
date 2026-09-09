/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import StdSimplexMeasure.ProdSlices

/-!
# Lebesgue volume of a finite-dimensional positive simplex

This file evaluates the Lebesgue volume of the set of nonnegative coordinate vectors whose
coordinate sum is bounded by a nonnegative real number. The proof first treats coordinates
indexed by `Fin n`, by induction and slicing, and then transports the result to any finite
type.

The code here must be revisited if and when Mathlib PR #37910 is accepted.
-/

open MeasureTheory
open scoped Classical

@[expose] public noncomputable section

/-- The positive simplex of radius `r` in coordinates indexed by `Fin n`: nonnegative vectors
whose coordinate sum is at most `r`. -/
def posSimplexFin (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

/-- The finite-coordinate positive simplex is measurable. -/
lemma measurableSet_posSimplexFin (n : ℕ) (r : ℝ) :
    MeasurableSet (posSimplexFin n r) := by
  have hsum : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ r})
  have h := (MeasurableSet.iInter fun i => measurableSet_le
    (measurable_const : Measurable fun _ : Fin n → ℝ => (0 : ℝ))
    (measurable_pi_apply i)).inter
      (measurableSet_le hsum (measurable_const : Measurable fun _ : Fin n → ℝ => r))
  convert h using 1; ext x; simp

/-- The volume formula for the zero-dimensional positive simplex. -/
lemma volume_posSimplexFin_zero (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplexFin 0 r) = ENNReal.ofReal r ^ 0 / Nat.factorial 0 := by
  rw [Measure.volume_pi_eq_dirac]
  simp [posSimplexFin, hr]

/-- The product-coordinate presentation of `posSimplexFin (n + 1) r`, obtained by separating
the zeroth coordinate. -/
private def posSimplexFinSuccSlices (n : ℕ) (r : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + ∑ i, p.2 i ≤ r}

/-- The product-coordinate presentation of a positive simplex is measurable. -/
private lemma measurableSet_posSimplexFinSuccSlices (n : ℕ) (r : ℝ) :
    MeasurableSet (posSimplexFinSuccSlices n r) := by
  have hsum : Measurable (fun p : ℝ × (Fin n → ℝ) => ∑ i, p.2 i) := by fun_prop
  change MeasurableSet ({p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} ∩
    ({p | ∀ i, 0 ≤ p.2 i} ∩ {p | p.1 + ∑ i, p.2 i ≤ r}))
  have h := (measurableSet_le
    (measurable_const : Measurable fun _ : ℝ × (Fin n → ℝ) => (0 : ℝ))
    measurable_fst).inter
    ((MeasurableSet.iInter fun i => measurableSet_le
      (measurable_const : Measurable fun _ : ℝ × (Fin n → ℝ) => (0 : ℝ))
      ((measurable_pi_apply i).comp (measurable_snd : Measurable Prod.snd))).inter
      (measurableSet_le (measurable_fst.add hsum)
        (measurable_const : Measurable fun _ : ℝ × (Fin n → ℝ) => r)))
  convert h using 1
  ext p
  simp

/-- Separating the zeroth coordinate maps a positive `(n + 1)`-simplex to its
product-coordinate presentation. -/
private lemma image_posSimplexFin_piFinSuccAbove (n : ℕ) (r : ℝ) :
    let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    e '' posSimplexFin (n + 1) r = posSimplexFinSuccSlices n r := by
  dsimp only
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hxsum⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [e, posSimplexFinSuccSlices] using hx0 0
    · intro i
      change 0 ≤ x (Fin.succ i)
      exact hx0 (Fin.succ i)
    · change x 0 + ∑ i, x (Fin.succ i) ≤ r
      simpa [Fin.sum_univ_succ] using hxsum
  · intro hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    rcases hp with ⟨ht0, hp0, hsum⟩
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [e] using ht0
      · change 0 ≤ p.2 j
        exact hp0 j
    · have hp := e.apply_symm_apply p
      have hp1 : (e.symm p) 0 = p.1 := congrArg Prod.fst hp
      have hp2 : (fun i => (e.symm p) (Fin.succ i)) = p.2 := congrArg Prod.snd hp
      rw [Fin.sum_univ_succ, hp1, hp2]
      exact hsum

/-- A slice of the product-coordinate presentation at `t ∈ [0, r]` is the positive simplex
of radius `r - t`. -/
private lemma preimage_posSimplexFinSuccSlices_of_mem (n : ℕ) (r t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) r) :
    Prod.mk t ⁻¹' posSimplexFinSuccSlices n r = posSimplexFin n (r - t) := by
  ext x
  simp only [posSimplexFinSuccSlices, posSimplexFin, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, hx0, hs⟩
    exact ⟨hx0, by linarith⟩
  · rintro ⟨hx0, hs⟩
    exact ⟨ht.1, hx0, by linarith⟩

/-- Outside `[0, r]`, the slices in the product-coordinate presentation are empty. -/
private lemma preimage_posSimplexFinSuccSlices_eq_empty_of_not_mem
    (n : ℕ) (r t : ℝ) (ht : t ∉ Set.Icc (0 : ℝ) r) :
    Prod.mk t ⁻¹' posSimplexFinSuccSlices n r = ∅ := by
  ext x
  simp only [posSimplexFinSuccSlices, Set.mem_preimage, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨ht0, hx0, hs⟩
  apply ht
  refine ⟨ht0, ?_⟩
  have hs0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx0 i
  linarith

/-- The one-dimensional integral used in the positive-simplex volume induction. -/
lemma lintegral_Icc_sub_pow_div_factorial (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ t in Set.Icc (0 : ℝ) r,
        ENNReal.ofReal (r - t) ^ n / Nat.factorial n =
      ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
  have hint : ∫ t in Set.Icc (0 : ℝ) r, (r - t) ^ n = r ^ (n + 1) / (n + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
    change (∫ t in (0 : ℝ)..r, (fun x : ℝ => x ^ n) (r - t)) = _
    calc
      _ = ∫ x in r - r..r - 0, x ^ n :=
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) r
      _ = _ := by simp [integral_pow]
  let q : ℝ := Nat.factorial n
  have hq : 0 < q := by positivity
  have hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) r, 0 ≤ (r - t) ^ n / q := by
    intro t ht
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) hq.le
  have hintg : IntegrableOn (fun t : ℝ => (r - t) ^ n / q) (Set.Icc 0 r) :=
    Continuous.integrableOn_Icc (by fun_prop)
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) r,
        ENNReal.ofReal (r - t) ^ n / Nat.factorial n) =
        ∫⁻ t in Set.Icc (0 : ℝ) r, ENNReal.ofReal ((r - t) ^ n / q) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      change ENNReal.ofReal (r - t) ^ n / Nat.factorial n =
        ENNReal.ofReal ((r - t) ^ n / q)
      symm
      rw [ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_pow (sub_nonneg.mpr ht.2)]
      simp [q]
    _ = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) r, (r - t) ^ n / q) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintg]
      filter_upwards [self_mem_ae_restrict (μ := volume) measurableSet_Icc] with t ht
      exact hnonneg t ht
    _ = ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
      rw [integral_div, hint]
      unfold q
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < Nat.factorial n)]
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < n + 1),
        ENNReal.ofReal_pow hr]
      have hn1 : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hfac : (0 : ℝ) < Nat.factorial n := by positivity
      calc
        ENNReal.ofReal r ^ (n + 1) / ENNReal.ofReal (n + 1) /
            ENNReal.ofReal (Nat.factorial n : ℝ) =
            ENNReal.ofReal (r ^ (n + 1) / (n + 1) / Nat.factorial n) := by
          rw [ENNReal.ofReal_div_of_pos hfac, ENNReal.ofReal_div_of_pos hn1,
            ENNReal.ofReal_pow hr]
        _ = ENNReal.ofReal (r ^ (n + 1) / Nat.factorial (n + 1)) := by
          congr 1
          rw [Nat.factorial_succ]
          push_cast
          field_simp
        _ = ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hr]
          simp

/-- The induction step for the volume of a positive simplex, obtained by slicing off its first
coordinate. -/
lemma volume_posSimplexFin_succ (n : ℕ)
    (ih : ∀ r : ℝ, 0 ≤ r → volume (posSimplexFin n r) =
      ENNReal.ofReal r ^ n / Nat.factorial n)
    (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplexFin (n + 1) r) =
      ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let T := posSimplexFinSuccSlices n r
  have hT : MeasurableSet T := measurableSet_posSimplexFinSuccSlices n r
  have he : e '' posSimplexFin (n + 1) r = T :=
    image_posSimplexFin_piFinSuccAbove n r
  have hmp := volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) 0
  have hv := hmp.measure_preimage hT.nullMeasurableSet
  calc
    volume (posSimplexFin (n + 1) r) = volume (e ⁻¹' T) := by
      congr 1
      exact (Set.preimage_eq_iff_eq_image e.bijective |>.2 he.symm).symm
    _ = volume T := hv
    _ = ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
      change (volume.prod volume) T = _
      rw [Measure.prod_apply hT]
      calc
        (∫⁻ t, volume (Prod.mk t ⁻¹' T)) =
            ∫⁻ t in Set.Icc (0 : ℝ) r,
              ENNReal.ofReal (r - t) ^ n / Nat.factorial n := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          simp only [Set.indicator_apply]
          split_ifs with ht
          · rw [preimage_posSimplexFinSuccSlices_of_mem n r t ht,
              ih (r - t) (sub_nonneg.mpr ht.2)]
          · have hempty : Prod.mk t ⁻¹' T = ∅ :=
              preimage_posSimplexFinSuccSlices_eq_empty_of_not_mem n r t ht
            rw [hempty, measure_empty]
        _ = ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) :=
          lintegral_Icc_sub_pow_div_factorial n r hr

/-- The `n`-dimensional volume of the positive simplex of radius `r` is `r ^ n / n!`. -/
theorem volume_posSimplexFin (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplexFin n r) = ENNReal.ofReal r ^ n / Nat.factorial n := by
  revert r
  induction n with
  | zero => intro r hr; exact volume_posSimplexFin_zero r hr
  | succ n ih =>
      intro r hr
      exact volume_posSimplexFin_succ n ih r hr

/-- The positive simplex of radius `r` indexed by an arbitrary finite type: nonnegative vectors
whose coordinate sum is at most `r`. -/
def posSimplex (α : Type*) [Fintype α] (r : ℝ) : Set (α → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

/-- The product-coordinate presentation of a positive simplex obtained by separating the
coordinate `i`. -/
def posSimplexSlices {α : Type*} [Fintype α] (i : α) (r : ℝ) :
    Set (ℝ × ({j : α // j ≠ i} → ℝ)) := by
  classical
  exact {p | 0 ≤ p.1 ∧ (∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ r}

/-- A positive simplex of negative radius is empty. -/
theorem posSimplex_eq_empty_of_neg {α : Type*} [Fintype α] {r : ℝ} (hr : r < 0) :
    posSimplex α r = ∅ := by
  ext x
  constructor
  · intro ⟨hx0, hs⟩
    have : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx0 i
    linarith
  · intro h
    exact h.elim

/-- A positive simplex is measurable. -/
theorem measurableSet_posSimplex (α : Type*) [Fintype α] (r : ℝ) :
    MeasurableSet (posSimplex α r) := by
  have hsum : Measurable (fun x : α → ℝ => ∑ i, x i) := by fun_prop
  change MeasurableSet ({x : α → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ r})
  have h := (MeasurableSet.iInter fun i => measurableSet_le
    (measurable_const : Measurable fun _ : α → ℝ => (0 : ℝ))
    (measurable_pi_apply i)).inter
      (measurableSet_le hsum (measurable_const : Measurable fun _ : α → ℝ => r))
  convert h using 1
  ext x
  simp

/-- Separating one coordinate identifies a positive simplex with its product-coordinate
presentation. -/
theorem image_posSimplex_funSplitAt {α : Type*} [Fintype α] (i : α) (r : ℝ) :
    Homeomorph.funSplitAt ℝ i '' posSimplex α r = posSimplexSlices i r := by
  classical
  ext p
  constructor
  · rintro ⟨x, ⟨hx0, hxsum⟩, rfl⟩
    refine ⟨hx0 i, fun j => hx0 j, ?_⟩
    rw [Fintype.sum_eq_add_sum_subtype_ne x i] at hxsum
    exact hxsum
  · intro hp
    let e := Homeomorph.funSplitAt ℝ i
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    rcases hp with ⟨hpi, hp0, hpsum⟩
    have he := e.apply_symm_apply p
    have he1 : e.symm p i = p.1 := congrArg Prod.fst he
    have he2 : (fun j : {j : α // j ≠ i} => e.symm p j) = p.2 :=
      congrArg Prod.snd he
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        rw [he1]
        exact hpi
      · rw [congrFun he2 ⟨j, hji⟩]
        exact hp0 ⟨j, hji⟩
    · rw [Fintype.sum_eq_add_sum_subtype_ne]
      rw [he1, he2]
      exact hpsum

/-- The product-coordinate presentation of a positive simplex is measurable. -/
theorem measurableSet_posSimplexSlices {α : Type*} [Fintype α] (i : α) (r : ℝ) :
    MeasurableSet (posSimplexSlices i r) := by
  rw [← image_posSimplex_funSplitAt i r]
  exact (Homeomorph.funSplitAt ℝ i).measurableEmbedding.measurableSet_image'
    (measurableSet_posSimplex α r)

/-- A slice of `posSimplexSlices i r` at a point of `[0, r]` is the positive simplex of
radius `r - t` in the remaining coordinates. -/
theorem preimage_posSimplexSlices_of_mem {α : Type*} [Fintype α]
    (i : α) (r t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
    Prod.mk t ⁻¹' posSimplexSlices i r = posSimplex {j : α // j ≠ i} (r - t) := by
  classical
  ext x
  simp only [posSimplexSlices, posSimplex, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, hx0, hs⟩
    exact ⟨hx0, by linarith⟩
  · rintro ⟨hx0, hs⟩
    exact ⟨ht.1, hx0, by linarith⟩

/-- Outside `[0, r]`, every slice of `posSimplexSlices i r` is empty. -/
theorem preimage_posSimplexSlices_eq_empty_of_not_mem {α : Type*} [Fintype α]
    (i : α) (r t : ℝ) (ht : t ∉ Set.Icc (0 : ℝ) r) :
    Prod.mk t ⁻¹' posSimplexSlices i r = ∅ := by
  classical
  ext x
  simp only [posSimplexSlices, Set.mem_preimage, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨ht0, hx0, hs⟩
  apply ht
  refine ⟨ht0, ?_⟩
  have hs0 : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ => hx0 j
  linarith

/-- The volume of the positive simplex indexed by `α` is
`r ^ Fintype.card α / (Fintype.card α)!`. -/
theorem volume_posSimplex (α : Type*) [Fintype α] (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplex α r) =
      ENNReal.ofReal r ^ Fintype.card α / Nat.factorial (Fintype.card α) := by
  let σ : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let e : (Fin (Fintype.card α) → ℝ) ≃ᵐ (α → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) σ
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : α => ℝ) σ
  have he : e '' posSimplexFin (Fintype.card α) r = posSimplex α r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro i
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using
          hy0 (σ.symm i)
      · simp only [e, MeasurableEquiv.coe_piCongrLeft]
        calc
          ∑ j, (Equiv.piCongrLeft (fun _ : α => ℝ) σ) y j =
              ∑ i, (Equiv.piCongrLeft (fun _ : α => ℝ) σ) y (σ i) :=
            (σ.sum_comp _).symm
          _ = ∑ i, y i := by
            apply Finset.sum_congr rfl
            intro i _
            exact Equiv.piCongrLeft_apply_apply (P := fun _ : α => ℝ) σ y i
          _ ≤ r := hys
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rcases hx with ⟨hx0, hxs⟩
      refine ⟨?_, ?_⟩
      · intro i
        have hp := congrFun (e.apply_symm_apply x) (σ i)
        have hp' : e.symm x i = x (σ i) := by
          calc
            e.symm x i = e (e.symm x) (σ i) := by
              simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
            _ = x (σ i) := hp
        rw [hp']
        exact hx0 (σ i)
      · have hp := e.apply_symm_apply x
        calc
          ∑ i, e.symm x i = ∑ j, e (e.symm x) j := by
            rw [← σ.sum_comp]
            simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          _ = ∑ j, x j := by rw [hp]
          _ ≤ r := hxs
  calc
    volume (posSimplex α r) = volume (e '' posSimplexFin (Fintype.card α) r) := by rw [he]
    _ = volume (posSimplexFin (Fintype.card α) r) := by
      rw [← hmp.map_eq, Measure.map_apply e.measurable
        (e.measurableSet_image.2 (measurableSet_posSimplexFin _ _))]
      rw [e.preimage_image]
    _ = _ := volume_posSimplexFin _ _ hr

/-- Real-valued form of the positive-simplex volume formula. -/
theorem volume_posSimplex_toReal (α : Type*) [Fintype α] (r : ℝ) (hr : 0 ≤ r) :
    (volume (posSimplex α r)).toReal =
      r ^ Fintype.card α / Nat.factorial (Fintype.card α) := by
  rw [volume_posSimplex α r hr]
  simp [ENNReal.toReal_div, ENNReal.toReal_ofReal hr]

/-- Tonelli's theorem on the triangle `0 ≤ t ≤ s ≤ r`. -/
lemma lintegral_Icc_triangle_swap (r : ℝ) (_hr : 0 ≤ r)
    (F : ℝ → ℝ → ENNReal) (hF : Measurable (Function.uncurry F)) :
    ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r, F t s =
      ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ t in Set.Icc (0 : ℝ) s, F t s := by
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) r ∧ p.2 ∈ Set.Icc p.1 r}
  have hS : MeasurableSet S :=
    measurableSet_prod_Icc_slice (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) r))
      measurable_id measurable_const
  have hG : Measurable (S.indicator fun p => F p.1 p.2) := hF.indicator hS
  have hcond (t s : ℝ) :
      t ∈ Set.Icc (0 : ℝ) r ∧ s ∈ Set.Icc t r ↔
        s ∈ Set.Icc (0 : ℝ) r ∧ t ∈ Set.Icc (0 : ℝ) s := by
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨⟨ht0, _htr⟩, ⟨hts, hsr⟩⟩
      exact ⟨⟨le_trans ht0 hts, hsr⟩, ⟨ht0, hts⟩⟩
    · intro ⟨⟨_hs0, hsr⟩, ⟨ht0, hts⟩⟩
      exact ⟨⟨ht0, le_trans hts hsr⟩, ⟨hts, hsr⟩⟩
  have hleft :
      ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r, F t s =
        ∫⁻ t, ∫⁻ s, S.indicator (fun p => F p.1 p.2) (t, s) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) r
    · rw [Set.indicator_of_mem ht, ← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Set.Icc t r
      · simp [Set.indicator_of_mem hs, Set.indicator_of_mem (show (t, s) ∈ S from ⟨ht, hs⟩)]
      · simp [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show (t, s) ∉ S from fun h => hs h.2)]
    · rw [Set.indicator_of_notMem ht]
      refine Eq.symm (lintegral_eq_zero_of_ae_eq_zero ?_)
      exact Filter.Eventually.of_forall fun s =>
        Set.indicator_of_notMem (fun h : (t, s) ∈ S => ht h.1)
          (fun p => F p.1 p.2)
  have hright :
      ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ t in Set.Icc (0 : ℝ) s, F t s =
        ∫⁻ s, ∫⁻ t, S.indicator (fun p => F p.1 p.2) (t, s) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) r
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) s
      · have hmem : (t, s) ∈ S := (hcond t s).2 ⟨hs, ht⟩
        simp [Set.indicator_of_mem ht, Set.indicator_of_mem hmem]
      · have hnmem : (t, s) ∉ S := fun h => ht ((hcond t s).1 h).2
        simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem hnmem]
    · rw [Set.indicator_of_notMem hs]
      refine Eq.symm (lintegral_eq_zero_of_ae_eq_zero ?_)
      exact Filter.Eventually.of_forall fun t =>
        Set.indicator_of_notMem (fun h : (t, s) ∈ S => hs ((hcond t s).1 h).1)
          (fun p => F p.1 p.2)
  rw [hleft, hright]
  exact lintegral_lintegral_swap hG.aemeasurable

/-- Pushing the positive `Fin n`-simplex forward under the coordinate-sum map. -/
theorem lintegral_posSimplexFin_comp_sum (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplexFin n r, g (∑ i, x i) =
      ∫⁻ s in Set.Icc (0 : ℝ) r,
        g s * (ENNReal.ofReal s ^ (n - 1) / Nat.factorial (n - 1)) := by
  induction n generalizing r g with
  | zero =>
      exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let T := posSimplexFinSuccSlices n r
      have hT : MeasurableSet T := measurableSet_posSimplexFinSuccSlices n r
      have he : e '' posSimplexFin (n + 1) r = T :=
        image_posSimplexFin_piFinSuccAbove n r
      have hpre : e ⁻¹' T = posSimplexFin (n + 1) r := by
        exact (Set.preimage_eq_iff_eq_image e.bijective).2 he.symm
      have hmp := volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0
      have hgT : Measurable fun p : ℝ × (Fin n → ℝ) => g (p.1 + ∑ i, p.2 i) := by
        fun_prop
      have hsum_e (p : ℝ × (Fin n → ℝ)) :
          ∑ i, e.symm p i = p.1 + ∑ i, p.2 i := by
        have hp := e.apply_symm_apply p
        have hp1 : e.symm p 0 = p.1 := congrArg Prod.fst hp
        have hp2 : (fun i => e.symm p (Fin.succ i)) = p.2 := congrArg Prod.snd hp
        rw [Fin.sum_univ_succ, hp1, hp2]
      calc
        ∫⁻ x in posSimplexFin (n + 1) r, g (∑ i, x i) =
            ∫⁻ x in e ⁻¹' T, g (∑ i, x i) := by rw [hpre]
        _ = ∫⁻ p in T, g (∑ i, e.symm p i) := by
          refine Eq.trans ?_
            (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
              (fun p => g (∑ i, e.symm p i)) T)
          apply setLIntegral_congr_fun (hpre ▸ measurableSet_posSimplexFin (n + 1) r)
          intro x _
          congr 1
          exact (e.symm_apply_apply x).symm
        _ = ∫⁻ p in T, g (p.1 + ∑ i, p.2 i) := by
          apply setLIntegral_congr_fun hT
          intro p _
          exact congrArg g (hsum_e p)
        _ = ∫⁻ t, ∫⁻ y in Prod.mk t ⁻¹' T, g (t + ∑ i, y i) := by
          rw [Measure.volume_eq_prod]
          exact setLIntegral_prod_slices T hT _ hgT
        _ = ∫⁻ t in Set.Icc (0 : ℝ) r,
              ∫⁻ y in posSimplexFin n (r - t), g (t + ∑ i, y i) := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ Set.Icc (0 : ℝ) r
          · rw [Set.indicator_of_mem ht, preimage_posSimplexFinSuccSlices_of_mem n r t ht]
          · rw [Set.indicator_of_notMem ht,
              preimage_posSimplexFinSuccSlices_eq_empty_of_not_mem n r t ht, setLIntegral_empty]
        _ = ∫⁻ s in Set.Icc (0 : ℝ) r,
              g s * (ENNReal.ofReal s ^ n / Nat.factorial n) := by
          cases n with
          | zero =>
              have hinner (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ y in posSimplexFin 0 (r - t), g (t + ∑ i, y i) = g t := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                have huniv : posSimplexFin 0 (r - t) = Set.univ := by
                  ext y
                  simp [posSimplexFin, hr't]
                rw [huniv, Measure.restrict_univ, Measure.volume_pi_eq_dirac, lintegral_dirac]
                simp
              apply setLIntegral_congr_fun measurableSet_Icc
              intro t ht
              change ∫⁻ y in posSimplexFin 0 (r - t), g (t + ∑ i, y i) =
                g t * (ENNReal.ofReal t ^ 0 / Nat.factorial 0)
              rw [hinner t ht]
              simp
          | succ m =>
              have hn' : 0 < m + 1 := Nat.succ_pos _
              have hinner (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ y in posSimplexFin (m + 1) (r - t), g (t + ∑ i, y i) =
                    ∫⁻ σ in Set.Icc (0 : ℝ) (r - t),
                      g (t + σ) *
                        (ENNReal.ofReal σ ^ m / Nat.factorial m) := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                simpa using ih hn' (r - t) hr't (fun σ => g (t + σ)) (by fun_prop)
              have hshift (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ σ in Set.Icc (0 : ℝ) (r - t),
                      g (t + σ) *
                        (ENNReal.ofReal σ ^ m / Nat.factorial m) =
                    ∫⁻ s in Set.Icc t r,
                      g s *
                        (ENNReal.ofReal (s - t) ^ m / Nat.factorial m) := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                have hmp' := measurePreserving_add_left (volume : Measure ℝ) t
                have hpre : (fun σ : ℝ => t + σ) ⁻¹' Set.Icc t r =
                    Set.Icc (0 : ℝ) (r - t) := by
                  ext σ
                  constructor
                  · intro h
                    simp only [Set.mem_preimage, Set.mem_Icc] at h ⊢
                    exact ⟨by linarith, by linarith⟩
                  · intro h
                    simp only [Set.mem_preimage, Set.mem_Icc] at h ⊢
                    exact ⟨by linarith, by linarith⟩
                have := hmp'.setLIntegral_comp_preimage (s := Set.Icc t r)
                  measurableSet_Icc (f := fun s =>
                    g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)) (by fun_prop)
                simpa [hpre] using this
              trans ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r,
                  g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)
              · apply setLIntegral_congr_fun measurableSet_Icc
                intro t ht
                exact (hinner t ht).trans (hshift t ht)
              · have hF : Measurable (Function.uncurry fun t s : ℝ =>
                    g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)) := by
                  fun_prop
                rw [lintegral_Icc_triangle_swap r hr _ hF]
                apply setLIntegral_congr_fun measurableSet_Icc
                intro s hs
                have hs0 : 0 ≤ s := hs.1
                have hinter := lintegral_Icc_sub_pow_div_factorial m s hs0
                calc
                  ∫⁻ t in Set.Icc (0 : ℝ) s,
                      g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m) =
                      g s * ∫⁻ t in Set.Icc (0 : ℝ) s,
                        ENNReal.ofReal (s - t) ^ m / Nat.factorial m := by
                    rw [lintegral_const_mul]
                    fun_prop
                  _ = g s * (ENNReal.ofReal s ^ (m + 1) / Nat.factorial (m + 1)) := by
                    rw [hinter]

/-- Pushing an arbitrary finite-dimensional positive simplex forward under the coordinate-sum
map. Requires a nonempty index type so that the exponent `card α - 1` is well-defined. -/
theorem lintegral_posSimplex_comp_sum {α : Type*} [Fintype α] [Nonempty α]
    (r : ℝ) (hr : 0 ≤ r) (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (∑ i, x i) =
      ∫⁻ s in Set.Icc (0 : ℝ) r,
        g s * (ENNReal.ofReal s ^ (Fintype.card α - 1) /
          Nat.factorial (Fintype.card α - 1)) := by
  let σ : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let e : (Fin (Fintype.card α) → ℝ) ≃ᵐ (α → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) σ
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : α => ℝ) σ
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hsum (y : Fin (Fintype.card α) → ℝ) :
      ∑ j, e y j = ∑ i, y i := by
    calc
      ∑ j, e y j = ∑ i, e y (σ i) := (σ.sum_comp _).symm
      _ = ∑ i, y i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Equiv.piCongrLeft_apply_apply (P := fun _ : α => ℝ) σ y i
  have himage : e ⁻¹' posSimplex α r = posSimplexFin (Fintype.card α) r := by
    ext y
    constructor
    · intro hy
      have hy' : e y ∈ posSimplex α r := hy
      rcases hy' with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro i
        have := hy0 (σ i)
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using this
      · simpa [hsum] using hys
    · intro hy
      rcases hy with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro j
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using hy0 (σ.symm j)
      · simpa [hsum] using hys
  calc
    ∫⁻ x in posSimplex α r, g (∑ i, x i) =
        ∫⁻ y in e ⁻¹' posSimplex α r, g (∑ j, e y j) :=
      (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding _ _).symm
    _ = ∫⁻ y in posSimplexFin (Fintype.card α) r, g (∑ i, y i) := by
      rw [himage]
      apply setLIntegral_congr_fun (measurableSet_posSimplexFin _ _)
      intro y _
      exact congrArg g (hsum y)
    _ = _ := lintegral_posSimplexFin_comp_sum (Fintype.card α) hn r hr g hg
