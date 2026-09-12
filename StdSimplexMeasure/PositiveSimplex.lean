/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import StdSimplexMeasure.ProdSlices

/-!
# Lebesgue volume of a finite-dimensional positive simplex

This file evaluates the Lebesgue volume of the set of nonnegative coordinate vectors whose
coordinate sum is bounded by a nonnegative real number. The proof first treats coordinates
indexed by `Fin n`, by induction and slicing, and then transports the result to any finite
type.

The last section records the push-forward of this measure under coordinate aggregation
(`lintegral_posSimplex_comp_aggregate`). That identity is the solid-simplex form of the
aggregation theorem for `stdSimplexMeasure`.

The volume development here must be revisited if and when Mathlib PR #37910 is accepted.
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
    measurableSet_region_between_cc measurable_id measurable_const
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) r))
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
          exact setLIntegral_prod_slices T hT _ hgT.aemeasurable
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

/-! ## Aggregation of a solid simplex -/

/-- Tonelli disintegration of a positive simplex after splitting along a decidable predicate. -/
theorem lintegral_posSimplex_split_pred {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (r : ℝ)
    (G : ({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ x in posSimplex α r, G (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p x) =
      ∫⁻ u in posSimplex {a : α // p a} r,
        ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p
  let T : Set (({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ)) :=
    {q | (∀ i, 0 ≤ q.1 i) ∧ (∀ i, 0 ≤ q.2 i) ∧ ∑ i, q.1 i + ∑ i, q.2 i ≤ r}
  have himage : e '' posSimplex α r = T := by
    ext q
    constructor
    · rintro ⟨x, ⟨hx0, hxs⟩, rfl⟩
      refine ⟨fun i ↦ hx0 i.1, fun i ↦ hx0 i.1, ?_⟩
      have hsum := Fintype.sum_subtype_add_sum_subtype p x
      simpa [e] using (hsum ▸ hxs)
    · intro hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      rcases hq with ⟨hu0, hv0, hsum⟩
      refine ⟨?_, ?_⟩
      · intro a
        by_cases ha : p a
        · simpa [e, ha] using hu0 ⟨a, ha⟩
        · simpa [e, ha] using hv0 ⟨a, ha⟩
      · have h1 : (fun i : {a : α // p a} ↦ e.symm q i) = q.1 := by
          funext i
          change (if h : p i.1 then q.1 ⟨i.1, h⟩ else q.2 ⟨i.1, h⟩) = q.1 i
          simp [i.property]
        have h2 : (fun i : {a : α // ¬p a} ↦ e.symm q i) = q.2 := by
          funext i
          change (if h : p i.1 then q.1 ⟨i.1, h⟩ else q.2 ⟨i.1, h⟩) = q.2 i
          simp [i.property]
        calc
          ∑ a, e.symm q a
              = (∑ i : {a : α // p a}, e.symm q i) +
                  ∑ i : {a : α // ¬p a}, e.symm q i :=
                (Fintype.sum_subtype_add_sum_subtype p (e.symm q)).symm
          _ = ∑ i, q.1 i + ∑ i, q.2 i := by rw [h1, h2]
          _ ≤ r := hsum
  have hT : MeasurableSet T := by
    rw [← himage]
    exact e.measurableEmbedding.measurableSet_image.2 (measurableSet_posSimplex α r)
  have hsection (u : {a : α // p a} → ℝ) :
      Prod.mk u ⁻¹' T =
        if u ∈ posSimplex {a : α // p a} r then
          posSimplex {a : α // ¬p a} (r - ∑ i, u i)
        else (∅ : Set ({a : α // ¬p a} → ℝ)) := by
    ext v
    by_cases hu : u ∈ posSimplex {a : α // p a} r
    · simp only [hu, ↓reduceIte]
      simp only [T, posSimplex, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hu0, hv0, hs⟩
        exact ⟨hv0, by linarith⟩
      · rintro ⟨hv0, hvs⟩
        exact ⟨hu.1, hv0, by linarith⟩
    · simp only [hu, ↓reduceIte, Set.mem_empty_iff_false, iff_false]
      intro hv
      simp only [T, Set.mem_preimage, Set.mem_ofPred_eq] at hv
      rcases hv with ⟨hu0, hv0, hs⟩
      exact hu ⟨hu0, by
        have : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ ↦ hv0 i
        linarith⟩
  calc
    ∫⁻ x in posSimplex α r, G (e x) =
        ∫⁻ q in T, G q ∂volume.prod volume := by
      rw [← himage]
      exact (hmp.restrict_image_emb e.measurableEmbedding
        (posSimplex α r)).lintegral_comp_emb e.measurableEmbedding G
    _ = ∫⁻ u, ∫⁻ v in Prod.mk u ⁻¹' T, G (u, v) :=
      setLIntegral_prod_slices T hT G hG.aemeasurable
    _ = ∫⁻ u in posSimplex {a : α // p a} r,
        ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
      rw [← lintegral_indicator (measurableSet_posSimplex _ r)]
      apply lintegral_congr
      intro u
      rw [hsection]
      by_cases hu : u ∈ posSimplex {a : α // p a} r
      · simp [hu]
      · simp [hu]

/-- A parameter-dependent nonnegative integral over a positive simplex whose radius decreases
with the parameter is measurable. -/
private theorem measurable_lintegral_posSimplex_sub
    {δ : Type*} [Fintype δ] (r : ℝ)
    (F : ℝ → (δ → ℝ) → ENNReal) (hF : Measurable (Function.uncurry F)) :
    Measurable fun s => ∫⁻ z in posSimplex δ (r - s), F s z := by
  let T : Set (ℝ × (δ → ℝ)) := {q | q.2 ∈ posSimplex δ (r - q.1)}
  have hT : MeasurableSet T := by
    have hsum : Measurable (fun q : ℝ × (δ → ℝ) => q.1 + ∑ i, q.2 i) := by fun_prop
    have hraw := (MeasurableSet.iInter fun i => measurableSet_le
      (measurable_const : Measurable fun _ : ℝ × (δ → ℝ) => (0 : ℝ))
      ((measurable_pi_apply i).comp measurable_snd)).inter
        (measurableSet_le hsum
          (measurable_const : Measurable fun _ : ℝ × (δ → ℝ) => r))
    have h : MeasurableSet ({q : ℝ × (δ → ℝ) | ∀ i, 0 ≤ q.2 i} ∩
        {q | q.1 + ∑ i, q.2 i ≤ r}) := by
      convert hraw using 1
      ext q
      simp
    convert h using 1
    ext q
    simp only [T, posSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor <;> rintro ⟨h0, hs⟩ <;> exact ⟨h0, by linarith⟩
  have hI : Measurable (T.indicator (Function.uncurry F)) := hF.indicator hT
  change Measurable (Function.uncurry
    (fun s z => T.indicator (Function.uncurry F) (s, z))) at hI
  have heq : (fun s => ∫⁻ z in posSimplex δ (r - s), F s z) =
      fun s => ∫⁻ z, T.indicator (Function.uncurry F) (s, z) := by
    funext s
    rw [← lintegral_indicator (measurableSet_posSimplex δ (r - s))]
    apply lintegral_congr
    intro z
    simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair]
  rw [heq]
  exact hI.lintegral_prod_right

/-- Fibrewise density for the push-forward of Lebesgue measure on a solid simplex under
coordinate aggregation. For a vector `z` this is the product of the solid-simplex volumes
of the fibres of `f`. -/
def posSimplexAggregateDensity {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (z : β → ℝ) : ENNReal :=
  ∏ k, ENNReal.ofReal (z k) ^ (Fintype.card {i : α // f i = k} - 1) /
    (Nat.factorial (Fintype.card {i : α // f i = k} - 1) : ENNReal)

/-- After splitting the source at one fibre, coordinate aggregation consists of summing that
fibre and aggregating the complementary coordinates. -/
private theorem linearMap_piEquivPiSubtypeProd_eq
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (k : β) :
    let p : α → Prop := fun a => f a = k
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ) p
    let β' := {j : β // j ≠ k}
    let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
    let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
      if h : j = k then s else z ⟨j, h⟩
    ∀ q, FunOnFinite.linearMap ℝ ℝ f (e.symm q) =
      assemble (∑ i, q.1 i) (FunOnFinite.linearMap ℝ ℝ f' q.2) := by
  classical
  dsimp only
  intro q
  let _ : Fintype {a : α // f a = k} := Fintype.ofFinite _
  let _ : Fintype {a : α // ¬f a = k} := Fintype.ofFinite _
  funext j
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hj : j = k
  · subst j
    rw [dif_pos rfl]
    rw [Finset.sum_subtype (p := fun a => f a = k)
      (Finset.univ.filter fun a => f a = k) (by simp)]
    apply Finset.sum_congr rfl
    intro a _
    simp [a.property]
  · simp only [dif_neg hj]
    rw [FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_subtype (p := fun a => f a = j)
      (Finset.univ.filter fun a => f a = j) (by simp)]
    change (∑ a : {a : α // f a = j},
      (if h : f a = k then q.1 ⟨a, h⟩ else q.2 ⟨a, h⟩)) = _
    simp only [Subtype.ext_iff] at ⊢
    rw [Finset.sum_subtype (p := fun a : {a : α // ¬f a = k} => f a = j)
      (Finset.univ.filter fun a : {a : α // ¬f a = k} => f a = j) (by simp)]
    apply Fintype.sum_equiv
      { toFun := fun a => ⟨⟨a, fun h => hj (a.property.symm.trans h)⟩, a.property⟩
        invFun := fun a => ⟨a.1.1, a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    intro a
    have hne : ¬f a = k := fun h => hj (a.property.symm.trans h)
    rw [dif_neg hne]
    congr 1

/-- The aggregation density factors when one target coordinate and its source fibre are
split off. -/
private theorem posSimplexAggregateDensity_split
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : β) (s : ℝ) (z : {j : β // j ≠ k} → ℝ) :
    let p : α → Prop := fun a => f a = k
    let β' := {j : β // j ≠ k}
    let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
    let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
      if h : j = k then s else z ⟨j, h⟩
    posSimplexAggregateDensity f (assemble s z) =
      (ENNReal.ofReal s ^ (Fintype.card {a : α // p a} - 1) /
        (Nat.factorial (Fintype.card {a : α // p a} - 1) : ENNReal)) *
        posSimplexAggregateDensity f' z := by
  classical
  dsimp only
  unfold posSimplexAggregateDensity
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun j : β =>
    ENNReal.ofReal (if h : j = k then s else z ⟨j, h⟩) ^
      (Fintype.card {i : α // f i = j} - 1) /
        (Nat.factorial (Fintype.card {i : α // f i = j} - 1) : ENNReal)) k]
  rw [dif_pos rfl]
  congr 1
  apply Fintype.prod_congr
  intro j
  let e : {i : α // f i = (j : β)} ≃
      {i : {a : α // ¬f a = k} //
        (⟨f i, i.property⟩ : {j : β // j ≠ k}) = j} :=
    { toFun := fun a => ⟨⟨a, fun h => j.property (a.property.symm.trans h)⟩,
        Subtype.ext a.property⟩
      invFun := fun a => ⟨a.1.1, congrArg Subtype.val a.property⟩
      left_inv := fun a => by ext; rfl
      right_inv := fun a => by ext; rfl }
  rw [dif_neg j.property]
  have hj : (⟨(j : β), j.property⟩ : {j : β // j ≠ k}) = j := Subtype.ext rfl
  rw [hj]
  apply congrArg (fun n : ℕ => ENNReal.ofReal (z j) ^ (n - 1) /
    (Nat.factorial (n - 1) : ENNReal))
  convert Fintype.card_congr e using 1
  congr 1
  apply Subsingleton.elim

/-- The solid-simplex aggregation formula when the target index type is empty. -/
theorem lintegral_posSimplex_comp_aggregate_of_isEmpty
    {α β : Type*} [Fintype α] [Fintype β] [IsEmpty β]
    (f : α → β) (_hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (_hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  let _ : IsEmpty α := ⟨fun a => isEmptyElim (f a)⟩
  have hα : posSimplex α r = Set.univ := by
    ext x
    simp [posSimplex, hr]
  have hβ : posSimplex β r = Set.univ := by
    ext z
    simp [posSimplex, hr]
  rw [hα, hβ, Measure.restrict_univ, Measure.volume_pi_eq_dirac,
    Measure.volume_pi_eq_dirac, lintegral_dirac]
  simp [Measure.restrict_univ, posSimplexAggregateDensity]
  congr 1
  funext b
  exact isEmptyElim b

/-- The solid-simplex aggregation formula when the target has a unique coordinate. -/
theorem lintegral_posSimplex_comp_aggregate_of_unique
    {α β : Type*} [Fintype α] [Fintype β] [Unique β]
    (f : α → β) (hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  let _ : Nonempty α := ⟨Classical.choose (hf default)⟩
  let e := MeasurableEquiv.piUnique (fun _ : β => ℝ)
  have hmp := volume_preserving_piUnique (fun _ : β => ℝ)
  have he_symm (s : ℝ) : e.symm s = fun _ : β => s := by
    funext j
    exact congrArg (e.symm s) (Subsingleton.elim j default)
  have hsimplex : e ⁻¹' Set.Icc (0 : ℝ) r = posSimplex β r := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Icc]
    change (0 ≤ z default ∧ z default ≤ r) ↔
      (∀ j, 0 ≤ z j) ∧ ∑ j, z j ≤ r
    constructor
    · rintro ⟨h0, hr⟩
      exact ⟨fun j => by simpa [Subsingleton.elim j default] using h0, by simpa using hr⟩
    · rintro ⟨h0, hr⟩
      exact ⟨h0 default, by simpa using hr⟩
  have hagg (x : α → ℝ) :
      FunOnFinite.linearMap ℝ ℝ f x = fun _ : β => ∑ i, x i := by
    funext k
    rw [FunOnFinite.linearMap_apply_apply]
    congr 1
    ext i
    simp [Subsingleton.elim (f i) k]
  rw [show (fun x => g (FunOnFinite.linearMap ℝ ℝ f x)) =
      (fun x => g (fun _ : β => ∑ i, x i)) by funext x; rw [hagg]]
  have hg' : Measurable (fun s : ℝ => g (fun _ : β => s)) := by
    exact hg.comp (by fun_prop)
  rw [lintegral_posSimplex_comp_sum r hr (fun s => g (fun _ : β => s)) hg']
  have hfiber : Fintype.card {i : α // f i = default} = Fintype.card α := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim (f i) default⟩
        left_inv := fun i => by ext; rfl
        right_inv := fun _ => rfl }
  calc
    (∫⁻ s in Set.Icc (0 : ℝ) r,
        (g fun _ : β => s) *
          (ENNReal.ofReal s ^ (Fintype.card α - 1) /
            Nat.factorial (Fintype.card α - 1))) =
        ∫⁻ s in Set.Icc (0 : ℝ) r,
          g (e.symm s) * posSimplexAggregateDensity f (e.symm s) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s _
      change (g fun _ : β => s) * _ = g (e.symm s) * _
      rw [he_symm]
      congr 1
      simp only [posSimplexAggregateDensity]
      rw [Fintype.prod_unique, hfiber]
    _ = ∫⁻ z in e ⁻¹' Set.Icc (0 : ℝ) r,
        g z * posSimplexAggregateDensity f z := by
      have hchange := (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
        (fun s => g (e.symm s) * posSimplexAggregateDensity f (e.symm s))
        (Set.Icc (0 : ℝ) r)).symm
      calc
        _ = ∫⁻ z in e ⁻¹' Set.Icc (0 : ℝ) r,
              g (e.symm (e z)) * posSimplexAggregateDensity f (e.symm (e z)) := hchange
        _ = _ := by
          apply setLIntegral_congr_fun (measurableSet_Icc.preimage e.measurable)
          intro z _
          change g (e.symm (e z)) * posSimplexAggregateDensity f (e.symm (e z)) = _
          rw [e.symm_apply_apply]
    _ = ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by rw [hsimplex]

/-- Pushing Lebesgue measure on a solid simplex forward under coordinate aggregation
(`FunOnFinite.linearMap`) weights the target solid simplex by the product of fibre volumes.

This is the solid-simplex form of the aggregation identity used for `stdSimplexMeasure`.
The unique-target case is `lintegral_posSimplex_comp_sum`. -/
theorem lintegral_posSimplex_comp_aggregate
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  induction hcard : Fintype.card β using Nat.strong_induction_on generalizing α β r with
  | h n ih =>
      cases isEmpty_or_nonempty β with
      | inl _ => exact lintegral_posSimplex_comp_aggregate_of_isEmpty f hf r hr g hg
      | inr _ =>
          cases subsingleton_or_nontrivial β with
          | inl _ =>
              let _ : Unique β :=
                { default := Classical.choice inferInstance
                  uniq := fun _ => Subsingleton.elim _ _ }
              exact lintegral_posSimplex_comp_aggregate_of_unique f hf r hr g hg
          | inr _ =>
              classical
              let k : β := Classical.choice inferInstance
              let β' := {j : β // j ≠ k}
              let p : α → Prop := fun a => f a = k
              let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
              have hf' : Function.Surjective f' := by
                intro j
                obtain ⟨a, ha⟩ := hf j
                exact ⟨⟨a, fun hak => j.property (ha.symm.trans hak)⟩, Subtype.ext ha⟩
              have hcard' : Fintype.card β' < n := by
                rw [← hcard]
                rw [Fintype.card_subtype_compl (fun j : β => j = k),
                  Fintype.card_subtype_eq k]
                exact Nat.sub_lt (Fintype.card_pos) zero_lt_one
              let eα := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ) p
              let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
                if h : j = k then s else z ⟨j, h⟩
              let G : ({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ) → ENNReal :=
                fun q => g (assemble (∑ i, q.1 i)
                  (FunOnFinite.linearMap ℝ ℝ f' q.2))
              have hG : Measurable G := by
                apply hg.comp
                apply measurable_pi_lambda _
                intro j
                by_cases hj : j = k
                · subst j
                  simp only [assemble, dif_pos rfl]
                  fun_prop
                · simp only [assemble, dif_neg hj]
                  fun_prop
              have hsource :
                  (∫⁻ x in posSimplex α r,
                    g (FunOnFinite.linearMap ℝ ℝ f x)) =
                    ∫⁻ u in posSimplex {a : α // p a} r,
                      ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
                calc
                  _ = ∫⁻ x in posSimplex α r, G (eα x) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex α r)
                    intro x _
                    have ha := linearMap_piEquivPiSubtypeProd_eq f k (eα x)
                    dsimp only [G]
                    apply congrArg g
                    simpa only [p, eα, β', f', assemble, eα.symm_apply_apply] using ha
                  _ = _ := lintegral_posSimplex_split_pred p r G hG
              let H : ℝ → ENNReal := fun s =>
                ∫⁻ z in posSimplex β' (r - s),
                  g (assemble s z) * posSimplexAggregateDensity f' z
              have hpair : Measurable (Function.uncurry (fun (s : ℝ) (z : β' → ℝ) =>
                  g (assemble s z) * posSimplexAggregateDensity f' z)) := by
                apply Measurable.mul
                · apply hg.comp
                  apply measurable_pi_lambda _
                  intro j
                  by_cases hj : j = k
                  · subst j
                    simp only [assemble, dif_pos rfl]
                    fun_prop
                  · simp only [assemble, dif_neg hj]
                    fun_prop
                · unfold posSimplexAggregateDensity
                  fun_prop
              have hH : Measurable H := by
                exact measurable_lintegral_posSimplex_sub r _ hpair
              let A := {a : α // p a}
              let _ : Nonempty A := ⟨⟨Classical.choose (hf k), Classical.choose_spec (hf k)⟩⟩
              have hscalar :
                  (∫⁻ x in posSimplex α r,
                    g (FunOnFinite.linearMap ℝ ℝ f x)) =
                    ∫⁻ s in Set.Icc (0 : ℝ) r,
                      H s * (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                        Nat.factorial (Fintype.card A - 1)) := by
                rw [hsource]
                calc
                  _ = ∫⁻ u in posSimplex A r, H (∑ i, u i) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex A r)
                    intro u hu
                    have hrs : 0 ≤ r - ∑ i, u i := sub_nonneg.mpr hu.2
                    have hrec := ih (Fintype.card β') hcard' f' hf'
                      (r - ∑ i, u i) hrs (fun z => g (assemble (∑ i, u i) z))
                      (by
                        apply hg.comp
                        apply measurable_pi_lambda _
                        intro j
                        by_cases hj : j = k
                        · subst j
                          simp only [assemble, dif_pos rfl]
                          fun_prop
                        · simp only [assemble, dif_neg hj]
                          fun_prop)
                      rfl
                    simpa only [G, H] using hrec
                  _ = _ := lintegral_posSimplex_comp_sum r hr H hH
              let pβ : β → Prop := fun j => j = k
              let eβ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : β => ℝ) pβ
              let Aβ := {j : β // pβ j}
              let _ : Fintype Aβ := Subtype.fintype pβ
              let _ : Unique Aβ :=
                { default := ⟨k, rfl⟩
                  uniq := fun a => Subtype.ext a.property }
              have heβ (q : (Aβ → ℝ) × (β' → ℝ)) :
                  eβ.symm q = assemble (∑ i, q.1 i) q.2 := by
                funext j
                by_cases hj : j = k
                · subst j
                  change (if h : k = k then q.1 ⟨k, h⟩ else q.2 ⟨k, h⟩) = _
                  simp only [dif_pos rfl, assemble]
                  rw [Fintype.sum_unique]
                  congr 2
                · change (if h : j = k then q.1 ⟨j, h⟩ else q.2 ⟨j, h⟩) = _
                  simp only [dif_neg hj, assemble]
              let Gβ : (Aβ → ℝ) × (β' → ℝ) → ENNReal := fun q =>
                g (eβ.symm q) * posSimplexAggregateDensity f (eβ.symm q)
              have hGβ : Measurable Gβ := by
                apply Measurable.mul
                · exact hg.comp eβ.symm.measurable
                · unfold posSimplexAggregateDensity
                  fun_prop
              have htarget :
                  (∫⁻ z in posSimplex β r,
                    g z * posSimplexAggregateDensity f z) =
                    ∫⁻ s in Set.Icc (0 : ℝ) r,
                      H s * (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                        Nat.factorial (Fintype.card A - 1)) := by
                calc
                  _ = ∫⁻ z in posSimplex β r, Gβ (eβ z) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex β r)
                    intro z _
                    simp only [Gβ, eβ.symm_apply_apply]
                  _ = ∫⁻ u in posSimplex Aβ r,
                      ∫⁻ z in posSimplex β' (r - ∑ i, u i), Gβ (u, z) :=
                    lintegral_posSimplex_split_pred pβ r Gβ hGβ
                  _ = ∫⁻ u in posSimplex Aβ r,
                      H (∑ i, u i) *
                        (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                          Nat.factorial (Fintype.card A - 1)) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex Aβ r)
                    intro u _
                    change (∫⁻ z in posSimplex β' (r - ∑ i, u i), Gβ (u, z)) = _
                    calc
                      _ = ∫⁻ z in posSimplex β' (r - ∑ i, u i),
                          (g (assemble (∑ i, u i) z) *
                            posSimplexAggregateDensity f' z) *
                            (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                              Nat.factorial (Fintype.card A - 1)) := by
                        apply setLIntegral_congr_fun (measurableSet_posSimplex β' _)
                        intro z _
                        change Gβ (u, z) = _
                        rw [show Gβ (u, z) = g (assemble (∑ i, u i) z) *
                            posSimplexAggregateDensity f (assemble (∑ i, u i) z) by
                          simp only [Gβ, heβ]]
                        rw [posSimplexAggregateDensity_split f k]
                        simp only [A]
                        ac_rfl
                      _ = H (∑ i, u i) *
                          (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                            Nat.factorial (Fintype.card A - 1)) := by
                        apply lintegral_mul_const'
                        exact ENNReal.div_ne_top (by simp) (by positivity)
                  _ = _ := by
                    have hm : Measurable (fun s => H s *
                        (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                          Nat.factorial (Fintype.card A - 1))) := by fun_prop
                    rw [lintegral_posSimplex_comp_sum r hr _ hm]
                    simp [Aβ, pβ]
              exact hscalar.trans htarget.symm
