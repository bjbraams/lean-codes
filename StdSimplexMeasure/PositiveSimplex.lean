import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue volume of a finite-dimensional positive simplex

This file evaluates the Lebesgue volume of the set of nonnegative coordinate vectors whose
coordinate sum is bounded by a nonnegative real number. The proof first treats coordinates
indexed by `Fin n`, by induction and slicing, and then transports the result to any finite type.
-/

open Fintype Set
open MeasureTheory

noncomputable section

/-- Fubini's theorem for an integral restricted to a measurable subset of a product. -/
lemma setIntegral_prod_slices
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → E) (hf : IntegrableOn f T (μ.prod ν)) :
    ∫ p in T, f p ∂μ.prod ν =
      ∫ x, ∫ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hT]
  rw [integral_prod _ (hf.integrable_indicator hT)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_indicator (measurable_prodMk_left hT)]
  apply integral_congr_ae
  filter_upwards [] with y
  rfl

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
  convert h using 1 <;> ext x <;> simp

/-- The volume formula for the zero-dimensional positive simplex. -/
lemma volume_posSimplexFin_zero (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplexFin 0 r) = ENNReal.ofReal r ^ 0 / Nat.factorial 0 := by
  rw [Measure.volume_pi_eq_dirac]
  simp [posSimplexFin, hr]

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
  let T : Set (ℝ × (Fin n → ℝ)) :=
    {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + ∑ i, p.2 i ≤ r}
  have hT : MeasurableSet T := by
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
    convert h using 1 <;> ext p <;> simp
  have he : e '' posSimplexFin (n + 1) r = T := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨hx0, hxsum⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [e] using hx0 0
      · intro i
        change 0 ≤ x (Fin.succ i)
        exact hx0 (Fin.succ i)
      · change x 0 + ∑ i, x (Fin.succ i) ≤ r
        simpa [Fin.sum_univ_succ] using hxsum
    · intro hp
      refine ⟨e.symm p, ?_, by simp⟩
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
      have hsections : ∀ t : ℝ, 0 ≤ t → t ≤ r →
          Prod.mk t ⁻¹' T = posSimplexFin n (r - t) := by
        intro t ht htr
        ext x
        simp only [T, posSimplexFin, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨_, hx0, hs⟩
          exact ⟨hx0, by linarith⟩
        · rintro ⟨hx0, hs⟩
          exact ⟨ht, hx0, by linarith⟩
      calc
        (∫⁻ t, volume (Prod.mk t ⁻¹' T)) =
            ∫⁻ t in Icc (0 : ℝ) r,
              ENNReal.ofReal (r - t) ^ n / Nat.factorial n := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          simp only [Set.indicator_apply]
          split_ifs with ht
          · rw [hsections t ht.1 ht.2, ih (r - t) (sub_nonneg.mpr ht.2)]
          · have hempty : Prod.mk t ⁻¹' T = ∅ := by
              ext x
              simp only [T, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
              constructor
              · intro h
                exfalso
                apply ht
                exact ⟨h.1, by
                  have hs0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => h.2.1 i
                  linarith [h.2.2, hs0]⟩
              · exact False.elim
            rw [hempty, measure_empty]
        _ = ENNReal.ofReal r ^ (n + 1) / Nat.factorial (n + 1) := by
          have hint : ∫ t in Icc (0 : ℝ) r, (r - t) ^ n = r ^ (n + 1) / (n + 1) := by
            rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
            change (∫ t in (0 : ℝ)..r, (fun x : ℝ => x ^ n) (r - t)) = _
            calc
              _ = ∫ x in r - r..r - 0, x ^ n :=
                intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) r
              _ = _ := by simp [integral_pow]
          let q : ℝ := Nat.factorial n
          have hq : 0 < q := by positivity
          have hnonneg : ∀ t ∈ Icc (0 : ℝ) r, 0 ≤ (r - t) ^ n / q := by
            intro t ht
            exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) hq.le
          have hintg : IntegrableOn (fun t : ℝ => (r - t) ^ n / q) (Icc 0 r) :=
            (Continuous.integrableOn_Icc (by fun_prop))
          calc
            (∫⁻ t in Icc (0 : ℝ) r,
                ENNReal.ofReal (r - t) ^ n / Nat.factorial n) =
                ∫⁻ t in Icc (0 : ℝ) r, ENNReal.ofReal ((r - t) ^ n / q) := by
              apply setLIntegral_congr_fun measurableSet_Icc
              intro t ht
              change ENNReal.ofReal (r - t) ^ n / Nat.factorial n =
                ENNReal.ofReal ((r - t) ^ n / q)
              symm
              rw [ENNReal.ofReal_div_of_pos hq,
                ENNReal.ofReal_pow (sub_nonneg.mpr ht.2)]
              simp [q]
            _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) r, (r - t) ^ n / q) := by
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
