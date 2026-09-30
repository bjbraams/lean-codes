/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SmallVariable
public import Carlson.Normalization.Basic
public import Carlson.R.Explicit

/-!
# The small-variable limit for all complex parameters

Carlson's Theorem 8.3-2 removes the conditions `re a, re a' > 0` from Theorem 8.3-1: if
`re (a' - bₖ) > 0` then, as `zₖ → 0`,
`R_{-a}(b; z)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ R_{-a}(b without k; z without k)/Γ(c - bₖ)`.

The proof follows Carlson. The recurrence 8.3(5) writes `R_{-a}(b; z)` through the functions
`R_{-a-1}(b + eᵢ + eⱼ; z)`, which lie one step closer to the region `re a, re a' > 0` where
Theorem 8.3-1 applies. Induction on the number of steps shows that the limit exists; it is given
by a function holomorphic in `(a, b)` on a convex region, and it agrees with the closed form on
the open subregion covered by Theorem 8.3-1, so the identity theorem identifies them. The other
nodes and the approach to zero stay in the right half-plane, as in Theorem 8.3-1 here.

## Main definitions

* `Carlson.smallVariableValue`: the closed-form limit.
* `Carlson.smallVariableRegion`: the parameter regions of the induction.

## Main results

* `Carlson.tendsto_regCarlsonR_update_zero`: Theorem 8.3-2.
* `Carlson.tendsto_regCarlsonR_update_zero_const`: the case of equal remaining nodes, with the
  one-node value `Carlson.regCarlsonR_const_node`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Complex Filter Set Dirichlet
open scoped Topology Classical
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- Deleting a parameter lowers the total parameter by that parameter. -/
theorem sum_eraseCarlsonParameter (k : ι) (b : ι → ℂ) :
    ∑ j, eraseCarlsonParameter k b j = ∑ j, b j - b k := by
  rw [Fintype.sum_eq_add_sum_subtype_ne b k]
  unfold eraseCarlsonParameter
  ring

/-- The value of Theorem 8.3-2 as a function of `p = (a, b)`:
`Γ(a' - bₖ) Γ(a')⁻¹ R_{-a}(b without k; z without k)/Γ(c - bₖ)`, `a' = ∑ bⱼ - a`. -/
def smallVariableValue (k : ι) (z : ι → ℂ) (p : ℂ × (ι → ℂ)) : ℂ :=
  Gamma (∑ j, p.2 j - p.1 - p.2 k) *
    ((Gamma (∑ j, p.2 j - p.1))⁻¹ *
      regCarlsonR (-p.1) (eraseCarlsonParameter k p.2) (eraseCarlsonVariable k z))

/-- The parameter region of the `n`-th induction step. -/
def smallVariableRegion (k : ι) (n : ℕ) : Set (ℂ × (ι → ℂ)) :=
  {p | 0 < (p.1 + n).re ∧ 0 < (∑ j, p.2 j - p.1 + n).re ∧ 0 < (∑ j, p.2 j - p.1 - p.2 k).re}

/-- The approach filter: `w → 0` through the open right half-plane. -/
abbrev rightApproach : Filter {v : ℂ // 0 < v.re} := comap Subtype.val (𝓝 0)

/-- The right-half-plane approach to `0` is a proper filter. -/
theorem rightApproach_neBot : rightApproach.NeBot := by
  refine (mem_closure_iff_comap_neBot (s := {v : ℂ | 0 < v.re})).mp ?_
  refine mem_closure_of_tendsto (f := fun n : ℕ => ((n : ℂ) + 1)⁻¹) (b := atTop) ?_
    (Eventually.of_forall fun n => ?_)
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    simpa [one_div] using h
  · show 0 < (((n : ℂ) + 1)⁻¹).re
    rw [show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_inv, ofReal_re]
    positivity

/-- The induction regions are open. -/
theorem isOpen_smallVariableRegion (k : ι) (n : ℕ) : IsOpen (smallVariableRegion k n) := by
  have h1 : Continuous fun p : ℂ × (ι → ℂ) => (p.1 + n).re := by fun_prop
  have h2 : Continuous fun p : ℂ × (ι → ℂ) => (∑ j, p.2 j - p.1 + n).re := by fun_prop
  have h3 : Continuous fun p : ℂ × (ι → ℂ) => (∑ j, p.2 j - p.1 - p.2 k).re := by fun_prop
  exact (isOpen_lt continuous_const h1).inter
    ((isOpen_lt continuous_const h2).inter (isOpen_lt continuous_const h3))

/-- The induction regions are convex. -/
theorem convex_smallVariableRegion (k : ι) (n : ℕ) : Convex ℝ (smallVariableRegion k n) := by
  intro p hp q hq α β hα hβ hαβ
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨h1', h2', h3'⟩ := hq
  have e1 : ((α • p + β • q).1 + n).re = α * (p.1 + n).re + β * (q.1 + n).re := by
    simp only [Prod.fst_add, Prod.smul_fst, add_re, smul_re, natCast_re, smul_eq_mul]
    linear_combination (-(n : ℝ)) * hαβ
  have e2 : (∑ j, (α • p + β • q).2 j - (α • p + β • q).1 + n).re =
      α * (∑ j, p.2 j - p.1 + n).re + β * (∑ j, q.2 j - q.1 + n).re := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, sub_re, add_re, smul_re,
      natCast_re, smul_eq_mul, re_sum]
    linear_combination (-(n : ℝ)) * hαβ
  have e3 : (∑ j, (α • p + β • q).2 j - (α • p + β • q).1 - (α • p + β • q).2 k).re =
      α * (∑ j, p.2 j - p.1 - p.2 k).re + β * (∑ j, q.2 j - q.1 - q.2 k).re := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, sub_re, add_re, smul_re,
      smul_eq_mul, re_sum]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show 0 < _; rw [e1]
    rcases eq_or_lt_of_le hα with h | h
    · subst h; simp at hαβ; subst hαβ; simpa using h1'
    · nlinarith [mul_pos h h1, mul_nonneg hβ h1'.le]
  · show 0 < _; rw [e2]
    rcases eq_or_lt_of_le hα with h | h
    · subst h; simp at hαβ; subst hαβ; simpa using h2'
    · nlinarith [mul_pos h h2, mul_nonneg hβ h2'.le]
  · show 0 < _; rw [e3]
    rcases eq_or_lt_of_le hα with h | h
    · subst h; simp at hαβ; subst hαβ; simpa using h3'
    · nlinarith [mul_pos h h3, mul_nonneg hβ h3'.le]

/-- Coordinates of the parameter vector are analytic. -/
private theorem analyticAt_snd_apply (j : ι) (p : ℂ × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : ℂ × (ι → ℂ) => q.2 j) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).comp
    (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).analyticAt p

/-- The total parameter is analytic. -/
private theorem analyticAt_sum_snd (p : ℂ × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : ℂ × (ι → ℂ) => ∑ j, q.2 j) p := by
  have := ((∑ j, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).comp
    (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).analyticAt p
  convert this using 1
  funext q
  simp

/-- The value of Theorem 8.3-2 is holomorphic in `(a, b)` where `re (a' - bₖ) > 0`. -/
theorem analyticAt_smallVariableValue (k : ι) {z : ι → ℂ}
    (hz : eraseCarlsonVariable k z ∈ carlsonRSlitDomain) {p : ℂ × (ι → ℂ)}
    (hp : 0 < (∑ j, p.2 j - p.1 - p.2 k).re) : AnalyticAt ℂ (smallVariableValue k z) p := by
  have hc : AnalyticAt ℂ (fun q : ℂ × (ι → ℂ) => ∑ j, q.2 j - q.1 - q.2 k) p :=
    ((analyticAt_sum_snd p).sub analyticAt_fst).sub (analyticAt_snd_apply k p)
  have hc' : AnalyticAt ℂ (fun q : ℂ × (ι → ℂ) => ∑ j, q.2 j - q.1) p :=
    (analyticAt_sum_snd p).sub analyticAt_fst
  have hR : AnalyticAt ℂ (fun q : ℂ × (ι → ℂ) =>
      regCarlsonR (-q.1) (eraseCarlsonParameter k q.2) (eraseCarlsonVariable k z)) p :=
    analyticAt_regCarlsonR_comp analyticAt_fst.neg
      (analyticAt_pi_iff.mpr fun j => analyticAt_snd_apply j.1 p) analyticAt_const hz
  refine analyticAt_Gamma_mul_comp hc
    (((differentiable_one_div_Gamma.analyticAt _).comp_of_eq hc' rfl).mul hR) ?_
  intro m hm
  have := congrArg re hm
  simp only [neg_re, natCast_re] at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The base case of the induction: Theorem 8.3-1 with positive endpoint exponents. -/
theorem tendsto_smallVariable_zero (k : ι) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {p : ℂ × (ι → ℂ)} (hp : p ∈ smallVariableRegion k 0) :
    Tendsto (fun v : {v : ℂ // 0 < v.re} => regCarlsonR (-p.1) p.2 (Function.update z k v))
      rightApproach (𝓝 (smallVariableValue k z p)) := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [Nat.cast_zero, add_zero] at h1 h2
  have H := tendsto_regCarlsonR_update_zero_of_pos k (a := p.1) (a' := ∑ j, p.2 j - p.1)
    (b := p.2) h1 h2 h3 (by ring) hz (E := {v : ℂ // 0 < v.re}) (l := rightApproach)
    (w := Subtype.val) (fun v => v.2) tendsto_comap
  rw [smallVariableValue]
  rw [div_eq_mul_inv, mul_assoc] at H
  convert H using 4


/-- The value produced by one application of the recurrence 8.3(5) at the index `i`. -/
def smallVariableStepValue (k i : ι) (z : ι → ℂ) (p : ℂ × (ι → ℂ)) : ℂ :=
  ∑ j, addDirichletUnit p.2 i j * ((∑ l, p.2 l - p.1) * Function.update z k 0 j + p.1 * z i) *
    smallVariableValue k z (p.1 + 1, addDirichletUnit (addDirichletUnit p.2 i) j)

/-- The double shift of 8.3(5) maps region `n + 1` into region `n`. -/
private theorem shift_mem_region (k i j : ι) (hik : i ≠ k) (n : ℕ) {p : ℂ × (ι → ℂ)}
    (hp : p ∈ smallVariableRegion k (n + 1)) :
    (p.1 + 1, addDirichletUnit (addDirichletUnit p.2 i) j) ∈ smallVariableRegion k n := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hk : addDirichletUnit (addDirichletUnit p.2 i) j k = p.2 k + if j = k then 1 else 0 := by
    have hki : k ≠ i := Ne.symm hik
    unfold addDirichletUnit
    by_cases hjk : j = k
    · subst hjk; rw [Function.update_self, Function.update_of_ne hki]; simp
    · rw [Function.update_of_ne (Ne.symm hjk), Function.update_of_ne hki]; simp [hjk]
  refine ⟨?_, ?_, ?_⟩
  · show 0 < (p.1 + 1 + n).re; push_cast at h1; simp only [add_re, one_re, natCast_re] at h1 ⊢
    linarith
  · show 0 < (∑ l, addDirichletUnit (addDirichletUnit p.2 i) j l - (p.1 + 1) + n).re
    rw [sum_addDirichletUnit, sum_addDirichletUnit]; push_cast at h2
    simp only [add_re, sub_re, one_re, natCast_re] at h2 ⊢; linarith
  · show 0 < (∑ l, addDirichletUnit (addDirichletUnit p.2 i) j l - (p.1 + 1) -
      addDirichletUnit (addDirichletUnit p.2 i) j k).re
    rw [sum_addDirichletUnit, sum_addDirichletUnit, hk]
    split_ifs <;> simp only [add_re, sub_re, one_re, zero_re] at h3 ⊢ <;> linarith

/-- One application of the recurrence 8.3(5) moves the limit from region `n` to region
`n + 1`. -/
theorem tendsto_smallVariable_step (k i : ι) (hik : i ≠ k) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (n : ℕ)
    (hIH : ∀ p ∈ smallVariableRegion k n,
      Tendsto (fun v : {v : ℂ // 0 < v.re} => regCarlsonR (-p.1) p.2 (Function.update z k v))
        rightApproach (𝓝 (smallVariableValue k z p)))
    {p : ℂ × (ι → ℂ)} (hp : p ∈ smallVariableRegion k (n + 1)) :
    Tendsto (fun v : {v : ℂ // 0 < v.re} => regCarlsonR (-p.1) p.2 (Function.update z k v))
      rightApproach (𝓝 (smallVariableStepValue k i z p)) := by
  have hrec : ∀ v : {v : ℂ // 0 < v.re}, regCarlsonR (-p.1) p.2 (Function.update z k v) =
      ∑ j, addDirichletUnit p.2 i j *
        ((∑ l, p.2 l - p.1) * Function.update z k (v : ℂ) j + p.1 * z i) *
        regCarlsonR (-(p.1 + 1)) (addDirichletUnit (addDirichletUnit p.2 i) j)
          (Function.update z k v) := by
    intro v
    rw [regCarlsonR_eq_sum_double_shift (-p.1) p.2 (carlsonRVariableDomain_update hz k v.2) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.update_of_ne hik, show -p.1 - 1 = -(p.1 + 1) by ring]
    ring
  simp_rw [hrec]
  unfold smallVariableStepValue
  refine tendsto_finsetSum _ fun j _ => ?_
  refine Tendsto.mul (Tendsto.const_mul _ (Tendsto.add_const _ (Tendsto.const_mul _ ?_)))
    (hIH _ (shift_mem_region k i j hik n hp))
  have hcont : Continuous fun v : ℂ => Function.update z k v j := by
    by_cases hjk : j = k
    · subst hjk; simp only [Function.update_self]; exact continuous_id
    · simpa [Function.update_of_ne hjk] using continuous_const
  exact (hcont.tendsto 0).comp tendsto_comap

omit [Fintype ι] in
/-- A double unit shift of the parameters, written out. -/
private theorem addDirichletUnit_addDirichletUnit_eq (b : ι → ℂ) (i j : ι) :
    addDirichletUnit (addDirichletUnit b i) j =
      fun l => b l + ((if l = i then 1 else 0) + (if l = j then 1 else 0)) := by
  funext l
  unfold addDirichletUnit
  by_cases hlj : l = j
  · subst hlj
    by_cases hli : l = i
    · subst hli; simp; ring
    · simp [hli]
  · by_cases hli : l = i
    · subst hli; simp [hlj]
    · simp [hli, hlj]

/-- The step value is holomorphic in `(a, b)` on region `n + 1`. -/
theorem analyticAt_smallVariableStepValue (k i : ι) (hik : i ≠ k) {z : ι → ℂ}
    (hz : eraseCarlsonVariable k z ∈ carlsonRSlitDomain) (n : ℕ) {q : ℂ × (ι → ℂ)}
    (hq : q ∈ smallVariableRegion k (n + 1)) :
    AnalyticAt ℂ (smallVariableStepValue k i z) q := by
  show AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => ∑ j, addDirichletUnit p.2 i j *
    ((∑ l, p.2 l - p.1) * Function.update z k 0 j + p.1 * z i) *
      smallVariableValue k z (p.1 + 1, addDirichletUnit (addDirichletUnit p.2 i) j)) q
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun j _ => ?_
  have hunit : (fun p : ℂ × (ι → ℂ) => addDirichletUnit p.2 i j) =
      fun p => p.2 j + if j = i then 1 else 0 := by
    funext p; unfold addDirichletUnit
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have hshift : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) =>
      (p.1 + 1, addDirichletUnit (addDirichletUnit p.2 i) j)) q := by
    refine (analyticAt_fst.add analyticAt_const).prod ?_
    simp_rw [addDirichletUnit_addDirichletUnit_eq]
    exact analyticAt_pi_iff.mpr fun l => (analyticAt_snd_apply l q).add analyticAt_const
  refine AnalyticAt.mul (AnalyticAt.mul ?_ ?_) ?_
  · rw [hunit]; exact (analyticAt_snd_apply j q).add analyticAt_const
  · exact (((analyticAt_sum_snd q).sub analyticAt_fst).mul analyticAt_const).add
      (analyticAt_fst.mul analyticAt_const)
  · exact (analyticAt_smallVariableValue k hz (shift_mem_region k i j hik n hq).2.2).comp_of_eq
      hshift rfl

/-- The regions increase with `n`. -/
private theorem region_zero_subset (k : ι) (n : ℕ) :
    smallVariableRegion k 0 ⊆ smallVariableRegion k n := by
  rintro p ⟨h1, h2, h3⟩
  simp only [Nat.cast_zero, add_zero] at h1 h2
  refine ⟨?_, ?_, h3⟩ <;> simp only [add_re, natCast_re] <;>
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The induction behind Theorem 8.3-2: on every region the limit is the closed form. -/
theorem tendsto_smallVariable_region (k i : ι) (hik : i ≠ k) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (n : ℕ) :
    ∀ p ∈ smallVariableRegion k n,
      Tendsto (fun v : {v : ℂ // 0 < v.re} => regCarlsonR (-p.1) p.2 (Function.update z k v))
        rightApproach (𝓝 (smallVariableValue k z p)) := by
  have hz' : eraseCarlsonVariable k z ∈ carlsonRSlitDomain :=
    fun j => carlsonRVariableDomain_subset_slitDomain hz j
  have := rightApproach_neBot
  induction n with
  | zero => exact fun p hp => tendsto_smallVariable_zero k hz hp
  | succ n ih =>
    intro p hp
    have hstep := tendsto_smallVariable_step k i hik hz n ih hp
    suffices h : smallVariableStepValue k i z p = smallVariableValue k z p by rwa [← h]
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Fintype.one_lt_card_iff.mpr ⟨i, k, hik⟩
    set p₀ : ℂ × (ι → ℂ) := (1, fun _ => 2)
    have hp₀ : p₀ ∈ smallVariableRegion k 0 := by
      refine ⟨by simp [p₀], ?_, ?_⟩ <;> simp [p₀, Finset.sum_const] <;> linarith
    have hF : AnalyticOnNhd ℂ (smallVariableStepValue k i z) (smallVariableRegion k (n + 1)) :=
      fun q hq => analyticAt_smallVariableStepValue k i hik hz' n hq
    have hG : AnalyticOnNhd ℂ (smallVariableValue k z) (smallVariableRegion k (n + 1)) :=
      fun q hq => analyticAt_smallVariableValue k hz' hq.2.2
    refine hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_smallVariableRegion k (n + 1)).isPreconnected (region_zero_subset k _ hp₀) ?_ hp
    filter_upwards [(isOpen_smallVariableRegion k 0).mem_nhds hp₀] with q hq
    exact tendsto_nhds_unique
      (tendsto_smallVariable_step k i hik hz n ih (region_zero_subset k _ hq))
      (tendsto_smallVariable_zero k hz hq)

/-- Theorem 8.3-2 with the classical decidability instances. -/
private theorem tendsto_regCarlsonR_update_zero_classical (k : ι) {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hz : z ∈ carlsonRVariableDomain)
    (hne : ∃ i, i ≠ k) {E : Type*} {l : Filter E} {w : E → ℂ}
    (hw : ∀ x, 0 < (w x).re) (hlim : Tendsto w l (𝓝 0)) :
    Tendsto (fun x => regCarlsonR (-a) b (Function.update z k (w x))) l
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z)))) := by
  obtain ⟨i, hik⟩ := hne
  set n : ℕ := ⌈|a.re| + |a'.re|⌉₊ + 1
  have hn : |a.re| + |a'.re| < n := by
    simp only [n]; push_cast; linarith [Nat.le_ceil (|a.re| + |a'.re|)]
  have ha' : ∑ j, b j - a = a' := by rw [← hsum]; ring
  have hp : ((a, b) : ℂ × (ι → ℂ)) ∈ smallVariableRegion k n := by
    refine ⟨?_, ?_, ?_⟩
    · show 0 < (a + n).re; simp only [add_re, natCast_re]
      linarith [neg_abs_le a.re, abs_nonneg a'.re]
    · show 0 < (∑ j, b j - a + n).re; rw [ha']; simp only [add_re, natCast_re]
      linarith [neg_abs_le a'.re, abs_nonneg a.re]
    · show 0 < (∑ j, b j - a - b k).re; rw [ha']; exact hk
  have H := tendsto_smallVariable_region k i hik hz n _ hp
  have hw' : Tendsto (fun x => (⟨w x, hw x⟩ : {v : ℂ // 0 < v.re})) l rightApproach :=
    tendsto_comap_iff.mpr hlim
  have := H.comp hw'
  simp only [smallVariableValue, ha'] at this
  exact this

/-- **Carlson's Theorem 8.3-2** (with Theorem 8.3-1): if `re (a' - bₖ) > 0`, where
`a + a' = ∑ bⱼ`, then as `zₖ → 0` through the right half-plane, with the other nodes in the right
half-plane,
`R_{-a}(b; z)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ R_{-a}(b₁, …, b̂ₖ, …; z₁, …, ẑₖ, …)/Γ(c - bₖ)`,
for all complex `a` and `b`. -/
theorem tendsto_regCarlsonR_update_zero [DecidableEq ι] (k : ι) {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hz : z ∈ carlsonRVariableDomain)
    (hne : ∃ i, i ≠ k) {E : Type*} {l : Filter E} {w : E → ℂ}
    (hw : ∀ x, 0 < (w x).re) (hlim : Tendsto w l (𝓝 0)) :
    Tendsto (fun x => regCarlsonR (-a) b (Function.update z k (w x))) l
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z)))) := by
  convert tendsto_regCarlsonR_update_zero_classical k hsum hk hz hne hw hlim

/-- On equal nodes in the right half-plane the regularized `R` function is a power, for all
complex parameters: `R_t(b; w, …, w)/Γ(c) = w^t/Γ(c)`. -/
theorem regCarlsonR_const_node {κ : Type*} [Fintype κ] (t : ℂ) (b : κ → ℂ) {w : ℂ}
    (hw : 0 < w.re) : regCarlsonR t b (fun _ => w) = w ^ t * (Gamma (∑ i, b i))⁻¹ := by
  have hz : (fun _ : κ => w) ∈ carlsonRVariableDomain := fun _ => hw
  have hF := analyticOnNhd_regCarlsonR_parameters t (carlsonRVariableDomain_subset_slitDomain hz)
  have hG : AnalyticOnNhd ℂ (fun b : κ → ℂ => w ^ t * (Gamma (∑ i, b i))⁻¹) univ := by
    intro b _
    have hs : AnalyticAt ℂ (fun b : κ → ℂ => ∑ i, b i) b := by
      have := ((∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) i)).analyticAt b
      convert this using 1; funext q; simp
    exact analyticAt_const.mul ((differentiable_one_div_Gamma.analyticAt _).comp_of_eq hs rfl)
  have h1 : (fun _ : κ => (1 : ℂ)) ∈ mvBetaConvergent := fun _ => by simp
  have heq := hF.eq_of_eventuallyEq hG (z₀ := fun _ => 1) (by
    filter_upwards [isOpen_mvBetaConvergent.mem_nhds h1] with c hc
    rw [regCarlsonR_eq_regCarlsonRIntegral t hc hz, regCarlsonRIntegral,
      regCarlsonDirichletAverage_const _ _ hc, div_eq_mul_inv])
  exact congrFun heq b

/-- The classical-instance form of `tendsto_regCarlsonR_update_zero_const`:
`R_{-a}(b; w, …, zₖ, …, w)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ w^{-a}/Γ(c - bₖ)`. -/
private theorem tendsto_regCarlsonR_update_zero_const_classical (k : ι) {a a' : ℂ} {b : ι → ℂ}
    {w₀ : ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hw₀ : 0 < w₀.re)
    (hne : ∃ i, i ≠ k) {E : Type*} {l : Filter E} {w : E → ℂ}
    (hw : ∀ x, 0 < (w x).re) (hlim : Tendsto w l (𝓝 0)) :
    Tendsto (fun x => regCarlsonR (-a) b (Function.update (fun _ => w₀) k (w x))) l
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ * (w₀ ^ (-a) * (Gamma (a + a' - b k))⁻¹)))) := by
  have H := tendsto_regCarlsonR_update_zero_classical k hsum hk (z := fun _ => w₀)
    (fun _ => hw₀) hne hw hlim
  have hE : eraseCarlsonVariable k (fun _ : ι => w₀) = fun _ => w₀ := rfl
  rw [hE, regCarlsonR_const_node _ _ hw₀, sum_eraseCarlsonParameter, ← hsum] at H
  exact H

/-- Theorem 8.3-2 when the remaining nodes are all equal to `w`, in the right half-plane:
`R_{-a}(b; w, …, zₖ, …, w)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ w^{-a}/Γ(c - bₖ)`. -/
theorem tendsto_regCarlsonR_update_zero_const [DecidableEq ι] (k : ι) {a a' : ℂ} {b : ι → ℂ}
    {w₀ : ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hw₀ : 0 < w₀.re)
    (hne : ∃ i, i ≠ k) {E : Type*} {l : Filter E} {w : E → ℂ}
    (hw : ∀ x, 0 < (w x).re) (hlim : Tendsto w l (𝓝 0)) :
    Tendsto (fun x => regCarlsonR (-a) b (Function.update (fun _ => w₀) k (w x))) l
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ * (w₀ ^ (-a) * (Gamma (a + a' - b k))⁻¹)))) := by
  convert tendsto_regCarlsonR_update_zero_const_classical k hsum hk hw₀ hne hw hlim

end Carlson
