/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SmallVariableContinuation

/-!
# The joint small-variable limit

Carlson's Theorems 8.3-1 and 8.3-2 describe `R_{-a}(b; z)` as one node `zₖ` tends to `0`, with
the other nodes fixed. This module proves the joint version: the other nodes may converge too.
If `z → z⁰` through the right half-plane, where `z⁰ₖ = 0` and the other `z⁰ⱼ` have positive real
part, then for `re (a' - bₖ) > 0`
`R_{-a}(b; z)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ R_{-a}(b without k; z⁰ without k)/Γ(c - bₖ)`.

The proof follows the one-variable proofs.
* For `re a, re a' > 0`, dominated convergence applies to the unit-interval representation
  (6.8-6). The product over the other nodes is bounded uniformly on a compact neighbourhood.
* The recurrence 8.3(5) and induction remove the restrictions on `a` and `a'`, and the identity
  theorem in the parameters identifies the limit.

This is the continuity of `R` at a point where one variable vanishes, which Carlson uses
throughout Chapter 9.

## Main results

* `Carlson.tendsto_regCarlsonR_nhdsWithin_zero_of_pos`: the joint Theorem 8.3-1.
* `Carlson.tendsto_regCarlsonR_nhdsWithin_zero`: the joint Theorem 8.3-2.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Dirichlet Complex Filter MeasureTheory Set
open scoped Topology Classical
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- The joint approach domain: `zₖ` in the closed and the other nodes in the open right
half-plane. -/
def smallVariableJointDomain (k : ι) : Set (ι → ℂ) :=
  {z | 0 ≤ (z k).re ∧ ∀ j, j ≠ k → 0 < (z j).re}

omit [Fintype ι] in
theorem carlsonRVariableDomain_subset_smallVariableJointDomain (k : ι) :
    carlsonRVariableDomain ⊆ smallVariableJointDomain (ι := ι) k :=
  fun _ hz => ⟨(hz k).le, fun j _ => hz j⟩

/-- The unit-interval integrand with the factor of the node `k` separated. -/
private def jointKernel (k : ι) (a a' : ℂ) (b z : ι → ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
    (((1 - u : ℂ) + (u : ℂ) * z k) ^ (-b k) *
      ∏ j : {j // j ≠ k}, ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j))

private theorem integral_jointKernel (k : ι) (a a' : ℂ) (b z : ι → ℂ) :
    (∫ u in Ioo (0 : ℝ) 1, jointKernel k a a' b z u) = carlsonRUnitIntervalIntegral a a' b z := by
  apply integral_congr_ae
  filter_upwards with u
  simp only [jointKernel]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]

private theorem integral_jointKernel_zero (k : ι) (a a' : ℂ) (b z : ι → ℂ) (hz : z k = 0) :
    (∫ u in Ioo (0 : ℝ) 1, jointKernel k a a' b z u) =
      carlsonRUnitIntervalIntegral a (a' - b k)
        (eraseCarlsonParameter k b) (eraseCarlsonVariable k z) := by
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  simp only [jointKernel, eraseCarlsonParameter, eraseCarlsonVariable, hz, mul_zero, add_zero]
  have hne : (1 - u : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hu.2).ne'
  rw [← mul_assoc, mul_assoc ((u : ℂ) ^ (a - 1)), ← cpow_add _ _ hne,
    show a' - 1 + -b k = a' - b k - 1 by ring]

/-- **Joint continuity of the unit-interval integral** as the node `k` tends to `0`. -/
theorem tendsto_unitIntervalIntegral_nhdsWithin_zero (k : ι) {a a' : ℂ} {b z₀ : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hak : 0 < (a' - b k).re) (hz₀ : z₀ k = 0)
    (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re) :
    Tendsto (fun z => carlsonRUnitIntervalIntegral a a' b z)
      (𝓝[smallVariableJointDomain k] z₀)
      (𝓝 (carlsonRUnitIntervalIntegral a (a' - b k)
        (eraseCarlsonParameter k b) (eraseCarlsonVariable k z₀))) := by
  set F := 𝓝[smallVariableJointDomain k] z₀
  -- a compact neighbourhood of the other nodes
  set K : Set ({j // j ≠ k} → ℂ) :=
    Set.pi univ fun j => Metric.closedBall (z₀ j) ((z₀ j).re / 2)
  have hK : IsCompact K := isCompact_univ_pi fun j => isCompact_closedBall _ _
  have hKre : ∀ w ∈ K, ∀ j : {j // j ≠ k}, (z₀ j).re / 2 ≤ (w j).re := by
    intro w hw j
    have h := hw j (mem_univ _)
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    have := abs_re_le_norm (w j - z₀ j)
    rw [sub_re, abs_le] at this
    linarith
  have hP : ContinuousOn (fun p : ℝ × ({j // j ≠ k} → ℂ) => ∏ j : {j // j ≠ k},
      ((1 - p.1 : ℂ) + (p.1 : ℂ) * p.2 j) ^ (-b j)) (Icc 0 1 ×ˢ K) := by
    apply continuousOn_finsetProd
    intro j _
    have hc : Continuous fun p : ℝ × ({j // j ≠ k} → ℂ) => (1 - p.1 : ℂ) + (p.1 : ℂ) * p.2 j := by
      fun_prop
    refine hc.continuousOn.cpow_const fun p hp => segment_mem_slitPlane hp.1 ?_
    have := hKre p.2 hp.2 j
    have := hz₀' j.1 j.2
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hP
  set E := Real.exp (Real.pi * |(b k).im|)
  set B := fun u : ℝ => ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - b k - 1)‖
  set W := fun u : ℝ => ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)‖
  set D : ℝ := 2 ^ (-(b k).re)
  have hFint : ∀ᶠ z in F, AEStronglyMeasurable (jointKernel k a a' b z)
      (volume.restrict (Ioo 0 1)) := by
    filter_upwards with z
    apply Measurable.aestronglyMeasurable
    unfold jointKernel
    fun_prop
  have hnear : ∀ᶠ z in F, ‖z k‖ < 1 ∧ (fun j : {j // j ≠ k} => z j) ∈ K := by
    have hc : Continuous fun z : ι → ℂ => (fun j : {j // j ≠ k} => z j) := by fun_prop
    have h1 : ∀ᶠ z in 𝓝 z₀, ‖z k‖ < 1 := by
      have : Tendsto (fun z : ι → ℂ => ‖z k‖) (𝓝 z₀) (𝓝 ‖z₀ k‖) :=
        ((continuous_apply k).tendsto z₀).norm
      rw [hz₀, norm_zero] at this
      exact this.eventually (eventually_lt_nhds one_pos)
    have h2 : ∀ᶠ z in 𝓝 z₀, (fun j : {j // j ≠ k} => z j) ∈ K := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      refine set_pi_mem_nhds finite_univ fun j _ => Metric.closedBall_mem_nhds _ ?_
      have := hz₀' j.1 j.2
      linarith
    exact nhdsWithin_le_nhds (h1.and h2)
  have hbound : ∀ᶠ z in F, ∀ᵐ u ∂(volume.restrict (Ioo 0 1)),
      ‖jointKernel k a a' b z u‖ ≤ (B u + W u * D) * (E * max C 0) := by
    filter_upwards [self_mem_nhdsWithin, hnear] with z hz hzn
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
    have hp : ‖((1 - u : ℂ) + (u : ℂ) * z k) ^ (-b k)‖ ≤ ((1 - u) ^ (-(b k).re) + D) * E :=
      norm_segment_cpow_le hu hz.1 hzn.1 (b k)
    have hq : ‖∏ j : {j // j ≠ k}, ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)‖ ≤ max C 0 :=
      (hC (u, fun j => z j) ⟨⟨hu.1.le, hu.2.le⟩, hzn.2⟩).trans (le_max_left _ _)
    calc
      ‖jointKernel k a a' b z u‖ = W u *
          (‖((1 - u : ℂ) + (u : ℂ) * z k) ^ (-b k)‖ *
            ‖∏ j : {j // j ≠ k}, ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)‖) := by
        simp only [jointKernel, W, norm_mul]
      _ ≤ W u * ((((1 - u) ^ (-(b k).re) + D) * E) * max C 0) := by
        gcongr
      _ = _ := by
        have hb' : W u * (1 - u) ^ (-(b k).re) = B u := norm_betaKernel_mul_rpow hu1 a a' (b k)
        rw [← mul_assoc, ← mul_assoc, mul_add, hb']
        ring
  have hBint : Integrable (fun u => (B u + W u * D) * (E * max C 0))
      (volume.restrict (Ioo 0 1)) := by
    exact (((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent ha hak).norm).add
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegral_convergent ha ha').norm).mul_const D)).mul_const _
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioo 0 1)),
      Tendsto (fun z => jointKernel k a a' b z u) F (𝓝 (jointKernel k a a' b z₀ u)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    have hcomp : ∀ j : ι, (1 - u : ℂ) + (u : ℂ) * z₀ j ∈ slitPlane →
        ContinuousAt (fun z : ι → ℂ => ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) z₀ := by
      intro j hj
      have hc : ContinuousAt (fun z : ι → ℂ => (1 - u : ℂ) + (u : ℂ) * z j) z₀ :=
        (continuous_const.add (continuous_const.mul (continuous_apply j))).continuousAt
      exact (continuousAt_cpow_const hj).comp_of_eq hc rfl
    have hk : ContinuousAt (fun z : ι → ℂ => ((1 - u : ℂ) + (u : ℂ) * z k) ^ (-b k)) z₀ := by
      refine hcomp k ?_
      rw [hz₀, mul_zero, add_zero, show (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (sub_pos.mpr hu.2)
    have hprod : ContinuousAt (fun z : ι → ℂ =>
        ∏ j : {j // j ≠ k}, ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) z₀ := by
      refine tendsto_finsetProd _ fun j _ => hcomp j ?_
      exact segment_mem_slitPlane ⟨hu.1.le, hu.2.le⟩ (hz₀' j.1 j.2)
    have H : ContinuousAt (fun z => jointKernel k a a' b z u) z₀ := by
      unfold jointKernel
      exact continuousAt_const.mul (hk.mul hprod)
    exact H.tendsto.mono_left nhdsWithin_le_nhds
  have H := tendsto_integral_filter_of_dominated_convergence _ hFint hbound hBint hlim
  rw [integral_jointKernel_zero k a a' b z₀ hz₀] at H
  simpa only [integral_jointKernel] using H

/-- The joint Theorem 8.3-1 with the classical decidability instances. -/
private theorem tendsto_regCarlsonR_nhdsWithin_zero_of_pos_classical
    (k : ι) {a a' : ℂ} {b z₀ : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hak : 0 < (a' - b k).re) (hsum : a + a' = ∑ j, b j)
    (hz₀ : z₀ k = 0) (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re) :
    Tendsto (regCarlsonR (-a) b) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (Gamma (a' - b k) / Gamma a' *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z₀))) := by
  have H := (tendsto_unitIntervalIntegral_nhdsWithin_zero k ha ha' hak hz₀ hz₀').mono_left
    (nhdsWithin_mono _ (carlsonRVariableDomain_subset_smallVariableJointDomain k))
  have hs : a + (a' - b k) = ∑ j : {j // j ≠ k}, eraseCarlsonParameter k b j := by
    rw [sum_eraseCarlsonParameter, ← hsum]; ring
  have hz' : eraseCarlsonVariable k z₀ ∈ carlsonRSlitDomain := fun j =>
    carlsonRightHalfPlane_subset_slitPlane (hz₀' j.1 j.2)
  rw [carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR ha hak hs hz'] at H
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGa' := Gamma_ne_zero_of_re_pos ha'
  have H' := H.const_mul ((Gamma a * Gamma a')⁻¹)
  have hval : (Gamma a * Gamma a')⁻¹ *
      ((Gamma a * Gamma (a' - b k)) * regCarlsonR (-a) (eraseCarlsonParameter k b)
          (eraseCarlsonVariable k z₀)) =
      Gamma (a' - b k) / Gamma a' * regCarlsonR (-a) (eraseCarlsonParameter k b)
          (eraseCarlsonVariable k z₀) := by field_simp
  rw [hval] at H'
  apply H'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR ha ha' hsum
      (carlsonRVariableDomain_subset_slitDomain hz)]
  field_simp

/-- **The joint Theorem 8.3-1**: for `re a, re a', re (a' - bₖ) > 0`, as `z → z⁰` through the
right half-plane, where `z⁰ₖ = 0` and the other `z⁰ⱼ` lie in the right half-plane,
`R_{-a}(b; z)/Γ(c) → Γ(a' - bₖ)/Γ(a') R_{-a}(b without k; z⁰ without k)/Γ(c - bₖ)`. -/
theorem tendsto_regCarlsonR_nhdsWithin_zero_of_pos [DecidableEq ι] (k : ι) {a a' : ℂ}
    {b z₀ : ι → ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re) (hak : 0 < (a' - b k).re)
    (hsum : a + a' = ∑ j, b j) (hz₀ : z₀ k = 0) (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re) :
    Tendsto (regCarlsonR (-a) b) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (Gamma (a' - b k) / Gamma a' *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z₀))) := by
  convert tendsto_regCarlsonR_nhdsWithin_zero_of_pos_classical k ha ha' hak hsum hz₀ hz₀'

/-! ### Removing the restrictions on the endpoint exponents -/

section Induction

variable (k : ι) {z₀ : ι → ℂ} (hz₀ : z₀ k = 0) (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re)
include hz₀ hz₀'

private theorem joint_zero {p : ℂ × (ι → ℂ)} (hp : p ∈ smallVariableRegion k 0) :
    Tendsto (regCarlsonR (-p.1) p.2) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (smallVariableValue k z₀ p)) := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [Nat.cast_zero, add_zero] at h1 h2
  have H := tendsto_regCarlsonR_nhdsWithin_zero_of_pos_classical k (a := p.1)
      (a' := ∑ j, p.2 j - p.1)
    (b := p.2) h1 h2 h3 (by ring) hz₀ hz₀'
  rw [smallVariableValue]
  rw [div_eq_mul_inv, mul_assoc] at H
  exact H

private theorem joint_step (i : ι) (hik : i ≠ k) (n : ℕ)
    (hIH : ∀ p ∈ smallVariableRegion k n,
      Tendsto (regCarlsonR (-p.1) p.2) (𝓝[carlsonRVariableDomain] z₀)
        (𝓝 (smallVariableValue k z₀ p)))
    {p : ℂ × (ι → ℂ)} (hp : p ∈ smallVariableRegion k (n + 1)) :
    Tendsto (regCarlsonR (-p.1) p.2) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (smallVariableStepValue k i z₀ p)) := by
  have hrec : ∀ z ∈ carlsonRVariableDomain, regCarlsonR (-p.1) p.2 z =
      ∑ j, addDirichletUnit p.2 i j * ((∑ l, p.2 l - p.1) * z j + p.1 * z i) *
        regCarlsonR (-(p.1 + 1)) (addDirichletUnit (addDirichletUnit p.2 i) j) z := by
    intro z hz
    rw [regCarlsonR_eq_sum_double_shift (-p.1) p.2 (carlsonRVariableDomain_subset_slitDomain hz) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -p.1 - 1 = -(p.1 + 1) by ring]
    ring
  have hupd : Function.update z₀ k 0 = z₀ := by
    rw [← hz₀]; exact Function.update_eq_self k z₀
  have hev : regCarlsonR (-p.1) p.2 =ᶠ[𝓝[carlsonRVariableDomain] z₀] fun z =>
      ∑ j, addDirichletUnit p.2 i j * ((∑ l, p.2 l - p.1) * z j + p.1 * z i) *
        regCarlsonR (-(p.1 + 1)) (addDirichletUnit (addDirichletUnit p.2 i) j) z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hrec z hz
  refine Tendsto.congr' hev.symm ?_
  unfold smallVariableStepValue
  rw [hupd]
  refine tendsto_finsetSum _ fun j _ => ?_
  refine Tendsto.mul (Tendsto.const_mul _ ?_) (hIH _ ?_)
  · exact ((((continuous_apply j).tendsto z₀).const_mul _).add
      (((continuous_apply i).tendsto z₀).const_mul _)).mono_left nhdsWithin_le_nhds
  · -- the double shift maps region `n + 1` into region `n`
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

omit hz₀ hz₀' in
private theorem region_zero_subset' (n : ℕ) :
    smallVariableRegion k 0 ⊆ smallVariableRegion k n := by
  rintro p ⟨h1, h2, h3⟩
  simp only [Nat.cast_zero, add_zero] at h1 h2
  refine ⟨?_, ?_, h3⟩ <;> simp only [add_re, natCast_re] <;>
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

omit [Fintype ι] in
private theorem nhdsWithin_neBot : (𝓝[carlsonRVariableDomain] z₀).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  refine mem_closure_of_tendsto (f := fun n : ℕ => Function.update z₀ k ((n : ℂ) + 1)⁻¹)
    (b := atTop) ?_ (Eventually.of_forall fun n => ?_)
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    simp only [one_div] at h
    have hc : Continuous fun v : ℂ => Function.update z₀ k v := by
      refine continuous_pi fun j => ?_
      by_cases hjk : j = k
      · subst hjk; simp only [Function.update_self]; exact continuous_id
      · simpa [Function.update_of_ne hjk] using continuous_const
    have := (hc.tendsto 0).comp h
    have e : Function.update z₀ k 0 = z₀ := by rw [← hz₀]; exact Function.update_eq_self k z₀
    rw [e] at this
    exact this
  · intro j
    by_cases hjk : j = k
    · subst hjk
      simp only [Function.update_self, carlsonRightHalfPlane, mem_ofPred_eq]
      rw [show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_inv, ofReal_re]
      positivity
    · rw [Function.update_of_ne hjk]; exact hz₀' j hjk

private theorem joint_region (i : ι) (hik : i ≠ k) (n : ℕ) :
    ∀ p ∈ smallVariableRegion k n,
      Tendsto (regCarlsonR (-p.1) p.2) (𝓝[carlsonRVariableDomain] z₀)
        (𝓝 (smallVariableValue k z₀ p)) := by
  have hz' : eraseCarlsonVariable k z₀ ∈ carlsonRSlitDomain := fun j =>
    carlsonRightHalfPlane_subset_slitPlane (hz₀' j.1 j.2)
  have := nhdsWithin_neBot k hz₀ hz₀'
  induction n with
  | zero => exact fun p hp => joint_zero k hz₀ hz₀' hp
  | succ n ih =>
    intro p hp
    have hstep := joint_step k hz₀ hz₀' i hik n ih hp
    suffices h : smallVariableStepValue k i z₀ p = smallVariableValue k z₀ p by rwa [← h]
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Fintype.one_lt_card_iff.mpr ⟨i, k, hik⟩
    set p₀ : ℂ × (ι → ℂ) := (1, fun _ => 2)
    have hp₀ : p₀ ∈ smallVariableRegion k 0 := by
      refine ⟨by simp [p₀], ?_, ?_⟩ <;> simp [p₀, Finset.sum_const] <;> linarith
    have hF : AnalyticOnNhd ℂ (smallVariableStepValue k i z₀) (smallVariableRegion k (n + 1)) :=
      fun q hq => analyticAt_smallVariableStepValue k i hik hz' n hq
    have hG : AnalyticOnNhd ℂ (smallVariableValue k z₀) (smallVariableRegion k (n + 1)) :=
      fun q hq => analyticAt_smallVariableValue k hz' hq.2.2
    refine hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_smallVariableRegion k (n + 1)).isPreconnected
      (region_zero_subset' k _ hp₀) ?_ hp
    filter_upwards [(isOpen_smallVariableRegion k 0).mem_nhds hp₀] with q hq
    exact tendsto_nhds_unique
      (joint_step k hz₀ hz₀' i hik n ih (region_zero_subset' k _ hq))
      (joint_zero k hz₀ hz₀' hq)

end Induction

/-- The joint Theorem 8.3-2 with the classical decidability instances. -/
private theorem tendsto_regCarlsonR_nhdsWithin_zero_classical (k : ι) {a a' : ℂ} {b z₀ : ι → ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hz₀ : z₀ k = 0)
    (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re) (hne : ∃ i, i ≠ k) :
    Tendsto (regCarlsonR (-a) b) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z₀)))) := by
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
  have H := joint_region k hz₀ hz₀' i hik n _ hp
  simp only [smallVariableValue, ha'] at H
  exact H

/-- **The joint Theorem 8.3-2**: if `re (a' - bₖ) > 0`, where `a + a' = ∑ bⱼ`, then as `z → z⁰`
through the right half-plane, where `z⁰ₖ = 0` and the other `z⁰ⱼ` lie in the right half-plane,
`R_{-a}(b; z)/Γ(c) → Γ(a' - bₖ) Γ(a')⁻¹ R_{-a}(b without k; z⁰ without k)/Γ(c - bₖ)`,
for all complex `a` and `b`. -/
theorem tendsto_regCarlsonR_nhdsWithin_zero [DecidableEq ι] (k : ι) {a a' : ℂ} {b z₀ : ι → ℂ}
    (hsum : a + a' = ∑ j, b j) (hk : 0 < (a' - b k).re) (hz₀ : z₀ k = 0)
    (hz₀' : ∀ j, j ≠ k → 0 < (z₀ j).re) (hne : ∃ i, i ≠ k) :
    Tendsto (regCarlsonR (-a) b) (𝓝[carlsonRVariableDomain] z₀)
      (𝓝 (Gamma (a' - b k) * ((Gamma a')⁻¹ *
        regCarlsonR (-a) (eraseCarlsonParameter k b) (eraseCarlsonVariable k z₀)))) := by
  convert tendsto_regCarlsonR_nhdsWithin_zero_classical k hsum hk hz₀ hz₀' hne

end Carlson
