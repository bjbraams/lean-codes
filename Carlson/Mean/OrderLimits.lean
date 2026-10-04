/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Properties
public import Dirichlet.Real.Support

/-!
# Infinite-order limits of hypergeometric means

For positive nodes and parameters the limit at positive infinite order is the
largest node, and the limit at negative infinite order is the smallest node.
Positive Dirichlet laws detect neighborhoods of every vertex,
even though the vertices themselves can have measure zero.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 3.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The hypergeometric mean tends to the largest node as its order tends to infinity. -/
theorem tendsto_carlsonMeanReal_order_atTop {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Tendsto (fun t : ℝ => carlsonMeanReal t b x) atTop (𝓝 (⨆ i, x i)) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
  have hmax : 0 < ⨆ i, x i := (hx (Classical.arbitrary ι)).trans_le (Finite.le_ciSup x _)
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨r, har, hr⟩ := exists_between (max_lt ha hmax)
    have hr0 : 0 < r := lt_of_le_of_lt (le_max_right a 0) har
    let S := {u : ι → ℝ | r < ∑ i, u i * x i}
    have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
    have hq0 : dirichletMeasure b S ≠ 0 := by
      intro hzero
      have he : ∀ᵐ u ∂dirichletMeasure b, ∑ i, u i * x i ≤ r := by
        simpa only [ae_iff, not_le] using hzero
      have hn := (ae_dirichlet_affine_le_iff hb r).mp he
      exact (not_le_of_gt hr) (ciSup_le hn)
    let q := (dirichletMeasure b).real S
    have hq : 0 < q := ENNReal.toReal_pos hq0 (measure_ne_top _ _)
    have hroot : Tendsto (fun t : ℝ => q ^ t⁻¹ * r) atTop (𝓝 r) := by
      have h := ((Real.continuousAt_const_rpow hq.ne').tendsto.comp
        tendsto_inv_atTop_zero).mul_const r
      simpa only [Real.rpow_zero, one_mul, Function.comp_def] using h
    filter_upwards [hroot.eventually (lt_mem_nhds (lt_of_le_of_lt (le_max_left a 0) har)),
      eventually_gt_atTop (0 : ℝ)] with t hat ht
    apply hat.trans_le
    have hpow : q * r ^ t ≤ carlsonRReal t b x := by
      calc
        _ = ∫ u in S, r ^ t ∂dirichletMeasure b := by
          simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply_univ, q]
        _ ≤ ∫ u in S, (∑ i, u i * x i) ^ t ∂dirichletMeasure b := by
          apply integral_mono_ae (integrable_const _) (integrable_carlsonRReal t hb hx).restrict
          filter_upwards [ae_restrict_mem hS] with u hu
          exact Real.rpow_le_rpow hr0.le hu.le ht.le
        _ ≤ carlsonRReal t b x :=
          setIntegral_le_integral (integrable_carlsonRReal t hb hx)
            ((ae_mem_stdSimplex_dirichletMeasure b).mono fun _ hu =>
              Real.rpow_nonneg (dirichlet_affine_mem (convex_Ioi 0) hx hu).le t)
    have h := Real.rpow_le_rpow (mul_pos hq (Real.rpow_pos_of_pos hr0 t)).le hpow
      (inv_pos.mpr ht).le
    simpa only [Real.mul_rpow hq.le (Real.rpow_pos_of_pos hr0 t).le,
      Real.rpow_rpow_inv hr0.le ht.ne', ← carlsonMeanReal_eq_rpow ht.ne' hb hx] using h
  · intro a ha
    exact Eventually.of_forall fun t =>
      ((carlsonMeanReal_bounds t hb (hx i) (fun j => hi.trans_le (Finite.ciInf_le x j)) (fun i => Finite.le_ciSup x i)).2).trans_lt ha

/-- The hypergeometric mean tends to the smallest node as its order tends to minus infinity. -/
theorem tendsto_carlsonMeanReal_order_atBot {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Tendsto (fun t : ℝ => carlsonMeanReal t b x) atBot (𝓝 (⨅ i, x i)) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
  have hmin : 0 < ⨅ i, x i := hi ▸ hx i
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le
      (carlsonMeanReal_bounds t hb hmin (fun j => Finite.ciInf_le x j)
        (fun j => Finite.le_ciSup x j)).1
  · intro a ha
    obtain ⟨r, hr, hra⟩ := exists_between ha
    have hr0 : 0 < r := hmin.trans hr
    let S := {u : ι → ℝ | (∑ i, u i * x i) < r}
    have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
    have hq0 : dirichletMeasure b S ≠ 0 := by
      intro hzero
      have he : ∀ᵐ u ∂dirichletMeasure b, r ≤ ∑ i, u i * x i := by
        simpa only [ae_iff, not_le] using hzero
      have hn := (ae_le_dirichlet_affine_iff hb r).mp he
      exact (not_le_of_gt hr) (le_ciInf hn)
    let q := (dirichletMeasure b).real S
    have hq : 0 < q := ENNReal.toReal_pos hq0 (measure_ne_top _ _)
    have hroot : Tendsto (fun t : ℝ => q ^ t⁻¹ * r) atBot (𝓝 r) := by
      have h := ((Real.continuousAt_const_rpow hq.ne').tendsto.comp
        tendsto_inv_atBot_zero).mul_const r
      simpa only [Real.rpow_zero, one_mul, Function.comp_def] using h
    filter_upwards [hroot.eventually (gt_mem_nhds hra),
      eventually_lt_atBot (0 : ℝ)] with t hat ht
    apply lt_of_le_of_lt _ hat
    have hpow : q * r ^ t ≤ carlsonRReal t b x := by
      calc
        _ = ∫ u in S, r ^ t ∂dirichletMeasure b := by
          simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply_univ, q]
        _ ≤ ∫ u in S, (∑ i, u i * x i) ^ t ∂dirichletMeasure b := by
          apply integral_mono_ae (integrable_const _) (integrable_carlsonRReal t hb hx).restrict
          filter_upwards [ae_restrict_mem hS,
            ae_restrict_of_ae (ae_mem_stdSimplex_dirichletMeasure b)] with u hu hu'
          exact Real.rpow_le_rpow_of_nonpos
            (dirichlet_affine_mem (convex_Ioi 0) hx hu') hu.le ht.le
        _ ≤ carlsonRReal t b x :=
          setIntegral_le_integral (integrable_carlsonRReal t hb hx)
            ((ae_mem_stdSimplex_dirichletMeasure b).mono fun _ hu =>
              Real.rpow_nonneg (dirichlet_affine_mem (convex_Ioi 0) hx hu).le t)
    have h := Real.rpow_le_rpow_of_nonpos (mul_pos hq (Real.rpow_pos_of_pos hr0 t)) hpow
      (inv_nonpos.mpr ht.le)
    simpa only [Real.mul_rpow hq.le (Real.rpow_pos_of_pos hr0 t).le,
      Real.rpow_rpow_inv hr0.le ht.ne, ← carlsonMeanReal_eq_rpow ht.ne hb hx] using h

end Carlson
