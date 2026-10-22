/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Inequalities
public import Dirichlet.Real.UniformConcentration

/-!
# Hypergeometric means of growing finite families

Brenner–Carlson (1987), Theorem 2 and (5.23)–(5.24). Both the finite index type
and the positive parameter weights may vary. Uniform bounds on the nodes and
divergence of the total parameter suffice; the normalized weights need not converge.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {α : Type*} {l : Filter α} [NeBot l] {κ : α → Type*}
  [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
  {b x : (n : α) → κ n → ℝ} {a A μ : ℝ}

/-- A limit of positive parameter-weighted node means stays in their common closed interval. -/
theorem weighted_node_mean_limit_mem_Icc (hb : ∀ n i, 0 < b n i)
    (hx : ∀ n i, x n i ∈ Icc a A)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ)) :
    μ ∈ Icc a A := by
  apply isClosed_Icc.mem_of_tendsto hm
  apply Eventually.of_forall
  intro n
  have hs : 0 < ∑ i, b n i :=
    Finset.sum_pos (fun i _ => hb n i) Finset.univ_nonempty
  apply dirichlet_affine_mem (convex_Icc a A) (hx n)
  exact ⟨fun i => (div_pos (hb n i) hs).le, by rw [← Finset.sum_div, div_self hs.ne']⟩

/-- **Brenner–Carlson (5.23).** Power averages converge for growing finite families. -/
theorem tendsto_carlsonRReal_varying (t : ℝ) (hb : ∀ n i, 0 < b n i)
    (ha : 0 < a) (hx : ∀ n i, x n i ∈ Icc a A)
    (hc : Tendsto (fun n => ∑ i, b n i) l atTop)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ)) :
    Tendsto (fun n => carlsonRReal t (b n) (x n)) l (𝓝 (μ ^ t)) := by
  apply tendsto_integral_dirichletMeasure_affine_varying hb hx hc hm _
    (weighted_node_mean_limit_mem_Icc hb hx hm)
  exact ContDiffOn.rpow_const_of_ne contDiffOn_id
    (fun y hy => (ha.trans_le hy.1).ne')

/-- **Brenner–Carlson (5.24).** Power-logarithm averages have the same growing-family limit. -/
theorem tendsto_carlsonLReal_varying (t : ℝ) (hb : ∀ n i, 0 < b n i)
    (ha : 0 < a) (hx : ∀ n i, x n i ∈ Icc a A)
    (hc : Tendsto (fun n => ∑ i, b n i) l atTop)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ)) :
    Tendsto (fun n => carlsonLReal t (b n) (x n)) l (𝓝 (μ ^ t * Real.log μ)) := by
  apply tendsto_integral_dirichletMeasure_affine_varying hb hx hc hm _
    (weighted_node_mean_limit_mem_Icc hb hx hm)
  have hp : ContDiffOn ℝ 1 (fun y : ℝ => y ^ t) (Icc a A) :=
    ContDiffOn.rpow_const_of_ne contDiffOn_id (fun y hy => (ha.trans_le hy.1).ne')
  exact hp.mul (ContDiffOn.log contDiffOn_id (fun y hy => (ha.trans_le hy.1).ne'))

/-- **Brenner–Carlson Theorem 2 (1987).** Every fixed real-order hypergeometric
mean tends to the limiting weighted arithmetic mean, even with varying dimension. -/
theorem tendsto_carlsonMeanReal_varying (t : ℝ) (hb : ∀ n i, 0 < b n i)
    (ha : 0 < a) (hx : ∀ n i, x n i ∈ Icc a A)
    (hc : Tendsto (fun n => ∑ i, b n i) l atTop)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ)) :
    Tendsto (fun n => carlsonMeanReal t (b n) (x n)) l (𝓝 μ) := by
  have hμ : 0 < μ := ha.trans_le (weighted_node_mean_limit_mem_Icc hb hx hm).1
  by_cases ht : t = 0
  · subst t
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_carlsonLReal_varying 0 hb ha hx hc hm)
    simpa only [Real.rpow_zero, one_mul, Real.exp_log hμ, carlsonMeanReal, ↓reduceIte,
      Function.comp_def] using h
  · have h := (Real.continuousAt_rpow_const _ t⁻¹
        (Or.inl (Real.rpow_pos_of_pos hμ t).ne')).tendsto.comp
      (tendsto_carlsonRReal_varying t hb ha hx hc hm)
    rw [Real.rpow_rpow_inv hμ.le ht] at h
    exact h.congr (fun n =>
      (carlsonMeanReal_eq_rpow ht (hb n) (fun i => ha.trans_le (hx n i).1)).symm)

/-- Ratio means, including their coincident-order values, have the same growing-family limit. -/
theorem tendsto_carlsonRatioMeanReal_varying (s t : ℝ) (hb : ∀ n i, 0 < b n i)
    (ha : 0 < a) (hx : ∀ n i, x n i ∈ Icc a A)
    (hc : Tendsto (fun n => ∑ i, b n i) l atTop)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ)) :
    Tendsto (fun n => carlsonRatioMeanReal s t (b n) (x n)) l (𝓝 μ) := by
  have hμ : 0 < μ := ha.trans_le (weighted_node_mean_limit_mem_Icc hb hx hm).1
  have hR r := tendsto_carlsonRReal_varying r hb ha hx hc hm
  have hL r := tendsto_carlsonLReal_varying r hb ha hx hc hm
  by_cases hst : s = t
  · subst s
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      ((hL t).div (hR t) (Real.rpow_pos_of_pos hμ t).ne')
    simpa [carlsonRatioMeanReal, Real.exp_log hμ,
      mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hμ t).ne', Function.comp_def] using h
  · have h := Real.continuous_exp.continuousAt.tendsto.comp
      (((hR t).log (Real.rpow_pos_of_pos hμ t).ne').sub
        ((hR s).log (Real.rpow_pos_of_pos hμ s).ne') |>.div_const (t - s))
    have he : (Real.log (μ ^ t) - Real.log (μ ^ s)) / (t - s) = Real.log μ := by
      rw [Real.log_rpow hμ, Real.log_rpow hμ]
      field_simp
    simpa only [he, Real.exp_log hμ, carlsonRatioMeanReal, hst, ↓reduceIte,
      Function.comp_def] using h

end Carlson
