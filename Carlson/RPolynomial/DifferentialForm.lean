/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.GeneratingIdentities
public import Mathlib.Analysis.Complex.TaylorSeries
public import Carlson.RPolynomial.Growth

/-!
# R-polynomials as directional derivatives (Exercise 7.8-6)

Along the diagonal direction `D = ∑ ∂/∂zᵢ`, the derivatives of `∏ zⱼ^{-bⱼ}` are the generating
relation 6.6-1 in the reciprocal nodes: `Dⁿ ∏ zⱼ^{-bⱼ} = (-1)ⁿ (∏ zⱼ^{-bⱼ}) Nₙ(b; z⁻¹)`.

## Main results

* `Carlson.iteratedDeriv_prod_add_cpow`: Exercise 7.8-6.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.8.
-/

open Complex Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- `(z w)^a = z^a w^a` when `|arg z| + |arg w| < π`. -/
theorem mul_cpow_of_abs_arg_add_lt' {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h : |arg z| + |arg w| < Real.pi) (a : ℂ) : (z * w) ^ a = z ^ a * w ^ a := by
  have hlog : log (z * w) = log z + log w := (log_mul_eq_add_log_iff hz hw).mpr
    ⟨by linarith [neg_abs_le (arg z), neg_abs_le (arg w)],
      by linarith [le_abs_self (arg z), le_abs_self (arg w)]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero hz hw), cpow_def_of_ne_zero hz, cpow_def_of_ne_zero hw,
    hlog, add_mul, exp_add]

/-- Near `t = 0` the shifted powers split: `(zᵢ + t)^{-bᵢ} = zᵢ^{-bᵢ} (1 + t/zᵢ)^{-bᵢ}`, and the
generating series in the nodes `-1/zᵢ` converges. -/
theorem eventually_prod_add_cpow (b z : ι → ℂ) (hz : ∀ i, z i ∈ slitPlane) :
    ∀ᶠ t in 𝓝 (0 : ℂ), (∀ i, ‖t * (-(z i)⁻¹)‖ < 1) ∧
      ∏ i, (z i + t) ^ (-b i) = (∏ i, z i ^ (-b i)) *
        carlsonRGeneratingKernel b (fun i => -(z i)⁻¹) t := by
  have hz0 : ∀ i, z i ≠ 0 := fun i => slitPlane_ne_zero (hz i)
  have hlt : ∀ i, |arg (z i)| < Real.pi := fun i => by
    rw [abs_lt]
    exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp (hz i)).1⟩
  have hev : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), ‖t * (-(z i)⁻¹)‖ < 1 ∧
      |arg (1 + t / z i)| < Real.pi - |arg (z i)| := fun i => by
    have hc : Continuous fun t : ℂ => t * (-(z i)⁻¹) := by fun_prop
    have h1 := (hc.tendsto 0).norm.eventually (gt_mem_nhds (by simp : ‖(0 : ℂ) * _‖ < 1))
    have hc2 : ContinuousAt (fun t : ℂ => arg (1 + t / z i)) 0 := by
      refine (continuousAt_arg (by simp)).comp (f := fun t : ℂ => 1 + t / z i) ?_
      fun_prop
    have h2 := hc2.abs.tendsto.eventually (gt_mem_nhds (show |arg (1 + 0 / z i)| <
      Real.pi - |arg (z i)| by simp; linarith [hlt i]))
    exact h1.and h2
  filter_upwards [eventually_all.mpr hev] with t ht
  refine ⟨fun i => (ht i).1, ?_⟩
  rw [carlsonRGeneratingKernel, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hu : 1 + t / z i ≠ 0 := by
    intro h0
    have := (ht i).1
    rw [norm_mul, norm_neg, norm_inv] at this
    have ht' : t = -z i := by field_simp [hz0 i] at h0; linear_combination h0
    rw [ht', norm_neg, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz0 i))] at this
    exact lt_irrefl _ this
  have hsplit : z i + t = z i * (1 + t / z i) := by have := hz0 i; field_simp
  rw [hsplit, mul_cpow_of_abs_arg_add_lt' (hz0 i) hu (by linarith [(ht i).2]),
    show 1 - t * -(z i)⁻¹ = 1 + t / z i by ring, cpow_neg (1 + t / z i), one_div]

/-- **Exercise 7.8-6**, with `D = ∑ ∂/∂zᵢ` written as `d/dt` along the diagonal:
`Dⁿ ∏ zⱼ^{-bⱼ} = (-1)ⁿ (∏ zⱼ^{-bⱼ}) Nₙ(b; z⁻¹)` for nodes in the slit plane, that is,
`(c)ₙ Rₙ(b, z⁻¹) = (-1)ⁿ ∏ zᵢ^{bᵢ} Dⁿ ∏ zⱼ^{-bⱼ}`. -/
theorem iteratedDeriv_prod_add_cpow (n : ℕ) (b z : ι → ℂ) (hz : ∀ i, z i ∈ slitPlane) :
    iteratedDeriv n (fun t => ∏ i, (z i + t) ^ (-b i)) 0 =
      (-1) ^ n * (∏ i, z i ^ (-b i)) * carlsonRPolynomialNumerator n b (fun i => (z i)⁻¹) := by
  set F : ℂ → ℂ := fun t => ∏ i, (z i + t) ^ (-b i)
  set P : ℂ := ∏ i, z i ^ (-b i)
  -- a ball on which `F` is holomorphic
  have hopen : IsOpen {t : ℂ | ∀ i, z i + t ∈ slitPlane} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_slitPlane.preimage (continuous_const.add continuous_id)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 (fun i => by simpa using hz i)
  have hF : DifferentiableOn ℂ F (Metric.ball 0 r) := by
    intro t ht
    refine (DifferentiableAt.differentiableWithinAt ?_)
    simp only [F]
    refine DifferentiableAt.fun_finsetProd (𝕜 := ℂ) (u := univ)
      (f := fun i t => (z i + t) ^ (-b i)) fun i _ => ?_
    exact ((differentiableAt_const _).add differentiableAt_id).cpow (differentiableAt_const _)
      (hball ht i)
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp (eventually_prod_add_cpow b z hz)
  set ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have ha : ∀ t : ℂ, ‖t‖ < ε → HasSum (fun m => iteratedDeriv m F 0 / (m.factorial : ℂ) * t ^ m)
      (F t) := fun t ht => by
    have h := Complex.hasSum_taylorSeries_on_ball hF
      (show t ∈ Metric.ball 0 r by simpa using ht.trans_le (min_le_left _ _))
    refine h.congr_fun fun m => ?_
    simp only [sub_zero, smul_eq_mul]; ring
  have hb : ∀ t : ℂ, ‖t‖ < ε → HasSum (fun m => P * (carlsonRPolynomialNumerator m b
      (fun i => -(z i)⁻¹) / (m.factorial : ℂ)) * t ^ m) (F t) := fun t ht => by
    obtain ⟨hconv, hsplit⟩ := hδev (show dist t 0 < δ by
      simpa using ht.trans_le (min_le_right _ _))
    have h := (hasSum_carlsonRPolynomialNumerator_div_factorial b (fun i => -(z i)⁻¹) t
      hconv).mul_left P
    simp only [F]
    rw [hsplit]
    refine h.congr_fun fun m => ?_
    ring
  have hcoeff := congrFun (coeff_eq_of_hasSum_pow hε ha hb) n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_eq_iff hf] at hcoeff
  rw [hcoeff]
  have hneg := carlsonRPolynomialNumerator_smul n b (fun i => (z i)⁻¹) (-1)
  simp only [neg_one_mul] at hneg
  rw [hneg]
  field_simp

end Carlson
