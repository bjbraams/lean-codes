/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.Gamma
public import ToMathlib.Analysis.SpecialFunctions.Bessel
public import SeveralComplexVariables.LocallyUniform

/-!
# Joint entire dependence of the regularized zero-F-one function

Carlson (1977), Exercise 6.9-19: the series `∑ zⁿ / (n! Γ(c+n))` is jointly
entire in `c` and `z`, including nonpositive integral `c`. Compact-uniform bounds
for shifted reciprocal Gamma give normal convergence directly, without division
by the Gamma factors appearing in the quadratic S-function identification.
-/

open Complex Set

public noncomputable section

namespace Carlson.TwoVariable

/-- Reciprocal Gamma is bounded uniformly over a compact base set and all natural shifts. -/
private theorem bounded_inv_Gamma_shifts {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ n : ℕ, ‖(Gamma (c + n))⁻¹‖ ≤ C := by
  obtain ⟨m, C, hC, hbound⟩ := exists_uniform_norm_inv_Gamma_add_nat hK
  have hsmall (j : Fin m) : ∃ D : ℝ, ∀ c ∈ K, ‖(Gamma (c + (j : ℕ)))⁻¹‖ ≤ D :=
    hK.exists_bound_of_continuousOn
      ((differentiable_one_div_Gamma.continuous.comp
        (continuous_id.add continuous_const)).continuousOn)
  choose D hD using hsmall
  refine ⟨C + ∑ j : Fin m, max (D j) 0, by positivity, ?_⟩
  intro c hc n
  by_cases hn : n < m
  · calc
      ‖(Gamma (c + n))⁻¹‖ ≤ D ⟨n, hn⟩ := hD ⟨n, hn⟩ c hc
      _ ≤ max (D ⟨n, hn⟩) 0 := le_max_left _ _
      _ ≤ ∑ j : Fin m, max (D j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ _)
      _ ≤ C + ∑ j : Fin m, max (D j) 0 := le_add_of_nonneg_left hC
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    subst n
    have hfact : (1 : ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
    have h := (hbound c hc k).trans (div_le_self hC hfact)
    have he : c + ((m + k : ℕ) : ℂ) = c + ((k : ℂ) + m) := by push_cast; ring
    have h' : ‖(Gamma (c + ((m + k : ℕ) : ℂ)))⁻¹‖ ≤ C := by rw [he]; exact h
    exact h'.trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_right _ _))

/-- The defining `₀F₁` series converges locally uniformly jointly in its parameter and argument. -/
theorem hasSumLocallyUniformlyOn_zeroFOne_joint :
    HasSumLocallyUniformlyOn
      (fun n : ℕ => fun p : Fin 2 → ℂ =>
        p 1 ^ n / (n.factorial * Gamma (p 0 + n)))
      (fun p : Fin 2 → ℂ => regularizedHGFun 0 {p 0} (p 1)) univ := by
  have hs : SummableLocallyUniformlyOn
      (fun n : ℕ => fun p : Fin 2 → ℂ =>
        p 1 ^ n / (n.factorial * Gamma (p 0 + n))) univ := by
    apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
    intro K hKU hK
    obtain ⟨C, hC, hbound⟩ := bounded_inv_Gamma_shifts (hK.image (continuous_apply 0))
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_apply 1).continuousOn
    refine ⟨fun n => C * (max R 0) ^ n / n.factorial,
      by simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial (max R 0)).mul_left C,
      ?_⟩
    intro n p hp
    have hb := hbound (p 0) (mem_image_of_mem _ hp) n
    have hz : ‖p 1‖ ≤ max R 0 := (hR p hp).trans (le_max_left _ _)
    rw [div_mul_eq_div_mul_one_div, one_div, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    calc
      ‖p 1‖ ^ n / n.factorial * ‖(Gamma (p 0 + n))⁻¹‖ ≤
          (max R 0) ^ n / n.factorial * C := by gcongr
      _ = C * (max R 0) ^ n / n.factorial := by ring
  exact hs.hasSumLocallyUniformlyOn.congr_right fun p _ =>
    (hasSum_regularizedHGFun_zero_singleton (p 0) (p 1)).tsum_eq

/-- **Carlson Exercise 6.9-19.** Regularized `₀F₁` is jointly entire in both variables. -/
theorem analyticOnNhd_zeroFOne_joint :
    AnalyticOnNhd ℂ (fun p : Fin 2 → ℂ => regularizedHGFun 0 {p 0} (p 1)) univ := by
  apply hasSumLocallyUniformlyOn_zeroFOne_joint.analyticOnNhd_pi _ isOpen_univ
  intro n p _
  have hc : AnalyticAt ℂ (fun q : Fin 2 → ℂ => (Gamma (q 0 + n))⁻¹) p :=
    (differentiable_one_div_Gamma.analyticAt _).comp_of_eq
      (((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt p).add analyticAt_const) rfl
  convert (((ContinuousLinearMap.proj (R := ℂ) 1).analyticAt p).pow n).mul
    ((analyticAt_const : AnalyticAt ℂ (fun _ : Fin 2 → ℂ => (n.factorial : ℂ)⁻¹) p).mul hc) using 1
  funext q
  simp only [Pi.mul_apply, Pi.pow_apply, ContinuousLinearMap.proj_apply,
    div_eq_mul_inv, mul_inv]

end Carlson.TwoVariable
