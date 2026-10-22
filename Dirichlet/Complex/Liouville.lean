/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Complex.Aggregation
public import StdSimplexMeasure.SimplexFTC

/-!
# Liouville's solid-simplex integral

Carlson (1977), Corollary 4.4-5. A continuous function of the coordinate sum
reduces a complex Dirichlet integral on a solid simplex to a single Mellin integral.
The proof adjoins a slack coordinate of parameter one and aggregates the other
coordinates. The dimension is positive; dimension one is included.
-/

open Complex MeasureTheory Set

public noncomputable section

namespace Dirichlet

/-- **Carlson Corollary 4.4-5 (Liouville).** A solid-simplex integral of a function
of the coordinate sum reduces to a single weighted integral. -/
theorem integral_posSimplex_sum_mul_monomial {n : ℕ} (hn : 0 < n)
    {b : Fin n → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1)) :
    (∫ x : Fin n → ℝ in posSimplexFin n 1,
      (∏ i, (x i : ℂ) ^ (b i - 1)) * g (∑ i, x i)) =
      mvBeta b * ∫ t : ℝ in Ioo 0 1, (t : ℂ) ^ ((∑ i, b i) - 1) * g t := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let β : Fin (n + 1) → ℂ := Fin.snoc b 1
  let q : Fin (n + 1) → Fin 2 := fun i => if i = Fin.last n then 1 else 0
  have hq : Function.Surjective q := by
    intro k
    fin_cases k
    · exact ⟨(⟨0, hn⟩ : Fin n).castSucc, by simp [q, hn.ne']⟩
    · exact ⟨Fin.last n, by simp [q]⟩
  have hβ : β ∈ mvBetaConvergent := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · norm_num [β]
    · simpa [β] using hb j
  have hblock {K : Type} [CommSemiring K] (u : Fin (n + 1) → K) :
      stdSimplexAggregate q u 0 = ∑ i : Fin n, u i.castSucc ∧
        stdSimplexAggregate q u 1 = u (Fin.last n) := by
    simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, q, Fin.castSucc_ne_last]
  have hb0 : stdSimplexAggregate q β 0 = ∑ i, b i := by simp [hblock β, β]
  have hb1 : stdSimplexAggregate q β 1 = 1 := by simp [hblock β, β]
  have hsum : ∑ i, β i = (∑ i, b i) + 1 := by simp [β, Fin.sum_univ_castSucc]
  have hprod : (∏ i, (Gamma (β i))⁻¹) = (∏ i, Gamma (b i))⁻¹ := by
    simp [β, Fin.prod_univ_castSucc, ← Finset.prod_inv_distrib]
  have h := complexDirichletIntegral_aggregate_fin_two hq hβ hg
  rw [complexDirichletIntegral_eq_Gamma_mul, regDirichletIntegral_eq_prod_inv_Gamma_mul,
    integral_stdSimplex_fin] at h
  have hleft : (∫ x : Fin n → ℝ in posSimplexFin n 1,
      (∏ i, ((finSimplexPoint x i : ℝ) : ℂ) ^ (β i - 1)) *
        g (stdSimplexAggregate q (finSimplexPoint x) 0)) =
      ∫ x : Fin n → ℝ in posSimplexFin n 1,
        (∏ i, (x i : ℂ) ^ (b i - 1)) * g (∑ i, x i) := by
    apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
    intro x _
    dsimp only
    rw [(hblock (finSimplexPoint x)).1]
    simp [Fin.prod_univ_castSucc, β, finSimplexPoint]
  rw [hleft, hsum, hprod, hb0, hb1, regEulerIntegral] at h
  have hG : Gamma ((∑ i, b i) + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simpa only [add_re, one_re] using add_pos (sum_re_pos_of_mem_mvBetaConvergent hb) zero_lt_one)
  have hGb : (∏ i, Gamma (b i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Gamma_ne_zero_of_re_pos (hb i))
  simp only [Gamma_one, mul_one, sub_self, cpow_zero] at h
  have hh := mul_left_cancel₀ hG h
  rw [mvBeta, div_eq_mul_inv, mul_assoc]
  calc
    _ = (∏ i, Gamma (b i)) * ((∏ i, Gamma (b i))⁻¹ *
        ∫ x : Fin n → ℝ in posSimplexFin n 1,
          (∏ i, (x i : ℂ) ^ (b i - 1)) * g (∑ i, x i)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hGb, one_mul]
    _ = _ := by rw [hh]

end Dirichlet
