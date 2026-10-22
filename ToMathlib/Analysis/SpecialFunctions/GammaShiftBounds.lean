/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Uniform bounds for shifted reciprocal Gamma functions

The reciprocal Gamma recurrence gives factorial decay after a common shift on
compact parameter sets. Mathlib's scalar hypergeometric convergence theorem then
gives a uniform bound on `n! / Gamma(c+n)` times any fixed decaying geometric factor.
These estimates include exceptional Gamma parameters.

The first three bounds were previously proved in `Pochhammer.Gamma`; that module
reexports them from this supporting layer.
-/

open Complex Set Polynomial
open scoped Topology NNReal ENNReal
@[expose] public noncomputable section
namespace Complex

/-- Reciprocal Gamma gains at least factorial decay under positive integer shifts
in the half-plane `1 ≤ re s`. -/
theorem norm_inv_Gamma_add_nat_le {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖(Gamma (s + n))⁻¹‖ ≤ ‖(Gamma s)⁻¹‖ / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : s + n ≠ 0 := ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
    have hnorm : (n + 1 : ℝ) ≤ ‖s + n‖ := by
      have H := re_le_norm (s + n)
      simp only [add_re, natCast_re] at H
      linarith
    have hrec : (Gamma (s + n + 1))⁻¹ = (s + n)⁻¹ * (Gamma (s + n))⁻¹ := by
      rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n)]
      field_simp
    rw [Nat.cast_succ, ← add_assoc, hrec, norm_mul, norm_inv]
    calc
      ‖s + n‖⁻¹ * ‖(Gamma (s + n))⁻¹‖ ≤ (n + 1 : ℝ)⁻¹ * (‖(Gamma s)⁻¹‖ / n.factorial) := by
        exact mul_le_mul (inv_anti₀ (by positivity) hnorm) ih (norm_nonneg _) (by positivity)
      _ = _ := by
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_eq_mul_inv,
            mul_inv_rev]; ring


/-- Reciprocal Gamma has uniform factorial decay after a common natural shift on any
compact set of complex arguments. -/
theorem exists_uniform_norm_inv_Gamma_add_nat {K : Set ℂ} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma (b + (n + m)))⁻¹‖ ≤ C / n.factorial := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_id.norm.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt (B + 1)
  have hre (b : ℂ) (hb : b ∈ K) : 1 ≤ (b + m).re := by
    have hbnd : ‖b‖ ≤ B := hB (mem_image_of_mem _ hb)
    have hr := neg_le_of_abs_le (abs_re_le_norm b)
    simp only [add_re, natCast_re]
    linarith
  have hc : Continuous (fun b : ℂ => (Gamma (b + m))⁻¹) :=
    differentiable_one_div_Gamma.continuous.comp (continuous_id.add continuous_const)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
  refine ⟨m, max C 0, le_max_right _ _, fun b hb n => ?_⟩
  have h := (Complex.norm_inv_Gamma_add_nat_le (hre b hb) n).trans
    (div_le_div_of_nonneg_right ((hC (mem_image_of_mem _ hb)).trans (le_max_left C 0))
      (by positivity))
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

/-- Uniform factorial decay for reciprocal Gamma after sufficiently many shifts
of the total parameter on a compact set. -/
theorem exists_uniform_norm_inv_Gamma_sum_add_nat {ι : Type*} [Fintype ι]
    {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma ((∑ i, b i) + (n + m)))⁻¹‖ ≤ C / n.factorial := by
  have hS : Continuous (fun b : ι → ℂ => ∑ i, b i) := by fun_prop
  obtain ⟨m, C, hC, hbound⟩ := exists_uniform_norm_inv_Gamma_add_nat (hK.image hS)
  exact ⟨m, C, hC, fun b hb n => hbound _ (Set.mem_image_of_mem _ hb) n⟩


end Complex

namespace Complex

/-- The scalar factorial-ratio majorant converges with any geometric factor below one. -/
private theorem summable_ascFactorial_div_factorial_mul_pow (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((m + 1).ascFactorial n : ℝ) / n.factorial * r ^ n) := by
  have hrad : (r : ℂ) ∈ Metric.eball 0
      (regularizedHGFunSeries {((m + 1 : ℕ) : ℂ)} 0).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one (by simp))
    rw [← ofReal_norm, norm_real, Real.norm_eq_abs, abs_of_nonneg hr, ENNReal.ofReal_lt_one]
    exact hr1
  have h := ((regularizedHGFunSeries {((m + 1 : ℕ) : ℂ)} 0).summable hrad).norm
  have hcoeff (n : ℕ) : regularizedHGFunCoeff {((m + 1 : ℕ) : ℂ)} 0 n =
      ((m + 1).ascFactorial n : ℂ) / n.factorial := by
    simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
      Multiset.map_zero, Multiset.prod_zero, mul_one]
    rw [← Nat.cast_ascFactorial]
  simpa only [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, hcoeff, norm_mul, norm_div, norm_pow, norm_natCast,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using h

/-- `n! / Gamma(c+n)` has a uniform geometric bound for `c` in a compact set.
No Gamma-regularity or real-part assumption is required. -/
theorem exists_uniform_norm_factorial_mul_inv_Gamma_mul_pow {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ n : ℕ,
      (n.factorial : ℝ) * ‖(Gamma (c + n))⁻¹‖ * r ^ n ≤ C := by
  have hD (n : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ c ∈ K, ‖(Gamma (c + n))⁻¹‖ ≤ D := by
    have hc := differentiable_one_div_Gamma.continuous.comp
      (continuous_id.add (continuous_const (y := (n : ℂ))))
    obtain ⟨D, hD⟩ := hK.bddAbove_image hc.norm.continuousOn
    exact ⟨max D 0, le_max_right _ _, fun c hc =>
      (hD (mem_image_of_mem _ hc)).trans (le_max_left _ _)⟩
  choose D hDpos hD using hD
  obtain ⟨m, G, hG, hgamma⟩ := exists_uniform_norm_inv_Gamma_add_nat hK
  let tail := fun k : ℕ => G * (m.factorial : ℝ) * r ^ m *
    (((m + 1).ascFactorial k : ℝ) / k.factorial * r ^ k)
  have htail : Summable tail := (summable_ascFactorial_div_factorial_mul_pow m hr hr1).mul_left _
  let M := fun n : ℕ => if n < m then (n.factorial : ℝ) * D n * r ^ n else tail (n - m)
  have hM : Summable M := by
    apply (summable_nat_add_iff m).mp
    simpa [M, Nat.not_lt.mpr (Nat.le_add_left m _)] using htail
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq hM.hasSum.tendsto_sum_nat.cauchySeq
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun c hc n => ?_⟩
  suffices h : (n.factorial : ℝ) * ‖(Gamma (c + n))⁻¹‖ * r ^ n ≤ M n from
    h.trans ((le_abs_self _).trans (hC n))
  by_cases hnm : n < m
  · simpa only [M, ite_eq_left hnm] using
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hD n c hc) (by positivity)) (pow_nonneg hr n)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnm)
  have hg : ‖(Gamma (c + (m + k : ℕ)))⁻¹‖ ≤ G / k.factorial := by
    simpa only [Nat.cast_add, add_comm (m : ℂ) (k : ℂ)] using hgamma c hc k
  calc
    _ ≤ ((m + k).factorial : ℝ) * (G / k.factorial) * r ^ (m + k) := by
      gcongr
    _ = M (m + k) := by
      simp only [M, Nat.not_lt.mpr (Nat.le_add_right m k), ite_false,
        Nat.add_sub_cancel_left, tail, pow_add, ← Nat.factorial_mul_ascFactorial m k,
        Nat.cast_mul]
      ring

end Complex
