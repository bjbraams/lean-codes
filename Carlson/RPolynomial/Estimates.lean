/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Data.Nat.Choose.Multinomial

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Pochhammer.Estimates
public import Pochhammer.Gamma

/-!
# Estimates for Carlson's R-polynomials

Home for the Section 6.2 bounds used in normally convergent series.

## Main results

* `Carlson.norm_eval_carlsonPowerPolynomial_le`: The power kernel represented by
  `carlsonPowerPolynomial` is uniformly bounded on the standard simplex by the corresponding
  power of the sum of the variable norms.
* `Carlson.norm_carlsonRPolynomialNumerator_le`: A crude bound on the Pochhammer numerator of
  the R-polynomial in terms of a bound on the parameters and the sum of the node norms.
* `Carlson.exists_summable_norm_regCarlsonR_div_factorial_bounded_variables`: A summable
  majorant uniform in compact parameter sets and bounded node vectors.
* `Carlson.exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters`: On compact
  parameter sets the exponential generating terms have a summable majorant.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Finset ProbabilityTheory Set
@[expose] public noncomputable section CarlsonRPolynomial
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The power kernel represented by `carlsonPowerPolynomial` is uniformly bounded on the
standard simplex by the corresponding power of the sum of the variable norms. -/
theorem norm_eval_carlsonPowerPolynomial_le (n : ℕ) (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖(carlsonPowerPolynomial n z).eval (fun i ↦ (u i : ℂ))‖ ≤
      (∑ i, ‖z i‖) ^ n := by
  rw [eval_carlsonPowerPolynomial, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_carlsonAffineForm_le_sum_norm z hu) n

/-- A crude bound on the Pochhammer numerator of the R-polynomial in terms of a bound on the
parameters and the sum of the node norms. -/
lemma norm_carlsonRPolynomialNumerator_le (n : ℕ) (b z : ι → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ i, ‖b i‖ ≤ B) :
    ‖carlsonRPolynomialNumerator n b z‖ ≤
      (B + n) ^ n * (∑ i, ‖z i‖) ^ n := by
  classical
  rw [carlsonRPolynomialNumerator_eq_multinomial_sum]
  calc
    ‖∑ m ∈ piAntidiag univ n,
        (Nat.multinomial univ m : ℂ) * (∏ i, z i ^ m i) *
          ∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖
        ≤ ∑ m ∈ piAntidiag univ n,
          (B + n) ^ n * ((Nat.multinomial univ m : ℝ) * ∏ i, ‖z i‖ ^ m i) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
      have hpoch := norm_prod_ascPochhammer_eval_le b m (mem_piAntidiag.mp hm).1 hB hb
      simp only [norm_mul, norm_natCast, norm_prod, norm_pow]
      calc
        (Nat.multinomial univ m : ℝ) * (∏ i, ‖z i‖ ^ m i) *
            ∏ i, ‖(ascPochhammer ℂ (m i)).eval (b i)‖
            ≤ (Nat.multinomial univ m : ℝ) * (∏ i, ‖z i‖ ^ m i) * (B + n) ^ n := by
          rw [norm_prod] at hpoch
          exact mul_le_mul_of_nonneg_left hpoch (by positivity)
        _ = _ := by ring
    _ = (B + n) ^ n * (∑ i, ‖z i‖) ^ n := by
      rw [← mul_sum, ← sum_pow_eq_sum_piAntidiag]

/-- A summable majorant uniform in compact parameter sets and bounded node vectors. -/
theorem exists_summable_norm_regCarlsonR_div_factorial_bounded_variables
    {K : Set (ι → ℂ)} (hK : IsCompact K) {Z : ℝ} (hZ : 0 ≤ Z) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n b, b ∈ K → ∀ z : ι → ℂ, (∑ i, ‖z i‖) ≤ Z →
      ‖(Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z‖ ≤ M n := by
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image (continuous_norm.continuousOn)
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbnd {b : ι → ℂ} (hb : b ∈ K) (i : ι) : ‖b i‖ ≤ B :=
    (norm_le_pi_norm b i).trans ((hB₀ (mem_image_of_mem _ hb)).trans (le_max_left _ _))
  let S := fun b : ι → ℂ => ∑ i, b i
  have hS : Continuous S := by dsimp [S]; fun_prop
  have hDb (n : ℕ) : ∃ D : ℝ, ∀ b ∈ K, ‖(Gamma (S b + n))⁻¹‖ ≤ D := by
    have hc : Continuous (fun b => (Gamma (S b + n))⁻¹) := by
      simpa only [one_div, Function.comp_def, Pi.add_apply] using!
        Complex.differentiable_one_div_Gamma.continuous.comp (hS.add continuous_const)
    obtain ⟨D, hD⟩ := hK.bddAbove_image hc.norm.continuousOn
    exact ⟨D, fun b hb => hD (mem_image_of_mem _ hb)⟩
  choose D hD using hDb
  obtain ⟨m, hm⟩ := exists_nat_gt ((Fintype.card ι : ℝ) * B + 1)
  have hre {b : ι → ℂ} (hb : b ∈ K) : 1 ≤ (S b + m).re := by
    have hn : ‖S b‖ ≤ (Fintype.card ι : ℝ) * B := by
      refine (norm_sum_le _ _).trans ?_
      simpa using (sum_le_sum fun i (_ : i ∈ Finset.univ) => hbnd hb i)
    have hr := neg_le_of_abs_le (abs_re_le_norm (S b))
    simp only [add_re, natCast_re]
    linarith
  have hgamma (k : ℕ) {b : ι → ℂ} (hb : b ∈ K) :
      ‖(Gamma (S b + (k + m)))⁻¹‖ ≤ max (D m) 0 / k.factorial := by
    have H := norm_invGamma_add_nat_le (hre hb) k
    have HD := (hD m b hb).trans (le_max_left (D m) 0)
    simpa only [add_assoc, add_comm, add_left_comm] using
      H.trans (div_le_div_of_nonneg_right HD (by positivity))
  let A := max (D m) 0 * Real.exp (B + m) * Z ^ m
  let M := fun n : ℕ => if n < m then
      (B + n) ^ n / n.factorial * Z ^ n * max (D n) 0
    else A * ((Real.exp 1 * Z) ^ (n - m) / (n - m).factorial)
  have hM : Summable M := by
    apply (summable_nat_add_iff m).mp
    have H := (Real.summable_pow_div_factorial (Real.exp 1 * Z)).mul_left A
    simpa [M, Nat.not_lt.mpr (Nat.le_add_left m _)] using H
  refine ⟨M, hM, ?_⟩
  intro n b hb z hz
  have hraw : ‖(n.factorial : ℂ)⁻¹ * regCarlsonRPolynomial n b z‖ ≤
      (B + n) ^ n / n.factorial * Z ^ n * ‖(Gamma (S b + n))⁻¹‖ := by
    have H := norm_carlsonRPolynomialNumerator_le n b z hB (hbnd hb)
    have H' : ‖carlsonRPolynomialNumerator n b z‖ ≤ (B + n) ^ n * Z ^ n :=
      H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz n) (by positivity))
    change ‖(n.factorial : ℂ)⁻¹ * regCarlsonRPolynomial n b z‖ ≤ _
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, norm_mul, norm_mul, norm_inv,
        Complex.norm_natCast]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹ * (((B + n) ^ n * Z ^ n) * ‖(Gamma (S b + n))⁻¹‖) := by
        gcongr
      _ = _ := by ring
  by_cases hnm : n < m
  · exact hraw.trans (by
      dsimp [M]; rw [ite_eq_left hnm]; gcongr; exact (hD n b hb).trans (le_max_left _ _))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnm)
  rw [Nat.add_comm m k] at hraw ⊢
  have hpow := Real.pow_div_factorial_le_exp (B + (k + m : ℕ)) (by positivity) (k + m)
  have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    simp [← Real.exp_nat_mul]
  calc
    _ ≤ (B + (k + m : ℕ)) ^ (k + m) / (k + m).factorial * Z ^ (k + m) *
        ‖(Gamma (S b + (k + m)))⁻¹‖ := by simpa only [Nat.cast_add] using hraw
    _ ≤ Real.exp (B + (k + m : ℕ)) * Z ^ (k + m) * (max (D m) 0 / k.factorial) := by
      gcongr
      exact hgamma k hb
    _ = M (k + m) := by
      simp only [M, Nat.not_lt.mpr (Nat.le_add_left m k), ite_false, Nat.add_sub_cancel_right,
        A, Nat.cast_add, pow_add, Real.exp_add, hexp, mul_pow]
      ring

/-- On compact parameter sets the exponential generating terms have a summable majorant. -/
theorem exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters
    (z : ι → ℂ) {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n b, b ∈ K →
      ‖(Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z‖ ≤ M n := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_regCarlsonR_div_factorial_bounded_variables hK
    (show 0 ≤ ∑ i, ‖z i‖ by positivity)
  exact ⟨M, hM, fun n b hb => hbound n b hb z le_rfl⟩

end Carlson
end CarlsonRPolynomial
