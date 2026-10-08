/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EndpointBridge
public import Carlson.RPolynomial.Estimates
public import Pochhammer.Estimates

/-!
# Geometric bounds for monic Jacobi polynomials

Carlson's numerator estimate and an elementary lower bound for its normalizing
Pochhammer factor give geometric bounds as the degree increases. Parameters and
endpoints may be complex, and coincident endpoints are included. The bounds use
endpoint distances and are preliminary estimates, not the sharp confocal-ellipse
root-growth theorem.

## Main results

* `norm_eval_jacobiOn_le_of_large_degree`: an explicit bound above a parameter-dependent
  degree threshold.
* `exists_geometric_bound_jacobiOn`: a geometric bound uniform on any compact set.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.4–7.5; the numerator bound derives from Chapter 6.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter
open scoped Topology

/-- At sufficiently large degrees, the monic Jacobi polynomial is bounded by
a geometric power of the sum of its endpoint distances. -/
theorem norm_eval_jacobiOn_le_of_large_degree (α β r s x : ℂ) (n : ℕ)
    (hn : 2 * (‖α‖ + ‖β‖ + 1) ≤ (n : ℝ)) :
    ‖(jacobiOn α β r s n).eval x‖ ≤ (6 * (‖x - r‖ + ‖x - s‖)) ^ n := by
  have hn0 : 0 < (n : ℝ) := by nlinarith [norm_nonneg α, norm_nonneg β]
  have hα : ‖α‖ ≤ (n : ℝ) := by nlinarith [norm_nonneg β]
  have hβ : ‖β‖ ≤ (n : ℝ) := by nlinarith [norm_nonneg α]
  have hre : (n : ℝ) / 2 ≤ (α + β + n + 1).re := by
    have ha := (abs_le.mp (abs_re_le_norm α)).1
    have hb := (abs_le.mp (abs_re_le_norm β)).1
    simp only [add_re, natCast_re, one_re]
    linarith
  have hp := ascPochhammer_eval_ne_zero_of_re_pos (lt_of_lt_of_le (half_pos hn0) hre) n
  rw [eval_jacobiOn_eq_numerator α β r s x n hp, norm_div]
  have hreflect : (ascPochhammer ℂ n).eval (-α - β - 2 * n) =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval (α + β + n + 1) := by
    rw [show -α - β - 2 * n = 1 - (α + β + n + 1) - n by ring]
    exact ascPochhammer_eval_reflect _ _
  rw [hreflect, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hden := pow_le_norm_ascPochhammer_eval (le_of_lt (half_pos hn0)) hre n
  have hnum := norm_carlsonRPolynomialNumerator_le n
    (pair (-α - n) (-β - n)) (pair (x - r) (x - s))
    (B := 2 * n) (by positivity) (by
      intro i
      fin_cases i
      · simpa [pair] using
          (norm_sub_le (-α) (n : ℂ)).trans (by simpa using (show ‖α‖ + n ≤ 2 * (n : ℝ) by linarith))
      · simpa [pair] using
          (norm_sub_le (-β) (n : ℂ)).trans
              (by simpa using (show ‖β‖ + n ≤ 2 * (n : ℝ) by linarith)))
  rw [carlsonRPolynomialNumerator_pair] at hnum
  simp only [Fin.sum_univ_two, pair_zero, pair_one] at hnum
  calc
    _ ≤ ((2 * n + n) ^ n * (‖x - r‖ + ‖x - s‖) ^ n) / ((n : ℝ) / 2) ^ n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (6 * (‖x - r‖ + ‖x - s‖)) ^ n := by
      rw [← mul_pow, ← div_pow]
      congr 1
      field_simp
      ring

/-- On each compact set, monic endpoint Jacobi polynomials have a common geometric
bound in the degree. No individual or total parameter restrictions are needed for
this bound on the totalized polynomial definitions. -/
theorem exists_geometric_bound_jacobiOn (α β r s : ℂ) {K : Set ℂ}
    (hK : IsCompact K) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ n x, x ∈ K →
      ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (‖α‖ + ‖β‖ + 1))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((continuous_id.sub continuous_const).norm.add
      (continuous_id.sub continuous_const).norm :
        Continuous (fun x : ℂ => ‖x - r‖ + ‖x - s‖)).continuousOn
  have hD (n : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖(jacobiOn α β r s n).eval x‖ ≤ D :=
    hK.exists_bound_of_continuousOn (jacobiOn α β r s n).continuous.continuousOn
  choose D hD using hD
  let C := 1 + ∑ n ∈ Finset.range N, max (D n) 0
  let R := max 1 (6 * B)
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, max (D n) 0 :=
    Finset.sum_nonneg fun n _ => le_max_right _ _
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hR : 1 ≤ R := le_max_left _ _
  refine ⟨C, R, by linarith, hR, ?_⟩
  intro n x hx
  by_cases hn : n < N
  · have hDn : D n ≤ C := by
      have := Finset.single_le_sum (f := fun n => max (D n) 0)
        (fun n _ => le_max_right _ _) (Finset.mem_range.mpr hn)
      have := (le_max_left (D n) 0).trans this
      dsimp [C]
      linarith
    exact (hD n x hx).trans (hDn.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hR)))
  · have hlarge : 2 * (‖α‖ + ‖β‖ + 1) ≤ (n : ℝ) :=
      hN.trans (Nat.cast_le.mpr (Nat.le_of_not_gt hn))
    have hxB : ‖x - r‖ + ‖x - s‖ ≤ B := by
      exact (le_abs_self _).trans (hB x hx)
    have hbase : 6 * (‖x - r‖ + ‖x - s‖) ≤ R :=
      (mul_le_mul_of_nonneg_left hxB (by norm_num)).trans (le_max_right _ _)
    exact (norm_eval_jacobiOn_le_of_large_degree α β r s x n hlarge).trans
      ((pow_le_pow_left₀ (by positivity) hbase n).trans
        (le_mul_of_one_le_left (by positivity) hC))

end Carlson.TwoVariable
