/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Divergence of generalized hypergeometric series

For a nonterminating regularized `pFq` series with `p > q + 1`, the ratio of
successive coefficient norms tends to infinity and its convergence radius is
zero. Together with Mathlib's entire and radius-one cases this completes the
radius classification in Carlson (1977), §2.4.

The coefficient-scaling calculation adapts Moritz Doll's radius-one and
infinite-radius proofs in `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`,
using that module's public coefficient recurrence and Mathlib's ratio test.
-/

open Filter
open scoped Topology

public noncomputable section

namespace Complex

/-- Factoring the large integer out of every factor of a shifted multiset product. -/
private theorem prod_shift_eq (a : Multiset ℂ) {n : ℕ} (hn : n ≠ 0) :
    (a.map (fun z => z + (n : ℂ))).prod =
      (n : ℂ) ^ a.card * (a.map (fun z => z / (n : ℂ) + 1)).prod := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have he : (fun z : ℂ => z + (n : ℂ)) = fun z => (n : ℂ) * (z / (n : ℂ) + 1) := by
    funext z
    field_simp
  rw [he, Multiset.prod_map_mul]
  simp

/-- The scaled coefficient product tends to one as its natural argument increases. -/
private theorem tendsto_prod_scaled (a : Multiset ℂ) :
    Tendsto (fun n : ℕ => (a.map (fun z => z / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  simpa using tendsto_multiset_prod a (fun z _ =>
    (tendsto_const_div_atTop_nhds_zero_nat z).add_const 1)

/-- In the nonterminating `p > q + 1` case, successive coefficient norms have
unbounded ratio, including denominator parameters at Gamma poles. -/
theorem tendsto_regularizedHGFunCoeff_ratio_atTop {a b : Multiset ℂ}
    (hab : b.card + 1 < a.card) (ha : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    Tendsto (fun n : ℕ => ‖regularizedHGFunCoeff a b (n + 1)‖ /
      ‖regularizedHGFunCoeff a b n‖) atTop atTop := by
  let d := a.card - b.card - 1
  have hd : d ≠ 0 := by dsimp [d]; omega
  have he : a.card = b.card + 1 + d := by dsimp [d]; omega
  let A := fun n : ℕ => (a.map (fun z => z / (n : ℂ) + 1)).prod
  let B := fun n : ℕ => (b.map (fun z => z / (n : ℂ) + 1)).prod
  have hD : Tendsto (fun n : ℕ => B n * (1 + (n : ℂ)⁻¹)) atTop (𝓝 1) := by
    simpa [B] using (tendsto_prod_scaled b).mul
      (tendsto_inv_atTop_nhds_zero_nat.const_add (1 : ℂ))
  have hlim : Tendsto (fun n => ‖A n / (B n * (1 + (n : ℂ)⁻¹))‖) atTop (𝓝 1) := by
    simpa [A] using ((tendsto_prod_scaled a).div hD (by norm_num)).norm
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd).comp tendsto_natCast_atTop_atTop
  apply (hpow.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hlim).congr'
  filter_upwards [eventually_atTop_regularizedHGFunCoeff_ne_zero b ha,
    eventually_ne_atTop 0, hD.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))]
    with n hn hn0 hden
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hscaled : 1 + (n : ℂ)⁻¹ ≠ 0 := (mul_ne_zero_iff.mp hden).2
  have hbn : B n ≠ 0 := (mul_ne_zero_iff.mp hden).1
  rw [← norm_div, regularizedHGFunCoeff_add_one_div_self hn,
    prod_shift_eq a hn0, prod_shift_eq b hn0]
  have hratio : (n : ℂ) ^ a.card * A n / ((n : ℂ) ^ b.card * B n * (n + 1)) =
      (n : ℂ) ^ d * (A n / (B n * (1 + (n : ℂ)⁻¹))) := by
    rw [he, pow_add, pow_add]
    field_simp
  symm
  change ‖(n : ℂ) ^ a.card * A n / ((n : ℂ) ^ b.card * B n * (n + 1))‖ = _
  rw [hratio, norm_mul, norm_pow, Complex.norm_natCast]

/-- **Carlson §2.4.** The nonterminating `p > q + 1` hypergeometric series has
zero convergence radius. Terminating numerator parameters are explicitly excluded. -/
theorem radius_regularizedHGFunSeries_eq_zero {a b : Multiset ℂ}
    (hab : b.card + 1 < a.card) (ha : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 0 :=
  FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto ℂ _
    (tendsto_regularizedHGFunCoeff_ratio_atTop hab ha)

/-- **Carlson §2.4, divergence assertion.** A nonterminating `p > q + 1`
regularized hypergeometric series does not converge at any nonzero argument. -/
theorem not_summable_regularizedHGFunCoeff_mul_pow {a b : Multiset ℂ}
    (hab : b.card + 1 < a.card) (ha : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k)
    {z : ℂ} (hz : z ≠ 0) :
    ¬ Summable (fun n : ℕ => regularizedHGFunCoeff a b n * z ^ n) := by
  have hne := eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply not_summable_of_ratio_norm_eventually_ge (r := 2) (by norm_num)
  · exact (hne.mono fun n hn => norm_ne_zero_iff.mpr (mul_ne_zero hn (pow_ne_zero _ hz))).frequently
  · filter_upwards [hne, (tendsto_regularizedHGFunCoeff_ratio_atTop hab ha).eventually_ge_atTop
      (2 / ‖z‖)] with n hn hr
    have hh := (div_le_div_iff₀ hz' (norm_pos_iff.mpr hn)).mp hr
    calc
      2 * ‖regularizedHGFunCoeff a b n * z ^ n‖ =
          (2 * ‖regularizedHGFunCoeff a b n‖) * ‖z‖ ^ n := by rw [norm_mul, norm_pow]; ring
      _ ≤ (‖regularizedHGFunCoeff a b (n + 1)‖ * ‖z‖) * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right hh (pow_nonneg (norm_nonneg _) _)
      _ = ‖regularizedHGFunCoeff a b (n + 1) * z ^ (n + 1)‖ := by
        rw [norm_mul, norm_pow, pow_succ]
        ring

end Complex
