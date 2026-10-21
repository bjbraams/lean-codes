/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SaddleUniform
public import ToMathlib.Analysis.Asymptotics.UniformRoot

/-!
# Compact-uniform growth of the second-kind Jacobi functions

The continuous nonvanishing saddle coefficient gives uniform two-sided geometric bounds
on every compact set off the focal segment. Taking `n`th roots proves the second-kind
compact-uniform assertion of Carlson's Theorem 7.5-1, for all complex parameters.
The first-kind polynomial assertion is separate.
-/

open Complex Filter Set
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The modulus of the second-kind geometric factor is the reciprocal elliptic mean radius. -/
theorem norm_four_div_jacobiSaddleScale {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ‖(4 : ℂ) / jacobiSaddleScale r s z‖ = 1 / jacobiEllipseRadius r s z := by
  rw [norm_div, norm_jacobiSaddleScale hz]
  norm_num only [norm_ofNat]
  have hμ : 0 < jacobiEllipseRadius r s z :=
    lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hz)
  field_simp

/-- Sharp-rate two-sided geometric bounds, uniform on any compact set off the segment.
The parameters are arbitrary complex numbers, and coincident foci are included. -/
theorem exists_uniform_geometric_bounds_jacobiSecondKind (α β r s : ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ K,
      a * (1 / jacobiEllipseRadius r s z) ^ n ≤ ‖jacobiSecondKind α β r s n z‖ ∧
        ‖jacobiSecondKind α β r s n z‖ ≤ b * (1 / jacobiEllipseRadius r s z) ^ n := by
  rcases K.eq_empty_or_nonempty with he | hne
  · subst he
    exact ⟨1, 1, zero_lt_one, zero_lt_one, Eventually.of_forall fun _ z hz => hz.elim⟩
  obtain ⟨C, hCcont, hCne, hC⟩ :=
    exists_continuous_tendstoUniformlyOn_jacobiSecondKind_div_geometric α β r s
  have hc : ContinuousOn (fun z => ‖C z‖) K :=
    (hCcont.mono fun z hz => hKs z hz).norm
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne hc
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn hne hc
  have hu₀ : 0 < ‖C u‖ := norm_pos_iff.mpr (hCne u (hKs u hu))
  have hv₀ : 0 < ‖C v‖ := norm_pos_iff.mpr (hCne v (hKs v hv))
  refine ⟨‖C u‖ / 2, 2 * ‖C v‖, by positivity, by positivity, ?_⟩
  have he := Metric.tendstoUniformlyOn_iff.mp (hC K hK hKs) (1 / 2) (by norm_num)
  filter_upwards [he] with n hn
  intro z hz
  let G := (4 : ℂ) / jacobiSaddleScale r s z
  let w := jacobiSecondKind α β r s n z / (C z * G ^ n)
  have hw : ‖w - 1‖ < 1 / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn z hz
  have hn1 := norm_sub_norm_le w 1
  have hn2 := norm_sub_norm_le (1 : ℂ) w
  rw [norm_one] at hn1 hn2
  rw [norm_sub_rev] at hn2
  have hwlo : 1 / 2 ≤ ‖w‖ := by linarith
  have hwhi : ‖w‖ ≤ 2 := by linarith
  have hG : G ≠ 0 := div_ne_zero (by norm_num) (jacobiSaddleScale_ne_zero (hKs z hz))
  have hden : 0 < ‖C z‖ * ‖G‖ ^ n :=
    mul_pos (norm_pos_iff.mpr (hCne z (hKs z hz))) (pow_pos (norm_pos_iff.mpr hG) n)
  dsimp only [w] at hwlo hwhi
  rw [norm_div, norm_mul, norm_pow] at hwlo hwhi
  have hlo := (le_div_iff₀ hden).mp hwlo
  have hhi := (div_le_iff₀ hden).mp hwhi
  have hminz : ‖C u‖ ≤ ‖C z‖ := hmin hz
  have hmaxz : ‖C z‖ ≤ ‖C v‖ := hmax hz
  have hnorm : ‖G‖ = 1 / jacobiEllipseRadius r s z :=
    norm_four_div_jacobiSaddleScale (hKs z hz)
  rw [← hnorm]
  constructor
  · calc
      _ ≤ ‖C z‖ / 2 * ‖G‖ ^ n := by gcongr
      _ ≤ _ := by linarith
  · calc
      _ ≤ (2 * ‖C z‖) * ‖G‖ ^ n := by linarith
      _ ≤ _ := by gcongr

/-- **Carlson's Theorem 7.5-1, compact-uniform second-kind root limit**. No restriction
on the complex Jacobi parameters is needed for this eventual-degree assertion. -/
theorem tendstoUniformlyOn_norm_jacobiSecondKind_rpow (α β r s : ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    TendstoUniformlyOn (fun n : ℕ => fun z =>
      ‖jacobiSecondKind α β r s n z‖ ^ (1 / (n : ℝ)))
      (fun z => 1 / jacobiEllipseRadius r s z) atTop K := by
  rcases K.eq_empty_or_nonempty with he | hne
  · subst he; exact tendstoUniformlyOn_empty
  have hμ (z : ℂ) (hz : z ∈ K) : 0 < jacobiEllipseRadius r s z :=
    lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius (hKs z hz))
  have hr : ContinuousOn (fun z => 1 / jacobiEllipseRadius r s z) K :=
    continuousOn_const.div (continuous_jacobiEllipseRadius r s).continuousOn
      (fun z hz => (hμ z hz).ne')
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn hne hr
  obtain ⟨a, b, ha, hb, hbound⟩ := exists_uniform_geometric_bounds_jacobiSecondKind α β r s hK hKs
  exact Real.tendstoUniformlyOn_rpow_of_geometric_bounds ha hb
    (le_of_lt (one_div_pos.mpr (hμ v hv)))
    (fun z hz => ⟨(one_div_pos.mpr (hμ z hz)).le, hmax hz⟩)
    (fun _ _ _ => norm_nonneg _) hbound

/-- Every compact set off the focal segment is free of second-kind zeros at all
sufficiently large degrees, uniformly in the evaluation point. -/
theorem eventually_jacobiSecondKind_ne_zero (α β r s : ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ K, jacobiSecondKind α β r s n z ≠ 0 := by
  obtain ⟨a, b, ha, _, h⟩ := exists_uniform_geometric_bounds_jacobiSecondKind α β r s hK hKs
  filter_upwards [h] with n hn
  intro z hz
  have hμ : 0 < jacobiEllipseRadius r s z :=
    lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius (hKs z hz))
  apply norm_pos_iff.mp
  exact (mul_pos ha (pow_pos (one_div_pos.mpr hμ) n)).trans_le (hn z hz).1

end Carlson.TwoVariable
