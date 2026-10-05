/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindLimits

/-!
# Maxima on confocal ellipses

Carlson's `p̂ₙ(ρ)` is the maximum of `‖pₙ‖` on the closed elliptic disk of mean radius `ρ`, and
`q̂ₙ(σ)` the supremum of `‖qₙ‖` on the closed elliptic exterior of mean radius `σ`. The sharp
upper bounds on these sets and the pointwise lower bounds at a point of the ellipse give
Theorem 7.5-2: `p̂ₙ(ρ)^{1/n} → ρ` and `q̂ₙ(σ)^{1/n} → 1/σ`.

## Main results

* `jacobiOnMax`, `jacobiSecondKindMax`: Carlson's `p̂ₙ(ρ)` and `q̂ₙ(σ)`.
* `tendsto_jacobiOnMax_rpow`, `tendsto_jacobiSecondKindMax_rpow`: Theorem 7.5-2.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Theorem 7.5-2.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial
open scoped Topology

namespace Carlson.TwoVariable

/-- Carlson's `p̂ₙ(ρ)`: the maximum modulus of `pₙ` on the closed elliptic disk of mean radius
`ρ`. -/
def jacobiOnMax (α β r s : ℂ) (n : ℕ) (ρ : ℝ) : ℝ :=
  sSup ((fun x => ‖(jacobiOn α β r s n).eval x‖) '' jacobiClosedEllipseDisk r s ρ)

/-- Carlson's `q̂ₙ(σ)`: the supremum of `‖qₙ‖` on the closed elliptic exterior of mean radius
`σ`. -/
def jacobiSecondKindMax (α β r s : ℂ) (n : ℕ) (σ : ℝ) : ℝ :=
  sSup ((fun y => ‖jacobiSecondKind α β r s n y‖) '' {y | σ ≤ jacobiEllipseRadius r s y})

/-- A point of the confocal ellipse of mean radius `ρ`, on the exterior of the segment. -/
theorem exists_jacobiEllipseRadius_eq (r s : ℂ) {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    ∃ x, jacobiEllipseRadius r s x = ρ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  refine ⟨jacobiJoukowski r s ρ, ?_⟩
  rw [jacobiEllipseRadius_jacobiJoukowski r s _ (by exact_mod_cast hρ0.ne')
    (by rw [norm_real, Real.norm_of_nonneg hρ0.le]; exact hρ.le), norm_real,
    Real.norm_of_nonneg hρ0.le]

/-- A sandwich for `n`-th roots: lower and upper geometric bounds with rates arbitrarily close to
`L` give convergence of the `n`-th roots to `L`. -/
theorem tendsto_rpow_of_bounds {a : ℕ → ℝ} {L : ℝ} (hL : 0 < L) (ha : ∀ n, 0 ≤ a n)
    (hup : ∀ ε > 0, ∃ C > 0, ∀ n, a n ≤ C * (L + ε) ^ n)
    (hlow : ∀ ε > 0, ε < L → ∃ c > 0, ∃ N, ∀ n, N ≤ n → c * (L - ε) ^ n ≤ a n) :
    Tendsto (fun n : ℕ => a n ^ (1 / (n : ℝ))) atTop (𝓝 L) := by
  have hroot (C : ℝ) (hC : 0 < C) : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := ((Real.continuousAt_const_rpow hC.ne').tendsto).comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  rw [tendsto_order]
  constructor
  · intro b hb
    rcases lt_or_ge b 0 with hb0 | hb0
    · exact Eventually.of_forall fun n => hb0.trans_le (Real.rpow_nonneg (ha n) _)
    set ε := (L - b) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨c, hc0, N, hN⟩ := hlow ε hε (by simp only [ε]; linarith)
    have hlim := (hroot c hc0).mul_const (L - ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds (show b < L - ε by simp only [ε]; linarith)),
      eventually_ge_atTop N, eventually_ne_atTop 0] with n h1 h2 h3
    refine h1.trans_le ?_
    have hbase : 0 ≤ L - ε := by simp only [ε]; linarith
    calc
      c ^ (1 / (n : ℝ)) * (L - ε) = (c * (L - ε) ^ n) ^ (1 / (n : ℝ)) := by
        rw [Real.mul_rpow hc0.le (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hN n h2) (by positivity)
  · intro b hb
    set ε := (b - L) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨C, hC0, hC⟩ := hup ε hε
    have hlim := (hroot C hC0).mul_const (L + ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds (show L + ε < b by simp only [ε]; linarith)),
      eventually_ne_atTop 0] with n h1 h3
    refine lt_of_le_of_lt ?_ h1
    have hbase : 0 ≤ L + ε := by linarith
    calc
      a n ^ (1 / (n : ℝ)) ≤ (C * (L + ε) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (ha n) (hC n) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hC0.le (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]

/-- Carlson's Theorem 7.5-2 for the polynomials: `p̂ₙ(ρ)^{1/n} → ρ`. -/
theorem tendsto_jacobiOnMax_rpow (α β r s : ℂ) (hc : IsGammaRegular (α + β + 2))
    {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    Tendsto (fun n : ℕ => jacobiOnMax α β r s n ρ ^ (1 / (n : ℝ))) atTop (𝓝 ρ) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  obtain ⟨x₀, hx₀⟩ := exists_jacobiEllipseRadius_eq r s hρ
  have hx₀s : x₀ ∉ segment ℝ r s := not_mem_segment_of_lt_jacobiEllipseRadius (hx₀ ▸ hρ)
  have hbdd (n : ℕ) : BddAbove ((fun x => ‖(jacobiOn α β r s n).eval x‖) ''
      jacobiClosedEllipseDisk r s ρ) :=
    ((isCompact_jacobiClosedEllipseDisk r s ρ).image
      (continuous_norm.comp (jacobiOn α β r s n).continuous)).bddAbove
  have hmem : x₀ ∈ jacobiClosedEllipseDisk r s ρ := show _ ≤ ρ from hx₀.le
  have hge (n : ℕ) : ‖(jacobiOn α β r s n).eval x₀‖ ≤ jacobiOnMax α β r s n ρ :=
    le_csSup (hbdd n) ⟨x₀, hmem, rfl⟩
  refine tendsto_rpow_of_bounds hρ0 (fun n => (norm_nonneg _).trans (hge n)) (fun ε hε => ?_)
    (fun ε hε hερ => ?_)
  · obtain ⟨C, hC0, hC⟩ := exists_bound_norm_eval_jacobiOn_of_le α β r s hρ hε
    refine ⟨C + 1, by linarith, fun n => csSup_le ⟨_, ⟨x₀, hmem, rfl⟩⟩ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hC n x hx).trans (by gcongr; linarith)
  · obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_eval_jacobiOn α β r s hc hx₀s hε
      (by rw [hx₀]; exact hερ.le)
    exact ⟨c, hc0, N, fun n hn => (hx₀ ▸ hN n hn).trans (hge n)⟩

/-- Carlson's Theorem 7.5-2 for the second-kind functions: `q̂ₙ(σ)^{1/n} → 1/σ`. -/
theorem tendsto_jacobiSecondKindMax_rpow (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {σ : ℝ} (hσ : ‖r - s‖ / 4 < σ) :
    Tendsto (fun n : ℕ => jacobiSecondKindMax α β r s n σ ^ (1 / (n : ℝ))) atTop
      (𝓝 (1 / σ)) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  obtain ⟨y₀, hy₀⟩ := exists_jacobiEllipseRadius_eq r s hσ
  have hy₀s : y₀ ∉ segment ℝ r s := not_mem_segment_of_lt_jacobiEllipseRadius (hy₀ ▸ hσ)
  have hmem : y₀ ∈ {y | σ ≤ jacobiEllipseRadius r s y} := show σ ≤ _ from hy₀.ge
  have hbdd (n : ℕ) : BddAbove ((fun y => ‖jacobiSecondKind α β r s n y‖) ''
      {y | σ ≤ jacobiEllipseRadius r s y}) := by
    obtain ⟨C, -, hC⟩ := exists_bound_jacobiSecondKind_exterior α β r s hσ one_pos
    exact ⟨C * (1 / σ + 1) ^ n, by rintro _ ⟨y, hy, rfl⟩; exact hC n y hy⟩
  have hge (n : ℕ) : ‖jacobiSecondKind α β r s n y₀‖ ≤ jacobiSecondKindMax α β r s n σ :=
    le_csSup (hbdd n) ⟨y₀, hmem, rfl⟩
  refine tendsto_rpow_of_bounds (by positivity) (fun n => (norm_nonneg _).trans (hge n))
    (fun ε hε => ?_) (fun ε hε hεσ => ?_)
  · obtain ⟨C, hC0, hC⟩ := exists_bound_jacobiSecondKind_exterior α β r s hσ hε
    refine ⟨C + 1, by linarith, fun n => csSup_le ⟨_, ⟨y₀, hmem, rfl⟩⟩ ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hC n y hy).trans (by gcongr; linarith)
  · obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_jacobiSecondKind α β r s hc hy₀s hε
      (by rw [hy₀]; exact hεσ)
    exact ⟨c, hc0, N, fun n hn => (hy₀ ▸ hN n hn).trans (hge n)⟩

end Carlson.TwoVariable
