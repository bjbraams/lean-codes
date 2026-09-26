/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Contour
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Contour coefficients of uniformly convergent Jacobi series

The second-kind functions define contour coefficient functionals. On a fixed
`C¹` cycle off the endpoint segment these functionals are bounded for the uniform
norm and commute with uniform limits of continuous functions. Consequently a
Jacobi series converging uniformly on a cycle of nonzero index has uniquely
determined coefficients, recovered by the contour formula.

Uniform convergence is a hypothesis here: large-degree estimates and sufficient
conditions for convergence in an elliptic disk remain separate work.

## Main results

* `jacobiContourCoefficient_polynomial`: agreement with polynomial coefficients,
  multiplied by the index.
* `exists_norm_jacobiContourCoefficient_le`: a bound in terms of the uniform norm.
* `tendsto_jacobiContourCoefficient`: continuity under uniform convergence.
* `jacobiContourCoefficient_eq_of_tendstoUniformlyOn`: coefficient recovery for a
  uniformly convergent Jacobi series.
* `jacobiSeries_coefficients_unique`: uniqueness on any cycle of nonzero index.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.2 and 7.5.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Metric ContinuousLinearMap Filter
open scoped Topology

/-- The normalized integral against the adjoint second-kind function on a cycle.
For index-one cycles this recovers the Jacobi expansion coefficient. -/
def jacobiContourCoefficient (α β r s : ℂ) (n : ℕ) (Γ : Cycle) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z))

/-- On polynomials, contour coefficients equal the algebraic coefficients times
the index, without any restriction on the individual complex parameters. -/
theorem jacobiContourCoefficient_polynomial (α β r s : ℂ) (n : ℕ) (p : ℂ[X])
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    jacobiContourCoefficient α β r s n Γ (fun z => p.eval z) =
      Γ.index r * carlsonJacobiCoefficient α β r s n p :=
  cycleIntegral_jacobiSecondKind_mul_polynomial α β r s n p Γ hΓ havoid

/-- The contour coefficient is bounded by a constant times any uniform bound
for its argument on the cycle. -/
theorem exists_norm_jacobiContourCoefficient_le (α β r s : ℂ) (n : ℕ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ) (M : ℝ), (∀ z ∈ Γ.range, ‖f z‖ ≤ M) →
      ‖jacobiContourCoefficient α β r s n Γ f‖ ≤ C * M := by
  obtain ⟨L, hL, hbound⟩ := Γ.exists_norm_integral_le (F := ℂ) hΓ
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn
    ((analyticOnNhd_jacobiSecondKind α β r s n).continuousOn.mono havoid)
  let K := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * L * K, by positivity, ?_⟩
  intro f M hf
  unfold jacobiContourCoefficient
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (L * (K * M)) := by
      gcongr
      apply hbound
      intro z hz
      rw [norm_mul]
      exact mul_le_mul ((hB z hz).trans (le_max_left _ _)) (hf z hz)
        (norm_nonneg _) hK
    _ = _ := by ring

/-- Contour coefficients respect subtraction of functions continuous on the cycle. -/
theorem jacobiContourCoefficient_sub (α β r s : ℂ) (n : ℕ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    {f g : ℂ → ℂ} (hf : ContinuousOn f Γ.range) (hg : ContinuousOn g Γ.range) :
    jacobiContourCoefficient α β r s n Γ (fun z => f z - g z) =
      jacobiContourCoefficient α β r s n Γ f - jacobiContourCoefficient α β r s n Γ g := by
  have hq := (analyticOnNhd_jacobiSecondKind α β r s n).continuousOn.mono havoid
  have hi := Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hq.fun_mul hf) subset_rfl
  have hj := Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hq.fun_mul hg) subset_rfl
  have he : (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * (f z - g z))) =
      (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) -
        (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * g z)) := by
    funext z
    ext; simp [mul_sub]
  unfold jacobiContourCoefficient
  rw [he, Γ.integral_sub hi hj, mul_sub]

/-- Contour coefficients commute with uniform limits of continuous functions.
The limiting function only needs to be defined on the cycle. -/
theorem tendsto_jacobiContourCoefficient (α β r s : ℂ) (n : ℕ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ N, ContinuousOn (F N) Γ.range)
    (hlim : TendstoUniformlyOn F f atTop Γ.range) :
    Tendsto (fun N => jacobiContourCoefficient α β r s n Γ (F N)) atTop
      (𝓝 (jacobiContourCoefficient α β r s n Γ f)) := by
  have hf : ContinuousOn f Γ.range := hlim.continuousOn (Frequently.of_forall hF)
  obtain ⟨C, hC, hbound⟩ := exists_norm_jacobiContourCoefficient_le α β r s n Γ hΓ havoid
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hCδ⟩ := exists_pos_mul_lt hε C
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) δ hδ] with N hN
  rw [dist_eq_norm, ← jacobiContourCoefficient_sub α β r s n Γ hΓ havoid (hF N) hf]
  apply (hbound _ δ ?_).trans_lt hCδ
  intro z hz
  exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hN z hz)

/-- A finite Jacobi sum has the expected contour coefficients, weighted by the
cycle index. Indices outside the finite sum have coefficient zero. -/
theorem jacobiContourCoefficient_sum (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (a : ℕ → ℂ) (n N : ℕ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    jacobiContourCoefficient α β r s n Γ
      (fun z => ∑ m ∈ Finset.range N, a m * (jacobiOn α β r s m).eval z) =
      if n < N then Γ.index r * a n else 0 := by
  have h := jacobiContourCoefficient_polynomial α β r s n
    (∑ m ∈ Finset.range N, a m • jacobiOn α β r s m) Γ hΓ havoid
  simpa [eval_finsetSum, eval_smul, map_sum, map_smul,
    carlsonJacobiCoefficient_apply_jacobiOn α β r s hc, Finset.mem_range] using h

/-- Uniform convergence of a Jacobi series on a cycle permits extraction of each
coefficient by the second-kind kernel. The cycle's index remains explicit. -/
theorem jacobiContourCoefficient_eq_of_tendstoUniformlyOn (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (a : ℕ → ℂ) {f : ℂ → ℂ}
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hlim : TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, a m * (jacobiOn α β r s m).eval z)
      f atTop Γ.range) (n : ℕ) :
    jacobiContourCoefficient α β r s n Γ f = Γ.index r * a n := by
  have hF (N : ℕ) : ContinuousOn
      (fun z => ∑ m ∈ Finset.range N, a m * (jacobiOn α β r s m).eval z) Γ.range :=
    (continuous_finsetSum _ (fun m _ => continuous_const.mul
      (jacobiOn α β r s m).continuous)).continuousOn
  have h := tendsto_jacobiContourCoefficient α β r s n Γ hΓ havoid hF hlim
  have he : (fun N => jacobiContourCoefficient α β r s n Γ
      (fun z => ∑ m ∈ Finset.range N, a m * (jacobiOn α β r s m).eval z))
      =ᶠ[atTop] (fun _ => Γ.index r * a n) := by
    filter_upwards [eventually_gt_atTop n] with N hN
    rw [jacobiContourCoefficient_sum α β r s hc a n N Γ hΓ havoid, ite_eq_left hN]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' he.symm)

/-- Two Jacobi series converging uniformly to the same function on a cycle of
nonzero index have identical coefficients. -/
theorem jacobiSeries_coefficients_unique (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) {a b : ℕ → ℂ} {f : ℂ → ℂ}
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r ≠ 0)
    (ha : TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, a m * (jacobiOn α β r s m).eval z)
      f atTop Γ.range)
    (hb : TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, b m * (jacobiOn α β r s m).eval z)
      f atTop Γ.range) : a = b := by
  funext n
  apply mul_left_cancel₀ hind
  exact (jacobiContourCoefficient_eq_of_tendstoUniformlyOn α β r s hc a Γ hΓ havoid ha n).symm.trans
    (jacobiContourCoefficient_eq_of_tendstoUniformlyOn α β r s hc b Γ hΓ havoid hb n)

end Carlson.TwoVariable
