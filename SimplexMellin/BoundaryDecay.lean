/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.FiniteRegularity
public import SimplexMellin.Image

/-!
# Frequency decay for kernels with nonzero boundary values

For a kernel with `N` derivatives near the closed simplex, its exponential-profile
Mellin transform has polynomial decay of order `N` on every positive vertical plane.
On a fixed-total-frequency hyperplane `∑ ξ i = t`, the radial Gamma factor is a
nonzero constant. Dividing it out gives the same decay for the unnormalized transform
`simplexMoment`. Smooth kernels therefore have rapid decay in all these directions,
without any vanishing at the faces.

These are fixed-total-frequency estimates. They do not assert the stationary-phase
asymptotics on rays where the total imaginary parameter tends to infinity.

## Main results

* `exists_norm_pow_mul_simplexMellin_le_of_contDiffNear`.
* `exists_norm_pow_mul_simplexMoment_le_hyperplane_of_contDiffNear`.
* `exists_norm_pow_mul_simplexMoment_le_hyperplane`.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped ContDiff FourierTransform
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- `C^N` boundary kernels give polynomial decay of order `N` for the full exponential-profile
Mellin transform, uniformly on each positive vertical plane. -/
theorem exists_norm_pow_mul_simplexMellin_le_of_contDiffNear [Nonempty ι] {N : ℕ}
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) :
    ∃ C, ∀ ξ : EuclideanSpace ℝ ι,
      ‖ξ‖ ^ N * ‖simplexMellin (mellinPlane c ξ) g‖ ≤ C := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  have hsm : ContDiff ℝ N (radialLog c φ g) := contDiff_radialLog_exp_of_contDiffNear hc hg
  obtain ⟨C, hC⟩ := Real.exists_norm_pow_mul_norm_fourier_le_of_integrable_iteratedFDeriv hsm
    (fun n hn => integrable_iteratedFDeriv_radialLog_exp_of_contDiffNear hc hg hn)
  refine ⟨C, fun ξ => ?_⟩
  have hpos : 0 < (∑ i, mellinPlane c ξ i).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty
  simpa only [fourier_radialLog hc hg.continuousOn (show ContinuousOn φ (Ioi 0) by fun_prop),
    φ, simplexMellinRadial_exp_eq hpos g] using hC ξ

/-- On a fixed-total-frequency hyperplane, the radial Gamma factor is constant. -/
theorem simplexMellin_eq_Gamma_mul_simplexMoment_of_sum_eq [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) (g : (ι → ℝ) → ℂ)
    (t : ℝ) (ξ : EuclideanSpace ℝ ι) (hξ : ∑ i, ξ i = t) :
    simplexMellin (mellinPlane c ξ) g =
      Gamma (((∑ i, c i : ℝ) : ℂ) - (2 * Real.pi : ℂ) * t * I) *
      simplexMoment (mellinPlane c ξ) g := by
  have hsum : ∑ i, mellinPlane c ξ i =
      ((∑ i, c i : ℝ) : ℂ) - (2 * Real.pi : ℂ) * t * I := by
    simp only [mellinPlane, Finset.sum_sub_distrib]
    rw [← ofReal_sum]
    have hz : ∑ i, (2 * Real.pi : ℂ) * (ξ i : ℂ) * I =
        (2 * Real.pi : ℂ) * t * I := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← ofReal_sum, hξ]
    rw [hz]
  have he := simplexMoment_eq_prod_Gamma_mul g 0 (mellinPlane c ξ) (fun i => by
    simpa using Gamma_ne_zero_of_re_pos (mellinPlane_mem hc ξ i))
  have hdiv : divMonomial 0 g = g := funext fun u => by simp [divMonomial]
  simp only [Nat.cast_zero, add_zero, hdiv] at he
  rw [simplexMellin, hsum, he]

/-- The unnormalized transform of a `C^N` boundary kernel decays to order `N` in all
fixed-sum imaginary directions, without any vanishing on the faces. -/
theorem exists_norm_pow_mul_simplexMoment_le_hyperplane_of_contDiffNear [Nonempty ι] {N : ℕ}
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (t : ℝ) :
    ∃ C, ∀ ξ : EuclideanSpace ℝ ι, (∑ i, ξ i = t) →
      ‖ξ‖ ^ N * ‖simplexMoment (mellinPlane c ξ) g‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_pow_mul_simplexMellin_le_of_contDiffNear hc hg
  have hsum : 0 < (∑ i, c i : ℝ) :=
    Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty
  let G : ℂ := Gamma (((∑ i, c i : ℝ) : ℂ) - (2 * Real.pi : ℂ) * t * I)
  have hΓ : 0 < ‖G‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by
      simpa [Complex.mul_re, Complex.mul_im] using hsum))
  refine ⟨C / ‖G‖, fun ξ hξ => ?_⟩
  apply (le_div_iff₀ hΓ).mpr
  have hb := hC ξ
  rw [simplexMellin_eq_Gamma_mul_simplexMoment_of_sum_eq hc g t ξ hξ, norm_mul] at hb
  calc
    (‖ξ‖ ^ N * ‖simplexMoment (mellinPlane c ξ) g‖) * ‖G‖ =
        ‖ξ‖ ^ N * (‖G‖ *
          ‖simplexMoment (mellinPlane c ξ) g‖) := by ring
    _ ≤ C := hb

/-- Smooth boundary kernels have rapid decay on positive fixed-sum vertical hyperplanes. -/
theorem exists_norm_pow_mul_simplexMoment_le_hyperplane [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (t : ℝ) (N : ℕ) :
    ∃ C, ∀ ξ : EuclideanSpace ℝ ι, (∑ i, ξ i = t) →
      ‖ξ‖ ^ N * ‖simplexMoment (mellinPlane c ξ) g‖ ≤ C :=
  exists_norm_pow_mul_simplexMoment_le_hyperplane_of_contDiffNear hc (hg N) t
end Dirichlet

end
