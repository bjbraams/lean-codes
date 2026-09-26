/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Confocal elliptic domains for Jacobi series

Carlson's mean radius is the arithmetic mean of the semimajor and semiminor
axes of the ellipse through a point, with fixed foci `r, s`. A formula in real
norms avoids choosing complex square roots. Its minimum is `‖r-s‖/4`, attained
precisely on the focal segment. When the foci coincide the radius is ordinary
distance, and the elliptic disks become metric disks.

## Main results

* `jacobiEllipseRadius_eq_min_iff`: the minimum locus is the focal segment.
* `jacobiEllipseRadius_lt_iff`: the equivalent sum-of-distances inequality.
* `convex_jacobiEllipseDisk`: convexity of every nondegenerate elliptic disk.
* `isCompact_jacobiClosedEllipseDisk`: compactness of closed elliptic disks.
* `jacobiEllipseRadius_affine`: covariance under complex affine maps.
* `exists_jacobiClosedEllipseDisk_subset`: every open neighborhood of the focal
  segment contains a nondegenerate closed elliptic disk.

These are the domains for the convergence theory; no large-degree asymptotic
estimate or Jacobi-series convergence assertion is made in this module.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.5, equations (1)–(5).
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Set Complex

/-- Carlson's mean radius of the confocal ellipse through `z`. -/
def jacobiEllipseRadius (r s z : ℂ) : ℝ :=
  (‖z - r‖ + ‖z - s‖ + Real.sqrt ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2)) / 4

/-- The open elliptic disk of prescribed mean radius. -/
def jacobiEllipseDisk (r s : ℂ) (ρ : ℝ) : Set ℂ := {z | jacobiEllipseRadius r s z < ρ}

/-- The closed elliptic disk of prescribed mean radius. -/
def jacobiClosedEllipseDisk (r s : ℂ) (ρ : ℝ) : Set ℂ := {z | jacobiEllipseRadius r s z ≤ ρ}

/-- The focal distance is bounded by the sum of distances from any point. -/
private theorem focal_distance_le (r s z : ℂ) : ‖r - s‖ ≤ ‖z - r‖ + ‖z - s‖ := by
  simpa only [dist_eq_norm, norm_sub_rev r z] using dist_triangle r z s

/-- The mean radius is continuous, including on the focal segment. -/
theorem continuous_jacobiEllipseRadius (r s : ℂ) : Continuous (jacobiEllipseRadius r s) := by
  unfold jacobiEllipseRadius
  fun_prop

/-- Every mean radius is at least one quarter of the focal distance. -/
theorem le_jacobiEllipseRadius (r s z : ℂ) : ‖r - s‖ / 4 ≤ jacobiEllipseRadius r s z := by
  have h := focal_distance_le r s z
  have := Real.sqrt_nonneg ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2)
  unfold jacobiEllipseRadius
  linarith

/-- A point has minimum mean radius exactly when it lies on the focal segment. -/
theorem jacobiEllipseRadius_eq_min_iff (r s z : ℂ) :
    jacobiEllipseRadius r s z = ‖r - s‖ / 4 ↔ z ∈ segment ℝ r s := by
  have hd := focal_distance_le r s z
  have hseg : ‖z - r‖ + ‖z - s‖ = ‖r - s‖ ↔ z ∈ segment ℝ r s := by
    simpa only [dist_eq_norm, norm_sub_rev r z, mem_segment_iff_wbtw] using
      (dist_add_dist_eq_iff (a := r) (b := z) (c := s))
  rw [← hseg]
  constructor
  · intro h
    have := Real.sqrt_nonneg ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2)
    unfold jacobiEllipseRadius at h
    linarith
  · intro h
    simp [jacobiEllipseRadius, h]

/-- At coincident foci, the mean radius is ordinary distance. -/
@[simp] theorem jacobiEllipseRadius_self (r z : ℂ) : jacobiEllipseRadius r r z = ‖z - r‖ := by
  simp only [jacobiEllipseRadius, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
    Real.sqrt_sq (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  ring

/-- Coincident foci give the ordinary open disk. -/
@[simp] theorem jacobiEllipseDisk_self (r : ℂ) (ρ : ℝ) :
    jacobiEllipseDisk r r ρ = Metric.ball r ρ := by
  ext z
  simp [jacobiEllipseDisk, Metric.mem_ball, dist_eq_norm]

/-- The sum-of-distances description of a nondegenerate elliptic disk. -/
theorem jacobiEllipseRadius_lt_iff (r s z : ℂ) {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    jacobiEllipseRadius r s z < ρ ↔ ‖z - r‖ + ‖z - s‖ < 2 * ρ + ‖r - s‖ ^ 2 / (8 * ρ) := by
  let S := ‖z - r‖ + ‖z - s‖
  let D := ‖r - s‖
  have hD : 0 ≤ D := norm_nonneg _
  have hS : D ≤ S := focal_distance_le r s z
  have hp : 0 < ρ := lt_of_le_of_lt (by positivity : 0 ≤ D / 4) hρ
  have hs : 0 ≤ S ^ 2 - D ^ 2 := by nlinarith
  have ht := Real.sqrt_nonneg (S ^ 2 - D ^ 2)
  have ht2 := Real.sq_sqrt hs
  change (S + Real.sqrt (S ^ 2 - D ^ 2)) / 4 < ρ ↔ S < 2 * ρ + D ^ 2 / (8 * ρ)
  rw [add_comm (2 * ρ), ← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity : 0 < 8 * ρ)]
  constructor
  · intro h
    have hpos : 0 < 4 * ρ - S + Real.sqrt (S ^ 2 - D ^ 2) := by linarith
    have hpos' : 0 < 4 * ρ - S - Real.sqrt (S ^ 2 - D ^ 2) := by linarith
    nlinarith [mul_pos hpos hpos']
  · intro h
    have hD' : D < 4 * ρ := by linarith
    have hSq : D ^ 2 < (4 * ρ) ^ 2 := by nlinarith
    have hS' : S < 4 * ρ := by nlinarith
    have hroot : Real.sqrt (S ^ 2 - D ^ 2) < 4 * ρ - S := by nlinarith
    linarith

/-- Elliptic disks are open. -/
theorem isOpen_jacobiEllipseDisk (r s : ℂ) (ρ : ℝ) : IsOpen (jacobiEllipseDisk r s ρ) :=
  isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const

/-- A nondegenerate elliptic disk is convex. -/
theorem convex_jacobiEllipseDisk (r s : ℂ) {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    Convex ℝ (jacobiEllipseDisk r s ρ) := by
  have h := ((convexOn_dist r (convex_univ : Convex ℝ (univ : Set ℂ))).add
    (convexOn_dist s convex_univ)).convex_lt (2 * ρ + ‖r - s‖ ^ 2 / (8 * ρ))
  have he : jacobiEllipseDisk r s ρ =
      {z ∈ (univ : Set ℂ) | dist z r + dist z s < 2 * ρ + ‖r - s‖ ^ 2 / (8 * ρ)} := by
    ext z
    simp only [jacobiEllipseDisk, mem_ofPred_eq, mem_univ, true_and, dist_eq_norm,
      jacobiEllipseRadius_lt_iff r s z hρ]
  rwa [he]

/-- Closed elliptic disks are compact, also at or below the degenerate radius. -/
theorem isCompact_jacobiClosedEllipseDisk (r s : ℂ) (ρ : ℝ) :
    IsCompact (jacobiClosedEllipseDisk r s ρ) := by
  have hc : IsClosed (jacobiClosedEllipseDisk r s ρ) :=
    isClosed_le (continuous_jacobiEllipseRadius r s) continuous_const
  apply (isCompact_closedBall r (4 * ρ)).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have ht := Real.sqrt_nonneg ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2)
  change jacobiEllipseRadius r s z ≤ ρ at hz
  unfold jacobiEllipseRadius at hz
  have := norm_nonneg (z - s)
  linarith

/-- Affine changes scale mean radii by the norm of the complex scale factor.
Zero scales and coincident endpoints are included. -/
theorem jacobiEllipseRadius_affine (r s z c d : ℂ) :
    jacobiEllipseRadius (c * r + d) (c * s + d) (c * z + d) =
      ‖c‖ * jacobiEllipseRadius r s z := by
  have he (u v : ℂ) : c * u + d - (c * v + d) = c * (u - v) := by ring
  simp only [jacobiEllipseRadius, he, norm_mul]
  rw [show (‖c‖ * ‖z - r‖ + ‖c‖ * ‖z - s‖) ^ 2 - (‖c‖ * ‖r - s‖) ^ 2 =
      ‖c‖ ^ 2 * ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  ring

/-- Every nondegenerate open elliptic disk contains its focal segment. -/
theorem segment_subset_jacobiEllipseDisk (r s : ℂ) {ρ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) :
    segment ℝ r s ⊆ jacobiEllipseDisk r s ρ := by
  intro z hz
  change jacobiEllipseRadius r s z < ρ
  rwa [(jacobiEllipseRadius_eq_min_iff r s z).mpr hz]

/-- An open neighborhood of the focal segment contains a closed elliptic disk
of strictly larger than minimum radius. Coincident foci are allowed. -/
theorem exists_jacobiClosedEllipseDisk_subset {r s : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hseg : segment ℝ r s ⊆ U) :
    ∃ ρ : ℝ, ‖r - s‖ / 4 < ρ ∧ jacobiClosedEllipseDisk r s ρ ⊆ U := by
  let a := ‖r - s‖ / 4
  let K := jacobiClosedEllipseDisk r s (a + 1) ∩ Uᶜ
  have hK : IsCompact K :=
    (isCompact_jacobiClosedEllipseDisk r s (a + 1)).inter_right hU.isClosed_compl
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne (continuous_jacobiEllipseRadius r s).continuousOn
    have hz0 : a < jacobiEllipseRadius r s z := by
      apply lt_of_le_of_ne (le_jacobiEllipseRadius r s z)
      intro he
      exact hz.2 (hseg ((jacobiEllipseRadius_eq_min_iff r s z).mp he.symm))
    have hz1 : jacobiEllipseRadius r s z ≤ a + 1 := hz.1
    refine ⟨(a + jacobiEllipseRadius r s z) / 2, ?_, ?_⟩
    · change a < (a + jacobiEllipseRadius r s z) / 2
      linarith
    intro w hw
    by_contra hwU
    have hw0 : jacobiEllipseRadius r s w ≤ (a + jacobiEllipseRadius r s z) / 2 := hw
    have hwK : w ∈ K := ⟨show jacobiEllipseRadius r s w ≤ a + 1 by linarith, hwU⟩
    have hwmin : jacobiEllipseRadius r s z ≤ jacobiEllipseRadius r s w := hmin hwK
    linarith
  · refine ⟨a + 1, by dsimp only [a]; linarith, ?_⟩
    intro w hw
    by_contra hwU
    exact hne ⟨w, hw, hwU⟩

end Carlson.TwoVariable
