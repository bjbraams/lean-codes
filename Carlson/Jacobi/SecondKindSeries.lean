/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindBounds
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Preliminary convergence regions for second-kind Jacobi series

If the coefficients satisfy `‖a n‖ ≤ C R^n`, the series of second-kind Jacobi
functions converges absolutely and uniformly on compact sets whose distance from
the endpoint segment exceeds `R`. The Jacobi parameters may be arbitrary complex
numbers. A finite initial part is controlled by compactness; the remaining terms
use the Euler integral and the simultaneous beta-shift estimates.

Distance from the segment gives a sufficient convergence region. This does not
yet identify the sharp confocal ellipse of convergence or prove divergence on
the other side of that ellipse.

## Main results

* `exists_summable_norm_mul_jacobiSecondKind`: a common summable majorant on
  compact sets separated from the segment by more than the coefficient growth rate.
* `tendstoUniformlyOn_sum_jacobiSecondKind`: uniform convergence on these sets.
* `tendstoLocallyUniformlyOn_sum_jacobiSecondKind`: local uniform convergence on
  the open region where distance from the segment exceeds the coefficient growth rate.
* `analyticOnNhd_tsum_jacobiSecondKind`: holomorphy of the sum on that region.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.5, especially the second-kind series in Theorem 7.5-3.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter Metric
open scoped Topology

/-- Geometric coefficient growth gives a summable uniform majorant for the
second-kind series on compact sets sufficiently far from the endpoint segment. -/
theorem exists_summable_norm_mul_jacobiSecondKind (α β r s : ℂ) {a : ℕ → ℂ}
    {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {K : Set ℂ} (hK : IsCompact K)
    (hdist : ∀ z ∈ K, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n z, z ∈ K →
      ‖a n * jacobiSecondKind α β r s n z‖ ≤ M n := by
  have havoid : K ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzs
    have := hdist z hz z hzs
    simp only [sub_self, norm_zero] at this
    linarith
  obtain ⟨N, hα, hβ, B, hB, hbound⟩ := exists_jacobiWeight_shift_bound α β
  have hD (n : ℕ) : ∃ D : ℝ, ∀ z ∈ K, ‖a n * jacobiSecondKind α β r s n z‖ ≤ D :=
    hK.exists_bound_of_continuousOn
      (continuousOn_const.mul ((analyticOnNhd_jacobiSecondKind α β r s n).continuousOn.mono havoid))
  choose D hD using hD
  let t := R / (4 * d)
  have ht : 0 ≤ t := div_nonneg hR (by positivity)
  have ht4 : 4 * t < 1 := by
    dsimp only [t]
    rw [show 4 * (R / (4 * d)) = R / d by ring, div_lt_one hd]
    exact hRd
  let A := C * B * R ^ N * (d⁻¹) ^ (N + 1)
  let tail := fun k : ℕ => A *
    (‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ * t ^ k)
  have htail : Summable tail :=
    (summable_norm_betaShiftNormalization_mul_pow (α + N + 1) (β + N + 1) ht ht4).mul_left A
  let M := fun n : ℕ => if n < N then D n else tail (n - N)
  have hM : Summable M := by
    apply (summable_nat_add_iff N).mp
    simpa [M, Nat.not_lt.mpr (Nat.le_add_left N _)] using htail
  refine ⟨M, hM, ?_⟩
  intro n z hz
  by_cases hn : n < N
  · simpa only [M, ite_eq_left hn] using hD n z hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
  have hq := norm_jacobiSecondKind_add_le α β r s N k hα hβ hB hd hbound (havoid hz)
    (hdist z hz)
  rw [norm_mul]
  apply (mul_le_mul (ha _) hq (norm_nonneg _) (mul_nonneg hC (pow_nonneg hR _))).trans
  apply le_of_eq
  simp only [M, Nat.not_lt.mpr (Nat.le_add_right N k), ite_false, Nat.add_sub_cancel_left,
    tail, A, t]
  rw [show N + k + 1 = (N + 1) + k by omega]
  simp only [pow_add, div_pow, mul_pow]
  ring

/-- The second-kind Jacobi series converges uniformly on compact sets separated
from the endpoint segment by more than the geometric growth rate of its coefficients. -/
theorem tendstoUniformlyOn_sum_jacobiSecondKind (α β r s : ℂ) {a : ℕ → ℂ}
    {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {K : Set ℂ} (hK : IsCompact K)
    (hdist : ∀ z ∈ K, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, a n * jacobiSecondKind α β r s n z)
      (fun z => ∑' n, a n * jacobiSecondKind α β r s n z) atTop K := by
  obtain ⟨M, hM, hbound⟩ :=
      exists_summable_norm_mul_jacobiSecondKind α β r s hC hR hd hRd ha hK hdist
  exact tendstoUniformlyOn_tsum_nat hM hbound

/-- On the same convergence region, the second-kind series is absolutely summable. -/
theorem summable_norm_mul_jacobiSecondKind (α β r s : ℂ) {a : ℕ → ℂ}
    {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {z : ℂ}
    (hdist : ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    Summable (fun n => ‖a n * jacobiSecondKind α β r s n z‖) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_mul_jacobiSecondKind α β r s hC hR hd hRd ha
    (isCompact_singleton (x := z)) (by intro w hw; simpa only [mem_singleton_iff.mp hw] using hdist)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n z (mem_singleton z)) hM

/-- Second-kind Jacobi series converge locally uniformly wherever distance from
the endpoint segment exceeds a geometric bound for coefficient growth. -/
theorem tendstoLocallyUniformlyOn_sum_jacobiSecondKind (α β r s : ℂ) {a : ℕ → ℂ}
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) :
    TendstoLocallyUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, a n * jacobiSecondKind α β r s n z)
      (fun z => ∑' n, a n * jacobiSecondKind α β r s n z) atTop
      {z | R < infDist z (segment ℝ r s)} := by
  have hU : IsOpen {z : ℂ | R < infDist z (segment ℝ r s)} :=
    isOpen_lt continuous_const (continuous_infDist_pt (segment ℝ r s))
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne
        (continuous_infDist_pt (segment ℝ r s)).continuousOn
    have hd : R < infDist z (segment ℝ r s) := hKU hz
    apply tendstoUniformlyOn_sum_jacobiSecondKind α β r s hC hR (hR.trans_lt hd) hd ha hK
    intro w hw v hv
    have hm : infDist z (segment ℝ r s) ≤ infDist w (segment ℝ r s) := hmin hw
    exact hm.trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem hv)
  · have hK0 : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hK0, TendstoUniformlyOn]

/-- The sum of a second-kind Jacobi series is holomorphic on the open region
where distance from the segment exceeds the geometric coefficient growth rate.
No restriction on the individual complex parameters or distinctness of endpoints is needed. -/
theorem analyticOnNhd_tsum_jacobiSecondKind (α β r s : ℂ) {a : ℕ → ℂ}
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) :
    AnalyticOnNhd ℂ (fun z => ∑' n, a n * jacobiSecondKind α β r s n z)
      {z | R < infDist z (segment ℝ r s)} := by
  have hU : IsOpen {z : ℂ | R < infDist z (segment ℝ r s)} :=
    isOpen_lt continuous_const (continuous_infDist_pt (segment ℝ r s))
  have havoid : {z | R < infDist z (segment ℝ r s)} ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzs
    change R < infDist z (segment ℝ r s) at hz
    have : R < (0 : ℝ) := by simpa only [infDist_zero_of_mem hzs] using hz
    linarith
  apply ((tendstoLocallyUniformlyOn_sum_jacobiSecondKind α β r s hC hR ha).differentiableOn
    (Eventually.of_forall fun N => ?_) hU).analyticOnNhd hU
  exact DifferentiableOn.fun_sum fun n _ => (differentiableOn_const (a n)).fun_mul
    ((analyticOnNhd_jacobiSecondKind α β r s n).differentiableOn.mono havoid)

end Carlson.TwoVariable
