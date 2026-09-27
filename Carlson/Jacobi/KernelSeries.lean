/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.PolynomialBounds
public import Carlson.Jacobi.SecondKindSeries

/-!
# Uniform summability of Jacobi kernel series

A geometric bound for the monic polynomials combines with the second-kind Euler
estimates to give a summable majorant for their products on separated compact
sets. These estimates justify uniform convergence of the candidate Cauchy-kernel
series. The sum is identified with the Cauchy kernel on an initial region in
`Carlson.Jacobi.CauchyKernel`; the full confocal-ellipse region remains further work.

## Main results

* `exists_summable_norm_jacobiOn_mul_jacobiSecondKind`: a common summable majorant
  on a product of sets under an explicit geometric polynomial bound.
* `tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind`: uniform convergence
  of the product series on that product set.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.5–7.6 (estimates underlying Lemma 7.6-1).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter
open scoped Topology

/-- A geometric bound for a family of coefficients gives a common summable
majorant for the corresponding second-kind series on separated compact sets. -/
theorem exists_summable_norm_family_mul_jacobiSecondKind (α β r s : ℂ)
    {a : ℕ → ℂ → ℂ} {K L : Set ℂ} {C R d : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (ha : ∀ n x, x ∈ K → ‖a n x‖ ≤ C * R ^ n) (hL : IsCompact L)
    (hdist : ∀ z ∈ L, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x, x ∈ K → ∀ z, z ∈ L →
      ‖a n x * jacobiSecondKind α β r s n z‖ ≤ M n := by
  have hb (n : ℕ) : ‖(C : ℂ) * (R : ℂ) ^ n‖ = C * R ^ n := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC, abs_of_nonneg hR]
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_mul_jacobiSecondKind α β r s
    hC hR hd hRd (fun n => (hb n).le) hL hdist
  refine ⟨M, hM, ?_⟩
  intro n x hx z hz
  have hm := hbound n z hz
  rw [norm_mul, hb] at hm
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (ha n x hx) (norm_nonneg _)).trans hm

/-- The polynomial and second-kind products have a common summable majorant
when the exterior set is farther from the segment than the polynomial growth rate. -/
theorem exists_summable_norm_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    {K L : Set ℂ} {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n x, x ∈ K → ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (hL : IsCompact L)
    (hdist : ∀ z ∈ L, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x, x ∈ K → ∀ z, z ∈ L →
      ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z‖ ≤ M n :=
  exists_summable_norm_family_mul_jacobiSecondKind α β r s hC hR hd hRd hp hL hdist

/-- The candidate Cauchy-kernel series converges uniformly on a product of sets
satisfying the geometric polynomial bound and the distance separation condition. -/
theorem tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    {K L : Set ℂ} {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n x, x ∈ K → ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (hL : IsCompact L)
    (hdist : ∀ z ∈ L, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    TendstoUniformlyOn
      (fun N (xz : ℂ × ℂ) => ∑ n ∈ Finset.range N,
        (jacobiOn α β r s n).eval xz.1 * jacobiSecondKind α β r s n xz.2)
      (fun xz => ∑' n, (jacobiOn α β r s n).eval xz.1 *
        jacobiSecondKind α β r s n xz.2) atTop (K ×ˢ L) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiOn_mul_jacobiSecondKind
    α β r s hC hR hd hRd hp hL hdist
  exact tendstoUniformlyOn_tsum_nat hM (fun n xz hxz => hbound n xz.1 hxz.1 xz.2 hxz.2)

end Carlson.TwoVariable
