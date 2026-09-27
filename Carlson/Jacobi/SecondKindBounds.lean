/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexSecondKind
public import Pochhammer.BetaShift

/-!
# Bounds for Jacobi functions of the second kind as the degree increases

At sufficiently large degrees, every fixed pair of complex Jacobi parameters
admits the native Euler representation. Raising the degree multiplies its weight
by `t(1-t)`, which is bounded by `1/4` on the unit interval. Together with the
reciprocal beta normalization, this gives uniform bounds wherever the evaluation
point stays a positive distance from the endpoint segment. The endpoints may be
arbitrary complex numbers, including coincident endpoints.

The distance-based estimate is preliminary. A second estimate keeps the
combined weight-resolvent factor intact; it can give the elliptic rate when
that factor has a suitable bound. Sharp bounds on exterior rays are proved
in `Carlson.Jacobi.SecondKindRayBounds`.

## Main results

* `exists_jacobiWeight_shift_bound`: a bounded continuous weight after a finite shift.
* `norm_jacobiSecondKind_add_le`: a bound uniform in the evaluation point and degree.
* `norm_jacobiSecondKind_add_le_of_kernel_bound`: a bound that retains the
  combined weight-resolvent factor and can attain the elliptic rate.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.4–7.5 and the Euler representation underlying §7.8.
-/

public noncomputable section
open Complex Polynomial Set MeasureTheory Filter
open scoped Topology
namespace Polynomial

/-- Simultaneous integer shifts factor out an ordinary polynomial from the
complex weight, away from its two endpoints. -/
theorem complexJacobiWeight_add_nat (a b z : ℂ) (k : ℕ) (hz : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    complexJacobiWeight (a + k) (b + k) z =
      complexJacobiWeight a b z * (z * (1 - z)) ^ k := by
  simp only [complexJacobiWeight, cpow_add _ _ hz, cpow_add _ _ hz1, cpow_natCast, mul_pow]
  ring

/-- After a finite degree shift the Jacobi weight is continuous and bounded on
the closed unit interval, for arbitrary complex parameters. -/
theorem exists_jacobiWeight_shift_bound (α β : ℂ) :
    ∃ N : ℕ, 0 < (α + N).re ∧ 0 < (β + N).re ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ‖complexJacobiWeight (α + N) (β + N) t‖ ≤ B := by
  obtain ⟨N, ha, hb⟩ := ((eventually_re_add_nat_pos α).and
    (eventually_re_add_nat_pos β)).exists
  have hcont : Continuous (fun t : ℝ => complexJacobiWeight (α + N) (β + N) t) := by
    simpa only [sub_add_cancel] using
      (continuous_complexJacobiWeight_succ (α := α + N - 1) (β := β + N - 1)
        (by simp only [sub_re, one_re]; linarith)
        (by simp only [sub_re, one_re]; linarith))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨N, ha, hb, max B 0, le_max_right _ _, fun t ht => (hB t ht).trans (le_max_left _ _)⟩

/-- A fixed bounded base weight controls all its higher degree shifts by
successive powers of one quarter. -/
theorem norm_complexJacobiWeight_add_nat_le {a b : ℂ} (hb : 0 < b.re)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖complexJacobiWeight a b t‖ ≤ B)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖complexJacobiWeight (a + k) (b + k) t‖ ≤ B * (1 / 4 : ℝ) ^ k := by
  by_cases ht1 : t = 1
  · subst t
    have hb0 : b + k ≠ 0 := ne_zero_of_re_pos (by
      simp only [add_re, natCast_re]
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
    simp [complexJacobiWeight, zero_cpow hb0, hB]
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hz : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have hz1 : 1 - (t : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]
    exact ofReal_ne_zero.mpr (sub_pos.mpr htlt).ne'
  rw [complexJacobiWeight_add_nat a b t k hz hz1, norm_mul, norm_pow]
  have he : ‖(t : ℂ) * (1 - t)‖ = t * (1 - t) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2))]
  rw [he]
  have hquarter : t * (1 - t) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (t - 1 / 2)]
  exact mul_le_mul (hbound t ⟨ht.1.le, ht.2⟩)
    (pow_le_pow_left₀ (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)) hquarter k)
    (pow_nonneg (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)) k) hB

end Polynomial

namespace Carlson.TwoVariable

/-- A positive lower bound for distance to a point bounds the integer
resolvent by the corresponding negative power of that distance. -/
theorem norm_jacobiResolvent_le (n : ℕ) {z t : ℂ} {d : ℝ} (hd : 0 < d)
    (hdt : d ≤ ‖z - t‖) :
    ‖(z - t) ^ (-(n + 1 : ℤ))‖ ≤ (d⁻¹) ^ (n + 1) := by
  rw [zpow_neg, show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega,
    zpow_natCast, norm_inv, norm_pow, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hd hdt) _

/-- A degree-uniform bound for second-kind Jacobi functions away from the endpoint
segment. The parameters need only enter the right half-plane after the base shift. -/
theorem norm_jacobiSecondKind_add_le (α β r s : ℂ) (N k : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re)
    {B d : ℝ} (hB : 0 ≤ B) (hd : 0 < d)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖complexJacobiWeight (α + N) (β + N) t‖ ≤ B)
    {z : ℂ} (hz : z ∉ segment ℝ r s)
    (hdist : ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    ‖jacobiSecondKind α β r s (N + k) z‖ ≤
      ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ *
        (B * (1 / 4 : ℝ) ^ k * (d⁻¹) ^ (N + k + 1)) := by
  have ha : 0 < (α + (N + k : ℕ) + 1).re := by
    simp only [add_re, natCast_re, Nat.cast_add, one_re] at *
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hb : 0 < (β + (N + k : ℕ) + 1).re := by
    simp only [add_re, natCast_re, Nat.cast_add, one_re] at *
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [jacobiSecondKind_eq_complexEulerIntegral_on_segment r s (N + k) ha hb hz, norm_mul]
  have he (a : ℂ) : a + (N + k : ℕ) + 1 = a + N + 1 + k := by push_cast; ring
  rw [he α, he β]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => complexJacobiWeight (α + (N + k)) (β + (N + k)) t *
      (z - ((t : ℂ) * r + (1 - t) * s)) ^ (-((N + k : ℕ) + 1 : ℤ)))
    (C := B * (1 / 4 : ℝ) ^ k * (d⁻¹) ^ (N + k + 1)) ?_
  · simpa using hi
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  rw [norm_mul]
  have htseg : (t : ℂ) * r + (1 - t) * s ∈ segment ℝ r s :=
    ⟨t, 1 - t, ht.1.le, sub_nonneg.mpr ht.2, by ring, by simp [real_smul]⟩
  apply mul_le_mul _ (norm_jacobiResolvent_le (N + k) hd (hdist _ htseg))
    (norm_nonneg _) (mul_nonneg hB (by positivity))
  simpa only [Nat.cast_add, ← add_assoc] using
    norm_complexJacobiWeight_add_nat_le hβ hB hbound k ht


/-- Bounding the combined Euler weight and resolvent retains the saddle-point
rate, instead of estimating the two factors separately. The distance bound is
used only for the fixed initial degree. -/
theorem norm_jacobiSecondKind_add_le_of_kernel_bound (α β r s : ℂ) (N k : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re)
    {B d q : ℝ} (hB : 0 ≤ B) (hd : 0 < d) (hq : 0 ≤ q)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖complexJacobiWeight (α + N) (β + N) t‖ ≤ B)
    {z : ℂ} (hz : z ∉ segment ℝ r s)
    (hdist : ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖)
    (hkernel : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖((t : ℂ) * (1 - t)) / (z - (t * r + (1 - t) * s))‖ ≤ q) :
    ‖jacobiSecondKind α β r s (N + k) z‖ ≤
      ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ *
        (B * (d⁻¹) ^ (N + 1) * q ^ k) := by
  have ha : 0 < (α + (N + k : ℕ) + 1).re := by
    simp only [add_re, natCast_re, Nat.cast_add, one_re] at *
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hb : 0 < (β + (N + k : ℕ) + 1).re := by
    simp only [add_re, natCast_re, Nat.cast_add, one_re] at *
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [jacobiSecondKind_eq_complexEulerIntegral_on_segment r s (N + k) ha hb hz, norm_mul]
  have he (a : ℂ) : a + (N + k : ℕ) + 1 = a + N + 1 + k := by push_cast; ring
  rw [he α, he β]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => complexJacobiWeight (α + (N + k)) (β + (N + k)) t *
      (z - ((t : ℂ) * r + (1 - t) * s)) ^ (-((N + k : ℕ) + 1 : ℤ)))
    (C := B * (d⁻¹) ^ (N + 1) * q ^ k) ?_
  · simpa using hi
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  by_cases ht1 : t = 1
  · subst t
    have hb0 : β + ((N : ℂ) + k) ≠ 0 := ne_zero_of_re_pos (by
      simp only [add_re, natCast_re, Nat.cast_add] at *
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
    simp only [ofReal_one, complexJacobiWeight, one_cpow, sub_self, zero_cpow hb0,
      mul_zero, zero_mul, norm_zero]
    positivity
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  let w : ℂ := t * r + (1 - t) * s
  have hw : w ∈ segment ℝ r s :=
    ⟨t, 1 - t, ht.1.le, sub_nonneg.mpr ht.2, by ring, by simp [w, real_smul]⟩
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have ht01 : 1 - (t : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]
    exact ofReal_ne_zero.mpr (sub_pos.mpr ht'.2).ne'
  have hfactor : complexJacobiWeight (α + (N + k)) (β + (N + k)) t *
      (z - w) ^ (-((N + k : ℕ) + 1 : ℤ)) =
      (complexJacobiWeight (α + N) (β + N) t * (z - w) ^ (-(N + 1 : ℤ))) *
        (((t : ℂ) * (1 - t)) / (z - w)) ^ k := by
    rw [show α + ((N : ℂ) + k) = (α + N) + k by ring,
      show β + ((N : ℂ) + k) = (β + N) + k by ring,
      complexJacobiWeight_add_nat _ _ _ _ ht0 ht01]
    simp only [zpow_neg, show (N + k : ℕ) + 1 = ((N + k + 1 : ℕ) : ℤ) by omega,
      show (N : ℤ) + 1 = ((N + 1 : ℕ) : ℤ) by omega, zpow_natCast,
      show N + k + 1 = (N + 1) + k by omega, pow_add, mul_inv_rev, div_pow]
    ring
  change ‖complexJacobiWeight _ _ t * (z - w) ^ _‖ ≤ _
  rw [hfactor, norm_mul, norm_mul, norm_pow]
  exact mul_le_mul
    (mul_le_mul (hbound t ⟨ht.1.le, ht.2⟩)
      (norm_jacobiResolvent_le N hd (hdist w hw)) (norm_nonneg _) hB)
    (pow_le_pow_left₀ (norm_nonneg _) (hkernel t ht') k) (by positivity) (by positivity)

end Carlson.TwoVariable
