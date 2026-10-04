/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Order
public import Carlson.R.EulerTransform

/-!
# Euler inversion and the geometric mean

Euler inversion identifies the mean of order minus the total parameter with the
weighted geometric mean. Combined with order monotonicity, this locates every real
hypergeometric mean relative to the geometric mean, including orders outside the
Euler integral's convergence strip.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 6.
-/

open Complex ProbabilityTheory Dirichlet
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Euler inversion for ordinary R, inherited from the regularized identity. -/
theorem carlsonR_euler (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    carlsonR t b z = (∏ i, z i ^ (-b i)) *
      carlsonR (-(∑ i, b i) - t) b (fun i => (z i)⁻¹) := by
  simp only [carlsonR, regCarlsonR_euler t b hz]
  ring

/-- Real Euler inversion is valid at every real order on positive nodes and parameters. -/
theorem carlsonRReal_euler [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal t b x = (∏ i, x i ^ (-b i)) *
      carlsonRReal (-(∑ i, b i) - t) b (fun i => (x i)⁻¹) := by
  apply Complex.ofReal_injective
  have h := carlsonR_euler (t : ℂ) (fun i => (b i : ℂ))
    (z := fun i => (x i : ℂ)) (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
  rw [← ofReal_carlsonRReal t hb hx] at h
  simpa only [← Complex.ofReal_sum, ← Complex.ofReal_neg, ← Complex.ofReal_sub,
    ← Complex.ofReal_inv, ← Complex.ofReal_cpow (hx _).le,
    ← ofReal_carlsonRReal (-(∑ i, b i) - t) hb (fun i => inv_pos.mpr (hx i)),
    ← Complex.ofReal_prod, ← Complex.ofReal_mul] using h

/-- At order minus the total parameter, R is a product of powers of the nodes. -/
theorem carlsonRReal_neg_sum [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal (-(∑ i, b i)) b x = ∏ i, x i ^ (-b i) := by
  simpa only [sub_self, carlsonRReal_zero hb, mul_one] using
    carlsonRReal_euler (-(∑ i, b i)) hb hx

/-- Carlson's mean of order minus the total parameter is the weighted geometric mean. -/
theorem carlsonMeanReal_neg_sum [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal (-(∑ i, b i)) b x =
      Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  rw [carlsonMeanReal, ite_eq_right (neg_ne_zero.mpr hc.ne'), carlsonRReal_neg_sum hb hx]
  congr 1
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hx i) (-b i)).ne'), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_rpow (hx i)]
  ring

/-- Orders at least minus the total parameter give means at least as large as the
weighted geometric mean. -/
theorem geometric_le_carlsonMeanReal [Nonempty ι] {t : ℝ} {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (ht : -(∑ i, b i) ≤ t) :
    Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) ≤ carlsonMeanReal t b x := by
  rw [← carlsonMeanReal_neg_sum hb hx]
  exact monotone_carlsonMeanReal hb hx ht

/-- Orders at most minus the total parameter give means at most the geometric mean. -/
theorem carlsonMeanReal_le_geometric [Nonempty ι] {t : ℝ} {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (ht : t ≤ -(∑ i, b i)) :
    carlsonMeanReal t b x ≤ Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) := by
  rw [← carlsonMeanReal_neg_sum hb hx]
  exact monotone_carlsonMeanReal hb hx ht

/-- Euler inversion in logarithmic form, for positive real data. -/
theorem log_carlsonRReal_euler [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Real.log (carlsonRReal t b x) = -(∑ i, b i * Real.log (x i)) +
      Real.log (carlsonRReal (-(∑ i, b i) - t) b (fun i => (x i)⁻¹)) := by
  rw [carlsonRReal_euler t hb hx, Real.log_mul
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) (-b i))).ne'
    (carlsonRReal_pos _ hb (fun i => inv_pos.mpr (hx i))).ne',
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hx i) (-b i)).ne')]
  simp only [Real.log_rpow (hx _), neg_mul, Finset.sum_neg_distrib]

/-- The mean raised to its order is R, also at order zero. -/
theorem carlsonMeanReal_rpow_order [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x ^ t = carlsonRReal t b x := by
  by_cases ht : t = 0
  · simp only [ht, Real.rpow_zero, carlsonRReal_zero hb]
  · exact carlsonMeanReal_rpow ht hb hx

/-- Euler inversion for the real mean at every nonzero order, including when the
transformed order is zero (Carlson 1965, Theorem 6). -/
theorem carlsonMeanReal_euler [Nonempty ι] {t : ℝ} (ht : t ≠ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x = (∏ i, x i ^ (-b i)) ^ t⁻¹ *
      carlsonMeanReal (-(∑ i, b i) - t) b (fun i => (x i)⁻¹) ^ ((-(∑ i, b i) - t) / t) := by
  have hx' i := inv_pos.mpr (hx i)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  rw [carlsonMeanReal_eq_rpow ht hb hx, carlsonRReal_euler t hb hx,
    Real.mul_rpow hp.le (carlsonRReal_pos _ hb hx').le,
    ← carlsonMeanReal_rpow_order (-(∑ i, b i) - t) hb hx',
    ← Real.rpow_mul (carlsonMeanReal_pos _ b _).le, div_eq_mul_inv]

end Carlson
