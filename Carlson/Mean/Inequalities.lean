/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Real
public import Dirichlet.Real.StrictAverage
public import ToMathlib.Analysis.Convex.NegativePower
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Elementary bounds for real hypergeometric means

Jensen's inequality bounds the real R-average between the power of its weighted
arithmetic mean and the weighted powers of its nodes. Taking the appropriate root
gives Carlson's power-mean comparisons. The logarithmic case is handled directly,
so no nonzero-order assumption is imposed on comparisons with the arithmetic mean.

All parameters and nodes are positive; every real order is permitted. Non-strict
inequalities include singleton index types and constant node vectors. Strict
versions assume only that some two nodes differ; no choice of dimension is needed.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), 759–766.
* B. C. Carlson, *Some inequalities for hypergeometric functions*, Proc. AMS 17
  (1966), 32–39.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A finite positive node vector has a common strictly positive lower bound. -/
private theorem exists_pos_le_nodes {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  exact ⟨x i, hx i, fun j => hi j (Finset.mem_univ j)⟩

/-- Power kernels are continuous on every closed half-line bounded away from zero. -/
private theorem continuousOn_rpow_Ici (t : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => y ^ t) (Ici a) := fun y hy =>
  (Real.continuousAt_rpow_const y t (Or.inl (ne_of_gt (ha.trans_le hy)))).continuousWithinAt

/-- For orders at least one, the R-average lies between the power of the arithmetic mean
and the weighted power sum. -/
theorem carlsonRReal_bounds_of_one_le {t : ℝ} (ht : 1 ≤ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t ≤ carlsonRReal t b x ∧
      carlsonRReal t b x ≤ ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact convexOn_dirichlet_average_bounds hb isClosed_Ici hax
    ((convexOn_rpow ht).subset (fun _ hy => ha.le.trans hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- The power-average bounds reverse for orders between zero and one. -/
theorem carlsonRReal_bounds_of_nonneg_of_le_one {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal t b x ≤ (∑ i, (b i / ∑ j, b j) * x i) ^ t ∧
      (∑ i, (b i / ∑ j, b j) * x i ^ t) ≤ carlsonRReal t b x := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact concaveOn_dirichlet_average_bounds hb isClosed_Ici hax
    ((Real.concaveOn_rpow ht ht1).subset (fun _ hy => ha.le.trans hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- Negative orders have the convex power-average bounds, without an Euler-strip restriction. -/
theorem carlsonRReal_bounds_of_nonpos {t : ℝ} (ht : t ≤ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t ≤ carlsonRReal t b x ∧
      carlsonRReal t b x ≤ ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact convexOn_dirichlet_average_bounds hb isClosed_Ici hax
    ((Real.convexOn_rpow_of_nonpos ht).subset (fun _ hy => ha.trans_le hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- The logarithmic average lies between the weighted logarithms and the logarithm of
the arithmetic mean. -/
theorem carlsonLReal_zero_bounds {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonLReal 0 b x ≤ Real.log (∑ i, (b i / ∑ j, b j) * x i) ∧
      (∑ i, (b i / ∑ j, b j) * Real.log (x i)) ≤ carlsonLReal 0 b x := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  have h := concaveOn_dirichlet_average_bounds hb isClosed_Ici hax
    (strictConcaveOn_log_Ioi.concaveOn.subset (fun _ hy => ha.trans_le hy)
      (convex_Ici a))
    (fun y hy => (Real.continuousAt_log (ne_of_gt (ha.trans_le hy))).continuousWithinAt)
  simpa only [carlsonLReal, Real.rpow_zero, one_mul] using h

/-- At nonzero real order the exponential definition is the positive real root of R. -/
theorem carlsonMeanReal_eq_rpow {t : ℝ} (ht : t ≠ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x = carlsonRReal t b x ^ t⁻¹ := by
  simp [carlsonMeanReal, ht, Real.rpow_def_of_pos (carlsonRReal_pos t hb hx), div_eq_mul_inv]

/-- Raising a nonzero-order mean back to its order recovers R. -/
theorem carlsonMeanReal_rpow {t : ℝ} (ht : t ≠ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x ^ t = carlsonRReal t b x := by
  rw [carlsonMeanReal_eq_rpow ht hb hx,
    Real.rpow_inv_rpow (carlsonRReal_pos t hb hx).le ht]

/-- At orders at least one, the hypergeometric mean bounds the arithmetic mean from above. -/
theorem arithmetic_le_carlsonMeanReal {t : ℝ} (ht : 1 ≤ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∑ i, (b i / ∑ j, b j) * x i) ≤ carlsonMeanReal t b x := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hA : 0 < ∑ i, (b i / ∑ j, b j) * x i := by
    rw [← carlsonRReal_one hb x]; exact carlsonRReal_pos 1 hb hx
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hA.le t)
    (carlsonRReal_bounds_of_one_le ht hb hx).1 (inv_nonneg.mpr ht0.le)
  simpa only [Real.rpow_rpow_inv hA.le ht0.ne', ← carlsonMeanReal_eq_rpow ht0.ne' hb hx] using h

/-- At every order at most one, including zero and negative orders, the hypergeometric
mean is bounded above by the arithmetic mean. -/
theorem carlsonMeanReal_le_arithmetic {t : ℝ} (ht : t ≤ 1) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x ≤ ∑ i, (b i / ∑ j, b j) * x i := by
  have hA : 0 < ∑ i, (b i / ∑ j, b j) * x i := by
    rw [← carlsonRReal_one hb x]; exact carlsonRReal_pos 1 hb hx
  rcases lt_trichotomy t 0 with hn | rfl | hp
  · have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hA t)
      (carlsonRReal_bounds_of_nonpos hn.le hb hx).1 (inv_nonpos.mpr hn.le)
    simpa only [Real.rpow_rpow_inv hA.le hn.ne, ← carlsonMeanReal_eq_rpow hn.ne hb hx] using h
  · have h := Real.exp_le_exp.mpr (carlsonLReal_zero_bounds hb hx).1
    simpa only [carlsonMeanReal, ↓reduceIte, Real.exp_log hA] using h
  · have h := Real.rpow_le_rpow (carlsonRReal_pos t hb hx).le
      (carlsonRReal_bounds_of_nonneg_of_le_one hp.le ht hb hx).1 (inv_nonneg.mpr hp.le)
    simpa only [Real.rpow_rpow_inv hA.le hp.ne', ← carlsonMeanReal_eq_rpow hp.ne' hb hx] using h

/-- For orders at least one, the weighted power mean bounds the hypergeometric mean above. -/
theorem carlsonMeanReal_le_powerMean {t : ℝ} (ht : 1 ≤ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x ≤ (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ t⁻¹ := by
  have ht0 := lt_of_lt_of_le zero_lt_one ht
  rw [carlsonMeanReal_eq_rpow ht0.ne' hb hx]
  exact Real.rpow_le_rpow (carlsonRReal_pos t hb hx).le
    (carlsonRReal_bounds_of_one_le ht hb hx).2 (inv_nonneg.mpr ht0.le)

/-- At nonzero orders at most one, the power mean bounds the hypergeometric mean below. -/
theorem powerMean_le_carlsonMeanReal {t : ℝ} (ht : t ≤ 1) (ht0 : t ≠ 0)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ t⁻¹ ≤ carlsonMeanReal t b x := by
  rw [carlsonMeanReal_eq_rpow ht0 hb hx]
  rcases lt_or_gt_of_ne ht0 with hn | hp
  · exact Real.rpow_le_rpow_of_nonpos (carlsonRReal_pos t hb hx)
      (carlsonRReal_bounds_of_nonpos hn.le hb hx).2 (inv_nonpos.mpr hn.le)
  · have hc : 0 < ∑ j, b j := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (hb i).le hc.le)
        (Real.rpow_nonneg (hx i).le t))
      (carlsonRReal_bounds_of_nonneg_of_le_one hp.le ht hb hx).2 (inv_nonneg.mpr hp.le)

/-- The geometric mean bounds the zero-order hypergeometric mean below. -/
theorem geometric_le_carlsonMeanReal_zero {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) ≤ carlsonMeanReal 0 b x := by
  simpa only [carlsonMeanReal, ↓reduceIte] using
    Real.exp_le_exp.mpr (carlsonLReal_zero_bounds hb hx).2

/-- Above order one, nonconstant R-averages lie strictly between the arithmetic power
and the weighted power sum. -/
theorem carlsonRReal_strict_bounds_of_one_lt {t : ℝ} (ht : 1 < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t < carlsonRReal t b x ∧
      carlsonRReal t b x < ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact strictConvexOn_dirichlet_average_bounds hb isClosed_Ici hax hne
    ((strictConvexOn_rpow ht).subset (fun _ hy => ha.le.trans hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- Between zero and one, the power-average bounds reverse strictly for nonconstant nodes. -/
theorem carlsonRReal_strict_bounds_of_pos_of_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonRReal t b x < (∑ i, (b i / ∑ j, b j) * x i) ^ t ∧
      (∑ i, (b i / ∑ j, b j) * x i ^ t) < carlsonRReal t b x := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact strictConcaveOn_dirichlet_average_bounds hb isClosed_Ici hax hne
    ((Real.strictConcaveOn_rpow ht ht1).subset (fun _ hy => ha.le.trans hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- Negative orders have strict convex power-average bounds for nonconstant nodes. -/
theorem carlsonRReal_strict_bounds_of_neg {t : ℝ} (ht : t < 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t < carlsonRReal t b x ∧
      carlsonRReal t b x < ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  exact strictConvexOn_dirichlet_average_bounds hb isClosed_Ici hax hne
    ((Real.strictConvexOn_rpow_of_neg ht).subset (fun _ hy => ha.trans_le hy) (convex_Ici a))
    (continuousOn_rpow_Ici t ha)

/-- For nonconstant nodes, the logarithmic average lies strictly between the weighted
logarithms and the logarithm of the arithmetic mean. -/
theorem carlsonLReal_zero_strict_bounds {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonLReal 0 b x < Real.log (∑ i, (b i / ∑ j, b j) * x i) ∧
      (∑ i, (b i / ∑ j, b j) * Real.log (x i)) < carlsonLReal 0 b x := by
  obtain ⟨a, ha, hax⟩ := exists_pos_le_nodes hx
  have h := strictConcaveOn_dirichlet_average_bounds hb isClosed_Ici hax hne
    (strictConcaveOn_log_Ioi.subset (fun _ hy => ha.trans_le hy)
      (convex_Ici a))
    (fun y hy => (Real.continuousAt_log (ne_of_gt (ha.trans_le hy))).continuousWithinAt)
  simpa only [carlsonLReal, Real.rpow_zero, one_mul] using h

/-- Above order one, nonconstant hypergeometric means lie strictly below the power mean. -/
theorem carlsonMeanReal_lt_powerMean {t : ℝ} (ht : 1 < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal t b x < (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ t⁻¹ := by
  have ht0 := zero_lt_one.trans ht
  rw [carlsonMeanReal_eq_rpow ht0.ne' hb hx]
  exact Real.rpow_lt_rpow (carlsonRReal_pos t hb hx).le
    (carlsonRReal_strict_bounds_of_one_lt ht hb hx hne).2 (inv_pos.mpr ht0)

/-- At nonzero orders below one, nonconstant hypergeometric means strictly exceed the power mean. -/
theorem powerMean_lt_carlsonMeanReal {t : ℝ} (ht : t < 1) (ht0 : t ≠ 0)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ t⁻¹ < carlsonMeanReal t b x := by
  rw [carlsonMeanReal_eq_rpow ht0 hb hx]
  rcases lt_or_gt_of_ne ht0 with hn | hp
  · exact Real.rpow_lt_rpow_of_neg (carlsonRReal_pos t hb hx)
      (carlsonRReal_strict_bounds_of_neg hn hb hx hne).2 (inv_lt_zero.mpr hn)
  · have hc : 0 < ∑ j, b j := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
    exact Real.rpow_lt_rpow
      (Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (hb i).le hc.le)
        (Real.rpow_nonneg (hx i).le t))
      (carlsonRReal_strict_bounds_of_pos_of_lt_one hp ht hb hx hne).2 (inv_pos.mpr hp)

end Carlson
