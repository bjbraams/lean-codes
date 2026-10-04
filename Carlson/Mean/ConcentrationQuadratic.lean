/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Concentration
public import Dirichlet.Real.Variance
public import ToMathlib.Analysis.Convex.LogReciprocal
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Quadratic concentration comparisons

At order two, Carlson–Tobey's concentration comparisons follow from the exact
formula `R₂(c w; x) = A² + V / (c + 1)`, where `A` and `V` are the weighted node
mean and variance. R is strictly decreasing and strictly log-convex in positive
concentration whenever the nodes are nonconstant. The R statements allow arbitrary
real nodes; the mean statements use positive nodes.

## References

* B. C. Carlson and M. D. Tobey, *A property of the hypergeometric mean value*,
  Proc. AMS 19 (1968), 255–262, Theorems 3–5 (quadratic case).
-/

open MeasureTheory ProbabilityTheory Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The quadratic R-average has an explicit concentration formula, for arbitrary real nodes. -/
theorem carlsonRReal_two_concentration {c : ℝ} (hc : 0 < c) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (x : ι → ℝ) :
    carlsonRReal 2 (fun i => c * w i) x = (∑ i, w i * x i) ^ 2 +
      ((∑ i, w i * x i ^ 2) - (∑ i, w i * x i) ^ 2) / (c + 1) := by
  simpa only [carlsonRReal, Real.rpow_two] using
    integral_dirichletMeasure_concentration_affine_sq hc hw hw1 x

omit [Nonempty ι] in
/-- Strict finite Jensen gives positive weighted node variance for nonconstant nodes. -/
private theorem node_variance_pos {w x : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) (hne : ∃ i j, x i ≠ x j) :
    0 < (∑ i, w i * x i ^ 2) - (∑ i, w i * x i) ^ 2 := by
  obtain ⟨i, j, hij⟩ := hne
  have h := (Even.strictConvexOn_pow (by decide : Even (2 : ℕ)) (by decide : (2 : ℕ) ≠ 0)).map_sum_lt
    (fun i _ => hw i) hw1 (fun i _ => mem_univ (x i))
    ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hij⟩
  simpa only [smul_eq_mul, sub_pos] using h

/-- The quadratic R-average is strictly decreasing in concentration for nonconstant real nodes. -/
theorem strictAntiOn_carlsonRReal_two_concentration {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hne : ∃ i j, x i ≠ x j) :
    StrictAntiOn (fun c : ℝ => carlsonRReal 2 (fun i => c * w i) x) (Ioi 0) := by
  intro c hc d hd hcd
  dsimp only
  rw [carlsonRReal_two_concentration hc hw hw1, carlsonRReal_two_concentration hd hw hw1]
  exact Real.strictAntiOn_add_div (node_variance_pos hw hw1 hne)
    (show c ∈ Ioi (-1) by change -1 < c; linarith [show 0 < c from hc])
    (show d ∈ Ioi (-1) by change -1 < d; linarith [show 0 < d from hd]) hcd

/-- The quadratic R-average is strictly log-convex in concentration for nonconstant real nodes. -/
theorem strictConvexOn_log_carlsonRReal_two_concentration {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hne : ∃ i j, x i ≠ x j) :
    StrictConvexOn ℝ (Ioi 0) (fun c : ℝ => Real.log (carlsonRReal 2 (fun i => c * w i) x)) := by
  apply ((Real.strictConvexOn_log_add_div (sq_nonneg (∑ i, w i * x i))
    (node_variance_pos hw hw1 hne) (k := 1)).subset
      (fun c hc => by change -1 < c; linarith [show 0 < c from hc]) (convex_Ioi 0)).congr
  intro c hc
  dsimp only
  rw [carlsonRReal_two_concentration hc hw hw1]

/-- The concentration derivative at order two is minus the node variance over `(c + 1)²`. -/
theorem hasDerivAt_carlsonRReal_two_concentration {c : ℝ} (hc : 0 < c) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (x : ι → ℝ) :
    HasDerivAt (fun d : ℝ => carlsonRReal 2 (fun i => d * w i) x)
      (-((∑ i, w i * x i ^ 2) - (∑ i, w i * x i) ^ 2) / (c + 1) ^ 2) c := by
  apply (Real.hasDerivAt_add_div (a := (∑ i, w i * x i) ^ 2)
    (by positivity : c + 1 ≠ 0)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hc] with d hd
  exact carlsonRReal_two_concentration hd hw hw1 x

/-- The derivative at quadratic order is strictly negative for nonconstant real nodes. -/
theorem deriv_carlsonRReal_two_concentration_neg {c : ℝ} (hc : 0 < c) {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hne : ∃ i j, x i ≠ x j) :
    deriv (fun d : ℝ => carlsonRReal 2 (fun i => d * w i) x) c < 0 := by
  rw [(hasDerivAt_carlsonRReal_two_concentration hc hw hw1 x).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (node_variance_pos hw hw1 hne)) (by positivity)

/-- The quadratic hypergeometric mean is strictly decreasing in concentration for positive,
nonconstant nodes. -/
theorem strictAntiOn_carlsonMeanReal_two_concentration {w x : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i)
    (hne : ∃ i j, x i ≠ x j) :
    StrictAntiOn (fun c : ℝ => carlsonMeanReal 2 (fun i => c * w i) x) (Ioi 0) := by
  intro c hc d hd hcd
  dsimp only
  rw [carlsonMeanReal_eq_rpow (by norm_num : (2 : ℝ) ≠ 0) (fun i => mul_pos hc (hw i)) hx,
    carlsonMeanReal_eq_rpow (by norm_num : (2 : ℝ) ≠ 0) (fun i => mul_pos hd (hw i)) hx]
  exact Real.rpow_lt_rpow (carlsonRReal_pos 2 (fun i => mul_pos hd (hw i)) hx).le
    (strictAntiOn_carlsonRReal_two_concentration hw hw1 hne hc hd hcd) (by norm_num)

end Carlson
