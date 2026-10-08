/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Ratio
public import Carlson.Mean.Minkowski

/-!
# The Beckenbach–Dresher inequality

For `0 < s ≤ 1 ≤ t` with `s < t`, the ratio mean is subadditive. Equality holds
exactly for proportional positive node vectors. Normalizing by the ratio mean
makes the R-averages of orders `s` and `t` equal; strict convexity of their difference
then gives the inequality, including either endpoint `s = 1` or `t = 1`.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 8.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The difference of a convex power average and a concave power average is strictly
convex in the nodes in the Beckenbach–Dresher range. -/
theorem strictConvexOn_carlsonRReal_sub {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : 1 ≤ t) (hst : s < t) {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    StrictConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i}
      (fun x => carlsonRReal t b x - carlsonRReal s b x) := by
  have hker : StrictConvexOn ℝ (Ioi 0) (fun z : ℝ => z ^ t - z ^ s) := by
    rcases ht.eq_or_lt with rfl | ht
    · exact ((convexOn_rpow le_rfl).sub_strictConcaveOn
        (Real.strictConcaveOn_rpow hs hst)).subset (fun _ hz => hz.le) (convex_Ioi 0)
    · exact ((strictConvexOn_rpow ht).sub_concaveOn
        (Real.concaveOn_rpow hs.le hs1)).subset (fun _ hz => hz.le) (convex_Ioi 0)
  have hc : ContinuousOn (fun z : ℝ => z ^ t - z ^ s) (Ioi 0) := fun z hz =>
    ((Real.continuousAt_rpow_const z t (Or.inl hz.ne')).sub
      (Real.continuousAt_rpow_const z s (Or.inl hz.ne'))).continuousWithinAt
  apply (strictConvexOn_dirichlet_average hb hker hc).congr
  intro x hx
  exact integral_sub (integrable_carlsonRReal t hb hx) (integrable_carlsonRReal s hb hx)

/-- Strict Beckenbach–Dresher inequality for nonproportional positive node vectors. -/
theorem carlsonRatioMeanReal_add_lt {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : 1 ≤ t) (hst : s < t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) :
    carlsonRatioMeanReal s t b (fun i => x i + y i) <
      carlsonRatioMeanReal s t b x + carlsonRatioMeanReal s t b y := by
  have hA := carlsonRatioMeanReal_pos s t b x
  have hB := carlsonRatioMeanReal_pos s t b y
  have hS := add_pos hA hB
  have h := (strictConvexOn_carlsonRReal_sub hs hs1 ht hst hb).map_normalized_add_lt
    hx hy (inv_mul_ne_inv_mul_of_not_proportional hne hA hB) hA hB
  rw [carlsonRReal_ratio_normalize hst.ne hb hx, carlsonRReal_ratio_normalize hst.ne hb hy,
    sub_self, sub_self, mul_zero, mul_zero, add_zero, sub_neg] at h
  have hz i := mul_pos (inv_pos.mpr hS) (add_pos (hx i) (hy i))
  have hm := (carlsonRatioMeanReal_lt_one_iff hst hb hz).mpr h
  rw [carlsonRatioMeanReal_mul hst.ne hb (fun i => add_pos (hx i) (hy i)) (inv_pos.mpr hS),
    inv_mul_eq_div, div_lt_one hS] at hm
  exact hm

/-- Proportional vectors give equality in ratio-mean addition at distinct orders. -/
theorem carlsonRatioMeanReal_add_eq_of_proportional {s t : ℝ} (hst : s ≠ t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i)
    (hxy : ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) :
    carlsonRatioMeanReal s t b (fun i => x i + y i) =
      carlsonRatioMeanReal s t b x + carlsonRatioMeanReal s t b y := by
  obtain ⟨a, ha, hxy⟩ := hxy
  have he : (fun i => x i + y i) = fun i => (1 + a) * x i := by
    funext i
    rw [hxy i]
    ring
  rw [he, carlsonRatioMeanReal_mul hst hb hx (by positivity), funext hxy,
    carlsonRatioMeanReal_mul hst hb hx ha]
  ring

/-- Beckenbach–Dresher inequality, including proportional vectors and singleton index types. -/
theorem carlsonRatioMeanReal_add_le {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : 1 ≤ t) (hst : s < t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonRatioMeanReal s t b (fun i => x i + y i) ≤
      carlsonRatioMeanReal s t b x + carlsonRatioMeanReal s t b y := by
  by_cases hxy : ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i
  · exact (carlsonRatioMeanReal_add_eq_of_proportional hst.ne hb hx hxy).le
  · exact (carlsonRatioMeanReal_add_lt hs hs1 ht hst hb hx hy hxy).le

/-- Equality in Beckenbach–Dresher occurs exactly for proportional positive vectors. -/
theorem carlsonRatioMeanReal_add_eq_iff {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : 1 ≤ t) (hst : s < t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonRatioMeanReal s t b (fun i => x i + y i) =
      carlsonRatioMeanReal s t b x + carlsonRatioMeanReal s t b y ↔
        ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i := by
  constructor
  · intro he
    by_contra h
    exact (carlsonRatioMeanReal_add_lt hs hs1 ht hst hb hx hy h).ne he
  · exact carlsonRatioMeanReal_add_eq_of_proportional hst.ne hb hx

end Carlson
