/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Inequalities
public import ToMathlib.Analysis.Integral.StrictMono

/-!
# Normalization, node monotonicity, and homogeneity of real means

The elementary mean properties hold for every real order at positive nodes and
positive Dirichlet parameters. They include the logarithmic order and singleton
index types. Bounds are stated using any common lower and upper bound on the nodes,
avoiding a choice of indexing or an artificial empty-index convention.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- On constant real nodes, R is a real power. -/
theorem carlsonRReal_const (t a : ℝ) {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    carlsonRReal t b (fun _ => a) = a ^ t := by
  let := isProbabilityMeasure_dirichletMeasure hb
  unfold carlsonRReal
  calc
    (∫ u, (∑ i, u i * a) ^ t ∂dirichletMeasure b) = ∫ _, a ^ t ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      rw [← Finset.sum_mul, hu.2, one_mul]
    _ = _ := by simp

/-- On constant real nodes, L is the power-logarithm kernel. -/
theorem carlsonLReal_const (t a : ℝ) {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    carlsonLReal t b (fun _ => a) = a ^ t * Real.log a := by
  let := isProbabilityMeasure_dirichletMeasure hb
  unfold carlsonLReal
  calc
    (∫ u, (∑ i, u i * a) ^ t * Real.log (∑ i, u i * a) ∂dirichletMeasure b) =
        ∫ _, a ^ t * Real.log a ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      rw [← Finset.sum_mul, hu.2, one_mul]
    _ = _ := by simp

/-- Every real order is normalized on a constant positive node vector. -/
theorem carlsonMeanReal_const (t : ℝ) {a : ℝ} (ha : 0 < a) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) : carlsonMeanReal t b (fun _ => a) = a := by
  by_cases ht : t = 0
  · subst t
    simp [carlsonMeanReal, carlsonLReal_const 0 a hb, Real.exp_log ha]
  · rw [carlsonMeanReal_eq_rpow ht hb (fun _ => ha), carlsonRReal_const t a hb,
      Real.rpow_rpow_inv ha.le ht]

/-- Nonnegative orders of R are monotone in the real nodes. -/
theorem carlsonRReal_mono_nodes {t : ℝ} (ht : 0 ≤ t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    carlsonRReal t b x ≤ carlsonRReal t b y := by
  apply integral_mono_ae (integrable_carlsonRReal t hb hx)
    (integrable_carlsonRReal t hb (fun i => (hx i).trans_le (hxy i)))
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  exact Real.rpow_le_rpow (dirichlet_affine_mem (convex_Ioi 0) hx hu).le
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hu.1 i)) ht

/-- Nonpositive orders of R are antitone in the real nodes. -/
theorem carlsonRReal_antitone_nodes {t : ℝ} (ht : t ≤ 0) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    carlsonRReal t b y ≤ carlsonRReal t b x := by
  apply integral_mono_ae (integrable_carlsonRReal t hb (fun i => (hx i).trans_le (hxy i)))
    (integrable_carlsonRReal t hb hx)
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  exact Real.rpow_le_rpow_of_nonpos (dirichlet_affine_mem (convex_Ioi 0) hx hu)
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hu.1 i)) ht

/-- The order-zero logarithmic average is monotone in its nodes. -/
theorem carlsonLReal_zero_mono_nodes {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    carlsonLReal 0 b x ≤ carlsonLReal 0 b y := by
  apply integral_mono_ae (integrable_carlsonLReal 0 hb hx)
    (integrable_carlsonLReal 0 hb (fun i => (hx i).trans_le (hxy i)))
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  simp only [Real.rpow_zero, one_mul]
  exact Real.log_le_log (dirichlet_affine_mem (convex_Ioi 0) hx hu)
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hu.1 i))

/-- The hypergeometric mean is monotone in its nodes at every real order. -/
theorem carlsonMeanReal_mono_nodes (t : ℝ) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    carlsonMeanReal t b x ≤ carlsonMeanReal t b y := by
  have hy i := (hx i).trans_le (hxy i)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [carlsonMeanReal_eq_rpow ht.ne hb hx, carlsonMeanReal_eq_rpow ht.ne hb hy]
    exact Real.rpow_le_rpow_of_nonpos (carlsonRReal_pos t hb hy)
      (carlsonRReal_antitone_nodes ht.le hb hx hxy) (inv_nonpos.mpr ht.le)
  · simpa only [carlsonMeanReal, ↓reduceIte] using
      Real.exp_le_exp.mpr (carlsonLReal_zero_mono_nodes hb hx hxy)
  · rw [carlsonMeanReal_eq_rpow ht.ne' hb hx, carlsonMeanReal_eq_rpow ht.ne' hb hy]
    exact Real.rpow_le_rpow (carlsonRReal_pos t hb hx).le
      (carlsonRReal_mono_nodes ht.le hb hx hxy) (inv_nonneg.mpr ht.le)

/-- Every common positive lower bound and upper bound for the nodes bounds the mean. -/
theorem carlsonMeanReal_bounds (t : ℝ) {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {a A : ℝ} (ha : 0 < a) (hlo : ∀ i, a ≤ x i) (hhi : ∀ i, x i ≤ A) :
    a ≤ carlsonMeanReal t b x ∧ carlsonMeanReal t b x ≤ A := by
  have hx i := ha.trans_le (hlo i)
  have hA : 0 < A := (hx (Classical.arbitrary ι)).trans_le (hhi _)
  constructor
  · simpa only [carlsonMeanReal_const t ha hb] using
      carlsonMeanReal_mono_nodes t hb (fun _ => ha) hlo
  · simpa only [carlsonMeanReal_const t hA hb] using
      carlsonMeanReal_mono_nodes t hb hx hhi

omit [Nonempty ι] in
/-- R is homogeneous of its real order under positive scaling. -/
theorem carlsonRReal_mul (t : ℝ) {b x : ι → ℝ}
    (hx : ∀ i, 0 < x i) {a : ℝ} (ha : 0 < a) :
    carlsonRReal t b (fun i => a * x i) = a ^ t * carlsonRReal t b x := by
  unfold carlsonRReal
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  have he : (∑ i, u i * (a * x i)) = a * ∑ i, u i * x i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [he, Real.mul_rpow ha.le (dirichlet_affine_mem (convex_Ioi 0) hx hu).le]

/-- Scaling the nodes adds the logarithm of the scale to the order-zero L-average. -/
theorem carlsonLReal_zero_mul {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) {a : ℝ} (ha : 0 < a) :
    carlsonLReal 0 b (fun i => a * x i) = Real.log a + carlsonLReal 0 b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hl : Integrable (fun u => Real.log (∑ i, u i * x i)) (dirichletMeasure b) := by
    simpa only [Real.rpow_zero, one_mul] using integrable_carlsonLReal 0 hb hx
  simp only [carlsonLReal, Real.rpow_zero, one_mul]
  calc
    (∫ u, Real.log (∑ i, u i * (a * x i)) ∂dirichletMeasure b) =
        ∫ u, (Real.log a + Real.log (∑ i, u i * x i)) ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      have he : (∑ i, u i * (a * x i)) = a * ∑ i, u i * x i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [he, Real.log_mul ha.ne' (dirichlet_affine_mem (convex_Ioi 0) hx hu).ne']
    _ = _ := by rw [integral_add (integrable_const _) hl]; simp

/-- The real hypergeometric mean is homogeneous of degree one at every order. -/
theorem carlsonMeanReal_mul (t : ℝ) {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) {a : ℝ} (ha : 0 < a) :
    carlsonMeanReal t b (fun i => a * x i) = a * carlsonMeanReal t b x := by
  by_cases ht : t = 0
  · subst t
    simp only [carlsonMeanReal, ↓reduceIte, carlsonLReal_zero_mul hb hx ha,
      Real.exp_add, Real.exp_log ha]
  · rw [carlsonMeanReal_eq_rpow ht hb (fun i => mul_pos ha (hx i)),
      carlsonRReal_mul t hx ha, Real.mul_rpow (Real.rpow_nonneg ha.le t)
        (carlsonRReal_pos t hb hx).le, Real.rpow_rpow_inv ha.le ht,
      ← carlsonMeanReal_eq_rpow ht hb hx]

omit [Nonempty ι] in
/-- Increasing at least one node strictly increases the affine form almost surely. -/
private theorem ae_affine_lt {b x y : ι → ℝ} (hxy : ∀ i, x i ≤ y i)
    (hlt : ∃ i, x i < y i) :
    ∀ᵐ u ∂dirichletMeasure b, (∑ i, u i * x i) < ∑ i, u i * y i := by
  obtain ⟨i, hi⟩ := hlt
  filter_upwards [ae_mem_stdSimplexInterior_dirichletMeasure b] with u hu
  exact Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hu.2 j).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hu.2 i)⟩

/-- At every real order the hypergeometric mean strictly increases if the nodes increase
coordinatewise and at least one coordinate increases strictly. -/
theorem carlsonMeanReal_strict_mono_nodes (t : ℝ) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i)
    (hxy : ∀ i, x i ≤ y i) (hlt : ∃ i, x i < y i) :
    carlsonMeanReal t b x < carlsonMeanReal t b y := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hy i := (hx i).trans_le (hxy i)
  have hlt' := ae_affine_lt (b := b) hxy hlt
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hR : carlsonRReal t b y < carlsonRReal t b x := by
      apply integral_lt_integral_of_ae_lt (integrable_carlsonRReal t hb hy)
        (integrable_carlsonRReal t hb hx)
      filter_upwards [hlt', ae_mem_stdSimplex_dirichletMeasure b] with u hu hmem
      exact Real.rpow_lt_rpow_of_neg (dirichlet_affine_mem (convex_Ioi 0) hx hmem) hu ht
    rw [carlsonMeanReal_eq_rpow ht.ne hb hx, carlsonMeanReal_eq_rpow ht.ne hb hy]
    exact Real.rpow_lt_rpow_of_neg (carlsonRReal_pos t hb hy) hR (inv_lt_zero.mpr ht)
  · have hL : carlsonLReal 0 b x < carlsonLReal 0 b y := by
      apply integral_lt_integral_of_ae_lt (integrable_carlsonLReal 0 hb hx)
        (integrable_carlsonLReal 0 hb hy)
      filter_upwards [hlt', ae_mem_stdSimplex_dirichletMeasure b] with u hu hmem
      simpa only [Real.rpow_zero, one_mul] using
        Real.log_lt_log (dirichlet_affine_mem (convex_Ioi 0) hx hmem) hu
    simpa only [carlsonMeanReal, ↓reduceIte] using Real.exp_lt_exp.mpr hL
  · have hR : carlsonRReal t b x < carlsonRReal t b y := by
      apply integral_lt_integral_of_ae_lt (integrable_carlsonRReal t hb hx)
        (integrable_carlsonRReal t hb hy)
      filter_upwards [hlt', ae_mem_stdSimplex_dirichletMeasure b] with u hu hmem
      exact Real.rpow_lt_rpow (dirichlet_affine_mem (convex_Ioi 0) hx hmem).le hu ht
    rw [carlsonMeanReal_eq_rpow ht.ne' hb hx, carlsonMeanReal_eq_rpow ht.ne' hb hy]
    exact Real.rpow_lt_rpow (carlsonRReal_pos t hb hx).le hR (inv_pos.mpr ht)

/-- The lower and upper node bounds are strict when a node exceeds the lower bound and
a node lies below the upper bound. -/
theorem carlsonMeanReal_strict_bounds (t : ℝ) {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {a A : ℝ} (ha : 0 < a) (hlo : ∀ i, a ≤ x i) (hhi : ∀ i, x i ≤ A)
    (hlo' : ∃ i, a < x i) (hhi' : ∃ i, x i < A) :
    a < carlsonMeanReal t b x ∧ carlsonMeanReal t b x < A := by
  have hx i := ha.trans_le (hlo i)
  have hA : 0 < A := (hx (Classical.arbitrary ι)).trans_le (hhi _)
  constructor
  · simpa only [carlsonMeanReal_const t ha hb] using
      carlsonMeanReal_strict_mono_nodes t hb (fun _ => ha) hlo hlo'
  · simpa only [carlsonMeanReal_const t hA hb] using
      carlsonMeanReal_strict_mono_nodes t hb hx hhi hhi'

end Carlson
