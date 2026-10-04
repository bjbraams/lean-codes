/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Euler
public import Carlson.Mean.Properties
public import ToMathlib.Analysis.Convex.GeometricMean

/-!
# Hölder inequalities for hypergeometric means

Geometric interpolation of the nodes gives the Hölder inequality for every
nonnegative order, including the logarithmic order. Strictness comes from finite
Hölder on the simplex interior, so the equality condition is proportionality of
the node vectors before taking the geometric interpolation.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 7.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Strict geometric interpolation at order zero. -/
theorem carlsonMeanReal_zero_geom_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    carlsonMeanReal 0 b (fun i => x i ^ a * y i ^ c) <
      carlsonMeanReal 0 b x ^ a * carlsonMeanReal 0 b y ^ c := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hz i := mul_pos (Real.rpow_pos_of_pos (hx i) a) (Real.rpow_pos_of_pos (hy i) c)
  have hi (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
      Integrable (fun u => Real.log (∑ i, u i * v i)) (dirichletMeasure b) := by
    simpa only [Real.rpow_zero, one_mul] using integrable_carlsonLReal 0 hb hv
  have h : carlsonLReal 0 b (fun i => x i ^ a * y i ^ c) <
      a * carlsonLReal 0 b x + c * carlsonLReal 0 b y := by
    simp only [carlsonLReal, Real.rpow_zero, one_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hi x hx).const_mul a) ((hi y hy).const_mul c)]
    apply integral_lt_integral_of_ae_lt (hi _ hz) (((hi x hx).const_mul a).add ((hi y hy).const_mul c))
    filter_upwards [ae_mem_stdSimplexInterior_dirichletMeasure b] with u hu
    have hfin := Real.sum_mul_rpow_mul_rpow_lt ha hc hac hu.2 hx hy hne
    have hlog := Real.log_lt_log (dirichlet_affine_mem (convex_Ioi 0) hz hu.1) hfin
    rw [Real.log_mul (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu.1) a).ne'
      (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hy hu.1) c).ne',
      Real.log_rpow (dirichlet_affine_mem (convex_Ioi 0) hx hu.1),
      Real.log_rpow (dirichlet_affine_mem (convex_Ioi 0) hy hu.1)] at hlog
    exact hlog
  simpa only [carlsonMeanReal, ↓reduceIte, Real.exp_add, ← Real.exp_mul, mul_comm] using
    Real.exp_lt_exp.mpr h

/-- Strict geometric interpolation at a positive order. -/
theorem carlsonMeanReal_geom_lt_of_pos {t : ℝ} (ht : 0 < t)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) <
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hz i := mul_pos (Real.rpow_pos_of_pos (hx i) a) (Real.rpow_pos_of_pos (hy i) c)
  have hnonneg (v : ι → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ) :
      ∀ᵐ u ∂dirichletMeasure b, 0 ≤ (∑ i, u i * v i) ^ r := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    exact (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hv hu) r).le
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.holderConjugate_one_div ha hc hac)
    (hnonneg x hx (a * t)) (hnonneg y hy (c * t))
    (memLp_carlsonAffine_rpow (a * t) (one_div_pos.mpr ha) hb hx)
    (memLp_carlsonAffine_rpow (c * t) (one_div_pos.mpr hc) hb hy)
  have he (v : ι → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ) (hr : 0 < r) :
      (∫ u, ((∑ i, u i * v i) ^ (r * t)) ^ (1 / r) ∂dirichletMeasure b) = carlsonRReal t b v := by
    have h := ae_carlsonAffine_rpow_rpow (r * t) (1 / r) b hv
    rw [show r * t * (1 / r) = t by field_simp] at h
    exact integral_congr_ae h
  rw [he x hx a ha, he y hy c hc, one_div_one_div, one_div_one_div] at hholder
  have hint : Integrable (fun u => (∑ i, u i * x i) ^ (a * t) *
      (∑ i, u i * y i) ^ (c * t)) (dirichletMeasure b) := by
    apply integrable_dirichletMeasure_of_continuousOn hb
    exact (ContinuousOn.rpow_const (by fun_prop)
      (fun u hu => Or.inl (dirichlet_affine_mem (convex_Ioi 0) hx hu).ne')).mul
      (ContinuousOn.rpow_const (by fun_prop)
        (fun u hu => Or.inl (dirichlet_affine_mem (convex_Ioi 0) hy hu).ne'))
  have hlt : carlsonRReal t b (fun i => x i ^ a * y i ^ c) <
      ∫ u, ((∑ i, u i * x i) ^ (a * t) * (∑ i, u i * y i) ^ (c * t)) ∂dirichletMeasure b := by
    apply integral_lt_integral_of_ae_lt (integrable_carlsonRReal t hb hz) hint
    filter_upwards [ae_mem_stdSimplexInterior_dirichletMeasure b] with u hu
    have h := Real.rpow_lt_rpow (dirichlet_affine_mem (convex_Ioi 0) hz hu.1).le
      (Real.sum_mul_rpow_mul_rpow_lt ha hc hac hu.2 hx hy hne) ht
    rwa [Real.mul_rpow (Real.rpow_nonneg (dirichlet_affine_mem (convex_Ioi 0) hx hu.1).le a)
      (Real.rpow_nonneg (dirichlet_affine_mem (convex_Ioi 0) hy hu.1).le c),
      ← Real.rpow_mul (dirichlet_affine_mem (convex_Ioi 0) hx hu.1).le,
      ← Real.rpow_mul (dirichlet_affine_mem (convex_Ioi 0) hy hu.1).le] at h
  have h := Real.rpow_lt_rpow (carlsonRReal_pos t hb hz).le (hlt.trans_le hholder) (inv_pos.mpr ht)
  rw [← carlsonMeanReal_eq_rpow ht.ne' hb hz,
    Real.mul_rpow (Real.rpow_nonneg (carlsonRReal_pos t hb hx).le a)
      (Real.rpow_nonneg (carlsonRReal_pos t hb hy).le c)] at h
  have he' (v : ι → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ) :
      (carlsonRReal t b v ^ r) ^ t⁻¹ = carlsonMeanReal t b v ^ r := by
    rw [carlsonMeanReal_eq_rpow ht.ne' hb hv,
      ← Real.rpow_mul (carlsonRReal_pos t hb hv).le,
      ← Real.rpow_mul (carlsonRReal_pos t hb hv).le, mul_comm r t⁻¹]
  rwa [he' x hx a, he' y hy c] at h

/-- Strict Hölder interpolation for every nonnegative order. -/
theorem carlsonMeanReal_geom_lt {t : ℝ} (ht : 0 ≤ t)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) <
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c := by
  rcases ht.eq_or_lt with rfl | ht
  · exact carlsonMeanReal_zero_geom_lt ha hc hac hb hx hy hne
  · exact carlsonMeanReal_geom_lt_of_pos ht ha hc hac hb hx hy hne

/-- Proportional positive vectors give equality in geometric interpolation at every order. -/
theorem carlsonMeanReal_geom_eq_of_proportional (t : ℝ) {a c : ℝ} (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i)
    (hxy : ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) =
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c := by
  obtain ⟨k, hk, hxy⟩ := hxy
  have he : (fun i => x i ^ a * y i ^ c) = fun i => k ^ c * x i := by
    funext i
    rw [hxy i, Real.mul_rpow hk.le (hx i).le]
    calc
      x i ^ a * (k ^ c * x i ^ c) = k ^ c * (x i ^ a * x i ^ c) := by ring
      _ = k ^ c * x i := by rw [← Real.rpow_add (hx i), hac, Real.rpow_one]
  rw [he, carlsonMeanReal_mul t hb hx (Real.rpow_pos_of_pos hk c), funext hxy,
    carlsonMeanReal_mul t hb hx hk, Real.mul_rpow hk.le (carlsonMeanReal_pos t b x).le]
  calc
    k ^ c * carlsonMeanReal t b x = k ^ c * (carlsonMeanReal t b x ^ a * carlsonMeanReal t b x ^ c) := by
      rw [← Real.rpow_add (carlsonMeanReal_pos t b x), hac, Real.rpow_one]
    _ = _ := by ring

/-- Hölder interpolation for every nonnegative order, including proportional vectors. -/
theorem carlsonMeanReal_geom_le {t : ℝ} (ht : 0 ≤ t)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) ≤
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c := by
  by_cases h : ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i
  · exact (carlsonMeanReal_geom_eq_of_proportional t hac hb hx h).le
  · exact (carlsonMeanReal_geom_lt ht ha hc hac hb hx hy h).le

/-- The exact equality condition for Hölder interpolation at nonnegative orders. -/
theorem carlsonMeanReal_geom_eq_iff {t : ℝ} (ht : 0 ≤ t)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) =
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c ↔
        ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i := by
  constructor
  · intro he
    by_contra h
    exact (carlsonMeanReal_geom_lt ht ha hc hac hb hx hy h).ne he
  · exact carlsonMeanReal_geom_eq_of_proportional t hac hb hx

/-- Positive-order R is strictly log-convex under geometric interpolation of nonproportional nodes. -/
theorem log_carlsonRReal_geom_lt_of_pos {t : ℝ} (ht : 0 < t)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    Real.log (carlsonRReal t b (fun i => x i ^ a * y i ^ c)) <
      a * Real.log (carlsonRReal t b x) + c * Real.log (carlsonRReal t b y) := by
  have h := Real.log_lt_log (carlsonMeanReal_pos t b _)
    (carlsonMeanReal_geom_lt_of_pos ht ha hc hac hb hx hy hne)
  rw [Real.log_mul (Real.rpow_pos_of_pos (carlsonMeanReal_pos t b x) a).ne'
    (Real.rpow_pos_of_pos (carlsonMeanReal_pos t b y) c).ne',
    Real.log_rpow (carlsonMeanReal_pos t b x), Real.log_rpow (carlsonMeanReal_pos t b y)] at h
  simp only [carlsonMeanReal, ite_eq_right ht.ne', Real.log_exp] at h
  have he : a * (Real.log (carlsonRReal t b x) / t) + c * (Real.log (carlsonRReal t b y) / t) =
      (a * Real.log (carlsonRReal t b x) + c * Real.log (carlsonRReal t b y)) / t := by ring
  rw [he] at h
  exact (div_lt_div_iff_of_pos_right ht).mp h

/-- Euler inversion gives strict log-convexity in logarithmic nodes also below minus the
sum of the parameters. -/
theorem log_carlsonRReal_geom_lt_of_lt_neg_sum {t : ℝ} {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (ht : t < -(∑ i, b i))
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    Real.log (carlsonRReal t b (fun i => x i ^ a * y i ^ c)) <
      a * Real.log (carlsonRReal t b x) + c * Real.log (carlsonRReal t b y) := by
  have hx' i := inv_pos.mpr (hx i)
  have hy' i := inv_pos.mpr (hy i)
  have hn : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, (y i)⁻¹ = k * (x i)⁻¹ := by
    rintro ⟨k, hk, he⟩
    apply hne
    refine ⟨k⁻¹, inv_pos.mpr hk, fun i => ?_⟩
    simpa only [inv_inv, mul_inv_rev, mul_comm] using congrArg Inv.inv (he i)
  have h := log_carlsonRReal_geom_lt_of_pos (sub_pos.mpr ht) ha hc hac hb hx' hy' hn
  have he : (fun i => (x i)⁻¹ ^ a * (y i)⁻¹ ^ c) =
      fun i => (x i ^ a * y i ^ c)⁻¹ := by
    funext i
    rw [Real.inv_rpow (hx i).le, Real.inv_rpow (hy i).le, mul_inv]
  rw [he] at h
  have hz i := mul_pos (Real.rpow_pos_of_pos (hx i) a) (Real.rpow_pos_of_pos (hy i) c)
  rw [log_carlsonRReal_euler t hb hz, log_carlsonRReal_euler t hb hx, log_carlsonRReal_euler t hb hy]
  have hl : (∑ i, b i * Real.log (x i ^ a * y i ^ c)) =
      a * (∑ i, b i * Real.log (x i)) + c * (∑ i, b i * Real.log (y i)) := by
    simp_rw [Real.log_mul (Real.rpow_pos_of_pos (hx _) a).ne' (Real.rpow_pos_of_pos (hy _) c).ne',
      Real.log_rpow (hx _), Real.log_rpow (hy _), mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [hl]
  linarith

/-- Strict reversed Hölder interpolation below minus the total parameter. -/
theorem lt_carlsonMeanReal_geom_of_lt_neg_sum {t : ℝ} {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (ht : t < -(∑ i, b i))
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i) :
    carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c <
      carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) := by
  have ht0 : t < 0 := ht.trans (neg_neg_of_pos
    (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty))
  have h := log_carlsonRReal_geom_lt_of_lt_neg_sum hb ht ha hc hac hx hy hne
  have hdiv := (div_lt_div_right_of_neg ht0).mpr h
  have he : (a * Real.log (carlsonRReal t b x) + c * Real.log (carlsonRReal t b y)) / t =
      a * (Real.log (carlsonRReal t b x) / t) + c * (Real.log (carlsonRReal t b y) / t) := by ring
  rw [he] at hdiv
  simpa only [carlsonMeanReal, ite_eq_right ht0.ne, Real.exp_add, ← Real.exp_mul, mul_comm] using
    Real.exp_lt_exp.mpr hdiv

/-- Hölder's usual conjugate-exponent form, for all nonnegative orders. -/
theorem carlsonMeanReal_holder {t p q : ℝ} (ht : 0 ≤ t) (hpq : p.HolderConjugate q)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i * y i) ≤
      carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
        carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ := by
  have h := carlsonMeanReal_geom_le ht (inv_pos.mpr hpq.pos) (inv_pos.mpr hpq.symm.pos)
    hpq.inv_add_inv_eq_one hb (fun i => Real.rpow_pos_of_pos (hx i) p)
      (fun i => Real.rpow_pos_of_pos (hy i) q)
  simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
    Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using h

/-- Strict Hölder in conjugate-exponent form when the powered vectors are not proportional. -/
theorem carlsonMeanReal_holder_lt {t p q : ℝ} (ht : 0 ≤ t) (hpq : p.HolderConjugate q)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i ^ q = k * x i ^ p) :
    carlsonMeanReal t b (fun i => x i * y i) <
      carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
        carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ := by
  have h := carlsonMeanReal_geom_lt ht (inv_pos.mpr hpq.pos) (inv_pos.mpr hpq.symm.pos)
    hpq.inv_add_inv_eq_one hb (fun i => Real.rpow_pos_of_pos (hx i) p)
      (fun i => Real.rpow_pos_of_pos (hy i) q) hne
  simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
    Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using h

/-- Reversed Hölder interpolation below minus the total parameter, including equality cases. -/
theorem le_carlsonMeanReal_geom_of_lt_neg_sum {t : ℝ} {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (ht : t < -(∑ i, b i))
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c ≤
      carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) := by
  by_cases h : ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i
  · exact (carlsonMeanReal_geom_eq_of_proportional t hac hb hx h).ge
  · exact (lt_carlsonMeanReal_geom_of_lt_neg_sum hb ht ha hc hac hx hy h).le

/-- Below minus the total parameter, equality in reversed Hölder still characterizes
proportional positive node vectors. -/
theorem carlsonMeanReal_geom_eq_iff_of_lt_neg_sum {t : ℝ} {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (ht : t < -(∑ i, b i))
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i ^ a * y i ^ c) =
      carlsonMeanReal t b x ^ a * carlsonMeanReal t b y ^ c ↔
        ∃ k : ℝ, 0 < k ∧ ∀ i, y i = k * x i := by
  constructor
  · intro he
    by_contra h
    exact (lt_carlsonMeanReal_geom_of_lt_neg_sum hb ht ha hc hac hx hy h).ne he.symm
  · exact carlsonMeanReal_geom_eq_of_proportional t hac hb hx

/-- At minus the total parameter, geometric interpolation is an identity for all positive vectors. -/
theorem carlsonMeanReal_neg_sum_geom (a c : ℝ) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal (-(∑ i, b i)) b (fun i => x i ^ a * y i ^ c) =
      carlsonMeanReal (-(∑ i, b i)) b x ^ a * carlsonMeanReal (-(∑ i, b i)) b y ^ c := by
  rw [carlsonMeanReal_neg_sum hb (fun i => mul_pos (Real.rpow_pos_of_pos (hx i) a)
    (Real.rpow_pos_of_pos (hy i) c)), carlsonMeanReal_neg_sum hb hx, carlsonMeanReal_neg_sum hb hy,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  simp_rw [Real.log_mul (Real.rpow_pos_of_pos (hx _) a).ne' (Real.rpow_pos_of_pos (hy _) c).ne',
    Real.log_rpow (hx _), Real.log_rpow (hy _), mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- Strict reversed Hölder in conjugate-exponent form below minus the total parameter. -/
theorem carlsonMeanReal_reverse_holder_lt {t p q : ℝ} (hpq : p.HolderConjugate q)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (ht : t < -(∑ i, b i))
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ k : ℝ, 0 < k ∧ ∀ i, y i ^ q = k * x i ^ p) :
    carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
      carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ < carlsonMeanReal t b (fun i => x i * y i) := by
  have h := lt_carlsonMeanReal_geom_of_lt_neg_sum hb ht
    (inv_pos.mpr hpq.pos) (inv_pos.mpr hpq.symm.pos) hpq.inv_add_inv_eq_one
    (fun i => Real.rpow_pos_of_pos (hx i) p) (fun i => Real.rpow_pos_of_pos (hy i) q) hne
  simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
    Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using h

/-- Reversed Hölder, including its identity endpoint at minus the total parameter. -/
theorem carlsonMeanReal_reverse_holder {t p q : ℝ} (hpq : p.HolderConjugate q)
    {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (ht : t ≤ -(∑ i, b i))
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
      carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ ≤ carlsonMeanReal t b (fun i => x i * y i) := by
  rcases ht.eq_or_lt with rfl | ht
  · have h := carlsonMeanReal_neg_sum_geom p⁻¹ q⁻¹ hb
      (fun i => Real.rpow_pos_of_pos (hx i) p) (fun i => Real.rpow_pos_of_pos (hy i) q)
    simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
      Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using h.ge
  · have h := le_carlsonMeanReal_geom_of_lt_neg_sum hb ht
      (inv_pos.mpr hpq.pos) (inv_pos.mpr hpq.symm.pos) hpq.inv_add_inv_eq_one
      (fun i => Real.rpow_pos_of_pos (hx i) p) (fun i => Real.rpow_pos_of_pos (hy i) q)
    simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
      Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using h

/-- Equality in conjugate-exponent Hölder is equivalent to proportionality of the
powered node vectors, including at order zero. -/
theorem carlsonMeanReal_holder_eq_iff {t p q : ℝ} (ht : 0 ≤ t)
    (hpq : p.HolderConjugate q) {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i * y i) =
      carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
        carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ ↔
      ∃ k : ℝ, 0 < k ∧ ∀ i, y i ^ q = k * x i ^ p := by
  simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
    Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using
    carlsonMeanReal_geom_eq_iff ht (inv_pos.mpr hpq.pos) (inv_pos.mpr hpq.symm.pos)
      hpq.inv_add_inv_eq_one hb (fun i => Real.rpow_pos_of_pos (hx i) p)
      (fun i => Real.rpow_pos_of_pos (hy i) q)

/-- Below the geometric order, equality in reversed conjugate-exponent Hölder is
 equivalent to proportionality of the powered node vectors. -/
theorem carlsonMeanReal_reverse_holder_eq_iff {t p q : ℝ}
    (hpq : p.HolderConjugate q) {b x y : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (ht : t < -(∑ i, b i)) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i * y i) =
      carlsonMeanReal t b (fun i => x i ^ p) ^ p⁻¹ *
        carlsonMeanReal t b (fun i => y i ^ q) ^ q⁻¹ ↔
      ∃ k : ℝ, 0 < k ∧ ∀ i, y i ^ q = k * x i ^ p := by
  simpa only [Real.rpow_rpow_inv (hx _).le hpq.ne_zero,
    Real.rpow_rpow_inv (hy _).le hpq.symm.ne_zero] using
    carlsonMeanReal_geom_eq_iff_of_lt_neg_sum hb ht (inv_pos.mpr hpq.pos)
      (inv_pos.mpr hpq.symm.pos) hpq.inv_add_inv_eq_one
      (fun i => Real.rpow_pos_of_pos (hx i) p) (fun i => Real.rpow_pos_of_pos (hy i) q)

end Carlson
