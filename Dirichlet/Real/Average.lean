/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Moments
public import Mathlib.Analysis.Convex.Integral

/-!
# Real Dirichlet averages and Jensen bounds

A continuous function of a convex combination of finitely many nodes is integrable
against every Dirichlet probability measure with positive parameters. Its average
lies between its value at the weighted barycenter and its weighted node values
when the function is convex; the inequalities reverse for concave functions.

These results do not assume a power kernel and are the probability foundation of
Carlson's hypergeometric mean inequalities. Mixed second moments show that equality
almost everywhere of affine combinations is equivalent to equality of their node
vectors. Convex kernels also give convex functions of the node vector.
-/

open MeasureTheory Set
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι]

/-- A Dirichlet-distributed vector belongs to the standard simplex almost surely. -/
theorem ae_mem_stdSimplex_dirichletMeasure (b : ι → ℝ) :
    ∀ᵐ u ∂dirichletMeasure b, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  rw [← dirichletMeasure_restrict b]
  exact self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet

/-- Every Dirichlet coordinate is strictly positive almost surely on the simplex. -/
theorem ae_mem_stdSimplexInterior_dirichletMeasure (b : ι → ℝ) :
    ∀ᵐ u ∂dirichletMeasure b, u ∈ stdSimplexInterior := by
  have h := ((absolutelyContinuous_dirichletMeasure b).restrict
    (Convexity.StdSimplex.coordinateSet ℝ ι)).ae_le
  rw [dirichletMeasure_restrict] at h
  exact h ae_mem_stdSimplexInterior

/-- Continuity on the compact simplex suffices for integrability against a Dirichlet
probability measure, even when its density is unbounded at the boundary. -/
theorem integrable_dirichletMeasure_of_continuousOn [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {f : (ι → ℝ) → E} (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Integrable f (dirichletMeasure b) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have h := hf.integrableOn_compact (μ := dirichletMeasure b)
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
  rwa [IntegrableOn, dirichletMeasure_restrict] at h

/-- A convex combination of real nodes remains in every convex set containing them. -/
theorem dirichlet_affine_mem {s : Set ℝ} (hs : Convex ℝ s) {x u : ι → ℝ}
    (hx : ∀ i, x i ∈ s) (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (∑ i, u i * x i) ∈ s := by
  simpa only [smul_eq_mul] using
    hs.sum_mem (fun i _ => hu.1 i) hu.2 (fun i _ => hx i)

/-- A continuous kernel on a convex set of nodes has an integrable Dirichlet average. -/
theorem integrable_dirichletMeasure_comp_affine [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hs : Convex ℝ s) (hx : ∀ i, x i ∈ s)
    {f : ℝ → ℝ} (hf : ContinuousOn f s) :
    Integrable (fun u => f (∑ i, u i * x i)) (dirichletMeasure b) := by
  apply integrable_dirichletMeasure_of_continuousOn hb
  exact hf.comp (by fun_prop) (fun _ hu => dirichlet_affine_mem hs hx hu)

/-- The expectation of the affine combination is the parameter-weighted arithmetic mean. -/
theorem integral_dirichletMeasure_affine [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (x : ι → ℝ) :
    (∫ u, (∑ i, u i * x i) ∂dirichletMeasure b) = ∑ i, (b i / ∑ j, b j) * x i := by
  let := isProbabilityMeasure_dirichletMeasure hb
  rw [integral_finsetSum _ (fun i _ =>
    ((memLp_dirichletMeasure_coordinate hb i 1).integrable (by simp)).mul_const _)]
  simp_rw [integral_mul_const, integral_dirichletMeasure_coordinate hb]

/-- Jensen's lower and upper bounds for a convex real Dirichlet average. -/
theorem convexOn_dirichlet_average_bounds [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hx : ∀ i, x i ∈ s)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hfc : ContinuousOn f s) :
    f (∑ i, (b i / ∑ j, b j) * x i) ≤
        (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) ∧
      (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) ≤
        ∑ i, (b i / ∑ j, b j) * f (x i) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hint := integrable_dirichletMeasure_comp_affine hb hf.1 hx hfc
  have haff : Integrable (fun u => ∑ i, u i * x i) (dirichletMeasure b) :=
    integrable_dirichletMeasure_of_continuousOn hb (by fun_prop)
  constructor
  · rw [← integral_dirichletMeasure_affine hb x]
    have hKs : convexHull ℝ (Set.range x) ⊆ s := convexHull_min (Set.range_subset_iff.2 hx) hf.1
    apply (hf.subset hKs (convex_convexHull ℝ _)).map_integral_le (hfc.mono hKs)
      ((Set.finite_range x).isCompact_convexHull ℝ).isClosed _ haff hint
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    exact dirichlet_affine_mem (convex_convexHull ℝ _)
      (fun i => subset_convexHull ℝ _ ⟨i, rfl⟩) hu
  · rw [← integral_dirichletMeasure_affine hb (fun i => f (x i))]
    apply integral_mono_ae hint (integrable_dirichletMeasure_of_continuousOn hb (by fun_prop))
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    simpa only [smul_eq_mul] using hf.map_sum_le (fun i _ => hu.1 i) hu.2 (fun i _ => hx i)

/-- The Jensen bounds reverse for a concave real Dirichlet average. -/
theorem concaveOn_dirichlet_average_bounds [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hx : ∀ i, x i ∈ s)
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) (hfc : ContinuousOn f s) :
    (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) ≤
        f (∑ i, (b i / ∑ j, b j) * x i) ∧
      (∑ i, (b i / ∑ j, b j) * f (x i)) ≤
        ∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b := by
  have h := convexOn_dirichlet_average_bounds hb hx hf.neg hfc.neg
  simpa only [Pi.neg_apply, integral_neg, mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] using h

/-- A coordinate times an affine combination has an explicit mixed second moment. -/
theorem integral_dirichletMeasure_coordinate_mul_affine [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (x : ι → ℝ) (i : ι) :
    (∫ u, u i * (∑ j, u j * x j) ∂dirichletMeasure b) =
      b i * ((∑ j, b j * x j) + x i) / ((∑ j, b j) * ((∑ j, b j) + 1)) := by
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [integral_finsetSum _ (fun j _ =>
    integrable_dirichletMeasure_of_continuousOn hb (by fun_prop))]
  simp_rw [integral_mul_const]
  have hm (j : ι) : (∫ u, u i * u j ∂dirichletMeasure b) =
      (b i * b j + if j = i then b i else 0) /
        ((∑ k, b k) * ((∑ k, b k) + 1)) := by
    by_cases hji : j = i
    · subst j
      simp only [← sq, integral_dirichletMeasure_coordinate_sq hb, ↓reduceIte]
      ring
    · rw [integral_dirichletMeasure_two_coordinates hb (Ne.symm hji), ite_eq_right hji, add_zero]
  simp_rw [hm, div_mul_eq_mul_div, add_mul, ← Finset.sum_div,
    Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- An affine combination under a positive Dirichlet law is almost surely constant
exactly when every node is that constant. No positivity of the nodes is required. -/
theorem ae_dirichlet_affine_eq_const_iff [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (a : ℝ) :
    ((fun u => ∑ i, u i * x i) =ᵐ[dirichletMeasure b] (fun _ => a)) ↔
      ∀ i, x i = a := by
  let := isProbabilityMeasure_dirichletMeasure hb
  constructor
  · intro h i
    have hc : 0 < ∑ j, b j := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
    have he := integral_congr_ae h
    rw [integral_dirichletMeasure_affine hb] at he
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at he
    have he' : ∑ j, b j * x j = a * ∑ j, b j := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div] at he
      exact (div_eq_iff hc.ne').mp he
    have hm := integral_congr_ae (h.mono (fun u hu => congrArg (fun v => u i * v) hu))
    rw [integral_dirichletMeasure_coordinate_mul_affine hb x i,
      integral_mul_const, integral_dirichletMeasure_coordinate hb, he'] at hm
    have hc1 : (∑ j, b j) + 1 ≠ 0 := by positivity
    field_simp [hc.ne', hc1] at hm
    nlinarith [hb i]
  · intro h
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    simp_rw [h, ← Finset.sum_mul, hu.2, one_mul]

/-- Two affine combinations agree almost surely under a positive Dirichlet law
exactly when their node vectors agree. -/
theorem ae_dirichlet_affine_eq_iff [Nonempty ι] {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ((fun u => ∑ i, u i * x i) =ᵐ[dirichletMeasure b]
      (fun u => ∑ i, u i * y i)) ↔ x = y := by
  constructor
  · intro h
    have he : (fun u => ∑ i, u i * (x i - y i)) =ᵐ[dirichletMeasure b] (fun _ => 0) := by
      filter_upwards [h] with u hu
      simp only [mul_sub, Finset.sum_sub_distrib, hu, sub_self]
    have hc := (ae_dirichlet_affine_eq_const_iff hb 0).mp he
    exact funext (fun i => sub_eq_zero.mp (hc i))
  · rintro rfl
    exact Filter.EventuallyEq.rfl

/-- A convex kernel gives a convex function of the Dirichlet average's node vector. -/
theorem convexOn_dirichlet_average [Nonempty ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hfc : ContinuousOn f s) :
    ConvexOn ℝ {x : ι → ℝ | ∀ i, x i ∈ s}
      (fun x => ∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) := by
  have hconv : Convex ℝ {x : ι → ℝ | ∀ i, x i ∈ s} := by
    intro x hx y hy a c ha hc hac i
    exact hf.1 (hx i) (hy i) ha hc hac
  refine ⟨hconv, ?_⟩
  intro x hx y hy a c ha hc hac
  have hz := hconv hx hy ha hc hac
  have hi := integrable_dirichletMeasure_comp_affine hb hf.1 hx hfc
  have hj := integrable_dirichletMeasure_comp_affine hb hf.1 hy hfc
  have hk := integrable_dirichletMeasure_comp_affine hb hf.1 hz hfc
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi.const_mul a) (hj.const_mul c)]
  apply integral_mono_ae hk ((hi.const_mul a).add (hj.const_mul c))
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  have he : (∑ i, u i * (a • x + c • y) i) =
      a * (∑ i, u i * x i) + c * (∑ i, u i * y i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he]
  exact hf.2 (dirichlet_affine_mem hf.1 hx hu) (dirichlet_affine_mem hf.1 hy hu) ha hc hac

end ProbabilityTheory
