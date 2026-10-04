/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Average
public import ToMathlib.Analysis.Integral.StrictMono

/-!
# Strict Jensen bounds for Dirichlet averages

Positive Dirichlet parameters detect every coordinate of an affine combination.
Consequently a nonconstant node vector gives strict integral Jensen inequalities.
The upper bound is strict too, since every simplex coordinate is positive almost
surely. The kernels need not be powers, and the nodes need not be positive.
-/

open MeasureTheory Set
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- An injective transformation of an affine combination of nonconstant nodes cannot
be almost surely constant under a positive Dirichlet law. -/
theorem not_ae_dirichlet_affine_comp_eq_const {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hs : Convex ℝ s) (hx : ∀ i, x i ∈ s)
    (hne : ∃ i j, x i ≠ x j) {f : ℝ → ℝ} (hf : InjOn f s) (a : ℝ) :
    ¬ ((fun u => f (∑ i, u i * x i)) =ᵐ[dirichletMeasure b] (fun _ => a)) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  intro h
  obtain ⟨v, hv, hv'⟩ := (h.and (ae_mem_stdSimplex_dirichletMeasure b)).exists
  have he : (fun u => ∑ i, u i * x i) =ᵐ[dirichletMeasure b]
      (fun _ => ∑ i, v i * x i) := by
    filter_upwards [h, ae_mem_stdSimplex_dirichletMeasure b] with u hu hu'
    exact hf (dirichlet_affine_mem hs hx hu') (dirichlet_affine_mem hs hx hv')
      (hu.trans hv.symm)
  have hc := (ae_dirichlet_affine_eq_const_iff hb _).mp he
  obtain ⟨i, j, hij⟩ := hne
  exact hij ((hc i).trans (hc j).symm)

/-- Both Jensen bounds are strict for a strictly convex kernel and nonconstant nodes. -/
theorem strictConvexOn_dirichlet_average_bounds {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hs : IsClosed s) (hx : ∀ i, x i ∈ s)
    (hne : ∃ i j, x i ≠ x j) {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) (hfc : ContinuousOn f s) :
    f (∑ i, (b i / ∑ j, b j) * x i) <
        (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) ∧
      (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) <
        ∑ i, (b i / ∑ j, b j) * f (x i) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hint := integrable_dirichletMeasure_comp_affine hb hf.1 hx hfc
  have haff : Integrable (fun u => ∑ i, u i * x i) (dirichletMeasure b) :=
    integrable_dirichletMeasure_of_continuousOn hb (by fun_prop)
  constructor
  · have h := hf.ae_eq_const_or_map_average_lt hfc hs
      ((ae_mem_stdSimplex_dirichletMeasure b).mono (fun _ hu => dirichlet_affine_mem hf.1 hx hu))
      haff hint
    rcases h with h | h
    · have hc := (ae_dirichlet_affine_eq_const_iff hb _).mp h
      obtain ⟨i, j, hij⟩ := hne
      exact False.elim (hij ((hc i).trans (hc j).symm))
    · simpa only [average_eq_integral, integral_dirichletMeasure_affine hb] using h
  · rw [← integral_dirichletMeasure_affine hb (fun i => f (x i))]
    apply integral_lt_integral_of_ae_lt hint
      (integrable_dirichletMeasure_of_continuousOn hb (by fun_prop))
    filter_upwards [ae_mem_stdSimplexInterior_dirichletMeasure b] with u hu
    obtain ⟨i, j, hij⟩ := hne
    simpa only [smul_eq_mul] using hf.map_sum_lt (fun i _ => hu.2 i) hu.1.2
      (fun i _ => hx i) ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hij⟩

/-- Both Jensen bounds reverse strictly for a strictly concave kernel and nonconstant nodes. -/
theorem strictConcaveOn_dirichlet_average_bounds {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {s : Set ℝ} (hs : IsClosed s) (hx : ∀ i, x i ∈ s)
    (hne : ∃ i j, x i ≠ x j) {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ s f) (hfc : ContinuousOn f s) :
    (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) <
        f (∑ i, (b i / ∑ j, b j) * x i) ∧
      (∑ i, (b i / ∑ j, b j) * f (x i)) <
        ∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b := by
  have h := strictConvexOn_dirichlet_average_bounds hb hs hx hne hf.neg hfc.neg
  simpa only [Pi.neg_apply, integral_neg, mul_neg, Finset.sum_neg_distrib, neg_lt_neg_iff] using h

/-- A strictly convex kernel gives a strictly convex Dirichlet average as a function
of its node vector. Positive parameters prevent loss of strictness under integration. -/
theorem strictConvexOn_dirichlet_average {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f) (hfc : ContinuousOn f s) :
    StrictConvexOn ℝ {x : ι → ℝ | ∀ i, x i ∈ s}
      (fun x => ∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) := by
  have hconv := convexOn_dirichlet_average hb hf.convexOn hfc
  refine ⟨hconv.1, ?_⟩
  intro x hx y hy hxy a c ha hc hac
  have hz := hconv.1 hx hy ha.le hc.le hac
  have hi := integrable_dirichletMeasure_comp_affine hb hf.1 hx hfc
  have hj := integrable_dirichletMeasure_comp_affine hb hf.1 hy hfc
  have hk := integrable_dirichletMeasure_comp_affine hb hf.1 hz hfc
  have haff (u : ι → ℝ) : (∑ i, u i * (a • x + c • y) i) =
      a * (∑ i, u i * x i) + c * (∑ i, u i * y i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  apply lt_of_le_of_ne (hconv.2 hx hy ha.le hc.le hac)
  intro he
  simp only [smul_eq_mul] at he
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul a) (hj.const_mul c)] at he
  have hle : ∀ᵐ u ∂dirichletMeasure b, f (∑ i, u i * (a • x + c • y) i) ≤
      a * f (∑ i, u i * x i) + c * f (∑ i, u i * y i) := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    rw [haff]
    exact hf.convexOn.2 (dirichlet_affine_mem hf.1 hx hu)
      (dirichlet_affine_mem hf.1 hy hu) ha.le hc.le hac
  have heq := (integral_eq_iff_of_ae_le hk ((hi.const_mul a).add (hj.const_mul c)) hle).mp he
  apply hxy
  apply (ae_dirichlet_affine_eq_iff hb).mp
  filter_upwards [heq, ae_mem_stdSimplex_dirichletMeasure b] with u hu hu'
  by_contra hne
  rw [haff] at hu
  exact (hf.2 (dirichlet_affine_mem hf.1 hx hu')
    (dirichlet_affine_mem hf.1 hy hu') hne ha hc hac).ne hu

/-- A strictly concave kernel gives a strictly concave function of the node vector. -/
theorem strictConcaveOn_dirichlet_average {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f) (hfc : ContinuousOn f s) :
    StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, x i ∈ s}
      (fun x => ∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) := by
  have h := (strictConvexOn_dirichlet_average hb hf.neg hfc.neg).neg
  simpa only [Pi.neg_def, integral_neg, neg_neg] using h

end ProbabilityTheory
