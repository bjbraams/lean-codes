/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Bridge
public import Dirichlet.Real.Moments
public import StdSimplexMeasure.MomentDetermination

/-!
# Merging two coordinates of a Dirichlet distribution

Let `u` be Dirichlet distributed with positive parameters `b`, and let `a ≠ a'` be two indices.
Writing the two coordinates `u a` and `u a'` as `v 0 · s` and `v 1 · s`, the proportion `v` has
the two-parameter Dirichlet (beta) law with parameters `b a` and `b a'`, independently of the
vector obtained by merging the two coordinates into `s`, which is Dirichlet with the merged
parameter `b a + b a'`. Equivalently, the Dirichlet measure is the image of the product of these
two Dirichlet measures under the merging map. Iterating the identity is the stick-breaking
representation of the Dirichlet distribution.

The measure identity is proved by comparing monomial moments on the compact simplex.

## Main definitions

* `Dirichlet.mergeMap`: the map from proportions and merged coordinates to coordinates.
* `Dirichlet.mergeParam`, `Dirichlet.pairParam`: the merged parameters and the parameters of
  the two merged coordinates.

## Main results

* `Dirichlet.dirichletMeasure_eq_map_mergeMap`: the measure identity.
* `Dirichlet.integral_dirichletMeasure_eq_merge`: the corresponding iterated integral.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, equation (4.21).
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [DecidableEq ι] {a a' : ι}

/-- The merged node, as an element of the index type with `a'` removed. -/
def mergeIndex (h : a ≠ a') : {i : ι // i ≠ a'} := ⟨a, h⟩

/-- The merged parameters: the parameter at the merged node is `b a + b a'`. -/
def mergeParam {R : Type*} [Add R] (a a' : ι) (b : ι → R) : {i : ι // i ≠ a'} → R :=
  fun j => if (j : ι) = a then b a + b a' else b j

/-- The parameters of the two merged nodes. -/
def pairParam {R : Type*} (a a' : ι) (b : ι → R) : Fin 2 → R := ![b a, b a']

/-- The merging map: the proportions `v` split the merged coordinate between `a` and `a'`.
It is defined over any ring of scalars, so that it can be complexified. -/
def mergeMap {R : Type*} [Mul R] (h : a ≠ a') (v : Fin 2 → R) (y : {i : ι // i ≠ a'} → R) :
    ι → R :=
  fun i => if hi : i = a' then v 1 * y (mergeIndex h) else
    if i = a then v 0 * y (mergeIndex h) else y ⟨i, hi⟩

/-- The merging map at the first merged index. -/
theorem mergeMap_apply_left {R : Type*} [Mul R] (h : a ≠ a') (v : Fin 2 → R)
    (y : {i : ι // i ≠ a'} → R) :
    mergeMap h v y a = v 0 * y (mergeIndex h) := by
  simp [mergeMap, h]

/-- The merging map at the second merged index. -/
theorem mergeMap_apply_right {R : Type*} [Mul R] (h : a ≠ a') (v : Fin 2 → R)
    (y : {i : ι // i ≠ a'} → R) :
    mergeMap h v y a' = v 1 * y (mergeIndex h) := by
  simp [mergeMap]

/-- The merging map away from the merged indices. -/
theorem mergeMap_apply_other {R : Type*} [Mul R] (h : a ≠ a') (v : Fin 2 → R)
    (y : {i : ι // i ≠ a'} → R)
    (k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}) :
    mergeMap h v y k.1.1 = y k.1 := by
  have h1 : (k.1 : ι) ≠ a' := k.1.2
  have h2 : (k.1 : ι) ≠ a := fun e => k.2 (Subtype.ext e)
  simp [mergeMap, h1, h2]

/-- The merged parameter at the merged node. -/
theorem mergeParam_apply_merge {R : Type*} [Add R] (h : a ≠ a') (b : ι → R) :
    mergeParam a a' b (mergeIndex h) = b a + b a' := by
  simp [mergeParam, mergeIndex]

/-- The merged parameters away from the merged node. -/
theorem mergeParam_apply_other {R : Type*} [Add R] (h : a ≠ a') (b : ι → R)
    (k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}) :
    mergeParam a a' b k.1 = b k.1.1 := by
  have h2 : (k.1 : ι) ≠ a := fun e => k.2 (Subtype.ext e)
  simp [mergeParam, h2]

/-- The merging map commutes with ring homomorphisms of the scalars, such as the inclusion of
the reals in the complex numbers. -/
theorem mergeMap_map {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (φ : R →+* S)
    (h : a ≠ a') (v : Fin 2 → R) (y : {i : ι // i ≠ a'} → R) :
    mergeMap h (fun k => φ (v k)) (fun j => φ (y j)) = fun i => φ (mergeMap h v y i) := by
  funext i
  unfold mergeMap
  split_ifs <;> simp

/-- The merging map is continuous. -/
theorem continuous_mergeMap (h : a ≠ a') :
    Continuous (fun p : (Fin 2 → ℝ) × ({i : ι // i ≠ a'} → ℝ) => mergeMap h p.1 p.2) := by
  refine continuous_pi fun i => ?_
  unfold mergeMap
  split_ifs <;> fun_prop

variable [Fintype ι]

/-- A product over `ι` splits off the two merged indices. -/
theorem prod_eq_merge {M : Type*} [CommMonoid M] (h : a ≠ a') (F : ι → M) :
    ∏ i, F i = F a' * (F a * ∏ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}, F k.1.1) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a',
    Fintype.prod_eq_mul_prod_subtype_ne (fun j : {i : ι // i ≠ a'} => F j.1) (mergeIndex h)]
  rfl

/-- A product over the merged index type splits off the merged node. -/
theorem prod_merged_eq {M : Type*} [CommMonoid M] (h : a ≠ a') (F : {i : ι // i ≠ a'} → M) :
    ∏ j, F j = F (mergeIndex h) * ∏ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}, F k.1 :=
  Fintype.prod_eq_mul_prod_subtype_ne _ _

/-- A sum over `ι` splits off the two merged indices. -/
theorem sum_eq_merge {M : Type*} [AddCommMonoid M] (h : a ≠ a') (F : ι → M) :
    ∑ i, F i = F a' + (F a + ∑ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}, F k.1.1) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ a',
    Fintype.sum_eq_add_sum_subtype_ne (fun j : {i : ι // i ≠ a'} => F j.1) (mergeIndex h)]
  rfl

/-- A sum over the merged index type splits off the merged node. -/
theorem sum_merged_eq {M : Type*} [AddCommMonoid M] (h : a ≠ a') (F : {i : ι // i ≠ a'} → M) :
    ∑ j, F j = F (mergeIndex h) + ∑ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h}, F k.1 :=
  Fintype.sum_eq_add_sum_subtype_ne _ _

/-- The merging map sends pairs of simplex points to simplex points. -/
theorem mergeMap_mem_coordinateSet (h : a ≠ a') {v : Fin 2 → ℝ} {y : {i : ι // i ≠ a'} → ℝ}
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hy : y ∈ Convexity.StdSimplex.coordinateSet ℝ {i : ι // i ≠ a'}) :
    mergeMap h v y ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  rw [Convexity.StdSimplex.mem_coordinateSet] at hv hy ⊢
  refine ⟨fun i => ?_, ?_⟩
  · unfold mergeMap
    split_ifs
    · exact mul_nonneg (hv.1 1) (hy.1 _)
    · exact mul_nonneg (hv.1 0) (hy.1 _)
    · exact hy.1 _
  · rw [sum_eq_merge h, mergeMap_apply_right, mergeMap_apply_left]
    simp_rw [mergeMap_apply_other]
    have hv2 : v 0 + v 1 = 1 := by simpa [Fin.sum_univ_two] using hv.2
    have hy2 := hy.2
    rw [sum_merged_eq h] at hy2
    linear_combination hy2 + y (mergeIndex h) * hv2

/-- Monomials of the merged coordinates. -/
theorem prod_mergeMap_pow (h : a ≠ a') (m : ι → ℕ) (v : Fin 2 → ℝ)
    (y : {i : ι // i ≠ a'} → ℝ) :
    ∏ i, mergeMap h v y i ^ m i =
      (∏ i, v i ^ pairParam a a' m i) * ∏ j, y j ^ mergeParam a a' m j := by
  rw [prod_eq_merge h, prod_merged_eq h, mergeMap_apply_right, mergeMap_apply_left,
    mergeParam_apply_merge, Fin.prod_univ_two]
  simp_rw [mergeMap_apply_other, mergeParam_apply_other]
  simp only [pairParam, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_pow, mul_pow, pow_add]
  ring

omit [DecidableEq ι] [Fintype ι] in
/-- The parameters of the two merged nodes are positive. -/
theorem pairParam_mem_mvRealBetaDomain {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    pairParam a a' b ∈ mvRealBetaDomain := by
  intro i; fin_cases i
  · exact hb a
  · exact hb a'

omit [Fintype ι] in
/-- The merged parameters are positive. -/
theorem mergeParam_mem_mvRealBetaDomain {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    mergeParam a a' b ∈ mvRealBetaDomain := by
  intro j
  unfold mergeParam
  split_ifs
  · exact add_pos (hb a) (hb a')
  · exact hb j

/-- **The merging identity for Dirichlet measures.** For positive parameters, the Dirichlet
measure is the image of the product of the two-node Dirichlet measure for the proportions and
the merged Dirichlet measure, under the merging map. -/
theorem dirichletMeasure_eq_map_mergeMap (h : a ≠ a') {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    dirichletMeasure b = ((dirichletMeasure (pairParam a a' b)).prod
      (dirichletMeasure (mergeParam a a' b))).map (fun p => mergeMap h p.1 p.2) := by
  have : Nonempty ι := ⟨a⟩
  have : Nonempty {i : ι // i ≠ a'} := ⟨mergeIndex h⟩
  have h2 := pairParam_mem_mvRealBetaDomain (a := a) (a' := a') hb
  have h' := mergeParam_mem_mvRealBetaDomain (a := a) (a' := a') hb
  have := isProbabilityMeasure_dirichletMeasure hb
  have := isProbabilityMeasure_dirichletMeasure h2
  have := isProbabilityMeasure_dirichletMeasure h'
  set μ := (dirichletMeasure (pairParam a a' b)).prod (dirichletMeasure (mergeParam a a' b))
  have hT := continuous_mergeMap (ι := ι) h
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  refine eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex (dirichletMeasure_restrict b)
    ?_ ?_
  · apply Measure.restrict_eq_self_of_ae_mem
    refine (ae_map_iff hT.measurable.aemeasurable hS).mpr ?_
    have h1 : ∀ᵐ p ∂μ, p.1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2) :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst)
        (ae_mem_of_restrict_eq_self
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ (Fin 2)).measurableSet
          (dirichletMeasure_restrict _))
    have h2 : ∀ᵐ p ∂μ, p.2 ∈ Convexity.StdSimplex.coordinateSet ℝ {i : ι // i ≠ a'} :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd)
        (ae_mem_of_restrict_eq_self
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
          (dirichletMeasure_restrict _))
    filter_upwards [h1, h2] with p hp1 hp2
    exact mergeMap_mem_coordinateSet h hp1 hp2
  · intro m
    rw [integral_map hT.measurable.aemeasurable (by fun_prop : Continuous fun u : ι → ℝ =>
      ∏ i, u i ^ m i).aestronglyMeasurable]
    simp_rw [prod_mergeMap_pow h m]
    rw [integral_prod_mul (μ := dirichletMeasure (pairParam a a' b))
      (ν := dirichletMeasure (mergeParam a a' b))
      (fun v : Fin 2 → ℝ => ∏ i, v i ^ pairParam a a' m i)
      (fun y => ∏ j, y j ^ mergeParam a a' m j),
      integral_dirichletMeasure_monomial hb, integral_dirichletMeasure_monomial h2,
      integral_dirichletMeasure_monomial h']
    have hsum_b : ∑ j, mergeParam a a' b j = ∑ i, b i := by
      rw [sum_eq_merge h, sum_merged_eq h, mergeParam_apply_merge]
      simp_rw [mergeParam_apply_other]
      ring
    have hsum_m : ∑ j, mergeParam a a' m j = ∑ i, m i := by
      rw [sum_eq_merge h, sum_merged_eq h, mergeParam_apply_merge]
      simp_rw [mergeParam_apply_other]
      ring
    have hprod : ∏ j, (ascPochhammer ℝ (mergeParam a a' m j)).eval (mergeParam a a' b j) =
        (ascPochhammer ℝ (m a + m a')).eval (b a + b a') *
          ∏ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h},
            (ascPochhammer ℝ (m k.1.1)).eval (b k.1.1) := by
      rw [prod_merged_eq h, mergeParam_apply_merge, mergeParam_apply_merge]
      simp_rw [mergeParam_apply_other]
    have hpos : 0 < (ascPochhammer ℝ (m a + m a')).eval (b a + b a') :=
      ascPochhammer_pos _ _ (add_pos (hb a) (hb a'))
    rw [hsum_b, hsum_m, hprod, prod_eq_merge h]
    simp only [pairParam, Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp

/-- **The merging identity for iterated integrals.** For positive parameters and a kernel
continuous on the simplex, the Dirichlet integral is an iterated integral over the proportions
and the merged coordinates. -/
theorem integral_dirichletMeasure_eq_merge (h : a ≠ a') {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ∫ u, g u ∂dirichletMeasure b =
      ∫ v, ∫ y, g (mergeMap h v y) ∂dirichletMeasure (mergeParam a a' b)
        ∂dirichletMeasure (pairParam a a' b) := by
  have : Nonempty ι := ⟨a⟩
  have : Nonempty {i : ι // i ≠ a'} := ⟨mergeIndex h⟩
  have := isProbabilityMeasure_dirichletMeasure hb
  have := isProbabilityMeasure_dirichletMeasure
    (pairParam_mem_mvRealBetaDomain (a := a) (a' := a') hb)
  have := isProbabilityMeasure_dirichletMeasure
    (mergeParam_mem_mvRealBetaDomain (a := a) (a' := a') hb)
  have hT := continuous_mergeMap (ι := ι) h
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hmap := dirichletMeasure_eq_map_mergeMap h hb
  have hm : AEStronglyMeasurable g (dirichletMeasure b) := by
    rw [← dirichletMeasure_restrict]
    exact hg.aestronglyMeasurable hS
  have hi : Integrable g (dirichletMeasure b) := by
    have hint : IntegrableOn g (Convexity.StdSimplex.coordinateSet ℝ ι) (dirichletMeasure b) :=
      hg.integrableOn_compact (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    rwa [IntegrableOn, dirichletMeasure_restrict] at hint
  rw [hmap] at hm hi
  rw [hmap, integral_map hT.measurable.aemeasurable hm]
  exact integral_prod _ ((integrable_map_measure hm hT.measurable.aemeasurable).mp hi)

end Dirichlet

end
