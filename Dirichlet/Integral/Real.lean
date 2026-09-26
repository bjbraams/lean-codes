/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Beta.Real
public import StdSimplexMeasure.Integral

import all StdSimplexMeasure.Measure.Basic

/-!
# Real Dirichlet monomial integrals

Shared analytic foundations for the real probability distribution and complex Dirichlet
integrals. No Dirichlet probability measure is constructed or imported here.

## Main results

* `ProbabilityTheory.lintegral_dirichletMonomial_of_unique`: The nonnegative Dirichlet monomial
  integral on a singleton index type: the simplex is a single point of mass one.
* `ProbabilityTheory.lintegral_dirichletMonomial_eq_mvRealBeta_of_subtype`: The induction step
  for the nonnegative Dirichlet monomial integral: slicing off the coordinate `i` reduces the
  integral over a nontrivial simplex to the integral over the simplex of the remaining
  coordinates, whose value is supplied as a hypothesis.
* `ProbabilityTheory.lintegral_dirichletMonomial_eq_mvRealBeta`: The nonnegative Dirichlet
  monomial integral, used to establish integrability before passing to the Bochner integral. The
  proof is a strong induction on the number of coordinates, slicing off one coordinate at a
  time.
* `ProbabilityTheory.mvRealBeta_eq_integral`: The integral representation of `mvRealBeta`.
* `ProbabilityTheory.integrableOn_mvRealBetaMonomial`: A real Dirichlet monomial is integrable
  at positive parameters, including when the index type is empty. This is the shared majorant
  for complex Dirichlet integrals.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Scaling the free coordinates in a simplex slice separates a Dirichlet monomial into its
distinguished-coordinate factor, radial factor, and lower-dimensional monomial. -/
private theorem prod_rpow_stdSimplexCoordMap_scale
    (i : ι) (b : ι → ℝ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    (∏ j, (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) j) ^ (b j - 1)) =
      t ^ (b i - 1) *
        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) *
          ∏ q : {j : ι // j ≠ i}, v q ^ (b q - 1) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hsum : ∑ q, (1 - t) * v q = 1 - t := by
    rw [← Finset.mul_sum, hv.2, mul_one]
  rw [stdSimplexCoordMap_apply_self, hsum]
  have hone : 1 - (1 - t) = t := by ring
  rw [hone]
  have hprod :
      (∏ q : {j : ι // j ≠ i},
        (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) q) ^ (b q - 1)) =
      ∏ q : {j : ι // j ≠ i}, ((1 - t) * v q) ^ (b q - 1) := by
    apply Finset.prod_congr rfl
    intro q _
    rw [stdSimplexCoordMap_apply_of_ne i q q.property]
  rw [hprod]
  have ht' : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
  simp_rw [Real.mul_rpow ht' (hv.1 _)]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (sub_pos.mpr ht.2)]
  ring

/-- The nonnegative Dirichlet monomial integral on a singleton index type: the simplex is a
single point of mass one. -/
theorem lintegral_dirichletMonomial_of_unique [Unique ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, ENNReal.ofReal (∏ i,
        u i ^ (b i - 1)) ∂stdSimplexMeasure =
      ENNReal.ofReal (mvRealBeta b) := by
  classical
  rw [stdSimplexMeasure_unique, MeasureTheory.setLIntegral_dirac]
  have hG : Gamma (b default) ≠ 0 := ne_of_gt (Gamma_pos_of_pos (hb default))
  simp [mvRealBeta, hG, Convexity.StdSimplex.coordinateSet]

open scoped Classical in
/-- The inner integral of a simplex slice of the nonnegative Dirichlet monomial: the
distinguished coordinate and the radial factor come out, leaving the lower-dimensional
monomial integral. -/
theorem lintegral_dirichletMonomial_slice (i : ι) (b : ι → ℝ) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
      ENNReal.ofReal (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^ (b k - 1))
        ∂stdSimplexMeasure) =
      ENNReal.ofReal (t ^ (b i - 1) * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
        ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
          ENNReal.ofReal (∏ q, v q ^ (b q - 1)) ∂stdSimplexMeasure := by
  calc
    _ = ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
        ENNReal.ofReal ((t ^ (b i - 1) * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
          ∏ q : {j : ι // j ≠ i}, v q ^ (b q - 1)) ∂stdSimplexMeasure := by
      apply setLIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
      intro v hv
      change ENNReal.ofReal
        (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^ (b k - 1)) = _
      rw [prod_rpow_stdSimplexCoordMap_scale i b ht hv]
    _ = _ := by
      rw [← lintegral_const_mul]
      · apply lintegral_congr
        intro v
        rw [← ENNReal.ofReal_mul (mul_nonneg
          (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _))]
      · fun_prop

open scoped Classical in
/-- The Jacobian power of a simplex slice merges with the radial factor of the Dirichlet
monomial into a single power of `1 - t`. -/
theorem pow_mul_rpow_sum_sub_one [Nontrivial ι] (i : ι) (b : ι → ℝ) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (1 - t) ^ (Fintype.card ι - 2) *
        (t ^ (b i - 1) * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) =
      t ^ (b i - 1) * (1 - t) ^ ((∑ q : {j : ι // j ≠ i}, b q) - 1) := by
  have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
  have hexp : (Fintype.card ι - 2 : ℝ) + (∑ q : {j : ι // j ≠ i}, (b q - 1)) =
      (∑ q : {j : ι // j ≠ i}, b q) - 1 := by
    have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      rw [hcard_rest, Nat.cast_sub (by omega)]
      norm_num
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hcast_rest]
    ring
  have hcast_d : ((Fintype.card ι - 2 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 2 := by
    rw [Nat.cast_sub hcard_two]
    norm_num
  calc
    (1 - t) ^ (Fintype.card ι - 2) *
        (t ^ (b i - 1) * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) =
        t ^ (b i - 1) *
          ((1 - t) ^ (Fintype.card ι - 2) * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by
      ring
    _ = t ^ (b i - 1) *
        (1 - t) ^ ((Fintype.card ι - 2 : ℕ) + (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (sub_pos.mpr ht.2)]
    _ = _ := by rw [hcast_d, hexp]

open scoped Classical in
/-- The induction step for the nonnegative Dirichlet monomial integral: slicing off the
coordinate `i` reduces the integral over a nontrivial simplex to the integral over the simplex
of the remaining coordinates, whose value is supplied as a hypothesis. -/
theorem lintegral_dirichletMonomial_eq_mvRealBeta_of_subtype [Nontrivial ι] (i : ι)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (hih : ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
        ENNReal.ofReal (∏ q, v q ^ (b q - 1)) ∂stdSimplexMeasure =
      ENNReal.ofReal (mvRealBeta fun q : {j : ι // j ≠ i} => b q)) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, ENNReal.ofReal (∏ i,
        u i ^ (b i - 1)) ∂stdSimplexMeasure =
      ENNReal.ofReal (mvRealBeta b) := by
  have hrest_nonempty : Nonempty {j : ι // j ≠ i} := by
    obtain ⟨j, hji⟩ := exists_ne i
    exact ⟨⟨j, hji⟩⟩
  have hc : 0 < ∑ q : {j : ι // j ≠ i}, b q :=
    Finset.sum_pos (fun q _ => hb q) Finset.univ_nonempty
  rw [lintegral_stdSimplex_split_at i _ (by fun_prop)]
  have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ENNReal.ofReal ((1 - t) ^ (Fintype.card ι - 2)) *
          (∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
            ENNReal.ofReal (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^ (b k - 1))
              ∂stdSimplexMeasure) =
        ENNReal.ofReal (mvRealBeta fun q : {j : ι // j ≠ i} => b q) *
          ENNReal.ofReal (t ^ (b i - 1) * (1 - t) ^ ((∑ q : {j : ι // j ≠ i}, b q) - 1)) := by
    filter_upwards [ae_restrict_of_ae (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
    have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
    rw [lintegral_dirichletMonomial_slice i b ht, hih, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr ht.2.le) _),
      pow_mul_rpow_sum_sub_one i b ht, mul_comm]
  rw [lintegral_congr_ae houter, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Icc_rpow_mul_one_sub_rpow (hb i) hc)]
  · rw [integral_Icc_rpow_mul_one_sub_rpow (hb i) hc, mul_comm,
      ← ENNReal.ofReal_mul (le_of_lt (beta_pos (hb i) hc))]
    congr 1
    dsimp only [mvRealBeta]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne b i, beta]
    have hGc : Gamma (∑ q : {j : ι // j ≠ i}, b q) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hc)
    field_simp
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- The nonnegative Dirichlet monomial integral, used to establish integrability before passing
to the Bochner integral. The proof is a strong induction on the number of coordinates, slicing
off one coordinate at a time. -/
theorem lintegral_dirichletMonomial_eq_mvRealBeta {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, ENNReal.ofReal (∏ i,
        u i ^ (b i - 1)) ∂stdSimplexMeasure =
      ENNReal.ofReal (mvRealBeta b) := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h n ih =>
      cases isEmpty_or_nonempty ι with
      | inl hι =>
          let _ := hι
          simp [mvRealBeta, stdSimplexMeasure_empty]
      | inr hι =>
          let _ := hι
          cases subsingleton_or_nontrivial ι with
          | inl hsub =>
              let : Unique ι := ⟨⟨Classical.choice hι⟩, fun a => hsub.elim _ _⟩
              exact lintegral_dirichletMonomial_of_unique hb
          | inr hnontrivial =>
              let _ := hnontrivial
              let i : ι := Classical.choice hι
              have hcard : Fintype.card {j : ι // j ≠ i} < n := by
                rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                exact Nat.sub_one_lt (Fintype.card_pos_iff.mpr hι).ne'
              exact lintegral_dirichletMonomial_eq_mvRealBeta_of_subtype i hb
                (ih _ hcard (fun j => hb j) rfl)

/-- The integral representation of `mvRealBeta`. -/
theorem mvRealBeta_eq_integral {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    mvRealBeta b =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ∏ i, u i ^ (b i - 1) ∂stdSimplexMeasure := by
  symm
  rw [integral_eq_lintegral_of_nonneg_ae]
  · rw [lintegral_dirichletMonomial_eq_mvRealBeta hb]
    apply ENNReal.toReal_ofReal
    cases isEmpty_or_nonempty ι with
    | inl hι =>
        let _ := hι
        simp [mvRealBeta]
    | inr hι =>
        let _ := hι
        exact (mvRealBeta_pos hb).le
  · filter_upwards [ae_restrict_mem (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu.1 j) _
  · let g : (ι → ℝ) → ℝ := fun u =>
      ∏ i, ((ENNReal.ofReal (u i)) ^ (b i - 1)).toReal
    have hg : AEStronglyMeasurable g
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
      apply Measurable.aestronglyMeasurable
      dsimp only [g]
      fun_prop
    refine hg.congr ?_
    filter_upwards [ae_restrict_mem (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    apply Finset.prod_congr rfl
    intro i _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (hu.1 i)]

/-- A real Dirichlet monomial is integrable at positive parameters, including when the
index type is empty. This is the shared majorant for complex Dirichlet integrals. -/
theorem integrableOn_mvRealBetaMonomial {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    IntegrableOn (fun u : ι → ℝ ↦ ∏ i, u i ^ (b i - 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      apply Integrable.of_integral_ne_zero
      rw [← mvRealBeta_eq_integral hb]
      exact ne_of_gt (mvRealBeta_pos hb)

end ProbabilityTheory

end
