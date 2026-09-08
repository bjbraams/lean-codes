/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.Dirichlet
import StdSimplexMeasure.MvBeta

/-!
# Regularized complex Dirichlet integrals on the standard simplex

This file defines regularized complex Dirichlet densities and their associated integral
functionals. These are complex-valued densities, not measures in the sense of Mathlib's
nonnegative `Measure` type.

## Main definitions and results

* `Complex.mvBeta_eq_integral`: the simplex integral representation of the multivariate Beta
  function.
* `regDirichletDensity`: the pointwise entire regularized Dirichlet density.
* `complexDirichletDensity`: the corresponding normalized complex density.
* `regDirichletIntegral`: integration against the regularized density.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex Fintype MeasureTheory MeasureTheory.Measure

public noncomputable section ComplexDirichlet

namespace Complex

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The complex Dirichlet monomial is integrable on the simplex whenever every parameter
has positive real part. -/
theorem integrableOn_mvBetaMonomial
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    IntegrableOn (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (b i - 1))
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      let a : ι → ℝ := fun i ↦ (b i).re
      have ha : a ∈ ProbabilityTheory.mvRealBetaDomain := fun i => hb i
      have hreal : IntegrableOn (fun u : ι → ℝ ↦ ∏ i, u i ^ (a i - 1))
          (stdSimplex ℝ ι) stdSimplexMeasure := by
        apply Integrable.of_integral_ne_zero
        rw [← ProbabilityTheory.mvRealBeta_eq_integral ha]
        exact ne_of_gt (ProbabilityTheory.mvRealBeta_pos ha)
      let P : Set (ι → ℝ) := {u | ∀ i, 0 < u i}
      have hPopen : IsOpen P := by
        rw [show P = ⋂ i, {u : ι → ℝ | 0 < u i} by ext u; simp [P]]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const (continuous_apply i)
      have hrealP := hreal.mono_set (Set.inter_subset_left :
        stdSimplex ℝ ι ∩ P ⊆ stdSimplex ℝ ι)
      have hcomplexP : IntegrableOn (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (b i - 1))
          (stdSimplex ℝ ι ∩ P) stdSimplexMeasure := by
        apply Integrable.mono hrealP
        · apply ContinuousOn.aestronglyMeasurable
          · apply continuousOn_finsetProd
            intro i _
            exact (Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.cpow_const
              (fun _ hu ↦ ofReal_mem_slitPlane.2 (hu.2 i))
          · exact (isClosed_stdSimplex ℝ ι).measurableSet.inter hPopen.measurableSet
        · filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
              ((isClosed_stdSimplex ℝ ι).measurableSet.inter hPopen.measurableSet)] with u hu
          simp only [Set.mem_inter_iff] at hu
          simp only [norm_prod]
          apply le_of_eq
          apply Finset.prod_congr rfl
          intro i _
          rw [norm_cpow_eq_rpow_re_of_pos (hu.2 i)]
          simp [a, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hu.2 i) _)]
      apply hcomplexP.congr_set_ae
      have hae : ∀ᵐ u ∂stdSimplexMeasure,
          u ∈ stdSimplex ℝ ι → ∀ i, 0 < u i :=
        (ae_restrict_iff' (isClosed_stdSimplex ℝ ι).measurableSet).mp
          (ae_zero_lt_of_mem_stdSimplex (ι := ι))
      filter_upwards [hae] with u hu
      apply propext
      constructor
      · intro hus
        exact ⟨hus, hu hus⟩
      · exact fun hus ↦ hus.1

/-- A simplex slice separates a complex Dirichlet monomial into its distinguished-coordinate,
radial, and lower-dimensional factors. -/
private theorem prod_cpow_stdSimplexCoordMap_scale
    (i : ι) (b : ι → ℂ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
    (∏ j, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) j : ℝ) : ℂ) ^ (b j - 1)) =
      (t : ℂ) ^ (b i - 1) *
        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) *
          ∏ q : {j : ι // j ≠ i}, (v q : ℂ) ^ (b q - 1) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hsum : ∑ q, (1 - t) * v q = 1 - t := by
    rw [← Finset.mul_sum, hv.2, mul_one]
  rw [stdSimplexCoordMap_apply_self, hsum]
  have hone : 1 - (1 - t) = t := by ring
  rw [hone]
  have hprod :
      (∏ q : {j : ι // j ≠ i},
        ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) q : ℝ) : ℂ) ^ (b q - 1)) =
      ∏ q : {j : ι // j ≠ i},
        (((1 - t : ℝ) : ℂ) * (v q : ℂ)) ^ (b q - 1) := by
    apply Finset.prod_congr rfl
    intro q _
    rw [stdSimplexCoordMap_apply_of_ne i q q.property, Complex.ofReal_mul]
  rw [hprod]
  have ht' : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
  simp_rw [Complex.mul_cpow_ofReal_nonneg ht' (hv.1 _)]
  rw [Finset.prod_mul_distrib]
  have hbase : ((1 - t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht.2.ne')
  have hpow : (∏ q : {j : ι // j ≠ i}, ((1 - t : ℝ) : ℂ) ^ (b q - 1)) =
      ((1 - t : ℝ) : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) := by
    induction (Finset.univ : Finset {j : ι // j ≠ i}) using Finset.induction_on with
    | empty => simp
    | @insert q s hqs ih =>
        rw [Finset.prod_insert hqs, Finset.sum_insert hqs, Complex.cpow_add _ _ hbase, ih]
  rw [hpow]
  push_cast
  ring

/-- The absolutely convergent simplex integral representation of the multivariate Beta
function. -/
theorem mvBeta_eq_integral {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = ∫ u in stdSimplex ℝ ι, ∏ i, (u i : ℂ) ^ (b i - 1) ∂stdSimplexMeasure := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h n ih =>
      cases isEmpty_or_nonempty ι with
      | inl hι =>
          let _ := hι
          simp [mvBeta, stdSimplexMeasure_empty]
      | inr hι =>
          let _ := hι
          cases subsingleton_or_nontrivial ι with
          | inl hsub =>
              let : Unique ι :=
                ⟨⟨Classical.choice hι⟩, fun a => hsub.elim _ _⟩
              rw [mvBeta, stdSimplexMeasure_unique, MeasureTheory.setIntegral_dirac]
              have hG : Gamma (b default) ≠ 0 := Gamma_ne_zero_of_re_pos (hb default)
              simp [hG, stdSimplex]
          | inr hnontrivial =>
              let _ := hnontrivial
              let i : ι := Classical.choice hι
              let b' : {j : ι // j ≠ i} → ℂ := fun j => b j
              have hb' : b' ∈ mvBetaConvergent := fun j => hb j
              have hcard : Fintype.card {j : ι // j ≠ i} < n := by
                rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                exact Nat.sub_one_lt (Fintype.card_pos_iff.mpr hι).ne'
              have hih := ih _ hcard (ι := {j : ι // j ≠ i}) hb'
              rw [integral_stdSimplex_split_at i _ (integrableOn_mvBetaMonomial b hb)]
              let c : ℂ := ∑ q : {j : ι // j ≠ i}, b q
              have hrest_nonempty : Nonempty {j : ι // j ≠ i} := by
                obtain ⟨j, hji⟩ := exists_ne i
                exact ⟨⟨j, hji⟩⟩
              have hc : 0 < c.re := by
                dsimp only [c]
                change 0 < Complex.reCLM (∑ q : {j : ι // j ≠ i}, b q)
                rw [map_sum Complex.reCLM b' Finset.univ]
                exact Finset.sum_pos (fun q _ => hb q) Finset.univ_nonempty
              have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
                  (∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                    ∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
                      (b k - 1) ∂stdSimplexMeasure) =
                    (t : ℂ) ^ (b i - 1) *
                      (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) * mvBeta b' := by
                intro t ht
                calc
                  _ = ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                      ((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                        ∏ q, (v q : ℂ) ^ (b q - 1) ∂stdSimplexMeasure := by
                          apply setIntegral_congr_fun (isClosed_stdSimplex ℝ _).measurableSet
                          intro v hv
                          exact prod_cpow_stdSimplexCoordMap_scale i b ht hv
                  _ = ((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                        ∏ q, (v q : ℂ) ^ (b q - 1) ∂stdSimplexMeasure := by
                          rw [MeasureTheory.integral_const_mul]
                  _ = _ := by rw [← hih rfl]
              have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
                rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
              have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
              have hexp : ((Fintype.card ι - 2 : ℕ) : ℂ) +
                  (∑ q : {j : ι // j ≠ i}, (b q - 1)) = c - 1 := by
                have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℂ) =
                    (Fintype.card ι : ℂ) - 1 := by
                  rw [hcard_rest, Nat.cast_sub (by omega)]
                  norm_num
                have hcast_two : ((Fintype.card ι - 2 : ℕ) : ℂ) =
                    (Fintype.card ι : ℂ) - 2 := by
                  rw [Nat.cast_sub hcard_two]
                  norm_num
                simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                  nsmul_eq_mul, mul_one, c]
                rw [hcast_rest, hcast_two]
                ring
              have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
                  ((1 - t) ^ (Fintype.card ι - 2)) •
                      (∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                        ∏ k, ((stdSimplexCoordMap i
                          (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^ (b k - 1)
                          ∂stdSimplexMeasure) =
                    ((t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1)) * mvBeta b' := by
                filter_upwards [ae_restrict_of_ae
                    (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
                  ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
                have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
                rw [hinner t ht]
                have hbase : ((1 - t : ℝ) : ℂ) ≠ 0 :=
                  Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht.2.ne')
                have hbase' : (1 - (t : ℂ)) ≠ 0 := by
                  intro hz
                  apply ht.2.ne
                  exact_mod_cast (sub_eq_zero.mp hz).symm
                rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.cpow_natCast]
                push_cast
                calc
                  ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
                      (((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                          mvBeta b')) =
                      (t : ℂ) ^ (b i - 1) *
                        ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
                          (1 - t : ℂ) ^
                            (∑ q : {j : ι // j ≠ i}, (b q - 1))) * mvBeta b' := by ring
                  _ = _ := by
                    rw [← Complex.cpow_add _ _ hbase', hexp]
              rw [integral_congr_ae houter]
              rw [integral_mul_const]
              have hbeta :
                  (∫ t in Set.Icc (0 : ℝ) 1,
                    (t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1)) =
                    betaIntegral (b i) c := by
                rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one,
                  integral_Icc_eq_integral_Ioc]
              rw [hbeta, betaIntegral_eq_Gamma_mul_div _ _ (hb i) hc]
              have hGc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
              have hGsum : Gamma (b i + c) ≠ 0 :=
                Gamma_ne_zero_of_re_pos (by simpa using add_pos (hb i) hc)
              have hGc' : Gamma (∑ q : {j : ι // j ≠ i}, b q) ≠ 0 := by
                simpa [c] using hGc
              have hGsum' : Gamma (b i + ∑ q : {j : ι // j ≠ i}, b q) ≠ 0 := by
                simpa [c] using hGsum
              dsimp only [mvBeta, b', c]
              rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
                Fintype.sum_eq_add_sum_subtype_ne b i]
              field_simp [hGc', hGsum']

end Complex

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The unnormalized complex Dirichlet monomial is integrable when every exponent parameter
has positive real part. -/
private theorem integrableOn_complexDirichletMonomial
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    IntegrableOn (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (b i - 1))
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  exact Complex.integrableOn_mvBetaMonomial b hb

/-- The regularized Dirichlet density with parameters `b` on `stdSimplexInterior`. For each
fixed `u`, this is an entire function of `b`. -/
def regDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  stdSimplexInterior.indicator (fun u ↦ ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The normalized complex Dirichlet density with parameters `b` on
`stdSimplexInterior`. -/
def complexDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  Gamma (∑ i, b i) * regDirichletDensity b u

/-- Simultaneously permuting the parameters and coordinates leaves the regularized Dirichlet
density unchanged. -/
theorem regDirichletDensity_perm (b : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    regDirichletDensity (b ∘ σ) (u ∘ σ) = regDirichletDensity b u := by
  unfold regDirichletDensity
  have hinter : (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
    have hsimp : (u ∘ σ) ∈ stdSimplex ℝ ι ↔ u ∈ stdSimplex ℝ ι := by
      change u ∈ (fun v ↦ v ∘ σ) ⁻¹' stdSimplex ℝ ι ↔ _
      rw [preimage_stdSimplex_perm]
    simp only [stdSimplexInterior]
    constructor
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mp hu,
        fun i ↦ by simpa using hp (σ.symm i)⟩
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mpr hu, fun i ↦ hp (σ i)⟩
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ
        (fun i ↦ (u i : ℂ) ^ (b i - 1) / Gamma (b i)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- The regularized Dirichlet density is a measurable function. -/
theorem measurable_regDirichletDensity (b : ι → ℂ) :
    Measurable (regDirichletDensity b) := by
  unfold regDirichletDensity
  apply Measurable.indicator _ measurableSet_stdSimplexInterior
  fun_prop

/-- The regularized Dirichlet density integrated over the standard simplex. -/
theorem regDirichletIntegral_normalization (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    ∫ u in stdSimplex ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure =
    1 / Gamma (∑ i, b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [regDirichletDensity, stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      have hbpos (i : ι) : 0 < (b i).re := by
        simpa [mvBetaConvergent] using hb i
      have hgamma (i : ι) : Gamma (b i) ≠ 0 := Gamma_ne_zero_of_re_pos (hbpos i)
      have hprod_gamma : (∏ i, Gamma (b i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hgamma i)
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hfun :
          regDirichletDensity b =ᵐ[stdSimplexMeasure.restrict (stdSimplex ℝ ι)]
            fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) / ∏ i, Gamma (b i) := by
        have hmem := self_mem_ae_restrict
          (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
        filter_upwards [hmem, hae] with u hu hupos
        rw [regDirichletDensity, Set.indicator_of_mem]
        · rw [Finset.prod_div_distrib]
        · exact ⟨hu, hupos⟩
      rw [integral_congr_ae hfun, integral_div, ← mvBeta_eq_integral hb]
      rw [mvBeta]
      field_simp

/-- Continuous functions are integrable over the standard simplex with respect to the
regularized Dirichlet density. -/
theorem integrableOn_regDirichletDensity_mul
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn
      (fun u => regDirichletDensity b u * f u)
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      rw [stdSimplexMeasure_empty]
      simpa [IntegrableOn] using
        (integrable_zero_measure (f := fun u => regDirichletDensity b u * f u))
  | inr hι =>
    let _ := hι
    let K := stdSimplex ℝ ι
    obtain ⟨C, hC⟩ := bddAbove_def.mp
      ((isCompact_stdSimplex ℝ ι).bddAbove_image hf.norm)
    have hf_le : ∀ u ∈ K, ‖f u‖ ≤ max C 0 := by
      intro u hu
      exact (hC _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    have hmono := integrableOn_complexDirichletMonomial b hb
    have hgamma : IntegrableOn
        (fun u : ι → ℝ ↦ (max C 0 / ∏ i, ‖Gamma (b i)‖) *
          ‖∏ i, (u i : ℂ) ^ (b i - 1)‖) K stdSimplexMeasure :=
      hmono.norm.const_mul _
    apply Integrable.mono hgamma
    · exact (measurable_regDirichletDensity b).aestronglyMeasurable.mul
        (hf.aestronglyMeasurable (isClosed_stdSimplex ℝ ι).measurableSet)
    · filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
          (isClosed_stdSimplex ℝ ι).measurableSet,
          ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
      have hinter : u ∈ stdSimplexInterior := ⟨hu, hupos⟩
      simp only [regDirichletDensity, Set.indicator_of_mem hinter, norm_mul, norm_prod,
        norm_div]
      have hden_pos : 0 < ∏ i, ‖Gamma (b i)‖ := Finset.prod_pos fun i _ ↦
        norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (hb i))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0),
        abs_of_nonneg (norm_nonneg _)]
      calc
        (∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ / ‖Gamma (b i)‖) * ‖f u‖ =
            ‖f u‖ / (∏ i, ‖Gamma (b i)‖) *
              ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ := by
          rw [Finset.prod_div_distrib]
          field_simp
        _ ≤ (max C 0 / ∏ i, ‖Gamma (b i)‖) *
              ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ := by
          gcongr
          exact hf_le u hu

/-- Integration of function `f` over the standard simplex with respect to the regularized
Dirichlet density. -/
def regDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in stdSimplex ℝ ι, regDirichletDensity b u * f u
    ∂stdSimplexMeasure

/-- `regDirichletIntegral` is additive. -/
theorem regDirichletIntegral_add (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hg : ContinuousOn g (stdSimplex ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => f u + g u) =
    regDirichletIntegral b f + regDirichletIntegral b g := by
  unfold regDirichletIntegral
  rw [← integral_add
    (integrableOn_regDirichletDensity_mul b hb hf)
    (integrableOn_regDirichletDensity_mul b hb hg)]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- `regDirichletIntegral` commutes with complex scalar multiplication. -/
theorem regDirichletIntegral_smul (b : ι → ℂ) (f : (ι → ℝ) → ℂ) (c : ℂ)
    : regDirichletIntegral b (fun u => c * f u) =
    c * regDirichletIntegral b f := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- The integral of `f` depends only on the values of `f` on the standard Simplex. -/
theorem regDirichletIntegral_congr
    (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    regDirichletIntegral b f =
      regDirichletIntegral b g := by
  unfold regDirichletIntegral
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [hfg hu]

/-- If `f` is continuous on the closed standard simplex, then
`b ↦ regDirichletIntegral b f` is analytic on the domain of absolute convergence. -/
theorem regDirichletIntegral_analyticOn {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    AnalyticOn ℂ (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  sorry

end ProbabilityTheory

end ComplexDirichlet
