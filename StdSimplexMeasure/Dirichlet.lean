/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Beta
import StdSimplexMeasure.Integral

/-!
# Real normalized Dirichlet measure on the standard simplex

The multivariate Dirichlet measure [KBJ00, Ch 49] is defined on the standard simplex in
symmetric variables, i.e. `stdSimplex ℝ ι`, or $E^{k-1}$ embedded in $ℝ^k$ where
`k = card ι`.

The construction uses the standard-simplex coordinate measure and integral API exported by
`StdSimplexMeasure.Measure` and `StdSimplexMeasure.Integral`. The coordinate constructions are
provided transitively by `StdSimplexMeasure.Coordinates`.

## Main definitions and results

## References

[KBJ00] Kotz, Samuel, Narayanaswamy Balakrishnan, and Norman L. Johnson. "Continuous
multivariate distributions, Volume 1: Models and applications." John Wiley & Sons, 2000.
Online: https://dx.doi.org/10.1002/0471722065.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The multivariate real Beta function. -/
noncomputable def mvRealBeta (b : ι → ℝ) : ℝ :=
  (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- Domain for `b` where the Beta function is defined as an integral. -/
def mvRealBetaDomain : Set (ι → ℝ) :=
  {b | ∀ i, 0 < b i}

/-- `mvRealBeta` is positive on `mvRealBetaDomain`. -/
theorem mvRealBeta_pos [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    0 < mvRealBeta b := by
  refine div_pos (Finset.prod_pos fun i _ => Gamma_pos_of_pos (hb i)) ?_
  exact Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty)

/-- Scaling the free coordinates in a simplex slice separates a Dirichlet monomial into its
distinguished-coordinate factor, radial factor, and lower-dimensional monomial. -/
private theorem prod_rpow_stdSimplexCoordMap_scale
    (i : ι) (b : ι → ℝ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
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

/-- The real Euler beta kernel is integrable on the closed unit interval. -/
private theorem integrableOn_Icc_rpow_mul_one_sub_rpow
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (c - 1)) (Set.Icc 0 1) := by
  have hcomplex := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (c : ℂ))
    (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hcomplex
  have hre : IntegrableOn
      (fun t : ℝ => Complex.reCLM
        ((t : ℂ) ^ ((a : ℂ) - 1) * (1 - (t : ℂ)) ^ ((c : ℂ) - 1)))
      (Set.Ioc 0 1) := Complex.reCLM.integrable_comp hcomplex
  refine (IntegrableOn.congr_fun hre ?_ measurableSet_Ioc).congr_set_ae Ioc_ae_eq_Icc.symm
  intro t ht
  change (Complex.re
    ((t : ℂ) ^ ((a : ℂ) - 1) * (1 - (t : ℂ)) ^ ((c : ℂ) - 1))) = _
  have ha_cast : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by norm_num
  have hc_cast : (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) := by norm_num
  have ht_cast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by norm_num
  rw [ha_cast, hc_cast, ht_cast, ← Complex.ofReal_cpow (le_of_lt ht.1),
    ← Complex.ofReal_cpow (by linarith [ht.2])]
  simp

/-- The real Euler beta integral in set-integral form. -/
private theorem integral_Icc_rpow_mul_one_sub_rpow
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ t in Set.Icc (0 : ℝ) 1, t ^ (a - 1) * (1 - t) ^ (c - 1) = beta a c := by
  have hbeta :
      (↑(∫ t in Set.Icc (0 : ℝ) 1,
        t ^ (a - 1) * (1 - t) ^ (c - 1)) : ℂ) =
        Complex.betaIntegral (a : ℂ) (c : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc]
    have hcast :
        (∫ t in Set.Ioc (0 : ℝ) 1,
          (↑(t ^ (a - 1) * (1 - t) ^ (c - 1)) : ℂ)) =
          ↑(∫ t in Set.Ioc (0 : ℝ) 1,
            t ^ (a - 1) * (1 - t) ^ (c - 1)) := integral_ofReal
    rw [← hcast]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    have ha_cast : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by norm_num
    have hc_cast : (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) := by norm_num
    have ht_cast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by norm_num
    rw [ha_cast, hc_cast, ht_cast, ← Complex.ofReal_cpow (le_of_lt ht.1),
      ← Complex.ofReal_cpow (by linarith [ht.2])]
    norm_cast
  apply Complex.ofReal_injective
  rw [hbeta, Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (c : ℂ) (by simpa) (by simpa)]
  simp [beta, ← Complex.Gamma_ofReal]

/-- The nonnegative Dirichlet monomial integral, used to establish integrability before passing
to the Bochner integral. -/
private theorem lintegral_dirichletMonomial_eq_mvRealBeta {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ∫⁻ u in stdSimplex ℝ ι, ENNReal.ofReal (∏ i, u i ^ (b i - 1)) ∂stdSimplexMeasure =
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
              let : Unique ι :=
                ⟨⟨Classical.choice hι⟩, fun a => hsub.elim _ _⟩
              rw [stdSimplexMeasure_unique, MeasureTheory.setLIntegral_dirac]
              have hG : Gamma (b default) ≠ 0 := ne_of_gt (Gamma_pos_of_pos (hb default))
              simp [mvRealBeta, hG, stdSimplex]
          | inr hnontrivial =>
              let _ := hnontrivial
              let i : ι := Classical.choice hι
              let b' : {j : ι // j ≠ i} → ℝ := fun j => b j
              have hb' : b' ∈ mvRealBetaDomain := fun j => hb j
              have hcard : Fintype.card {j : ι // j ≠ i} < n := by
                rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                exact Nat.sub_one_lt (Fintype.card_pos_iff.mpr hι).ne'
              have hih := ih _ hcard (ι := {j : ι // j ≠ i}) hb'
              rw [lintegral_stdSimplex_split_at i _ (by fun_prop)]
              have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
                  (∫⁻ v in stdSimplex ℝ {j : ι // j ≠ i},
                    ENNReal.ofReal
                      (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                        (b k - 1)) ∂stdSimplexMeasure) =
                    ENNReal.ofReal
                      (t ^ (b i - 1) *
                        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ENNReal.ofReal (mvRealBeta b') := by
                intro t ht
                calc
                  _ = ∫⁻ v in stdSimplex ℝ {j : ι // j ≠ i},
                      ENNReal.ofReal
                        ((t ^ (b i - 1) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                            ∏ q : {j : ι // j ≠ i}, v q ^ (b q - 1))
                          ∂stdSimplexMeasure := by
                        apply setLIntegral_congr_fun (isClosed_stdSimplex ℝ _).measurableSet
                        intro v hv
                        change ENNReal.ofReal
                          (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                            (b k - 1)) = _
                        rw [prod_rpow_stdSimplexCoordMap_scale i b ht hv]
                  _ = ENNReal.ofReal
                        (t ^ (b i - 1) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ∫⁻ v in stdSimplex ℝ {j : ι // j ≠ i},
                        ENNReal.ofReal (∏ q, v q ^ (b q - 1))
                          ∂stdSimplexMeasure := by
                        rw [← lintegral_const_mul]
                        · apply lintegral_congr
                          intro v
                          rw [← ENNReal.ofReal_mul (mul_nonneg
                            (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _))]
                        · fun_prop
                  _ = _ := by rw [hih rfl]
              have hrest_nonempty : Nonempty {j : ι // j ≠ i} := by
                obtain ⟨j, hji⟩ := exists_ne i
                exact ⟨⟨j, hji⟩⟩
              let c : ℝ := ∑ q : {j : ι // j ≠ i}, b q
              have hc : 0 < c := Finset.sum_pos (fun q _ => hb q) Finset.univ_nonempty
              have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
                  ENNReal.ofReal ((1 - t) ^ (Fintype.card ι - 2)) *
                      (∫⁻ v in stdSimplex ℝ {j : ι // j ≠ i},
                        ENNReal.ofReal
                          (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                            (b k - 1)) ∂stdSimplexMeasure) =
                    ENNReal.ofReal (t ^ (b i - 1) * (1 - t) ^ (c - 1)) *
                      ENNReal.ofReal (mvRealBeta b') := by
                filter_upwards [ae_restrict_of_ae
                    (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
                  ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
                have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
                rw [hinner t ht]
                have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
                  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
                have hexp : (Fintype.card ι - 2 : ℝ) +
                    (∑ q : {j : ι // j ≠ i}, (b q - 1)) = c - 1 := by
                  have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℝ) =
                      (Fintype.card ι : ℝ) - 1 := by
                    rw [hcard_rest, Nat.cast_sub (by omega)]
                    norm_num
                  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                    nsmul_eq_mul, mul_one, c]
                  rw [hcast_rest]
                  ring
                have hcast_d : ((Fintype.card ι - 2 : ℕ) : ℝ) =
                    (Fintype.card ι : ℝ) - 2 := by
                  rw [Nat.cast_sub hcard_two]
                  norm_num
                rw [← mul_assoc,
                  ← ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr ht.2.le) _)]
                congr 1
                apply congrArg ENNReal.ofReal
                calc
                  (1 - t) ^ (Fintype.card ι - 2) *
                      (t ^ (b i - 1) *
                        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) =
                      t ^ (b i - 1) *
                        ((1 - t) ^ (Fintype.card ι - 2) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by ring
                  _ = t ^ (b i - 1) *
                      (1 - t) ^ ((Fintype.card ι - 2 : ℕ) +
                        (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by
                        rw [← Real.rpow_natCast,
                          ← Real.rpow_add (sub_pos.mpr ht.2)]
                  _ = _ := by rw [hcast_d, hexp]
              rw [lintegral_congr_ae houter]
              simp_rw [mul_comm _ (ENNReal.ofReal (mvRealBeta b'))]
              rw [lintegral_const_mul' (ENNReal.ofReal (mvRealBeta b')) _ ENNReal.ofReal_ne_top]
              rw [← ofReal_integral_eq_lintegral_ofReal
                (integrableOn_Icc_rpow_mul_one_sub_rpow (hb i) hc)]
              · rw [integral_Icc_rpow_mul_one_sub_rpow (hb i) hc]
                rw [mul_comm, ← ENNReal.ofReal_mul (le_of_lt (beta_pos (hb i) hc))]
                congr 1
                dsimp only [mvRealBeta, b', c]
                rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
                  Fintype.sum_eq_add_sum_subtype_ne b i]
                rw [beta]
                have hGc : Gamma (∑ q : {j : ι // j ≠ i}, b q) ≠ 0 :=
                  ne_of_gt (Gamma_pos_of_pos hc)
                field_simp
              · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
                exact mul_nonneg (Real.rpow_nonneg ht.1 _)
                  (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- The integral representation of `mvRealBeta`. -/
theorem mvRealBeta_eq_integral {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    mvRealBeta b =
      ∫ u in stdSimplex ℝ ι, ∏ i, u i ^ (b i - 1) ∂stdSimplexMeasure := by
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
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu.1 j) _
  · let g : (ι → ℝ) → ℝ := fun u =>
      ∏ i, ((ENNReal.ofReal (u i)) ^ (b i - 1)).toReal
    have hg : AEStronglyMeasurable g
        (stdSimplexMeasure.restrict (stdSimplex ℝ ι)) := by
      apply Measurable.aestronglyMeasurable
      dsimp only [g]
      fun_prop
    refine hg.congr ?_
    filter_upwards [ae_restrict_mem (μ := stdSimplexMeasure)
        (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    apply Finset.prod_congr rfl
    intro i _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (hu.1 i)]

/-- The interior of `stdSimplex ℝ ι` relative to its affine hull. -/
def stdSimplexInterior : Set (ι → ℝ) :=
  {u | u ∈ stdSimplex ℝ ι ∧ ∀ i, 0 < u i}

/-- The real-valued Dirichlet PDF with parameters `b`. This PDF is supported on
`stdSimplexInterior ι`. -/
def dirichletPdfReal (b : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / mvRealBeta b) *
    stdSimplexInterior.indicator (fun u ↦ ∏ i, u i ^ (b i - 1)) u

/-- The `ENNReal`-valued Dirichlet PDF. -/
def dirichletPdf (b : ι → ℝ) (u : ι → ℝ) : ENNReal :=
  ENNReal.ofReal (dirichletPdfReal b u)

/-- The Dirichlet measure on the standard simplex. -/
def dirichletMeasure
    (b : ι → ℝ) : Measure (ι → ℝ) :=
  stdSimplexMeasure.withDensity (dirichletPdf b)

/-- The `stdSimplexInterior` is a measurable set. -/
theorem measurableSet_stdSimplexInterior :
    MeasurableSet (stdSimplexInterior (ι := ι)) := by
  have hpos : IsOpen {u : ι → ℝ | ∀ i, 0 < u i} := by
    rw [show {u : ι → ℝ | ∀ i, 0 < u i} =
        ⋂ i, {u : ι → ℝ | 0 < u i} by
      ext u
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)
  change MeasurableSet (stdSimplex ℝ ι ∩ {u : ι → ℝ | ∀ i, 0 < u i})
  exact (isClosed_stdSimplex ℝ ι).measurableSet.inter hpos.measurableSet

/-- The real-valued Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdfReal (b : ι → ℝ) :
    Measurable (dirichletPdfReal b) := by
  unfold dirichletPdfReal
  exact measurable_const.mul
    ((by
      fun_prop :
      Measurable (fun u : ι → ℝ => ∏ i, u i ^ (b i - 1))).indicator
        (measurableSet_stdSimplexInterior (ι := ι)))

/-- The (ENNReal) Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdf (b : ι → ℝ) :
    Measurable (dirichletPdf b) := by
  exact ENNReal.measurable_ofReal.comp
    (measurable_dirichletPdfReal b)

/-- `stdSimplexMeasure` is a `SigmaFinite` measure. -/
instance :
    SigmaFinite (stdSimplexMeasure (ι := ι)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      rw [stdSimplexMeasure_empty]
      infer_instance
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.sigmaFinite_map

/-- The Radon-Nikodym derivative of the Dirichlet measure is almost everywhere
equal to the Dirichlet PDF. -/
theorem rnDeriv_dirichletMeasure {b : ι → ℝ} (_ : b ∈ mvRealBetaDomain) :
    (dirichletMeasure b).rnDeriv stdSimplexMeasure =ᵐ[stdSimplexMeasure]
      dirichletPdf b := by
  rw [dirichletMeasure]
  exact Measure.rnDeriv_withDensity _ (measurable_dirichletPdf b)

/-- The real-valued Dirichlet density is nonnegative. -/
theorem dirichletPdfReal_nonneg [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (u : ι → ℝ) :
    0 ≤ dirichletPdfReal b u := by
  unfold dirichletPdfReal
  refine mul_nonneg
    (le_of_lt (one_div_pos.mpr (mvRealBeta_pos hb))) ?_
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu]
    exact Finset.prod_nonneg fun i _ =>
      (rpow_pos_of_pos (hu.2 i) _).le
  · simp [Set.indicator_of_notMem hu]

/-- Unwraps an integral against the Dirichlet measure into an integral against the
standard simplex measure, explicitly multiplying the function by the Dirichlet density. -/
theorem integral_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (f : (ι → ℝ) → ℝ) :
    ∫ u, f u ∂(dirichletMeasure b) =
      ∫ u in stdSimplex ℝ ι,
        f u * dirichletPdfReal b u ∂stdSimplexMeasure := by
  rw [dirichletMeasure]
  have hlt :
      ∀ᵐ u ∂stdSimplexMeasure, dirichletPdf b u < ⊤ := by
    filter_upwards with u
    simp [dirichletPdf]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_dirichletPdf b) hlt f]
  rw [← integral_indicator
    (isClosed_stdSimplex ℝ ι).measurableSet]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ stdSimplex ℝ ι
  · have hnonneg := dirichletPdfReal_nonneg hb u
    simp [hu, dirichletPdf,
      ENNReal.toReal_ofReal hnonneg, mul_comm]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- The measure of the standard simplex under the Dirichlet measure equals 1. -/
theorem dirichletMeasure_stdSimplex
    [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    dirichletMeasure b (stdSimplex ℝ ι) = 1 := by
  let p : (ι → ℝ) → ℝ := fun u => ∏ i, u i ^ (b i - 1)
  have hp_int : IntegrableOn p (stdSimplex ℝ ι) stdSimplexMeasure := by
    apply Integrable.of_integral_ne_zero
    rw [← mvRealBeta_eq_integral hb]
    exact ne_of_gt (mvRealBeta_pos hb)
  have hd_int : IntegrableOn (dirichletPdfReal b) (stdSimplex ℝ ι)
      stdSimplexMeasure := by
    apply hp_int.const_mul (1 / mvRealBeta b) |>.congr
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
    filter_upwards [hmem, hae] with u hu hpos
    simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
  have hd_integral :
      ∫ u in stdSimplex ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure = 1 := by
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
    calc
      ∫ u in stdSimplex ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure =
          ∫ u in stdSimplex ℝ ι, (1 / mvRealBeta b) * p u ∂stdSimplexMeasure := by
            apply integral_congr_ae
            filter_upwards [hmem, hae] with u hu hpos
            simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
      _ = (1 / mvRealBeta b) * ∫ u in stdSimplex ℝ ι, p u ∂stdSimplexMeasure := by
        rw [MeasureTheory.integral_const_mul]
      _ = 1 := by
        rw [← mvRealBeta_eq_integral hb]
        field_simp [ne_of_gt (mvRealBeta_pos hb)]
  unfold dirichletMeasure
  rw [withDensity_apply _ (isClosed_stdSimplex ℝ ι).measurableSet]
  unfold dirichletPdf
  rw [← ofReal_integral_eq_lintegral_ofReal hd_int]
  · rw [hd_integral]
    simp
  · filter_upwards with u
    exact dirichletPdfReal_nonneg hb u

/-- The Dirichlet density vanishes outside `stdSimplex ℝ ι`. -/
theorem dirichletPdf_eq_zero_of_not_mem_stdSimplex
    (b : ι → ℝ) {u : ι → ℝ} (hu : u ∉ stdSimplex ℝ ι) :
    dirichletPdf b u = 0 := by
  simp [dirichletPdf, dirichletPdfReal, stdSimplexInterior, hu]

/-- The Dirichlet measure is restricted to the standard simplex. -/
theorem dirichletMeasure_restrict (b : ι → ℝ) :
    (dirichletMeasure b).restrict (stdSimplex ℝ ι) =
      dirichletMeasure b := by
  unfold dirichletMeasure
  rw [restrict_withDensity
    (isClosed_stdSimplex ℝ ι).measurableSet]
  rw [← withDensity_indicator
    (isClosed_stdSimplex ℝ ι).measurableSet]
  apply withDensity_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ stdSimplex ℝ ι
  · simp [hu]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- The Dirichlet measure satisfies `isProbabilityMeasure`. -/
theorem isProbabilityMeasure_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    IsProbabilityMeasure (dirichletMeasure b) := by
  refine ⟨?_⟩
  rw [← dirichletMeasure_restrict b]
  rw [Measure.restrict_apply_univ]
  exact dirichletMeasure_stdSimplex hb

/-- The total mass / integral of the constant function 1 with respect to the Dirichlet
measure is 1. -/
theorem integral_dirichletMeasure_one [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    ∫ _, (1 : ℝ) ∂(dirichletMeasure b) = 1 := by
  let : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure hb
  simp

/-- The Dirichlet measure is absolutely continuous with respect to `stdSimplexMeasure`. -/
theorem absolutelyContinuous_dirichletMeasure (b : ι → ℝ) :
    dirichletMeasure b ≪ stdSimplexMeasure :=
  withDensity_absolutelyContinuous _ _

/-- Defining the Dirichlet measure for the case of all `b` parameters equal. -/
def dirichletMeasureUniform (α : ℝ) : Measure (ι → ℝ) :=
  dirichletMeasure (fun _ => α)

/-- The case of all `b` parameters equal to 1 reduces to scaled Lebesgue measure. -/
theorem dirichletMeasureUniform_one :
    dirichletMeasureUniform (ι := ι) 1 =
      (1 / stdSimplexMeasure (stdSimplex ℝ ι)) •
      stdSimplexMeasure.restrict (stdSimplex ℝ ι) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let : IsEmpty ι := hι
      simp [dirichletMeasureUniform, dirichletMeasure, stdSimplexMeasure_empty]
  | inr hι =>
      let : Nonempty ι := hι
      let b : ι → ℝ := fun _ => 1
      have hb : b ∈ mvRealBetaDomain := by simp [b, mvRealBetaDomain]
      have hs := (isClosed_stdSimplex ℝ ι).measurableSet
      rw [show dirichletMeasureUniform (ι := ι) 1 = dirichletMeasure b by rfl]
      rw [← dirichletMeasure_restrict b]
      unfold dirichletMeasure
      rw [restrict_withDensity hs]
      have hd : dirichletPdf b =ᵐ[stdSimplexMeasure.restrict (stdSimplex ℝ ι)]
          fun _ => ENNReal.ofReal (1 / mvRealBeta b) := by
        have hmem := self_mem_ae_restrict (μ := stdSimplexMeasure) hs
        have hpos := ae_zero_lt_of_mem_stdSimplex (ι := ι)
        filter_upwards [hmem, hpos] with u hu hupos
        simp [dirichletPdf, dirichletPdfReal, stdSimplexInterior, hu, hupos, b]
      rw [withDensity_congr_ae hd, withDensity_const]
      congr 1
      rw [stdSimplexMeasure_stdSimplex]
      unfold mvRealBeta
      have hcpos : 0 < Fintype.card ι := Fintype.card_pos
      have hgamma : 0 < Gamma (Fintype.card ι : ℝ) :=
        Gamma_pos_of_pos (by exact_mod_cast hcpos)
      simp only [b, Finset.prod_const_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Gamma_one]
      have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
      rw [show (Fintype.card ι : ℝ) = ((Fintype.card ι - 1 : ℕ) : ℝ) + 1 by
        exact_mod_cast hcard]
      rw [Gamma_nat_eq_factorial]
      simp

/-- Simultaneously permuting the parameters and coordinates leaves the Dirichlet density
unchanged. -/
theorem dirichletPdf_perm (b : ι → ℝ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    dirichletPdf (b ∘ σ) (u ∘ σ) = dirichletPdf b u := by
  unfold dirichletPdf dirichletPdfReal
  have hbeta : mvRealBeta (b ∘ σ) = mvRealBeta b := by
    unfold mvRealBeta
    simp only [Function.comp_apply, Equiv.sum_comp]
    congr 1
    exact Equiv.prod_comp σ (fun i => Gamma (b i))
  have hinter : (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
    have hsimp : (u ∘ σ) ∈ stdSimplex ℝ ι ↔ u ∈ stdSimplex ℝ ι := by
      change u ∈ (fun v => v ∘ σ) ⁻¹' stdSimplex ℝ ι ↔ _
      rw [preimage_stdSimplex_perm]
    simp only [stdSimplexInterior]
    constructor
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mp hu, fun i => by simpa using hp (σ.symm i)⟩
    · rintro ⟨hu, hp⟩
      exact ⟨hsimp.mpr hu, fun i => hp (σ i)⟩
  rw [hbeta]
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    congr 2
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ (fun i => u i ^ (b i - 1)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- Permuting coordinates together with parameters is a measure-preserving transformation of
`dirichletMeasure`. -/
theorem measurePreserving_dirichletMeasure_perm (b : ι → ℝ) (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    (dirichletMeasure b) (dirichletMeasure (b ∘ σ)) := by
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun x := x ∘ σ
    invFun x := x ∘ σ.symm
    left_inv x := by funext i; simp
    right_inv x := by funext i; simp
    measurable_toFun := continuous_pi (fun i => continuous_apply (σ i)) |>.measurable
    measurable_invFun := continuous_pi (fun i => continuous_apply (σ.symm i)) |>.measurable
  }
  have hg : MeasurePreserving g stdSimplexMeasure stdSimplexMeasure := by
    simpa [g] using measurePreserving_stdSimplexMeasure_perm σ
  refine ⟨g.measurable, ?_⟩
  change Measure.map g (dirichletMeasure b) = dirichletMeasure (b ∘ σ)
  unfold dirichletMeasure
  ext s hs
  rw [Measure.map_apply g.measurable hs]
  rw [withDensity_apply _ (g.measurable hs), withDensity_apply _ hs]
  have hchange := hg.setLIntegral_comp_preimage hs (measurable_dirichletPdf (b ∘ σ))
  rw [← hchange]
  apply setLIntegral_congr_fun (g.measurable hs)
  intro x hx
  exact (dirichletPdf_perm b σ x).symm

/-- Dirichlet measure is closed under marginalisation or coarsening: pushing
`dirichletMeasure b` forward along `stdSimplexAggregate f` gives the Dirichlet
measure for the aggregated parameter vector. -/
theorem measurePreserving_stdSimplexAggregate_dirichletMeasure
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    MeasurePreserving (stdSimplexAggregate f)
      (dirichletMeasure b) (dirichletMeasure (stdSimplexAggregate f b)) := by
  sorry

/-- Coordinate aggregation restated via the explicit density, unfolding
`measurePreserving_stdSimplexAggregate_dirichletMeasure` in terms of `stdSimplexMeasure` and
`dirichletPdf` directly rather than the bundled `dirichletMeasure`. -/
theorem stdSimplexAggregate_withDensity
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    Measure.map (stdSimplexAggregate f)
      (stdSimplexMeasure.withDensity (fun u ↦ ENNReal.ofReal (dirichletPdfReal b u))) =
      stdSimplexMeasure.withDensity
        (fun v ↦ ENNReal.ofReal (dirichletPdfReal (stdSimplexAggregate f b) v)) :=
  (measurePreserving_stdSimplexAggregate_dirichletMeasure hf hb).map_eq

/-- The integral of a power product (generalized monomial) against the Dirichlet measure. -/
theorem integral_dirichletMeasure_power_product {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℝ) (hm : b + m ∈ mvRealBetaDomain) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (Gamma (∑ i, b i) / Gamma (∑ i, (b i + m i))) *
        ∏ i, (Gamma (b i + m i) / Gamma (b i)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp [dirichletMeasure, stdSimplexMeasure_empty]
  | inr h =>
      let : Nonempty ι := h
      rw [integral_dirichletMeasure hb]
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
      have hint :
          (∫ u in stdSimplex ℝ ι,
            (∏ i, u i ^ m i) * dirichletPdfReal b u ∂stdSimplexMeasure) =
          (1 / mvRealBeta b) *
            ∫ u in stdSimplex ℝ ι, ∏ i, u i ^ ((b + m) i - 1)
              ∂stdSimplexMeasure := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hmem, hae] with u hu hpos
        have hui : u ∈ stdSimplexInterior := ⟨hu, hpos⟩
        rw [dirichletPdfReal, Set.indicator_of_mem hui]
        rw [show (∏ i, u i ^ m i) * ((1 / mvRealBeta b) * ∏ i, u i ^ (b i - 1)) =
          (1 / mvRealBeta b) * ((∏ i, u i ^ m i) * ∏ i, u i ^ (b i - 1)) by ring]
        rw [← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          u i ^ m i * u i ^ (b i - 1) = u i ^ (m i + (b i - 1)) :=
            (rpow_add (hpos i) (m i) (b i - 1)).symm
          _ = u i ^ ((b + m) i - 1) := by
            congr 1
            simp only [Pi.add_apply]
            ring
      rw [hint, ← mvRealBeta_eq_integral hm]
      unfold mvRealBeta
      simp only [Pi.add_apply]
      have hb_sum : Gamma (∑ i, b i) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty))
      have hm_sum : Gamma (∑ i, (b i + m i)) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos
          (Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty))
      have hb_each : ∀ i, Gamma (b i) ≠ 0 := fun i =>
        ne_of_gt (Gamma_pos_of_pos (hb i))
      rw [Finset.prod_div_distrib]
      field_simp

/-- A quotient of gamma values separated by a natural number equals the corresponding rising
factorial. -/
theorem gamma_add_nat_div_gamma_eq_ascPochhammer
    (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) / Gamma x = (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [ne_of_gt (Gamma_pos_of_pos hx)]
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show x + ((n : ℝ) + 1) = (x + n) + 1 by ring]
      rw [Gamma_add_one (by positivity : x + (n : ℝ) ≠ 0)]
      rw [ascPochhammer_succ_eval]
      rw [mul_div_assoc, ih]
      ring

/-- The integral of a monomial against the Dirichlet measure. -/
/- The `[Nonempty ι]` hypothesis is essential.  For an empty index type the left side is
zero, while the empty products and the degree-zero rising factorial make the right side one. -/
theorem integral_dirichletMeasure_monomial [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℕ) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (∏ i, (ascPochhammer ℝ (m i)).eval (b i)) /
        (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) := by
  let mr : ι → ℝ := fun i => m i
  have hm : b + mr ∈ mvRealBetaDomain := by
    intro i
    exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)
  have hpow := integral_dirichletMeasure_power_product hb mr hm
  have hfun : (fun u : ι → ℝ => ∏ i, u i ^ mr i) = fun u => ∏ i, u i ^ m i := by
    funext u
    simp [mr, rpow_natCast]
  rw [hfun] at hpow
  rw [hpow]
  have hsum_pos : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hsum : (∑ i, (b i + mr i)) = (∑ i, b i) + (∑ i, m i) := by
    simp [mr, Finset.sum_add_distrib]
  rw [hsum]
  have hnum : Gamma ((∑ i, b i) + (∑ i, m i)) / Gamma (∑ i, b i) =
      (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) :=
    gamma_add_nat_div_gamma_eq_ascPochhammer _ hsum_pos _
  have hprod : ∏ i, (Gamma (b i + mr i) / Gamma (b i)) =
      ∏ i, (ascPochhammer ℝ (m i)).eval (b i) := by
    apply Finset.prod_congr rfl
    intro i _
    simpa [mr] using gamma_add_nat_div_gamma_eq_ascPochhammer (b i) (hb i) (m i)
  rw [hprod]
  have hG : Gamma (∑ i, b i) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hGN : Gamma ((∑ i, b i) + (∑ i, m i)) ≠ 0 := by
    apply ne_of_gt (Gamma_pos_of_pos ?_)
    have hm_nonneg : (0 : ℝ) ≤ ∑ i, m i := by positivity
    linarith
  have hP : (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) ≠ 0 := by
    rw [← hnum]
    exact div_ne_zero hGN hG
  have hratio : Gamma (∑ i, b i) / Gamma ((∑ i, b i) + (∑ i, m i)) =
      ((ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i))⁻¹ := by
    rw [← hnum]
    field_simp
  rw [hratio, div_eq_mul_inv, mul_comm]

/-- The mean of a single `u i`; a specialization of monomial integration. -/
theorem integral_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ∂(dirichletMeasure b) = (b i) / (∑ j, b j) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℝ := fun j => if j = i then 1 else 0
  have hm : b + m ∈ mvRealBetaDomain := by
    intro j
    dsimp [m]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (hb j) zero_le_one
    · simpa using hb j
  have hpow := integral_dirichletMeasure_power_product hb m hm
  have hsum_pos : 0 < ∑ j, b j :=
    Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hgamma_sum : Gamma (∑ j, b j) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i := by
    funext u
    simp [m]
  rw [hprod] at hpow
  have hsum_m : ∑ j, (b j + m j) = (∑ j, b j) + 1 := by
    simp [m, Finset.sum_add_distrib]
  have hprod_m : ∏ j, (Gamma (b j + m j) / Gamma (b j)) = b i := by
    calc
      ∏ j, (Gamma (b j + m j) / Gamma (b j)) =
          ∏ j, if j = i then b i else 1 := by
            apply Finset.prod_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp [m, Gamma_add_one, (hb i).ne',
                ne_of_gt (Gamma_pos_of_pos (hb i))]
            · simp [m, hji, ne_of_gt (Gamma_pos_of_pos (hb j))]
      _ = b i := by simp
  rw [hpow, hsum_m, hprod_m, Gamma_add_one hsum_pos.ne']
  field_simp

/-- The second raw moment of one coordinate under a Dirichlet measure. -/
theorem integral_dirichletMeasure_coordinate_sq
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ^ 2 ∂(dirichletMeasure b) =
      b i * (b i + 1) / ((∑ j, b j) * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun j => if j = i then 2 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i ^ 2 := by
    funext u
    simp [m]
  rw [hprod] at h
  rw [h]
  have hnum : ∏ j, (ascPochhammer ℝ (m j)).eval (b j) = b i * (b i + 1) := by
    calc
      _ = ∏ j, if j = i then b i * (b i + 1) else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [m, ascPochhammer_succ_eval]
        · simp [m, hji]
      _ = _ := by simp
  have hsum : ∑ j, m j = 2 := by simp [m]
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

/-- The mixed raw moment of two distinct coordinates under a Dirichlet measure. -/
theorem integral_dirichletMeasure_two_coordinates
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, u i * u j ∂(dirichletMeasure b) =
      b i * b j / ((∑ k, b k) * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun k => if k = i then 1 else if k = j then 1 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ k, u k ^ m k) = fun u => u i * u j := by
    funext u
    simp only [m, pow_ite, pow_one, pow_zero]
    rw [show (∏ k, if k = i then u k else if k = j then u k else 1) =
        ∏ k, (if k = i then u i else 1) * (if k = j then u j else 1) by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hprod] at h
  rw [h]
  have hnum : ∏ k, (ascPochhammer ℝ (m k)).eval (b k) = b i * b j := by
    calc
      _ = ∏ k, if k = i then b i else if k = j then b j else 1 := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [m]
        · by_cases hkj : k = j
          · subst k
            simp [m, hki]
          · simp [m, hki, hkj]
      _ = ∏ k, (if k = i then b i else 1) * (if k = j then b j else 1) := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp [hki, hkj, hij, hij.symm]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsum : ∑ k, m k = 2 := by
    simp only [m]
    rw [show (∑ k, if k = i then 1 else if k = j then 1 else 0) =
        (∑ k, if k = i then 1 else 0) + ∑ k, (if k = j then 1 else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    simp
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

/-- The variance of the coordinate `u i`. -/
theorem variance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i - b i / ∑ j, b j) ^ 2 ∂(dirichletMeasure b) =
      (b i) * (∑ j, b j - b i) / ((∑ j, b j) ^ 2 * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure hb
  let S := ∑ j, b j
  have hS : 0 < S := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hmean := integral_dirichletMeasure_coordinate hb i
  have hsquare := integral_dirichletMeasure_coordinate_sq hb i
  have hmean_int : Integrable (fun u : ι → ℝ => u i) (dirichletMeasure b) := by
    apply Integrable.of_integral_ne_zero
    rw [hmean]
    exact div_ne_zero (hb i).ne' hS.ne'
  have hsquare_int : Integrable (fun u : ι → ℝ => u i ^ 2) (dirichletMeasure b) := by
    apply Integrable.of_integral_ne_zero
    rw [hsquare]
    exact div_ne_zero
      (mul_ne_zero (hb i).ne' (add_pos_of_pos_of_nonneg (hb i) zero_le_one).ne')
      (mul_ne_zero hS.ne' (add_pos_of_pos_of_nonneg hS zero_le_one).ne')
  have hconst : Integrable (fun _ : ι → ℝ => (b i / S) ^ 2) (dirichletMeasure b) :=
    integrable_const _
  calc
    ∫ u, (u i - b i / ∑ j, b j) ^ 2 ∂(dirichletMeasure b) =
        ∫ u, (u i ^ 2 - (2 * (b i / S)) * u i + (b i / S) ^ 2)
          ∂(dirichletMeasure b) := by
            apply integral_congr_ae
            filter_upwards [] with u
            simp only [S]
            ring
    _ = (∫ u, u i ^ 2 ∂(dirichletMeasure b)) -
        (2 * (b i / S)) * (∫ u, u i ∂(dirichletMeasure b)) + (b i / S) ^ 2 := by
      have heq : (fun u : ι → ℝ => u i ^ 2 - 2 * (b i / S) * u i + (b i / S) ^ 2) =
          (fun u : ι → ℝ => u i ^ 2) - (fun u : ι → ℝ => 2 * (b i / S) * u i) +
            (fun _ : ι → ℝ => (b i / S) ^ 2) := by rfl
      rw [heq]
      rw [integral_add' (hsquare_int.sub (hmean_int.const_mul _)) hconst,
        integral_sub' hsquare_int (hmean_int.const_mul _), integral_const_mul, integral_const]
      simp
    _ = _ := by
      rw [hsquare, hmean]
      dsimp [S] at hS ⊢
      field_simp
      ring

/-- The covariance of distinct coordinates `u i` and `u j`. -/
theorem covariance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, (u i - b i / ∑ k, b k) * (u j - b j / ∑ k, b k)
      ∂(dirichletMeasure b) =
      -(b i) * (b j) / ((∑ k, b k) ^ 2 * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure hb
  let S := ∑ k, b k
  have hS : 0 < S := Finset.sum_pos (fun k _ => hb k) Finset.univ_nonempty
  have hmeani := integral_dirichletMeasure_coordinate hb i
  have hmeanj := integral_dirichletMeasure_coordinate hb j
  have hcross := integral_dirichletMeasure_two_coordinates hb hij
  have hi_int : Integrable (fun u : ι → ℝ => u i) (dirichletMeasure b) := by
    apply Integrable.of_integral_ne_zero
    rw [hmeani]
    exact div_ne_zero (hb i).ne' hS.ne'
  have hj_int : Integrable (fun u : ι → ℝ => u j) (dirichletMeasure b) := by
    apply Integrable.of_integral_ne_zero
    rw [hmeanj]
    exact div_ne_zero (hb j).ne' hS.ne'
  have hcross_int : Integrable (fun u : ι → ℝ => u i * u j) (dirichletMeasure b) := by
    apply Integrable.of_integral_ne_zero
    rw [hcross]
    exact div_ne_zero (mul_ne_zero (hb i).ne' (hb j).ne')
      (mul_ne_zero hS.ne' (add_pos_of_pos_of_nonneg hS zero_le_one).ne')
  have hconst : Integrable (fun _ : ι → ℝ => (b i / S) * (b j / S))
      (dirichletMeasure b) := integrable_const _
  calc
    ∫ u, (u i - b i / ∑ k, b k) * (u j - b j / ∑ k, b k)
        ∂(dirichletMeasure b) =
      ∫ u, u i * u j - (b j / S) * u i - (b i / S) * u j +
        (b i / S) * (b j / S) ∂(dirichletMeasure b) := by
          apply integral_congr_ae
          filter_upwards [] with u
          simp only [S]
          ring
    _ = (∫ u, u i * u j ∂(dirichletMeasure b)) -
        (b j / S) * (∫ u, u i ∂(dirichletMeasure b)) -
        (b i / S) * (∫ u, u j ∂(dirichletMeasure b)) +
        (b i / S) * (b j / S) := by
      have heq : (fun u : ι → ℝ => u i * u j - (b j / S) * u i -
          (b i / S) * u j + (b i / S) * (b j / S)) =
        (((fun u : ι → ℝ => u i * u j) - (fun u : ι → ℝ => (b j / S) * u i)) -
          (fun u : ι → ℝ => (b i / S) * u j)) +
          (fun _ : ι → ℝ => (b i / S) * (b j / S)) := by rfl
      rw [heq]
      rw [integral_add'
          ((hcross_int.sub (hi_int.const_mul _)).sub (hj_int.const_mul _)) hconst,
        integral_sub' (hcross_int.sub (hi_int.const_mul _)) (hj_int.const_mul _),
        integral_sub' hcross_int (hi_int.const_mul _), integral_const_mul,
        integral_const_mul, integral_const]
      simp
    _ = _ := by
      rw [hcross, hmeani, hmeanj]
      dsimp [S] at hS ⊢
      field_simp
      ring

/- Specializations to the two-variable Dirichlet (Beta) density and measure that is defined
in Mathlib `ProbabilityTheory.betaMeasure`. -/

/-- For two parameters, `mvRealBetaDomain` is just positivity of both parameters. -/
@[simp] theorem mem_mvRealBetaDomain_fin_two (α β : ℝ) :
    (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain ↔
      0 < α ∧ 0 < β := by
  simp [mvRealBetaDomain]

/-- In the two-variable case, `mvRealBeta` is the ordinary beta function. -/
@[simp] theorem mvRealBeta_fin_two (α β : ℝ) :
    mvRealBeta (![α, β] : Fin 2 → ℝ) = beta α β := by
  simp [mvRealBeta, beta]

/-- Under `x ↦ ![x, 1 - x]`, the relative interior of the two-coordinate simplex
corresponds to the open unit interval. -/
@[simp] theorem mem_stdSimplexInterior_fin_two (x : ℝ) :
    (![x, 1 - x] : Fin 2 → ℝ) ∈ stdSimplexInterior ↔
      0 < x ∧ x < 1 := by
  constructor
  · intro h
    constructor
    · simpa using h.2 (0 : Fin 2)
    · have h1 : 0 < 1 - x := by
        simpa using h.2 (1 : Fin 2)
      exact sub_pos.mp h1
  · rintro ⟨hx0, hx1⟩
    constructor
    · change
        (∀ i : Fin 2, 0 ≤ (![x, 1 - x] : Fin 2 → ℝ) i) ∧
          ∑ i : Fin 2, (![x, 1 - x] : Fin 2 → ℝ) i = 1
      constructor
      · rw [Fin.forall_fin_two]
        constructor
        · simpa using hx0.le
        · simpa using (sub_pos.mpr hx1).le
      · simp
    · rw [Fin.forall_fin_two]
      constructor
      · simpa using hx0
      · simpa using sub_pos.mpr hx1

/-- The two-variable real Dirichlet density is the beta density under the
parametrization `x ↦ ![x, 1 - x]`. -/
@[simp] theorem dirichletPdfReal_fin_two (α β x : ℝ) :
    dirichletPdfReal (![α, β] : Fin 2 → ℝ) ![x, 1 - x] =
      betaPDFReal α β x := by
  rw [dirichletPdfReal, betaPDFReal, mvRealBeta_fin_two]
  by_cases hx : 0 < x ∧ x < 1
  · simp [hx, mul_assoc]
  · rw [if_neg hx]
    simp [mem_stdSimplexInterior_fin_two, hx]

/-- The two-variable `ENNReal`-valued Dirichlet density is the beta density. -/
@[simp] theorem dirichletPdf_fin_two (α β x : ℝ) :
    dirichletPdf (![α, β] : Fin 2 → ℝ) ![x, 1 - x] = betaPDF α β x := by
  simp [dirichletPdf, betaPDF]

/-- Projection onto the first coordinate sends the coordinate measure on the
two-coordinate affine simplex to Lebesgue measure. -/
private theorem map_stdSimplexMeasure_fin_two :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (stdSimplexMeasure (ι := Fin 2)) = volume := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [stdSimplexMeasure_eq_at (1 : Fin 2)]
  unfold stdSimplexMeasureAt
  rw [Measure.map_map]
  · let A := {j : Fin 2 // j ≠ 1}
    let e : A ≃ Fin 1 :=
      Fintype.equivOfCardEq (by simp [A, Fintype.card_subtype_compl])
    let T := MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm
    have hT : Measure.map T volume = volume :=
      (volume_measurePreserving_piCongrLeft (fun _ : A => ℝ) e.symm).map_eq
    let U := MeasurableEquiv.funUnique (Fin 1) ℝ
    have hU : Measure.map U volume = volume :=
      (volume_preserving_funUnique (Fin 1) ℝ).map_eq
    rw [← hU]
    calc
      Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
          (volume : Measure (A → ℝ)) =
          Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
            (Measure.map T volume) := by rw [hT]
      _ = Measure.map
          (((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1) ∘ T) volume :=
        Measure.map_map
          ((measurable_pi_apply 0).comp (measurable_stdSimplexCoordMap 1)) T.measurable
      _ = Measure.map U volume := by
        congr 1
        funext x
        simp only [Function.comp_apply]
        rw [stdSimplexCoordMap_apply_of_ne (R := ℝ) (1 : Fin 2) (0 : Fin 2) (by omega)]
        have he : (⟨0, by omega⟩ : A) = e.symm (e ⟨0, by omega⟩) := by simp
        rw [he, MeasurableEquiv.piCongrLeft_apply_apply]
        change x (e ⟨0, by omega⟩) = x default
        exact congrArg x (Subsingleton.elim _ _)
  · exact measurable_pi_apply 0
  · exact measurable_stdSimplexCoordMap (1 : Fin 2)

/-- The first-coordinate push-forward of a two-coordinate Dirichlet measure is Mathlib's
beta measure. -/
private theorem map_dirichletMeasure_fin_two_direct (a b : ℝ) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![a, b])) = betaMeasure a b := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply 0) hs]
  rw [dirichletMeasure, withDensity_apply _ ((measurable_pi_apply 0) hs)]
  rw [betaMeasure, withDensity_apply _ hs]
  rw [← map_stdSimplexMeasure_fin_two]
  rw [← lintegral_indicator hs]
  have hpdf : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [lintegral_map (hpdf.indicator hs) (measurable_pi_apply 0)]
  rw [← lintegral_indicator ((measurable_pi_apply 0) hs)]
  apply lintegral_congr_ae
  have hmem : ∀ᵐ u ∂(stdSimplexMeasure (ι := Fin 2)),
      u ∈ stdSimplexAffineSet (R := ℝ) := by
    rw [stdSimplexMeasure_restrict_stdSimplexAffineSet]
    exact self_mem_ae_restrict isClosed_stdSimplexAffineSet.measurableSet
  filter_upwards [hmem] with u hu
  by_cases hus : u ∈ (fun u : Fin 2 → ℝ => u 0) ⁻¹' s
  · simp only [Set.mem_preimage] at hus
    simp [hus]
    have hu1 : u 1 = 1 - u 0 := by
      have hsum : ∑ i, u i = 1 := mem_fintypeAffineCoords_iff_sum.mp hu
      simpa [Fin.sum_univ_two] using congrArg (fun x => x - u 0) hsum
    have huv : u = ![u 0, 1 - u 0] := by
      funext j
      fin_cases j <;> simp [hu1]
    rw [huv]
    exact dirichletPdf_fin_two a b _
  · simp only [Set.mem_preimage] at hus
    simp [hus]

/-- Marginalization of the Dirichlet density with respect to the `i` coordinate. -/
theorem betaMarginal [Nontrivial ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    Measure.map (fun u ↦ u i) (dirichletMeasure b) =
      betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) := by
  classical
  let q : ι → Fin 2 := fun j => if j = i then 0 else 1
  have hq : Function.Surjective q := by
    intro k
    fin_cases k
    · exact ⟨i, by simp [q]⟩
    · obtain ⟨j, hji⟩ := exists_ne i
      exact ⟨j, by simp [q, hji]⟩
  have hcoord (u : ι → ℝ) : stdSimplexAggregate q u 0 = u i := by
    change (FunOnFinite.linearMap ℝ ℝ q) u 0 = u i
    rw [FunOnFinite.linearMap_apply_apply]
    have hfilter : Finset.univ.filter (fun x => q x = (0 : Fin 2)) = {i} := by
      ext j
      simp [q]
    rw [hfilter]
    simp
  have hparam : stdSimplexAggregate q b =
      (![b i, ∑ j ∈ Finset.univ.erase i, b j] : Fin 2 → ℝ) := by
    funext k
    fin_cases k
    · exact hcoord b
    · change (FunOnFinite.linearMap ℝ ℝ q) b 1 = _
      rw [FunOnFinite.linearMap_apply_apply]
      have hfilter : Finset.univ.filter (fun x => q x = (1 : Fin 2)) =
          Finset.univ.erase i := by
        ext j
        simp [q]
      rw [hfilter]
      simp
  have hp := measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb
  calc
    Measure.map (fun u : ι → ℝ => u i) (dirichletMeasure b) =
        Measure.map (fun v : Fin 2 → ℝ => v 0)
          (Measure.map (stdSimplexAggregate q) (dirichletMeasure b)) := by
            rw [Measure.map_map]
            · congr 1
              funext u
              exact (hcoord u).symm
            · exact measurable_pi_apply 0
            · fun_prop
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (stdSimplexAggregate q b)) := by rw [hp.map_eq]
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (![b i, ∑ j ∈ Finset.univ.erase i, b j])) := by rw [hparam]
    _ = betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) :=
      map_dirichletMeasure_fin_two_direct _ _

/-- The push-forward of the two-variable Dirichlet measure under the first
coordinate is the beta measure. -/
theorem map_dirichletMeasure_fin_two
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![α, β])) = betaMeasure α β := by
  have hb : (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain := by
    simpa using And.intro hα hβ
  simpa using
    (betaMarginal (b := (![α, β] : Fin 2 → ℝ)) hb (0 : Fin 2))

/- TODO: The Gamma ratio characterization. If X_i are independent Gamma(b_i, 1)-distributed
then (X_i / ∑_j X_j)_i is Dirichlet(b)-distributed. -/

end ProbabilityTheory

end DirichletDistribution
-- #lint
