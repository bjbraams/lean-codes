/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import StdSimplexMeasure.Dirichlet
public import StdSimplexMeasure.MvBeta
public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

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

open Complex Fintype Filter MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section ComplexDirichlet

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

/-- Multiplying one factor of a convergent Dirichlet monomial by the logarithm of its
coordinate preserves integrability.  This is the basic domination estimate needed when
differentiating a simplex Mellin integral with respect to a parameter. -/
theorem integrableOn_mvBetaMonomial_mul_log
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) (i : ι) :
    IntegrableOn
      (fun u : ι → ℝ ↦
        (∏ j, (u j : ℂ) ^ (b j - 1)) * Complex.log (u i : ℂ))
      (stdSimplex ℝ ι) stdSimplexMeasure := by
  let _ : Nonempty ι := ⟨i⟩
  let δ : ℝ := (b i).re / 2
  have hδ : 0 < δ := half_pos (hb i)
  let b' : ι → ℂ := fun j ↦ b j - if j = i then δ else 0
  have hb' : b' ∈ mvBetaConvergent := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [b', δ]
      linarith [hb i]
    · simpa [b', hji] using hb j
  have hdom := (integrableOn_mvBetaMonomial b' hb').norm.const_mul (1 / δ)
  apply Integrable.mono hdom
  · have hmono := (integrableOn_mvBetaMonomial b hb).aestronglyMeasurable
    have hlog : AEStronglyMeasurable
        (fun u : ι → ℝ ↦ Complex.log (u i : ℂ))
        (stdSimplexMeasure.restrict (stdSimplex ℝ ι)) := by
      exact (Complex.measurable_log.comp
        (Complex.measurable_ofReal.comp (measurable_pi_apply i))).aestronglyMeasurable
    exact hmono.mul hlog
  · have hpos := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    filter_upwards [self_mem_ae_restrict (s := stdSimplex ℝ ι)
        (isClosed_stdSimplex ℝ ι).measurableSet, hpos] with u hu hupos
    have hui : 0 < u i := hupos i
    have hui1 : u i ≤ 1 := (hu.2.symm ▸ Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i))
    simp only [norm_mul, norm_prod]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
      Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hnorm (j : ι) :
        ‖(u j : ℂ) ^ (b j - 1)‖ = u j ^ ((b j).re - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos (hupos j)]
      simp
    have hnorm' (j : ι) :
        ‖(u j : ℂ) ^ (b' j - 1)‖ = u j ^ ((b' j).re - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos (hupos j)]
      simp
    rw [hnorm i, hnorm' i]
    simp_rw [hnorm, hnorm']
    have hrest :
        (∏ j : {j : ι // j ≠ i}, u j ^ ((b j).re - 1)) =
          ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [b', j.property]
    rw [hrest]
    rw [← Complex.ofReal_log hui.le]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hlog := Real.abs_log_mul_self_rpow_lt (u i) δ hui hui1 hδ
    have hpow : u i ^ ((b i).re - 1) =
        u i ^ (((b i).re - δ - 1) + δ) := by
      congr 1
      ring
    rw [hpow, Real.rpow_add hui]
    have hbi' : (b' i).re - 1 = (b i).re - δ - 1 := by simp [b']
    rw [hbi']
    rw [abs_of_pos (one_div_pos.mpr hδ)]
    simp_rw [abs_of_pos (Real.rpow_pos_of_pos (hupos _) _)]
    have hnonneg : 0 ≤ u i ^ ((b i).re - δ - 1) *
        ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1) :=
      mul_nonneg (Real.rpow_nonneg (hu.1 i) _)
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    calc
      (u i ^ ((b i).re - δ - 1) * u i ^ δ) *
          (∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) * |Real.log (u i)| =
          (u i ^ δ * |Real.log (u i)|) *
            (u i ^ ((b i).re - δ - 1) *
              ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) := by ring
      _ ≤ (1 / δ) *
            (u i ^ ((b i).re - δ - 1) *
              ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) := by
        gcongr
        simpa [abs_mul, mul_comm,
          abs_of_pos (Real.rpow_pos_of_pos hui _)] using hlog.le

/-- A simplex slice separates a complex Dirichlet monomial into its distinguished-coordinate,
radial, and lower-dimensional factors. -/
theorem prod_cpow_stdSimplexCoordMap_scale
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

/-- The product of reciprocal Gamma factors used to regularize a Dirichlet integral is entire
in the parameter vector. -/
theorem analyticOnNhd_prod_invGamma :
    AnalyticOnNhd ℂ (fun b : ι → ℂ ↦ ∏ i, (Gamma (b i))⁻¹) Set.univ := by
  apply DifferentiableOn.analyticOnNhd_pi _ isOpen_univ
  intro b _
  apply DifferentiableAt.differentiableWithinAt
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hi := Complex.differentiable_one_div_Gamma.differentiableAt.comp b
        (ContinuousLinearMap.proj i).differentiableAt
      change DifferentiableAt ℂ (fun b : ι → ℂ ↦ (Gamma (b i))⁻¹) b at hi
      rw [show (fun b : ι → ℂ ↦ ∏ j ∈ insert i s, (Gamma (b j))⁻¹) =
          (fun b ↦ (Gamma (b i))⁻¹) * (fun b ↦ ∏ j ∈ s, (Gamma (b j))⁻¹) by
        funext x
        exact Finset.prod_insert his]
      exact hi.mul ih

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

/-- On the convergence region, regularization amounts to multiplying the unregularized
simplex Mellin integral by the product of reciprocal Gamma factors. -/
theorem regDirichletIntegral_eq_prod_invGamma_mul
    (b : ι → ℂ) (f : (ι → ℝ) → ℂ) :
    regDirichletIntegral b f =
      (∏ i, (Gamma (b i))⁻¹) *
        ∫ u in stdSimplex ℝ ι, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u
          ∂stdSimplexMeasure := by
  classical
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hmem := self_mem_ae_restrict
    (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
  have hpos : ∀ᵐ u ∂stdSimplexMeasure.restrict (stdSimplex ℝ ι), ∀ i, 0 < u i := by
    cases isEmpty_or_nonempty ι with
    | inl hι =>
        let _ := hι
        simp
    | inr hι =>
        let _ := hι
        exact ae_zero_lt_of_mem_stdSimplex (ι := ι)
  filter_upwards [hmem, hpos] with u hu hupos
  have hinter : u ∈ stdSimplexInterior := ⟨hu, hupos⟩
  rw [regDirichletDensity, Set.indicator_of_mem hinter]
  rw [Finset.prod_div_distrib, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  ring

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

/-- The Dirichlet monomial `∏ i, (u i) ^ (b i - 1)` is entire in the parameter vector at
every interior simplex point. -/
theorem hasFDerivAt_mvBetaMonomial {u : ι → ℝ} (hu : ∀ i, 0 < u i) (b : ι → ℂ) :
    HasFDerivAt (fun c : ι → ℂ ↦ ∏ i, (u i : ℂ) ^ (c i - 1))
      (∑ i, ((Complex.log (u i : ℂ) * ∏ j, (u j : ℂ) ^ (b j - 1)) •
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ))) b := by
  classical
  let p : ι → ((ι → ℂ) →L[ℂ] ℂ) :=
    fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
  let g : ι → (ι → ℂ) → ℂ := fun i c ↦ (u i : ℂ) ^ (c i - 1)
  let g' : ι → (ι → ℂ) →L[ℂ] ℂ := fun i ↦
    ((u i : ℂ) ^ (b i - 1) * Complex.log (u i : ℂ)) • p i
  have hg i : HasFDerivAt (g i) (g' i) b := by
    have hproj : HasFDerivAt (fun c : ι → ℂ ↦ c i) (p i) b := (p i).hasFDerivAt
    have hsub : HasFDerivAt (fun c : ι → ℂ ↦ c i - 1) (p i) b := hproj.sub_const 1
    have h0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hu i).ne'
    simpa [g, g', mul_comm] using hsub.const_cpow (Or.inl h0)
  have hprod :=
    HasFDerivAt.finsetProd (u := (Finset.univ : Finset ι)) (fun i _ ↦ hg i)
  refine hprod.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [g, g', p, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hprod_erase :
      (∏ j, (u j : ℂ) ^ (b j - 1)) =
        (u i : ℂ) ^ (b i - 1) *
          ∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j - 1) :=
    (Finset.mul_prod_erase Finset.univ (fun j ↦ (u j : ℂ) ^ (b j - 1))
      (Finset.mem_univ i)).symm
  rw [hprod_erase]
  ring

/-- If `f` is continuous on the closed standard simplex, then
`b ↦ regDirichletIntegral b f` is analytic on the domain of absolute convergence. -/
theorem regDirichletIntegral_analyticOn {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    AnalyticOn ℂ (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      have hconst : (fun b : ι → ℂ ↦ regDirichletIntegral b f) = fun _ ↦ 0 := by
        funext b
        simp [regDirichletIntegral, stdSimplexMeasure_empty]
      rw [hconst]
      exact analyticOn_const
  | inr hι =>
    let _ := hι
    have hH : AnalyticOnNhd ℂ (fun b : ι → ℂ ↦ ∏ i, (Gamma (b i))⁻¹) Set.univ :=
      analyticOnNhd_prod_invGamma
    let μ := stdSimplexMeasure.restrict (stdSimplex ℝ ι)
    let G : (ι → ℂ) → ℂ := fun b ↦
      ∫ u, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u ∂μ
    have hG : AnalyticOnNhd ℂ G mvBetaConvergent := by
      refine analyticOnNhd_integral_of_dominated_of_fderiv_le
        (μ := μ) (U := mvBetaConvergent) (F := fun b u ↦
          (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
        Complex.isOpen_mvBetaConvergent ?_
      intro b hb
      let α : ι → ℝ := fun i ↦ (b i).re / 2
      have hα i : 0 < α i := half_pos (hb i)
      let s : Set (ι → ℂ) := {c | ∀ i, α i < (c i).re}
      have hsopen : IsOpen s := by
        rw [show s = ⋂ i, {c : ι → ℂ | α i < (c i).re} by ext c; simp [s]]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const
            (Complex.continuous_re.comp (continuous_apply i))
      have hsb : b ∈ s := fun i ↦ half_lt_self (hb i)
      have hs_nhds : s ∈ 𝓝 b := hsopen.mem_nhds hsb
      let a : ι → ℂ := fun i ↦ (α i : ℂ)
      have ha : a ∈ mvBetaConvergent := fun i ↦ by simpa [a] using hα i
      obtain ⟨Cf, hCf⟩ := bddAbove_def.mp
        ((isCompact_stdSimplex ℝ ι).bddAbove_image hf.norm)
      let C : ℝ := max Cf 0
      have hC0 : 0 ≤ C := le_max_right _ _
      have hf_le : ∀ u ∈ stdSimplex ℝ ι, ‖f u‖ ≤ C := fun u hu ↦
        (hCf _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
      let bound : (ι → ℝ) → ℝ := fun u ↦
        C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖
      let p : ι → ((ι → ℂ) →L[ℂ] ℂ) :=
        fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
      let F' : (ι → ℂ) → (ι → ℝ) → (ι → ℂ) →L[ℂ] ℂ := fun c u ↦
        ∑ i, ((Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (c j - 1)) * f u) • p i)
      refine ⟨s, bound, F', hs_nhds, ?meas, ?int, ?F'meas, ?bd, ?bdint, ?diff⟩
      · filter_upwards [hs_nhds] with c hc
        have hc' : c ∈ mvBetaConvergent := fun i ↦ (hα i).trans (hc i)
        exact ((integrableOn_mvBetaMonomial c hc').mul_continuousOn hf
          (isCompact_stdSimplex ℝ ι)).1
      · change IntegrableOn (fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
            (stdSimplex ℝ ι) stdSimplexMeasure
        exact (integrableOn_mvBetaMonomial b hb).mul_continuousOn hf
          (isCompact_stdSimplex ℝ ι)
      · apply Finset.aestronglyMeasurable_fun_sum
        intro i _
        have hmono := (integrableOn_mvBetaMonomial_mul_log b hb i).aestronglyMeasurable
        have hfmeas :=
          hf.aestronglyMeasurable (μ := stdSimplexMeasure)
            (isClosed_stdSimplex ℝ ι).measurableSet
        have hscal : AEStronglyMeasurable
            (fun u ↦ Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (b j - 1)) * f u) μ :=
          (hmono.mul hfmeas).congr <| Eventually.of_forall fun u ↦ by
            simp [mul_assoc, mul_left_comm, mul_comm]
        exact hscal.smul_const _
      · filter_upwards [self_mem_ae_restrict (isClosed_stdSimplex ℝ ι).measurableSet,
            ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c hc
        have hui i : 0 < u i := hupos i
        have hui1 i : u i ≤ 1 :=
          (hu.2.symm ▸ Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i))
        have hmon : ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ ≤
            ‖∏ j, (u j : ℂ) ^ (a j - 1)‖ := by
          simp only [norm_prod]
          refine Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_
          have hjpos : 0 < u j := hui j
          rw [norm_cpow_eq_rpow_re_of_pos hjpos, norm_cpow_eq_rpow_re_of_pos hjpos]
          simp only [sub_re, one_re]
          exact Real.rpow_le_rpow_of_exponent_ge hjpos (hui1 j)
            (sub_le_sub_right (le_of_lt (hc j)) 1)
        have hproj (i : ι) : ‖p i‖ ≤ 1 :=
          (p i).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1) fun v ↦ by
            simpa [p] using (norm_le_pi_norm v i)
        have hsum : ‖F' c u‖ ≤
            ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ := by
          refine (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [norm_smul, norm_mul, norm_mul]
          refine mul_le_mul_of_nonneg_left (hproj i) (by positivity) |>.trans_eq ?_
          ring
        refine hsum.trans ?_
        calc
          ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ ≤
            ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (a j - 1)‖ * C := by
            gcongr <;> first | exact hmon | exact hf_le u hu
          _ = C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖ := by
            simp [norm_mul, mul_comm, mul_left_comm, Finset.mul_sum]
          _ = bound u := rfl
      · have hterm i := (integrableOn_mvBetaMonomial_mul_log a ha i).norm
        have hsum := integrable_finsetSum (s := Finset.univ) fun i _ ↦ hterm i
        simpa [bound] using hsum.const_mul C
      · filter_upwards [self_mem_ae_restrict (isClosed_stdSimplex ℝ ι).measurableSet,
            ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c hc
        have hmon := hasFDerivAt_mvBetaMonomial hupos c
        have hfconst : HasFDerivAt (fun _ : ι → ℂ ↦ f u)
            (0 : (ι → ℂ) →L[ℂ] ℂ) c := hasFDerivAt_const (f u) c
        have hmul := hmon.mul hfconst
        have hF'eq :
            f u • ∑ i, (Complex.log (u i : ℂ) *
                ∏ j, (u j : ℂ) ^ (c j - 1)) • p i =
              F' c u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_smul]
          simp [F', p, mul_assoc, mul_left_comm, mul_comm]
        refine hmul.congr_fderiv ?_
        have hz : ((∏ i, (u i : ℂ) ^ (c i - 1)) • (0 : (ι → ℂ) →L[ℂ] ℂ)) = 0 := by
          ext v; simp
        rw [hz, zero_add]
        simpa [p] using hF'eq
    have hEq : (fun b ↦ regDirichletIntegral b f) =
        fun b ↦ (∏ i, (Gamma (b i))⁻¹) * G b := by
      funext b
      exact regDirichletIntegral_eq_prod_invGamma_mul b f
    rw [hEq]
    exact ((hH.mono (Set.subset_univ _)).mul hG).analyticOn

end ProbabilityTheory

end ComplexDirichlet
