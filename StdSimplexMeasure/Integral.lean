/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import StdSimplexMeasure.Measure

/-!
# Integrals on the standard simplex

This file develops change-of-coordinates, slicing, permutation, monomial, and aggregation
formulas for integrals with respect to `stdSimplexMeasure`.
-/

open Fintype Set

noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure

universe u

variable {ι : Type u} [Fintype ι]

local instance integralDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Scaling the free coordinates by `c` divides the Bochner integral by
`c ^ (card ι - 1)`. -/
theorem integral_smul_free_coords
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (c : ℝ) (hc : 0 < c)
    (f : ({j : ι // j ≠ i} → ℝ) → E) :
  ∫ x, f (c • x) ∂volume =
    (c ^ (Fintype.card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
  let e : ({j : ι // j ≠ i} → ℝ) ≃ₜ ({j : ι // j ≠ i} → ℝ) :=
    Homeomorph.smulOfNeZero c hc.ne'
  have hmap : Measure.map e volume =
      ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume := by
    simpa [e] using volume_map_smul_free_coords i c hc
  calc
    ∫ x, f (c • x) ∂volume = ∫ x, f x ∂Measure.map e volume := by
      simpa [e] using (e.isClosedEmbedding.integral_map f).symm
    _ = ∫ x, f x ∂(ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume) := by rw [hmap]
    _ = (c ^ (card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
      rw [integral_smul_measure]
      simp [(pow_pos hc _).le]

/-- Integration over the standard simplex can be computed in any free-coordinate chart. This is
stated for functions taking values in a normed real vector space. -/
theorem integral_stdSimplex_eq_integral_freeCoords
    [Nonempty ι] (i : ι)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact
    (isClosedEmbedding_stdSimplexCoordMap i).integral_map f

/-- The beta integral at positive integer parameters, in a form convenient for simplex
monomial integrals. -/
theorem integral_Icc_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) 1, t ^ a * (1 - t) ^ b =
      (Nat.factorial a * Nat.factorial b : ℝ) / Nat.factorial (a + b + 1) := by
  have hbeta :
      (↑(∫ t in Set.Icc (0 : ℝ) 1, t ^ a * (1 - t) ^ b) : ℂ) =
        Complex.betaIntegral (a + 1) (b + 1) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one]
    rw [integral_Icc_eq_integral_Ioc]
    have hc : (∫ t in Set.Ioc (0 : ℝ) 1,
        (↑(t ^ a * (1 - t) ^ b) : ℂ)) =
        ↑(∫ t in Set.Ioc (0 : ℝ) 1, t ^ a * (1 - t) ^ b) := integral_ofReal
    rw [← hc]
    apply integral_congr_ae
    filter_upwards [] with t
    simp [Complex.ofReal_sub, Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [hbeta]
  rw [Complex.betaIntegral_eval_nat_add_one_right (by norm_num; positivity) b]
  have hprod : (∏ j ∈ Finset.range (b + 1), ((a : ℂ) + 1 + j)) =
      (((a + 1).ascFactorial (b + 1) : ℕ) : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    ring
  rw [hprod]
  push_cast
  have hfac : (Nat.factorial (a + b + 1) : ℂ) =
      (Nat.factorial a : ℂ) * ((a + 1).ascFactorial (b + 1) : ℂ) := by
    norm_cast
    simpa [Nat.add_assoc] using (Nat.factorial_mul_ascFactorial a (b + 1)).symm
  rw [hfac]
  have ha : (Nat.factorial a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos a).ne'
  have hs : ((a + 1).ascFactorial (b + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ascFactorial_pos a (b + 1)).ne'
  field_simp [ha, hs]

/-- Evaluates an integral over the standard simplex by separating out the `i`-th coordinate.
This theorem provides the standard Fubini reduction (integration by slices) for the simplex.
It expresses the integral of a function `f` over the $(k-1)$-simplex (where $k$ is `card ι`)
as an iterated integral:
1. An outer 1D integral over the isolated coordinate $t \in [0, 1]$.
2. An inner integral over the $(k-2)$-simplex of the remaining coordinates $v$.
Because the remaining coordinates are subject to the constraint $\sum v = 1 - t$, they are
scaled by $(1 - t)$ to map them back to a standard unit $(k-1)$-simplex.
This change of variables introduces a Jacobian determinant factor of $(1 - t)^{k - 2}$. -/
theorem integral_stdSimplex_split_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) [Nontrivial ι]
    (f : (ι → ℝ) → E)
    (hf : IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
    ∫ t in Set.Icc (0 : ℝ) 1,
      ((1 - t) ^ (Fintype.card ι - 2)) •
      ∫ v in stdSimplex ℝ {j // j ≠ i}, f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j))
        ∂stdSimplexMeasure := by
  sorry

/-- The integral of a function over the standard simplex is invariant under coordinate
permutations. -/
theorem integral_stdSimplex_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Equiv.Perm ι) (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f (u ∘ σ) ∂stdSimplexMeasure =
    ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure := by
  have hp := measurePreserving_stdSimplexMeasure_perm σ
  have he : MeasurableEmbedding (fun u : ι → ℝ => u ∘ σ) := by
    apply (continuous_pi (fun j => continuous_apply (σ j))).measurableEmbedding
    intro u v huv
    funext j
    have := congrFun huv (σ.symm j)
    simpa using this
  have hr := hp.restrict_preimage_emb he (stdSimplex ℝ ι)
  rw [preimage_stdSimplex_perm] at hr
  exact hr.integral_comp he f

/-- Continuous functions are integrable on the standard simplex. -/
theorem ContinuousOn.integrableOn_stdSimplex
    [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E}
    (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    IntegrableOn f (stdSimplex ℝ ι) stdSimplexMeasure := by
  apply hf.integrableOn_of_subset_isCompact
    (isCompact_stdSimplex ℝ ι)
    (isClosed_stdSimplex ℝ ι).measurableSet
    Subset.rfl
  rw [← Measure.restrict_apply_univ]
  exact measure_ne_top _ _

/-- The integral of `f` over the standard simplex depends only on the values of `f` on
the standard simplex. -/
theorem integral_stdSimplex_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : (ι → ℝ) → E}
    (hfg : Set.EqOn f g (stdSimplex ℝ ι)) :
    ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure =
      ∫ u in stdSimplex ℝ ι, g u ∂stdSimplexMeasure := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [self_mem_ae_restrict
      (μ := stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
  exact hfg hu

/-- For a single-point index set, the integral over the simplex reduces to evaluation at the
all-ones vector. (Base case for induction.) -/
theorem integral_stdSimplex_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Unique ι] (f : (ι → ℝ) → E) :
  ∫ u in stdSimplex ℝ ι, f u ∂stdSimplexMeasure = f (fun _ ↦ 1) := by
  classical
  rw [stdSimplexMeasure_unique]
  change ∫ u, f u ∂(dirac (fun _ : ι => (1 : ℝ))).restrict (stdSimplex ℝ ι) = _
  rw [MeasureTheory.restrict_dirac' (isClosed_stdSimplex ℝ ι).measurableSet]
  have hmem : (fun _ : ι => (1 : ℝ)) ∈ stdSimplex ℝ ι := by simp [stdSimplex]
  rw [if_pos hmem]
  exact MeasureTheory.integral_dirac f (fun _ : ι => (1 : ℝ))

/-- Reduce a monomial integral on a nontrivial simplex to the monomial integral on the simplex
obtained by deleting coordinate `i`. -/
theorem integral_stdSimplex_explicit_monomial_succ [Nontrivial ι] (i : ι) (m : ι → ℕ) :
  ∫ u in stdSimplex ℝ ι, (∏ j, u j ^ m j) ∂stdSimplexMeasure =
    (Nat.factorial (m i) * Nat.factorial (card ι + (∑ j, m j) - 2 - m i)
      / Nat.factorial (card ι + ∑ j, m j - 1) : ℝ)
      * ∫ u in stdSimplex ℝ {j : ι // j ≠ i}, (∏ j, u j ^ m j.val) ∂stdSimplexMeasure := by
  have hf : IntegrableOn (fun u : ι → ℝ => ∏ j, u j ^ m j)
      (stdSimplex ℝ ι) stdSimplexMeasure := by
    apply ContinuousOn.integrableOn_stdSimplex
    fun_prop
  rw [integral_stdSimplex_split_at i _ hf]
  have hfactor (t : ℝ) (v : {j : ι // j ≠ i} → ℝ)
      (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
      (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j) =
        t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hvsum : ∑ q, v q = 1 := hv.2
    rw [stdSimplexCoordMap_apply_self, ← Finset.mul_sum, hvsum]
    simp only [mul_one, sub_sub_cancel]
    have hprod :
        (∏ q : {j : ι // j ≠ i},
          stdSimplexCoordMap i (fun q => (1 - t) * v q) q.val ^ m q.val) =
        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val) *
          ∏ q : {j : ι // j ≠ i}, v q ^ m q.val := by
      calc
        _ = ∏ q : {j : ι // j ≠ i}, ((1 - t) * v q) ^ m q.val := by
          apply Finset.prod_congr rfl
          intro q _
          rw [stdSimplexCoordMap_apply_of_ne i q.val q.property]
        _ = _ := by
          simp_rw [mul_pow, Finset.prod_mul_distrib,
            ← Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    ring
  have hinner (t : ℝ) :
      ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
          (∏ j, stdSimplexCoordMap i (fun q => (1 - t) * v q) j ^ m j)
          ∂stdSimplexMeasure =
        (t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) *
          ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
            (∏ q, v q ^ m q.val) ∂stdSimplexMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict
      (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ _).measurableSet] with v hv
    exact hfactor t v hv
  simp_rw [hinner]
  simp only [smul_eq_mul]
  have hcard : 2 ≤ card ι := Nat.succ_le_iff.mpr Fintype.one_lt_card
  have hsum : ∑ j, m j = m i + ∑ q : {j : ι // j ≠ i}, m q.val :=
    Fintype.sum_eq_add_sum_subtype_ne m i
  let b : ℕ := card ι - 2 + ∑ q : {j : ι // j ≠ i}, m q.val
  have hb : card ι + (∑ j, m j) - 2 - m i = b := by
    rw [hsum]
    dsimp [b]
    omega
  have hden : card ι + (∑ j, m j) - 1 = m i + b + 1 := by
    rw [hsum]
    dsimp [b]
    omega
  let A : ℝ := ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
    (∏ q, v q ^ m q.val) ∂stdSimplexMeasure
  calc
    ∫ t in Icc (0 : ℝ) 1,
        (1 - t) ^ (card ι - 2) *
          ((t ^ m i * (1 - t) ^ (∑ q : {j : ι // j ≠ i}, m q.val)) * A) =
        A * ∫ t in Icc (0 : ℝ) 1, t ^ m i * (1 - t) ^ b := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show b = (card ι - 2) + ∑ q : {j : ι // j ≠ i}, m q.val by rfl,
        pow_add]
      ring
    _ = A * ((Nat.factorial (m i) * Nat.factorial b : ℝ) /
        Nat.factorial (m i + b + 1)) := by
      rw [integral_Icc_pow_mul_one_sub_pow]
    _ = _ := by
      rw [hb, hden]
      dsimp [A]
      ring

/-- The integral of a monomial with natural exponents over the standard simplex. -/
theorem integral_stdSimplex_explicit_monomial (m : ι → ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, (∏ i, u i ^ m i) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  classical
  suffices h : ∀ n : ℕ, ∀ (α : Type u) [Fintype α], card α = n →
      ∀ (a : α → ℕ), Nonempty α →
        ∫ u in stdSimplex ℝ α, (∏ j, u j ^ a j) ∂stdSimplexMeasure =
          (∏ j, Nat.factorial (a j)) /
            (Nat.factorial (card α + (∑ j, a j) - 1) : ℝ) by
    exact h (card ι) ι rfl m inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro α _ hα a hne
      letI : Nonempty α := hne
      cases subsingleton_or_nontrivial α with
      | inl hs =>
          letI : Unique α := ⟨⟨Classical.choice hne⟩, fun x => hs.elim x _⟩
          rw [integral_stdSimplex_unique]
          simp
          field_simp
      | inr hn =>
          letI : Nontrivial α := hn
          let i : α := Classical.choice hne
          rw [integral_stdSimplex_explicit_monomial_succ i a]
          have hlt : card {j : α // j ≠ i} < n := by
            rw [← hα, Fintype.card_subtype_compl]
            exact Nat.sub_lt (Fintype.card_pos_iff.mpr hne) Nat.zero_lt_one
          have hsub : Nonempty {j : α // j ≠ i} := by
            obtain ⟨j, hj⟩ := exists_ne i
            exact ⟨⟨j, hj⟩⟩
          rw [ih (card {j : α // j ≠ i}) hlt {j : α // j ≠ i} rfl
            (fun j => a j.val) hsub]
          have hsum : ∑ j, a j = a i + ∑ q : {j : α // j ≠ i}, a q.val :=
            Fintype.sum_eq_add_sum_subtype_ne a i
          have hcardsub : card {j : α // j ≠ i} = card α - 1 := by
            simpa using Fintype.card_subtype_compl (fun j : α => j = i)
          have hidx : card {j : α // j ≠ i} +
              (∑ q : {j : α // j ≠ i}, a q.val) - 1 =
              card α + (∑ j, a j) - 2 - a i := by
            rw [hcardsub, hsum]
            have hc : 2 ≤ card α := Nat.succ_le_iff.mpr Fintype.one_lt_card
            omega
          rw [hidx, Fintype.prod_eq_mul_prod_subtype_ne _ i]
          field_simp
          norm_cast

/-- The integral of the constant function 1 over the standard simplex. -/
theorem integral_stdSimplex_constant [Nonempty ι] :
    ∫ _ in stdSimplex ℝ ι, (1 : ℝ) ∂stdSimplexMeasure =
      1 / (Nat.factorial (card ι - 1) : ℝ) := by
  rw [MeasureTheory.setIntegral_const, Measure.real, stdSimplexMeasure_stdSimplex_toReal]
  ring

/-- Equality between a Finsupp.prod and a full finite product for the same exponent
vector. -/
theorem MvPolynomial_monomial_eq (m : ι →₀ ℕ) (u : ι → ℝ) :
    m.prod (fun i n => u i ^ n) = ∏ i, u i ^ (m i) := by
  rw [Finsupp.prod]
  refine Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => ?_)
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]

/-- The integral of a `MvPolynomial` monomial over the standard simplex. -/
theorem integral_stdSimplex_MvPolynomial_monomial (m : ι →₀ ℕ) [Nonempty ι] :
    ∫ u in stdSimplex ℝ ι, m.prod (fun i n => u i ^ n) ∂stdSimplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (card ι + (∑ i, m i) - 1) : ℝ) := by
  simp_rw [MvPolynomial_monomial_eq]
  exact integral_stdSimplex_explicit_monomial (⇑m)

/-- Transformation of integrals under coordinate aggregation. The measurability hypothesis is
stated for the weighted target measure, which is exactly the push-forward measure occurring in
the change of variables. -/
theorem integral_stdSimplex_comp_aggregate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Surjective f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (κ → ℝ) → E)
    (hg : AEStronglyMeasurable g
      (((stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)).withDensity
        (stdSimplexAggregateDensity f))) :
    ∫ u in stdSimplex ℝ ι,
        g (stdSimplexAggregate f u) ∂stdSimplexMeasure
      =
    ∫ v in stdSimplex ℝ κ,
        (∏ k,
          v k ^ (stdSimplexAggregateFiberCard f k - 1) /
            Nat.factorial
              (stdSimplexAggregateFiberCard f k - 1)) •
          g v
        ∂stdSimplexMeasure := by
  let μ := (stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let ν := (stdSimplexMeasure (ι := κ)).restrict (stdSimplex ℝ κ)
  let d := stdSimplexAggregateDensity f
  have hagg : Measurable (stdSimplexAggregate (R := ℝ) f) := by
    exact (FunOnFinite.continuous_linearMap ℝ ℝ f).measurable
  have hd : Measurable d := by
    unfold d stdSimplexAggregateDensity
    fun_prop
  have hd_top : ∀ v, d v ≠ ⊤ := by
    intro v
    unfold d stdSimplexAggregateDensity
    apply ENNReal.prod_ne_top
    intro k _
    exact ENNReal.div_ne_top (by simp) (by simp [Nat.factorial_ne_zero])
  have hmeasure : Measure.map (stdSimplexAggregate f) μ = ν.withDensity d := by
    simpa only [μ, ν, d] using
      (map_stdSimplexMeasure_restrict_stdSimplex_aggregate f hf)
  have hgmap : AEStronglyMeasurable g (Measure.map (stdSimplexAggregate f) μ) := by
    rw [hmeasure]
    exact hg
  have hd_lt : ∀ᵐ v ∂ν, d v < ⊤ :=
    Filter.Eventually.of_forall fun v => lt_top_iff_ne_top.mpr (hd_top v)
  calc
    ∫ u, g (stdSimplexAggregate f u) ∂μ =
        ∫ v, g v ∂Measure.map (stdSimplexAggregate f) μ := by
      exact (integral_map hagg.aemeasurable hgmap).symm
    _ = ∫ v, g v ∂ν.withDensity d := by
      rw [hmeasure]
    _ = ∫ v, (d v).toReal • g v ∂ν := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hd_lt]
    _ = ∫ v in stdSimplex ℝ κ,
        (∏ k, v k ^ (stdSimplexAggregateFiberCard f k - 1) /
          Nat.factorial (stdSimplexAggregateFiberCard f k - 1)) • g v
          ∂stdSimplexMeasure := by
      apply integral_congr_ae
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (isClosed_stdSimplex ℝ κ).measurableSet
      filter_upwards [hmem] with v hv
      congr 1
      unfold d stdSimplexAggregateDensity
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro k _
      rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      · simp
      · exact hv.1 k

end MeasureTheory

end StdSimplexIntegral
-- #lint
