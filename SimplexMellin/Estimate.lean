/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Quantitative estimates for the regularized Dirichlet transform

On each compact set of parameters, the entire regularized Dirichlet transform `T_b[g]` of a kernel
smooth near the simplex is bounded by a constant times a bound for finitely many derivatives of
`g` on the simplex (step 1, item 5 of the programme). The proof bounds the explicit continuation
formula `regDirichletShiftFormula` piece by piece:

* the native integral by the supremum of the kernel, on compact subsets of `Re b > 0`
  (`exists_norm_regDirichletIntegral_le`, comparing with the density at `min Re b`);
* a tangential derivative costs one order of derivatives
  (`IteratedFDerivBoundOnSimplex.tangentDeriv`), so the shifted integrals along a list of
  tangential shifts are bounded by the derivatives up to the length of the list
  (`exists_norm_shiftedDirichletIntegral_le`);
* division by the power partition denominator costs a constant (Leibniz rule,
  `exists_iteratedFDerivBound_div_powerPartitionDenom`);
* the Pochhammer factors are bounded on compact sets.

Every continuation agrees with the explicit formula on its region, so the bound holds for all
of them (`exists_norm_regDirichletContinuation_le`) and for the entire transform
(`exists_norm_regDirichletTransform_le`). The order needed on `-N < re (b i)` is
`(card ι - 1) N`.

## Main results

* `Dirichlet.IteratedFDerivBoundOnSimplex`: derivatives of order at most `L` bounded by `A` on
  the simplex.
* `Dirichlet.exists_norm_regDirichletContinuation_le`: the estimate on `-N < re (b i)`.
* `Dirichlet.exists_norm_regDirichletTransform_le`: the estimate for the entire transform.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace Dirichlet

open Measure

variable {ι : Type*} [Fintype ι]

/-- On a compact set of parameters with positive real parts, the native regularized integral is
bounded by a constant times the supremum of the kernel on the simplex. -/
theorem exists_norm_regDirichletIntegral_le {K : Set (ι → ℂ)} (hK : IsCompact K)
    (hKb : K ⊆ mvBetaConvergent) :
    ∃ C, 0 ≤ C ∧ ∀ (h : (ι → ℝ) → ℂ) (A : ℝ),
      ContinuousOn h (Convexity.StdSimplex.coordinateSet ℝ ι) → 0 ≤ A →
      (∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ‖h u‖ ≤ A) →
      ∀ b ∈ K, ‖regDirichletIntegral b h‖ ≤ C * A := by
  -- A uniform lower bound `σ` for the real parts on `K`.
  have hσi : ∀ i, ∃ σ > 0, ∀ b ∈ K, σ ≤ (b i).re := by
    intro i
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨b₀, hb₀, hmin⟩ := hK.exists_isMinOn hKne
        (continuous_re.comp (continuous_apply i)).continuousOn
      exact ⟨(b₀ i).re, hKb hb₀ i, fun b hb => hmin hb⟩
  choose σi hσipos hσi using hσi
  set σ : ℝ := (∑ i, (σi i)⁻¹ + 1)⁻¹
  have hσpos : 0 < σ := inv_pos.mpr (add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun j _ => (inv_pos.mpr (hσipos j)).le) one_pos)
  have hσle : ∀ i, σ ≤ σi i := by
    intro i
    have h1 : (σi i)⁻¹ ≤ ∑ j, (σi j)⁻¹ + 1 := by
      have := Finset.single_le_sum (f := fun j => (σi j)⁻¹)
        (fun j _ => (inv_pos.mpr (hσipos j)).le) (Finset.mem_univ i)
      linarith
    calc σ ≤ ((σi i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hσipos i)) h1
      _ = σi i := inv_inv _
  have hσ1 : σ ≤ 1 := by
    simp only [σ]
    exact inv_le_one_of_one_le₀ (by
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (inv_pos.mpr (hσipos j)).le])
  -- A uniform bound for the reciprocal Gamma factors on `K`.
  have hcont : Continuous fun b : ι → ℂ => ∏ i, ‖(Gamma (b i))⁻¹‖ := by
    refine continuous_finsetProd _ fun i _ => ?_
    have h1 : Continuous fun b : ι → ℂ => (Gamma (b i))⁻¹ :=
      Continuous.comp (g := fun s => (Gamma s)⁻¹) differentiable_one_div_Gamma.continuous
        (continuous_apply i)
    exact h1.norm
  obtain ⟨G, hG⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  -- The comparison density at `σ`.
  set w : (ι → ℝ) → ℝ := fun u => ‖regDirichletDensity (fun _ => (σ : ℂ)) u‖
  have hσb : (fun _ : ι => (σ : ℂ)) ∈ mvBetaConvergent := fun i => by simpa using hσpos
  have hwi : IntegrableOn w (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
    have := integrableOn_regDirichletDensity_mul _ hσb (f := fun _ => (1 : ℂ)) continuousOn_const
    refine this.norm.congr (Eventually.of_forall fun u => ?_)
    simp [w]
  set Γσ : ℝ := Real.Gamma σ
  have hΓσ : 0 < Γσ := Real.Gamma_pos_of_pos hσpos
  set C : ℝ := |G| * Γσ ^ Fintype.card ι *
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, w u ∂stdSimplexMeasure
  have hw0 : 0 ≤ ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, w u ∂stdSimplexMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  refine ⟨C, by positivity, fun h A hh hA hhA b hb => ?_⟩
  -- Pointwise comparison on the interior.
  have hpt : ∀ u ∈ stdSimplexInterior, ‖regDirichletDensity b u * h u‖ ≤
      (|G| * Γσ ^ Fintype.card ι * A) * w u := by
    intro u hu
    have hpos : ∀ i, 0 < u i := hu.2
    have hu1 : ∀ i, u i ≤ 1 :=
      fun i => (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu.1 i).2
    simp only [w, regDirichletDensity, indicator_of_mem hu, norm_mul, norm_prod, norm_div]
    have hwu : ∏ i, ‖(u i : ℂ) ^ ((σ : ℂ) - 1)‖ / ‖Gamma (σ : ℂ)‖ =
        (∏ i, u i ^ (σ - 1)) / Γσ ^ Fintype.card ι := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [norm_cpow_eq_rpow_re_of_pos (hpos i)]
        simp
      · rw [Complex.Gamma_ofReal, norm_real, Real.norm_of_nonneg hΓσ.le]
    rw [hwu]
    have hmono : ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ ≤ ∏ i, u i ^ (σ - 1) := by
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
      rw [norm_cpow_eq_rpow_re_of_pos (hpos i)]
      simp only [sub_re, one_re]
      exact Real.rpow_le_rpow_of_exponent_ge (hpos i) (hu1 i)
        (by linarith [hσle i, hσi i b hb])
    have hGb : ∏ i, ‖(Gamma (b i))⁻¹‖ ≤ |G| :=
      (Real.le_norm_self _).trans ((hG b hb).trans (le_abs_self _))
    have hP0 : 0 ≤ ∏ i, u i ^ (σ - 1) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i).le _
    have hsplit : ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ / ‖Gamma (b i)‖ =
        (∏ i, ‖(u i : ℂ) ^ (b i - 1)‖) * ∏ i, ‖(Gamma (b i))⁻¹‖ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [norm_inv, div_eq_mul_inv]
    rw [hsplit]
    have hhu : ‖h u‖ ≤ A := hhA u hu.1
    calc (∏ i, ‖(u i : ℂ) ^ (b i - 1)‖) * (∏ i, ‖(Gamma (b i))⁻¹‖) * ‖h u‖
        ≤ (∏ i, u i ^ (σ - 1)) * |G| * A := by gcongr
      _ = |G| * Γσ ^ Fintype.card ι * A * ((∏ i, u i ^ (σ - 1)) / Γσ ^ Fintype.card ι) := by
          field_simp
  unfold regDirichletIntegral
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖regDirichletDensity b u * h u‖
        ∂stdSimplexMeasure
      ≤ ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          (|G| * Γσ ^ Fintype.card ι * A) * w u ∂stdSimplexMeasure := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hwi.const_mul _) ?_
        filter_upwards [ae_mem_stdSimplexInterior (ι := ι)] with u hu using hpt u hu
    _ = C * A := by
        rw [integral_const_mul]; simp only [C]; ring

/-- The derivatives of order at most `L` of `f` are bounded by `A` on the simplex. -/
def IteratedFDerivBoundOnSimplex (L : ℕ) (f : (ι → ℝ) → ℂ) (A : ℝ) : Prop :=
  ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ∀ k ≤ L, ‖iteratedFDeriv ℝ k f u‖ ≤ A

/-- A bound of a higher order implies a bound of a lower order. -/
theorem IteratedFDerivBoundOnSimplex.of_le {L L' : ℕ} {f : (ι → ℝ) → ℂ} {A : ℝ}
    (h : IteratedFDerivBoundOnSimplex L' f A) (hL : L ≤ L') :
    IteratedFDerivBoundOnSimplex L f A :=
  fun u hu k hk => h u hu k (hk.trans hL)

/-- A tangential derivative consumes one order of the derivative bound. -/
theorem IteratedFDerivBoundOnSimplex.tangentDeriv {L : ℕ} {f : (ι → ℝ) → ℂ} {A : ℝ}
    (hf : ContDiffNearStdSimplex (L + 1) f) (h : IteratedFDerivBoundOnSimplex (L + 1) f A)
    (j k : ι) :
    IteratedFDerivBoundOnSimplex L (stdSimplexTangentDeriv j k f)
      (‖stdSimplexTangentVector j k‖ * A) := by
  intro u hu m hm
  obtain ⟨U, hU, hsub, hfU⟩ := hf
  have hd : ContDiffOn ℝ L (fun y => fderiv ℝ f y) U :=
    hfU.fderiv_of_isOpen hU (by exact_mod_cast le_rfl)
  have hdu : ContDiffAt ℝ L (fun y => fderiv ℝ f y) u := hd.contDiffAt (hU.mem_nhds (hsub hu))
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := stdSimplexTangentVector j k) hdu
    (n := m) (by exact_mod_cast hm)
  unfold stdSimplexTangentDeriv
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (h u hu (m + 1) (by omega)) (norm_nonneg _)

open scoped Classical in
/-- On a compact subset of its shift region, the shifted Dirichlet integral along a list `l` is
bounded by a constant times a bound for the derivatives of order at most `length l` of the
kernel on the simplex. -/
theorem exists_norm_shiftedDirichletIntegral_le (i : ι) (l : List {j : ι // j ≠ i})
    {K : Set (ι → ℂ)} (hK : IsCompact K) (hKl : K ⊆ shiftRegion i l) :
    ∃ C, 0 ≤ C ∧ ∀ (h : (ι → ℝ) → ℂ) (A : ℝ), ContDiffNearStdSimplex l.length h → 0 ≤ A →
      IteratedFDerivBoundOnSimplex l.length h A →
      ∀ b ∈ K, ‖shiftedDirichletIntegral i l b h‖ ≤ C * A := by
  induction l generalizing K with
  | nil =>
    have hKb : K ⊆ mvBetaConvergent := by
      intro b hb j
      have hb' := hKl hb
      by_cases hji : j = i
      · subst j; simpa [shiftRegion] using hb'.1
      · simpa using hb'.2 ⟨j, hji⟩
    obtain ⟨C, hC, hbd⟩ := exists_norm_regDirichletIntegral_le hK hKb
    refine ⟨C, hC, fun h A hh hA hhA b hb => ?_⟩
    exact hbd h A hh.continuousOn hA (fun u hu => by
      simpa using hhA u hu 0 le_rfl) b hb
  | cons j l ih =>
    set K₀ := (fun b : ι → ℂ => b + Pi.single (j : ι) 1 - Pi.single i 1) '' K
    set K₁ := (fun b : ι → ℂ => b + Pi.single (j : ι) 1) '' K
    have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
    have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
    have hK₀l : K₀ ⊆ shiftRegion i l := by
      rintro _ ⟨b, hb, rfl⟩; exact (shiftRegion_cons i j l (hKl hb)).1
    have hK₁l : K₁ ⊆ shiftRegion i l := by
      rintro _ ⟨b, hb, rfl⟩; exact (shiftRegion_cons i j l (hKl hb)).2
    obtain ⟨C₀, hC₀, h₀⟩ := ih hK₀ hK₀l
    obtain ⟨C₁, hC₁, h₁⟩ := ih hK₁ hK₁l
    set v := ‖stdSimplexTangentVector (j : ι) i‖
    refine ⟨C₀ + C₁ * v, by positivity, fun h A hh hA hhA b hb => ?_⟩
    have hh' : ContDiffNearStdSimplex (l.length + 1) h := hh
    have hhA' : IteratedFDerivBoundOnSimplex (l.length + 1) h A := hhA
    rw [shiftedDirichletIntegral]
    have e₀ := h₀ h A (hh'.of_le (Nat.le_succ _)) hA (hhA'.of_le (Nat.le_succ _)) _
      ⟨b, hb, rfl⟩
    have e₁ := h₁ (stdSimplexTangentDeriv (j : ι) i h) (v * A) (hh'.tangentDeriv j i)
      (by positivity) (hhA'.tangentDeriv hh' j i) _ ⟨b, hb, rfl⟩
    calc ‖_ - _‖ ≤ C₀ * A + C₁ * (v * A) := (norm_sub_le _ _).trans (add_le_add e₀ e₁)
      _ = (C₀ + C₁ * v) * A := by ring

/-- Dividing by the power partition denominator multiplies the derivative bound on the simplex
by a constant depending only on `M` and `L`. -/
theorem exists_iteratedFDerivBound_div_powerPartitionDenom (M L : ℕ) :
    ∃ Q, 0 ≤ Q ∧ ∀ (f : (ι → ℝ) → ℂ) (A : ℝ), ContDiffNearStdSimplex L f → 0 ≤ A →
      IteratedFDerivBoundOnSimplex L f A →
      IteratedFDerivBoundOnSimplex L (fun u => f u / powerPartitionDenom M u) (Q * A) := by
  have hd : ContDiff ℝ ⊤ (powerPartitionDenom (ι := ι) M) := by
    unfold powerPartitionDenom
    exact ContDiff.sum fun j _ =>
      (Complex.ofRealCLM.contDiff.comp
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).contDiff).pow M
  set V : Set (ι → ℝ) := {u | powerPartitionDenom M u ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun hd.continuous continuous_const
  have hΔV : Convexity.StdSimplex.coordinateSet ℝ ι ⊆ V :=
    fun u hu => powerPartitionDenom_ne_zero M hu
  set q : (ι → ℝ) → ℂ := fun u => (powerPartitionDenom M u)⁻¹
  have hq : ContDiffOn ℝ ⊤ q V := hd.contDiffOn.inv fun u hu => hu
  -- Bounds for the derivatives of `q` on the simplex.
  have hqb : ∀ k : ℕ, ∃ B, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      ‖iteratedFDeriv ℝ k q u‖ ≤ B := by
    intro k
    have hc : ContinuousOn (fun u => ‖iteratedFDeriv ℝ k q u‖)
        (Convexity.StdSimplex.coordinateSet ℝ ι) := by
      have h1 := (hq.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top)
        hV.uniqueDiffOn).mono hΔV
      refine (h1.congr fun u hu => ?_).norm
      exact (iteratedFDerivWithin_of_isOpen k hV (hΔV hu)).symm
    obtain ⟨B, hB⟩ :=
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).exists_bound_of_continuousOn hc
    exact ⟨B, fun u hu => (Real.le_norm_self _).trans (hB u hu)⟩
  choose B hB using hqb
  set B' : ℝ := ∑ k ∈ Finset.range (L + 1), |B k|
  have hB' : ∀ k ≤ L, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      ‖iteratedFDeriv ℝ k q u‖ ≤ B' := by
    intro k hk u hu
    refine (hB k u hu).trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 ^ L * B', by positivity, fun f A hf hA hfA u hu k hk => ?_⟩
  obtain ⟨U, hU, hsub, hfU⟩ := hf
  set W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have huW : u ∈ W := ⟨hsub hu, hΔV hu⟩
  have hfW : ContDiffOn ℝ L f W := hfU.mono inter_subset_left
  have hqW : ContDiffOn ℝ L q W := (hq.mono inter_subset_right).of_le (by exact_mod_cast le_top)
  have heq : (fun u => f u / powerPartitionDenom M u) = fun u => f u * q u := by
    funext u; simp [q, div_eq_mul_inv]
  rw [heq, ← iteratedFDerivWithin_of_isOpen k hW huW]
  refine (norm_iteratedFDerivWithin_mul_le hfW hqW hW.uniqueDiffOn huW
    (by exact_mod_cast hk)).trans ?_
  have hterm : ∀ m ∈ Finset.range (k + 1),
      (k.choose m : ℝ) * ‖iteratedFDerivWithin ℝ m f W u‖ *
        ‖iteratedFDerivWithin ℝ (k - m) q W u‖ ≤ (k.choose m : ℝ) * (A * B') := by
    intro m hm
    have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [iteratedFDerivWithin_of_isOpen m hW huW, iteratedFDerivWithin_of_isOpen (k - m) hW huW,
      mul_assoc]
    gcongr
    · exact hfA u hu m (hm'.trans hk)
    · exact hB' (k - m) (by omega) u hu
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hsum]
  calc (2 : ℝ) ^ k * (A * B') ≤ 2 ^ L * (A * B') := by
        gcongr
        · exact one_le_two
    _ = 2 ^ L * B' * A := by ring

open scoped Classical in
/-- **Quantitative continuation estimate, finite order.** On a compact subset `K` of the region
`-N < re (b i)`, every continuation `F` of the regularized Dirichlet integral of a kernel with
`L = (card ι - 1) * N` derivatives near the simplex satisfies `‖F b‖ ≤ C A` whenever the
derivatives of order at most `L` of the kernel are bounded by `A` on the simplex. The constant
depends only on `K` and `N`. -/
theorem exists_norm_regDirichletContinuation_le (N : ℕ) {K : Set (ι → ℂ)} (hK : IsCompact K)
    (hKN : K ⊆ dirichletConvergenceRegion N) :
    ∃ C, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ) (F : (ι → ℂ) → ℂ) (A : ℝ),
      ContDiffNearStdSimplex ((Fintype.card ι - 1) * N) f →
      AnalyticOn ℂ F (dirichletConvergenceRegion N) →
      EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent → 0 ≤ A →
      IteratedFDerivBoundOnSimplex ((Fintype.card ι - 1) * N) f A →
      ∀ b ∈ K, ‖F b‖ ≤ C * A := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    refine ⟨0, le_rfl, fun f F A _ _ hEq _ _ b _ => ?_⟩
    have hb : b ∈ (mvBetaConvergent : Set (ι → ℂ)) := fun i => isEmptyElim i
    rw [hEq hb]
    simp [regDirichletIntegral, MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
    set L := (Fintype.card ι - 1) * N
    set M := L + N
    obtain ⟨Q, hQ, hQb⟩ := exists_iteratedFDerivBound_div_powerPartitionDenom (ι := ι) M L
    have hshift : ∀ i, ∃ Cᵢ, 0 ≤ Cᵢ ∧ ∀ (h : (ι → ℝ) → ℂ) (A : ℝ),
        ContDiffNearStdSimplex L h → 0 ≤ A → IteratedFDerivBoundOnSimplex L h A →
        ∀ b ∈ K, ‖shiftedDirichletIntegral i (shiftList i N) (b + Pi.single i (M : ℂ)) h‖ ≤
          Cᵢ * A := by
      intro i
      have hKi : IsCompact ((fun b : ι → ℂ => b + Pi.single i (M : ℂ)) '' K) :=
        hK.image (by fun_prop)
      have hKis : (fun b : ι → ℂ => b + Pi.single i (M : ℂ)) '' K ⊆
          shiftRegion i (shiftList i N) := by
        rintro _ ⟨b, hb, rfl⟩
        exact add_single_mem_shiftRegion_shiftList (hKN hb) i
      obtain ⟨Cᵢ, hCᵢ, hb⟩ := exists_norm_shiftedDirichletIntegral_le i (shiftList i N) hKi hKis
      refine ⟨Cᵢ, hCᵢ, fun h A hh hA hhA b hbK => ?_⟩
      rw [shiftList_length] at hb
      exact hb h A hh hA hhA _ ⟨b, hbK, rfl⟩
    choose Cs hCs hCsb using hshift
    have hpoch : ∀ i, ∃ P, ∀ b ∈ K, ‖(ascPochhammer ℂ M).eval (b i)‖ ≤ P := by
      intro i
      obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn
        ((Polynomial.differentiable (ascPochhammer ℂ M)).continuous.comp
          (continuous_apply i)).continuousOn
      exact ⟨P, fun b hb => by simpa using hP b hb⟩
    choose P hP using hpoch
    refine ⟨∑ i, |P i| * Cs i * Q, Finset.sum_nonneg fun i _ => by
      have := hCs i; positivity, fun f F A hf hF hEq hA hfA b hb => ?_⟩
    obtain ⟨hFa, hFe⟩ := regDirichletShiftFormula_spec (N := N) hf
    have hFF : F b = regDirichletShiftFormula N f b :=
      eqOn_dirichletContinuation hF hFa.analyticOn (hEq.trans hFe.symm) (hKN hb)
    rw [hFF, regDirichletShiftFormula, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    have hg : ContDiffNearStdSimplex L (fun u => f u / powerPartitionDenom M u) :=
      contDiffNear_div_powerPartitionDenom hf M
    have h1 := hCsb i _ (Q * A) hg (by positivity) (hQb f A hf hA hfA) b hb
    calc ‖(ascPochhammer ℂ M).eval (b i)‖ *
          ‖shiftedDirichletIntegral i (shiftList i N) (b + Pi.single i (M : ℂ))
            (fun u => f u / powerPartitionDenom M u)‖
        ≤ |P i| * (Cs i * (Q * A)) :=
          mul_le_mul ((hP i b hb).trans (le_abs_self _)) h1 (norm_nonneg _) (abs_nonneg _)
      _ = |P i| * Cs i * Q * A := by ring

/-- **Quantitative estimate for the entire transform** (step 1, item 5). For every compact set
`K` of parameters there are an order `L` and a constant `C` such that the entire regularized
transform of every kernel smooth near the simplex satisfies `‖T_b[g]‖ ≤ C A` on `K` whenever the
derivatives of `g` of order at most `L` are bounded by `A` on the simplex. -/
theorem exists_norm_regDirichletTransform_le {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ L C, 0 ≤ C ∧ ∀ (g : (ι → ℝ) → ℂ) (hg : SmoothNearStdSimplex g) (A : ℝ), 0 ≤ A →
      IteratedFDerivBoundOnSimplex L g A → ∀ b ∈ K, ‖regDirichletTransform g hg b‖ ≤ C * A := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have hKN : K ⊆ dirichletConvergenceRegion N := by
    intro b hb i
    have h1 : ‖b‖ ≤ R := by simpa using hR hb
    have h2 : |(b i).re| ≤ ‖b‖ := (abs_re_le_norm _).trans (norm_le_pi_norm b i)
    linarith [neg_abs_le (b i).re]
  obtain ⟨C, hC, hbd⟩ := exists_norm_regDirichletContinuation_le N hK hKN
  refine ⟨(Fintype.card ι - 1) * N, C, hC, fun g hg A hA hgA b hb => ?_⟩
  have hT := isRegDirichletContinuation_transform hg
  exact hbd g _ A (hg _) (hT.1.analyticOn.mono (subset_univ _)) hT.2 hA hgA b hb

end Dirichlet
