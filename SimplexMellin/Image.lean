/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Hyperplane
public import ToMathlib.Analysis.Complex.Carlson

/-!
# The image of the simplex Mellin transform

For a kernel `g` on the simplex `Δ`, the simplex Mellin transform is
`S_g(b) = ∫_Δ ∏ u^(b - 1) g = ∏ Γ(b i) T_b[g]` (`simplexMoment`). This module characterizes the
transforms of kernels smooth near `Δ` and vanishing near its faces (`exists_kernel_iff`): they
are the entire functions `S` with

* the sum-shift equation `S(b) = ∑ i, S(b + e i)` (from `∑ u i = 1`),
* the bound `‖S b‖ ≤ C ∏ i, max 1 (δ ^ (Re b i - 1))`, and
* Paley–Wiener bounds on one hyperplane `∑ b = s₀`.

Necessity (`simplexMoment_necessity`) collects the entire continuation
(`differentiable_simplexMoment`, by a shift of parameters and the Gamma factors), the sum-shift
equation (`simplexMoment_eq_sum`), the bound (`norm_integral_monomial_mul_le_of_vanish`) and the
hyperplane bounds (`norm_integral_hyperplane_le`). Sufficiency (`exists_kernel_of_sum_shift`) takes
the kernel from the hyperplane theorem `exists_kernel_of_paleyWiener`. The difference `D` of `S`
and the transform of that kernel satisfies the sum-shift equation and vanishes on `∑ b = s₀`,
hence on all hyperplanes `∑ b = s₀ - n`. On the lines `z ↦ D(b + (t - z)/k · 𝟙)` it is of
exponential type and bounded on the imaginary axis, so Carlson's theorem
(`Complex.eqOn_zero_of_natCast_eq_zero`) makes it vanish where `Re ∑ b ≤ Re s₀`; the identity
theorem does the rest.

The bound in the second condition cannot be dropped: `sin (2π (∑ b - s₀)) S_g(b)` satisfies the
sum-shift equation and vanishes on `∑ b = s₀`, and is excluded only by its growth in `Im ∑ b`.

## Main results

* `Dirichlet.differentiable_simplexMoment`, `Dirichlet.simplexMoment_eq_sum`.
* `Dirichlet.exists_kernel_of_sum_shift`: global sufficiency.
* `Dirichlet.simplexMoment_necessity`: global necessity.
* `Dirichlet.exists_kernel_iff`: **the Paley–Wiener description of the image**.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Dirichlet

open Measure

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The simplex Mellin transform `S_g(b) = ∫_Δ ∏ u^(b - 1) g = ∏ Γ(b i) T_b[g]`, as a native
integral. -/
def simplexMoment (b : ι → ℂ) (g : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (∏ i, (u i : ℂ) ^ (b i - 1)) * g u
    ∂stdSimplexMeasure

/-- Shifting the parameters by `m` and dividing the kernel by the monomial `(∏ u)^m`:
`S_g(b) = ∏ Γ(b i + m) T_(b + m)[g / (∏ u)^m]` where the Gamma factors do not vanish. -/
theorem simplexMoment_eq_prod_Gamma_mul (g : (ι → ℝ) → ℂ) (m : ℕ) (b : ι → ℂ)
    (hb : ∀ i, Gamma (b i + m) ≠ 0) :
    simplexMoment b g = (∏ i, Gamma (b i + m)) *
      regDirichletIntegral (fun i => b i + m) (divMonomial m g) := by
  unfold simplexMoment regDirichletIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_stdSimplexInterior (ι := ι)] with u hu
  simp only [regDirichletDensity, indicator_of_mem hu, divMonomial]
  have hpos : ∀ i, 0 < u i := hu.2
  have hu0 : ∀ i, (u i : ℂ) ≠ 0 := fun i => ofReal_ne_zero.mpr (hpos i).ne'
  have hfac : ∀ i, (u i : ℂ) ^ (b i + m - 1) = (u i : ℂ) ^ (b i - 1) * (u i : ℂ) ^ m := by
    intro i
    rw [show b i + m - 1 = (b i - 1) + (m : ℂ) by ring, cpow_add _ _ (hu0 i), cpow_natCast]
  have hmono : ((((∏ i, u i) ^ m : ℝ)) : ℂ) = ∏ i, (u i : ℂ) ^ m := by
    push_cast; rw [Finset.prod_pow]
  have hG : ∏ i, Gamma (b i + m) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  have hU : ∏ i, (u i : ℂ) ^ m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hu0 i)
  rw [Finset.prod_div_distrib, hmono]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib]
  field_simp

/-- **The simplex Mellin transform is entire** for a kernel continuous on the simplex and vanishing
at the points with a coordinate below `δ > 0`. -/
theorem differentiable_simplexMoment {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    Differentiable ℂ fun b => simplexMoment b g := by
  intro b₀
  obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, |(b₀ i).re|)
  set V : Set (ι → ℂ) := {b | ∀ i, 0 < (b i).re + m}
  have hVo : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((continuous_re.comp (continuous_apply i)).add continuous_const)
  have hb₀ : b₀ ∈ V := fun i => by
    have : |(b₀ i).re| ≤ ∑ j, |(b₀ j).re| :=
      Finset.single_le_sum (f := fun j => |(b₀ j).re|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    linarith [neg_abs_le (b₀ i).re]
  have hre : ∀ b ∈ V, ∀ i, 0 < (b i + m).re := fun b hb i => by simpa using hb i
  have heq : (fun b => simplexMoment b g) =ᶠ[𝓝 b₀] fun b => (∏ i, Gamma (b i + m)) *
      regDirichletIntegral (fun i => b i + m) (divMonomial m g) := by
    filter_upwards [hVo.mem_nhds hb₀] with b hb
    exact simplexMoment_eq_prod_Gamma_mul g m b fun i => Gamma_ne_zero_of_re_pos (hre b hb i)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.mul ?_ ?_
  · have hGa : ∀ i, AnalyticAt ℂ Gamma (b₀ i + m) := fun i =>
      DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re})
        (fun s hs => (differentiableAt_Gamma _ fun k h => by
          rw [h] at hs
          simp only [mem_ofPred_eq, neg_re, natCast_re] at hs
          linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]).differentiableWithinAt)
        ((isOpen_lt continuous_const continuous_re).mem_nhds (hre b₀ hb₀ i))
    refine (Finset.analyticAt_fun_prod _ fun i _ => ?_).differentiableAt
    exact (hGa i).comp_of_eq
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b₀).add
        analyticAt_const) rfl
  · have hshift : (fun i => b₀ i + m) ∈ mvBetaConvergent := hre b₀ hb₀
    have hT := ((regDirichletIntegral_analyticOn (continuousOn_divMonomial hg hδ hgsupp m))
      |>.differentiableOn.differentiableAt (Complex.isOpen_mvBetaConvergent.mem_nhds hshift))
    have hadd : DifferentiableAt ℂ (fun b : ι → ℂ => fun i => b i + (m : ℂ)) b₀ := by fun_prop
    exact DifferentiableAt.comp (g := fun c => regDirichletIntegral c (divMonomial m g)) b₀ hT hadd

/-- **The sum-shift equation** `S_g(b) = ∑ i, S_g(b + e i)`, from `∑ i, u i = 1` on the simplex. -/
theorem simplexMoment_eq_sum {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (b : ι → ℂ) :
    simplexMoment b g = ∑ i, simplexMoment (b + Pi.single i 1) g := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hint : ∀ c : ι → ℂ, IntegrableOn (fun u => (∏ i, (u i : ℂ) ^ (c i - 1)) * g u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
    intro c
    have h := (continuousOn_monomial_mul_of_vanish hg hδ hgsupp
      (fun i => c i - 1)).integrableOn_compact
      (μ := stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    rwa [IntegrableOn, Measure.restrict_restrict hS, inter_self] at h
  unfold simplexMoment
  rw [← integral_finsetSum _ fun i _ => hint _]
  refine setIntegral_congr_fun hS fun u hu => ?_
  by_cases hgu : g u = 0
  · simp [hgu]
  have hpos : ∀ i, 0 < u i := fun i => hδ.trans_le (hgsupp u hu hgu i)
  have hu0 : ∀ i, (u i : ℂ) ≠ 0 := fun i => ofReal_ne_zero.mpr (hpos i).ne'
  have hshift : ∀ i, ∏ j, (u j : ℂ) ^ ((b + Pi.single i 1 : ι → ℂ) j - 1) =
      (u i : ℂ) * ∏ j, (u j : ℂ) ^ (b j - 1) := by
    intro i
    have : ∀ j, (u j : ℂ) ^ ((b + Pi.single i 1 : ι → ℂ) j - 1) =
        (u j : ℂ) ^ (b j - 1) * (u j : ℂ) ^ ((Pi.single i (1 : ℂ) : ι → ℂ) j) := by
      intro j
      rw [← cpow_add _ _ (hu0 j)]
      simp only [Pi.add_apply]
      ring_nf
    simp_rw [this]
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  simp_rw [hshift, mul_assoc, ← Finset.sum_mul]
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  rw [hsum, one_mul]

/-- `∏ max 1 (δ ^ y i) ≤ e^(|log δ| ∑ |y i|)`. -/
theorem prod_max_one_rpow_le {δ : ℝ} (hδ : 0 < δ) (y : ι → ℝ) :
    ∏ i, max 1 (δ ^ y i) ≤ Real.exp (|Real.log δ| * ∑ i, |y i|) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => zero_le_one.trans (le_max_left _ _)) fun i _ => ?_
  refine max_le (Real.one_le_exp (by positivity)) ?_
  rw [Real.rpow_def_of_pos hδ]
  refine Real.exp_le_exp.mpr ?_
  calc Real.log δ * y i ≤ |Real.log δ * y i| := le_abs_self _
    _ = |Real.log δ| * |y i| := abs_mul _ _

/-- A parameter vector on the hyperplane `∑ b = s` is the hyperplane parameter of its coordinates
off `i₀`. -/
theorem hyperplaneParam_restrict (i₀ : ι) {s : ℂ} {b : ι → ℂ} (hb : ∑ i, b i = s) :
    hyperplaneParam i₀ s (fun j => b j) = b := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp only [hyperplaneParam, dite_true]
    rw [← hb, Fintype.sum_eq_add_sum_subtype_ne _ i]
    ring
  · simp [hyperplaneParam, hi]

/-- Hyperplane parameters depend holomorphically on the coordinates. -/
theorem differentiable_hyperplaneParam (i₀ : ι) (s : ℂ) :
    Differentiable ℂ (hyperplaneParam i₀ s) := by
  refine differentiable_pi.mpr fun i => ?_
  by_cases hi : i = i₀
  · subst hi
    simp only [hyperplaneParam, dite_true]
    fun_prop
  · simp only [hyperplaneParam, hi, dite_false]
    fun_prop

/-- **Global sufficiency.** Let `S` be entire on `ℂ^ι` with
* the sum-shift equation `S(b) = ∑ i, S(b + e i)`,
* the bound `‖S b‖ ≤ C ∏ i, max 1 (δ ^ (Re b i - 1))` for some `δ > 0`, and
* Paley–Wiener bounds on one hyperplane `∑ b = s₀` (as in `exists_kernel_of_paleyWiener`).

Then `S` is the simplex Mellin transform of a kernel continuous on and smooth near the simplex
and vanishing near its faces. The kernel is given by the hyperplane theorem; the difference of
the two entire functions vanishes on the hyperplanes `∑ b = s₀ - n` by the sum-shift equation,
hence on `Re ∑ b ≤ Re s₀` by Carlson's theorem on lines, hence everywhere. -/
theorem exists_kernel_of_sum_shift (i₀ : ι) (s₀ : ℂ) {S : (ι → ℂ) → ℂ}
    (hS : Differentiable ℂ S) (hshift : ∀ b, S b = ∑ i, S (b + Pi.single i 1))
    {C δ : ℝ} (hδ : 0 < δ) (hbd : ∀ b, ‖S b‖ ≤ C * ∏ i, max 1 (δ ^ ((b i).re - 1)))
    {ρ : {j : ι // j ≠ i₀} → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (hpw : ∀ N : ℕ, ∃ C, ∀ ζ : {j : ι // j ≠ i₀} → ℂ,
      ‖S (hyperplaneParam i₀ s₀ fun j => -(2 * π * I) * ζ j)‖ ≤
        C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|)) :
    ∃ g : (ι → ℝ) → ℂ, ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι) ∧
      SmoothNearStdSimplex g ∧
      (∃ δ > 0, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) ∧
      (fun b => simplexMoment b g) = S := by
  obtain ⟨g, hgc, hgs, ⟨δ', hδ', hv⟩, hg⟩ :=
    exists_kernel_of_paleyWiener i₀ s₀ (hS.comp (differentiable_hyperplaneParam i₀ s₀)) hρ hpw
  refine ⟨g, hgc, hgs, ⟨δ', hδ', hv⟩, ?_⟩
  set D : (ι → ℂ) → ℂ := fun b => S b - simplexMoment b g
  have hD : Differentiable ℂ D := hS.sub (differentiable_simplexMoment hgc hδ' hv)
  have hDshift : ∀ b, D b = ∑ i, D (b + Pi.single i 1) := by
    intro b
    simp only [D, Finset.sum_sub_distrib, ← hshift, ← simplexMoment_eq_sum hgc hδ' hv]
  -- `D` vanishes on the hyperplanes `∑ b = s₀ - n`.
  have hsum_single : ∀ (b : ι → ℂ) (i : ι), ∑ j, (b + Pi.single i 1 : ι → ℂ) j = ∑ j, b j + 1 := by
    intro b i
    simp [Finset.sum_add_distrib]
  have hD0 : ∀ n : ℕ, ∀ b : ι → ℂ, ∑ i, b i = s₀ - n → D b = 0 := by
    intro n
    induction n with
    | zero =>
      intro b hb
      rw [Nat.cast_zero, sub_zero] at hb
      simp only [D]
      rw [← hyperplaneParam_restrict i₀ hb, sub_eq_zero]
      exact (hg _).symm
    | succ n ih =>
      intro b hb
      rw [hDshift b]
      refine Finset.sum_eq_zero fun i _ => ih _ ?_
      rw [hsum_single, hb]
      push_cast
      ring
  -- A bound for `D` of exponential type in the real parts.
  set A : ℝ := ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g u‖ ∂stdSimplexMeasure
  set L : ℝ := max |Real.log δ| |Real.log δ'|
  have hL : 0 ≤ L := (abs_nonneg _).trans (le_max_left _ _)
  have hDbd : ∀ b, ‖D b‖ ≤ (|C| + |A|) * Real.exp (L * ∑ i, |(b i).re - 1|) := by
    intro b
    have hsum : 0 ≤ ∑ i, |(b i).re - 1| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hE : ∀ {d : ℝ}, 0 < d → |Real.log d| ≤ L →
        ∏ i, max 1 (d ^ ((b i).re - 1)) ≤ Real.exp (L * ∑ i, |(b i).re - 1|) := by
      intro d hd hdL
      exact (prod_max_one_rpow_le hd _).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdL hsum))
    have hP : ∀ d : ℝ, 0 ≤ ∏ i, max 1 (d ^ ((b i).re - 1)) := fun d =>
      Finset.prod_nonneg fun _ _ => zero_le_one.trans (le_max_left _ _)
    have h1 : ‖S b‖ ≤ |C| * Real.exp (L * ∑ i, |(b i).re - 1|) :=
      (hbd b).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (hP δ)).trans
        (mul_le_mul_of_nonneg_left (hE hδ (le_max_left _ _)) (abs_nonneg _)))
    have h2 : ‖simplexMoment b g‖ ≤ |A| * Real.exp (L * ∑ i, |(b i).re - 1|) :=
      (norm_integral_monomial_mul_le_of_vanish hgc hδ' hv b).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self A) (hP δ')).trans
          (mul_le_mul_of_nonneg_left (hE hδ' (le_max_right _ _)) (abs_nonneg _)))
    calc ‖D b‖ ≤ ‖S b‖ + ‖simplexMoment b g‖ := norm_sub_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
  -- Carlson's theorem on lines: `D` vanishes where `Re ∑ b ≤ Re s₀`.
  have hk : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  set k : ℝ := (Fintype.card ι : ℝ)
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hkc : ((k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by simp [k]
  have hk0' : (Fintype.card ι : ℂ) ≠ 0 := hkc ▸ hk0
  have hleft : ∀ b : ι → ℂ, (∑ i, b i).re ≤ s₀.re → D b = 0 := by
    intro b hb
    set t : ℂ := s₀ - ∑ i, b i
    have ht : 0 ≤ t.re := by simp only [t, sub_re]; linarith
    set φ : ℂ → ℂ := fun z => D fun i => b i + (t - z) / k
    have hsumφ : ∀ z : ℂ, ∑ i, (b i + (t - z) / k) = s₀ - z := by
      intro z
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hkc]
      simp only [t]
      field_simp
      ring
    have hφd : Differentiable ℂ φ := hD.comp (by fun_prop)
    set β : ℝ := ∑ i, |(b i).re + t.re / k - 1|
    have hφbd : ∀ z : ℂ, ‖φ z‖ ≤ (|C| + |A|) * Real.exp (L * β) * Real.exp (L * |z.re|) := by
      intro z
      refine (hDbd _).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hL
      have hterm : ∀ i, |(b i + (t - z) / k).re - 1| ≤
          |(b i).re + t.re / k - 1| + |z.re| / k := by
        intro i
        have hre : (b i + (t - z) / k).re = (b i).re + t.re / k - z.re / k := by
          rw [add_re, show (t - z) / (k : ℂ) = ((1 / k : ℝ) : ℂ) * (t - z) by
            push_cast; ring, re_ofReal_mul, sub_re]
          ring
        rw [hre, show (b i).re + t.re / k - z.re / k - 1 =
          ((b i).re + t.re / k - 1) + (-(z.re / k)) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_div, abs_of_pos hk]
      calc ∑ i, |(b i + (t - z) / k).re - 1|
          ≤ ∑ i, (|(b i).re + t.re / k - 1| + |z.re| / k) := Finset.sum_le_sum fun i _ => hterm i
        _ = β + |z.re| := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              show (Fintype.card ι : ℝ) = k from rfl, mul_div_cancel₀ _ hk.ne']
    have hzero := Complex.eqOn_zero_of_natCast_eq_zero (f := φ)
      (Differentiable.diffContOnCl fun z => hφd z)
      (C := (|C| + |A|) * Real.exp (L * β)) (τ := L) (c := 0)
      (fun z _ => (hφbd z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (abs_re_le_norm z) hL)) (by positivity)))
      (fun y => by simpa using hφbd (y * I)) Real.pi_pos
      (fun n => hD0 n _ (hsumφ n)) t ht
    simpa [φ] using hzero
  -- The identity theorem.
  have hDan : AnalyticOnNhd ℂ D univ := hD.differentiableOn.analyticOnNhd_of_finiteDimensional
    isOpen_univ
  set b₁ : ι → ℂ := fun _ => (s₀ - 1) / k
  have hW : IsOpen {b : ι → ℂ | (∑ i, b i).re < s₀.re} :=
    isOpen_lt (continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_apply i))
      continuous_const
  have hb₁ : (∑ i, b₁ i).re < s₀.re := by
    have : ∑ i, b₁ i = s₀ - 1 := by
      simp only [b₁, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hkc]
      field_simp
    rw [this, sub_re, one_re]
    linarith
  have hev : D =ᶠ[𝓝 b₁] 0 := by
    filter_upwards [hW.mem_nhds hb₁] with b hb
    exact hleft b (le_of_lt hb)
  have hDz := hDan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ b₁) hev
  funext b
  have := hDz (mem_univ b)
  simp only [D, Pi.zero_apply, sub_eq_zero] at this
  exact this.symm

/-- **Global necessity.** For a kernel smooth near the simplex and vanishing at the points with a
coordinate below `δ > 0`, the simplex Mellin transform is entire, satisfies the sum-shift equation
and the bound `‖S_g(b)‖ ≤ ‖g‖₁ ∏ i, max 1 (δ ^ (Re b i - 1))`, and has Paley–Wiener bounds for
the box `|w j| ≤ |log δ|` on every hyperplane `∑ b = s`. -/
theorem simplexMoment_necessity {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g) {δ : ℝ}
    (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    Differentiable ℂ (fun b => simplexMoment b g) ∧
      (∀ b, simplexMoment b g = ∑ i, simplexMoment (b + Pi.single i 1) g) ∧
      (∀ b, ‖simplexMoment b g‖ ≤
        (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ‖g u‖ ∂stdSimplexMeasure) *
          ∏ i, max 1 (δ ^ ((b i).re - 1))) ∧
      ∀ (i₀ : ι) (s : ℂ) (N : ℕ), ∃ C, ∀ ζ : {j : ι // j ≠ i₀} → ℂ,
        ‖simplexMoment (hyperplaneParam i₀ s fun j => -(2 * π * I) * ζ j) g‖ ≤
          C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, |Real.log δ| * |(ζ j).im|) :=
  ⟨differentiable_simplexMoment hgs.continuousOn hδ hgsupp,
    simplexMoment_eq_sum hgs.continuousOn hδ hgsupp,
    norm_integral_monomial_mul_le_of_vanish hgs.continuousOn hδ hgsupp,
    fun i₀ s N => norm_integral_hyperplane_le i₀ hgs hδ hgsupp s N⟩

/-- **Paley–Wiener description of the image.** Fix `i₀` and `s₀`. A function `S` on `ℂ^ι` is the
simplex Mellin transform `b ↦ ∫_Δ ∏ u^(b - 1) g` of a kernel `g` smooth near the simplex and
vanishing near its faces if and only if
* `S` is entire,
* `S` satisfies the sum-shift equation `S(b) = ∑ i, S(b + e i)`,
* `‖S b‖ ≤ C ∏ i, max 1 (δ ^ (Re b i - 1))` for some `C` and `δ > 0`, and
* on the hyperplane `∑ b = s₀`, `ζ ↦ S(b(-2πi ζ))` has Paley–Wiener bounds for some box. -/
theorem exists_kernel_iff (i₀ : ι) (s₀ : ℂ) (S : (ι → ℂ) → ℂ) :
    (∃ g : (ι → ℝ) → ℂ, SmoothNearStdSimplex g ∧
      (∃ δ > 0, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) ∧
      (fun b => simplexMoment b g) = S) ↔
    Differentiable ℂ S ∧ (∀ b, S b = ∑ i, S (b + Pi.single i 1)) ∧
      (∃ C δ : ℝ, 0 < δ ∧ ∀ b, ‖S b‖ ≤ C * ∏ i, max 1 (δ ^ ((b i).re - 1))) ∧
      ∃ ρ : {j : ι // j ≠ i₀} → ℝ, (∀ j, 0 ≤ ρ j) ∧ ∀ N : ℕ, ∃ C,
        ∀ ζ : {j : ι // j ≠ i₀} → ℂ,
          ‖S (hyperplaneParam i₀ s₀ fun j => -(2 * π * I) * ζ j)‖ ≤
            C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|) := by
  constructor
  · rintro ⟨g, hgs, ⟨δ, hδ, hv⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := simplexMoment_necessity hgs hδ hv
    exact ⟨h1, h2, ⟨_, δ, hδ, h3⟩, fun _ => |Real.log δ|, fun _ => abs_nonneg _,
      h4 i₀ s₀⟩
  · rintro ⟨hS, hshift, ⟨C, δ, hδ, hbd⟩, ρ, hρ, hpw⟩
    obtain ⟨g, -, hgs, hv, hg⟩ := exists_kernel_of_sum_shift i₀ s₀ hS hshift hδ hbd hρ hpw
    exact ⟨g, hgs, hv, hg⟩

end Dirichlet
