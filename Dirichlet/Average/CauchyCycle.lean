/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Cauchy
public import Dirichlet.Average.CauchyContinuation
public import ComplexAnalysis.Cycle.Cauchy

/-!
# Averages of Cauchy's integral formula on cycles

Carlson's Representation 5.11-2 expresses the Dirichlet average of `f⁽ⁿ⁾` as a contour integral
of `f` against the R-function `R_{-n-1}(b, s - z)`. The circle case is
`Dirichlet.Average.Cauchy`. Here the contour is an arbitrary `C¹` cycle `Γ` in an open set `U` on
which `f` is holomorphic, homologous to zero in `U` and avoiding the convex hull of the nodes;
the formula carries the index `m` of `Γ` on the hull, so a positively oriented Jordan curve
enclosing the hull gives Carlson's statement. For nonzero index the continued resolvent gives
the entire regularized continuation in the Dirichlet parameters, the contour form of 6.3-6.

Cauchy's formula for derivatives on cycles is derived first: differentiation under the cycle
integral raises the order of the Cauchy kernel, and the order-zero homology form of Cauchy's
formula identifies the result.

## Main results

* `Complex.Cycle.hasDerivAt_integral_kernel`: differentiation under a cycle integral.
* `Complex.Cycle.factorial_mul_integral_cauchyKernel`: Cauchy's formula for derivatives on
  cycles homologous to zero.
* `Dirichlet.cycleIntegral_regDirichletIntegral`: Fubini for a cycle and the simplex.
* `Dirichlet.regCarlsonDirichletAverage_iteratedDeriv_eq_cycleIntegral`: Representation 5.11-2
  on cycles.
* `Dirichlet.isRegCarlsonContinuation_cycleIntegral`: the continued cycle representation for
  all complex parameters.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§5.11, 6.3.
* J. B. Conway, *Functions of One Complex Variable I*, Theorem IV.5.4.
-/

public noncomputable section

open Set MeasureTheory Metric Filter ContinuousLinearMap Complex
open scoped unitInterval Topology

namespace Complex.Cycle

variable (Γ : Cycle)

/-- Differentiation under the integral sign for a cycle integral of a kernel depending
holomorphically on a parameter. -/
theorem hasDerivAt_integral_kernel (hΓ : Γ.IsC1) {U V : Set ℂ} (hU : IsOpen U)
    (hΓV : Γ.range ⊆ V) {K K' : ℂ → ℂ → ℂ}
    (hK : ContinuousOn (fun p : ℂ × ℂ ↦ K p.1 p.2) (U ×ˢ V))
    (hK' : ContinuousOn (fun p : ℂ × ℂ ↦ K' p.1 p.2) (U ×ˢ V))
    (hd : ∀ z ∈ U, ∀ w ∈ V, HasDerivAt (fun z ↦ K z w) (K' z w) z) {x : ℂ} (hx : x ∈ U) :
    HasDerivAt (fun z ↦ Γ.integral (fun w ↦ toSpanSingleton ℂ (K z w)))
      (Γ.integral (fun w ↦ toSpanSingleton ℂ (K' x w))) x := by
  unfold Cycle.integral
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  set γ := (Γ.loop i).2
  have hγ := hΓ i
  have hV : ∀ t : ℝ, γ.extend t ∈ V := fun t ↦ hΓV (Γ.loop_extend_mem_range i t)
  have hrepr : ∀ G : ℂ → ℂ, curveIntegral (fun w ↦ toSpanSingleton ℂ (G w)) γ =
      ∫ t in Icc (0 : ℝ) 1, derivWithin γ.extend I t * G (γ.extend t) := by
    intro G
    rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
    simp [curveIntegralFun_def, toSpanSingleton_apply, smul_eq_mul]
  simp only [hrepr]
  have hder : ContinuousOn (derivWithin γ.extend I) (Icc 0 1) :=
    hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hint : IntegrableOn (derivWithin γ.extend I) (Icc (0 : ℝ) 1) :=
    hder.integrableOn_compact isCompact_Icc
  have hmap : ContinuousOn (fun p : ℂ × ℝ ↦ (p.1, γ.extend p.2)) (U ×ˢ Icc 0 1) :=
    (continuous_fst.prodMk (γ.continuous_extend.comp continuous_snd)).continuousOn
  have hmaps : MapsTo (fun p : ℂ × ℝ ↦ (p.1, γ.extend p.2)) (U ×ˢ Icc 0 1) (U ×ˢ V) :=
    fun p hp ↦ ⟨hp.1, hV p.2⟩
  exact hasDerivAt_integral_mul_of_continuousOn_compact isCompact_Icc hint hU hx
    (F := fun z t ↦ K z (γ.extend t)) (F' := fun z t ↦ K' z (γ.extend t))
    (hK.comp hmap hmaps) (hK'.comp hmap hmaps) fun z hz t _ ↦ hd z hz _ (hV t)

/-- The Cauchy kernel of order `k + 1` on a cycle, as a function of the evaluation point. -/
noncomputable def cauchyKernelIntegral (f : ℂ → ℂ) (k : ℕ) (ζ : ℂ) : ℂ :=
  Γ.integral (fun s ↦ toSpanSingleton ℂ (f s * (s - ζ) ^ (-(k + 1 : ℤ))))

/-- Off the cycle, differentiating the Cauchy kernel integral raises the order. -/
theorem hasDerivAt_cauchyKernelIntegral (hΓ : Γ.IsC1) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.range) (k : ℕ) {ζ : ℂ} (hζ : ζ ∉ Γ.range) :
    HasDerivAt (Γ.cauchyKernelIntegral f k) ((k + 1) * Γ.cauchyKernelIntegral f (k + 1) ζ) ζ := by
  have hne : ∀ p ∈ Γ.rangeᶜ ×ˢ Γ.range, p.2 - p.1 ≠ 0 := fun p hp h ↦
    hp.1 (by rw [← sub_eq_zero.mp h]; exact hp.2)
  have hK : ∀ m : ℤ, ContinuousOn (fun p : ℂ × ℂ ↦ f p.2 * (p.2 - p.1) ^ m)
      (Γ.rangeᶜ ×ˢ Γ.range) := fun m ↦
    (hf.comp continuous_snd.continuousOn fun p hp ↦ hp.2).mul
      ((continuous_snd.sub continuous_fst).continuousOn.zpow₀ m fun p hp ↦ Or.inl (hne p hp))
  have h := Γ.hasDerivAt_integral_kernel hΓ Γ.isOpen_compl_range subset_rfl
    (K := fun z s ↦ f s * (s - z) ^ (-((k : ℤ) + 1)))
    (K' := fun z s ↦ (k + 1) * (f s * (s - z) ^ (-((k : ℤ) + 1) - 1)))
    (hK _) ((continuousOn_const.mul (hK _))) (fun z hz s hs ↦ by
      have hsz : s - z ≠ 0 := hne (z, s) ⟨hz, hs⟩
      have h1 := (hasDerivAt_zpow (-((k : ℤ) + 1)) (s - z) (Or.inl hsz)).comp z
        ((hasDerivAt_id z).const_sub s)
      convert h1.const_mul (f s) using 1
      simp only [Function.comp_def]
      push_cast
      ring) hζ
  have hsm : (Γ.integral fun w ↦ toSpanSingleton ℂ ((k + 1 : ℂ) * (f w * (w - ζ) ^
      (-((k : ℤ) + 1) - 1)))) = (k + 1 : ℂ) * Γ.integral (fun w ↦ toSpanSingleton ℂ
        (f w * (w - ζ) ^ (-((k : ℤ) + 1) - 1))) := by
    rw [← smul_eq_mul, ← Cycle.integral_smul]; congr 1; funext w; ext; simp [smul_eq_mul]
  rw [hsm] at h
  unfold cauchyKernelIntegral
  convert h using 4
  push_cast
  ring_nf

/-- Iterated derivatives of the order-one Cauchy kernel integral. -/
theorem iteratedDeriv_cauchyKernelIntegral (hΓ : Γ.IsC1) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.range) (n : ℕ) {ζ : ℂ} (hζ : ζ ∉ Γ.range) :
    iteratedDeriv n (Γ.cauchyKernelIntegral f 0) ζ =
      n.factorial * Γ.cauchyKernelIntegral f n ζ := by
  induction n generalizing ζ with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (Γ.cauchyKernelIntegral f 0) =ᶠ[𝓝 ζ]
        fun ξ ↦ n.factorial * Γ.cauchyKernelIntegral f n ξ := by
      filter_upwards [Γ.isOpen_compl_range.mem_nhds hζ] with ξ hξ using ih hξ
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((Γ.hasDerivAt_cauchyKernelIntegral hΓ hf n hζ).const_mul _).deriv, Nat.factorial_succ]
    push_cast; ring

/-- **Cauchy's formula for derivatives on cycles.** For a `C¹` cycle homologous to zero in an
open set `U` and `f` holomorphic on `U`,
`n!/(2πi) ∫_Γ f(s) (s - ζ)^{-n-1} ds = ind(Γ, ζ) f⁽ⁿ⁾(ζ)` at every point `ζ ∈ U` off the
cycle. -/
theorem factorial_mul_integral_cauchyKernel {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (n : ℕ) {ζ : ℂ} (hζ : ζ ∈ U) (hζΓ : ζ ∉ Γ.range) :
    (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.cauchyKernelIntegral f n ζ =
      Γ.index ζ * iteratedDeriv n f ζ := by
  have hfc : ContinuousOn f Γ.range := hf.continuousOn.mono hΓU
  -- the order-one integral is the index times `f` near `ζ`
  set m := Γ.index ζ
  have hW : ∀ᶠ ξ in 𝓝 ζ, ξ ∈ U ∧ ξ ∉ Γ.range ∧ Γ.index ξ = m := by
    have h1 := hU.mem_nhds hζ
    have h2 := Γ.isOpen_compl_range.mem_nhds hζΓ
    have h3 := (Γ.isOpen_setOf_index_eq hΓ m).mem_nhds ⟨hζΓ, rfl⟩
    filter_upwards [h1, h2, h3] with ξ a b c using ⟨a, b, c.2⟩
  have he : Γ.cauchyKernelIntegral f 0 =ᶠ[𝓝 ζ] fun ξ ↦ (2 * (Real.pi : ℂ) * Complex.I * m) *
      f ξ := by
    filter_upwards [hW] with ξ ⟨hξU, hξΓ, hξm⟩
    have h := Γ.integral_sub_inv_smul_eq_index_smul hU hΓ hΓU hind hf hξU hξΓ
    rw [hξm, smul_eq_mul] at h
    rw [← h, cauchyKernelIntegral]
    congr 1; funext s; ext
    simp [smul_eq_mul, zpow_neg, mul_comm]
  have hd := Γ.iteratedDeriv_cauchyKernelIntegral hΓ hfc n hζΓ
  rw [he.iteratedDeriv_eq, iteratedDeriv_const_mul_field] at hd
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [mul_comm (n.factorial : ℂ), mul_assoc, ← hd]
  field_simp

end Complex.Cycle

namespace Dirichlet
open Complex
variable {ι : Type*} [Fintype ι]

/-- A kernel continuous on a cycle times the simplex may be integrated in either order against a
native regularized Dirichlet density. -/
theorem cycleIntegral_regDirichletIntegral (Γ : Cycle) (hΓ : Γ.IsC1) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {F : ℂ → (ι → ℝ) → ℂ}
    (hF : ContinuousOn (fun p : ℂ × (ι → ℝ) => F p.1 p.2)
      (Γ.range ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Γ.integral (fun s => toSpanSingleton ℂ (regDirichletIntegral b (F s))) =
      regDirichletIntegral b (fun u => Γ.integral (fun s => toSpanSingleton ℂ (F s u))) := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := MeasureTheory.Measure.stdSimplexMeasure (ι := ι)
  have hK : IsCompact K := Convexity.StdSimplex.isCompact_coordinateSet ℝ ι
  have hd : IntegrableOn (regDirichletDensity b) K μ :=
    integrableOn_regDirichletDensity b hb
  -- each loop separately
  have hloop : ∀ i, curveIntegral (fun s => toSpanSingleton ℂ (regDirichletIntegral b (F s)))
      (Γ.loop i).2 = regDirichletIntegral b
        (fun u => curveIntegral (fun s => toSpanSingleton ℂ (F s u)) (Γ.loop i).2) ∧
      IntegrableOn (fun u => regDirichletDensity b u *
        curveIntegral (fun s => toSpanSingleton ℂ (F s u)) (Γ.loop i).2) K μ := by
    intro i
    set γ := (Γ.loop i).2
    have hrepr : ∀ G : ℂ → ℂ, curveIntegral (fun w ↦ toSpanSingleton ℂ (G w)) γ =
        ∫ t in Icc (0 : ℝ) 1, derivWithin γ.extend I t * G (γ.extend t) := by
      intro G
      rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
      simp [curveIntegralFun_def, toSpanSingleton_apply, smul_eq_mul]
    simp only [hrepr]
    have hbase : IntegrableOn (fun p : ℝ × (ι → ℝ) => regDirichletDensity b p.2)
        (Icc 0 1 ×ˢ K) (volume.prod μ) := by
      rw [IntegrableOn, ← Measure.prod_restrict]
      simpa only [one_mul] using
        (integrableOn_const isCompact_Icc.measure_ne_top :
          IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc 0 1)).mul_prod hd
    have hder : ContinuousOn (derivWithin γ.extend I) (Icc 0 1) :=
      (hΓ i).continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
    have hkernel : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
        derivWithin γ.extend I p.1 * F (γ.extend p.1) p.2) (Icc 0 1 ×ˢ K) := by
      apply ContinuousOn.mul
      · exact hder.comp continuous_fst.continuousOn fun p hp => hp.1
      · exact hF.comp ((γ.continuous_extend.comp continuous_fst).prodMk
          continuous_snd).continuousOn
          (fun p hp => ⟨Γ.loop_extend_mem_range i p.1, hp.2⟩)
    have hint := hbase.mul_continuousOn hkernel (isCompact_Icc.prod hK)
    rw [IntegrableOn, ← Measure.prod_restrict] at hint
    have hswap := integral_integral_swap
      (f := fun t u => regDirichletDensity b u *
        (derivWithin γ.extend I t * F (γ.extend t) u)) hint
    refine ⟨?_, ?_⟩
    · simpa only [regDirichletIntegral, smul_eq_mul, ← integral_const_mul, mul_left_comm, K, μ]
        using hswap
    · have h2 := hint.integral_prod_right
      simp only [integral_const_mul] at h2
      exact h2
  unfold Cycle.integral
  simp only [fun i => (hloop i).1]
  unfold regDirichletIntegral
  rw [← integral_finsetSum _ (fun i _ => (hloop i).2)]
  congr 1; funext u; rw [Finset.mul_sum]


/-- **Representation 5.11-2** on `C¹` cycles, for every derivative order: if `f` is
holomorphic on an open set `U` containing the convex hull of the variables, and `Γ` is a `C¹`
cycle in `U` avoiding that hull, homologous to zero in `U`, with index `m` on the hull, then
`n!/(2πi) ∫_Γ f(s) R_{-n-1}(b, s - z) ds = m F⁽ⁿ⁾(b, z)`, in regularized form. For a
positively oriented Jordan curve enclosing the hull, `m = 1`. -/
theorem regCarlsonDirichletAverage_iteratedDeriv_eq_cycleIntegral (n : ℕ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) {U : Set ℂ} (hU : IsOpen U) (Γ : Cycle)
    (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    (hhull : convexHull ℝ (Set.range z) ⊆ U)
    (havoid : Γ.range ⊆ (convexHull ℝ (Set.range z))ᶜ) {m : ℂ}
    (hm : ∀ w ∈ convexHull ℝ (Set.range z), Γ.index w = m) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Γ.integral (fun s => toSpanSingleton ℂ (regCarlsonResolvent n b z s * f s)) =
      m * regCarlsonDirichletAverage b z (iteratedDeriv n f) := by
  have hF : ContinuousOn (fun p : ℂ × (ι → ℝ) => carlsonCauchyKernel n z p.2 p.1 * f p.1)
      (Γ.range ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    ((continuousOn_carlsonCauchyKernel n z).mono (fun _ hp => ⟨havoid hp.1, hp.2⟩)).mul
      ((hf.continuousOn.mono hΓU).comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have hres : ∀ s, regCarlsonResolvent n b z s * f s =
      regDirichletIntegral b (fun u => carlsonCauchyKernel n z u s * f s) := by
    intro s
    rw [regCarlsonResolvent_eq_regDirichletIntegral]
    unfold regDirichletIntegral
    rw [← integral_mul_const]
    congr 1; funext u; ring
  simp only [hres]
  rw [cycleIntegral_regDirichletIntegral Γ hΓ hb hF]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet fun u hu => ?_
  dsimp only
  have hmem := carlsonAffineForm_mem_convexHull z hu
  have hζΓ : carlsonAffineForm z u ∉ Γ.range := fun h => havoid h hmem
  have hc := Γ.factorial_mul_integral_cauchyKernel hU hΓ hΓU hind hf n (hhull hmem) hζΓ
  rw [hm _ hmem] at hc
  have heq : Γ.integral (fun s => toSpanSingleton ℂ (carlsonCauchyKernel n z u s * f s)) =
      Γ.cauchyKernelIntegral f n (carlsonAffineForm z u) := by
    unfold Cycle.cauchyKernelIntegral carlsonCauchyKernel
    congr 1; funext s; rw [mul_comm]
  rw [heq]
  linear_combination (regDirichletDensity b u) * hc


/-- The continued resolvent integrated against a continuous function over a `C¹` cycle avoiding
the convex hull of the nodes is entire in the Dirichlet parameters. -/
theorem analyticOnNhd_cycleIntegral_continuedRegCarlsonResolvent (n : ℕ) (z : ι → ℂ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (convexHull ℝ (Set.range z))ᶜ) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.range) :
    AnalyticOnNhd ℂ (fun b : ι → ℂ => Γ.integral (fun s =>
      toSpanSingleton ℂ (continuedRegCarlsonResolvent n b z s * f s))) Set.univ := by
  set W : Set ((ι → ℂ) × ℂ) := {p | (p.2, z) ∈ carlsonResolventDomain}
  have hH : AnalyticOnNhd ℂ (fun p : (ι → ℂ) × ℂ =>
      continuedRegCarlsonResolvent n p.1 z p.2) W := by
    intro p hp
    exact (analyticOnNhd_continuedRegCarlsonResolvent n (p.1, p.2, z)
      ⟨mem_univ _, hp⟩).comp_of_eq (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)) rfl
  have hmem : ∀ i (t : ℝ), (Γ.loop i).2.extend t ∈ Γ.range := fun i t =>
    Γ.loop_extend_mem_range i t
  have hWmem : ∀ i (t : ℝ), ∀ b : ι → ℂ, (b, (Γ.loop i).2.extend t) ∈ W := fun i t b =>
    mem_carlsonResolventDomain_of_not_mem_convexHull (havoid (hmem i t))
  unfold Cycle.integral
  refine Finset.analyticOnNhd_fun_sum _ (fun i _ => ?_)
  set γ := (Γ.loop i).2
  have hγc : ContinuousOn γ.extend (Icc (0 : ℝ) 1) := γ.continuous_extend.continuousOn
  have hd : ContinuousOn (fun t => derivWithin γ.extend I t) (Icc (0 : ℝ) 1) :=
    (hΓ i).continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hg : IntegrableOn (fun t : ℝ => derivWithin γ.extend I t * f (γ.extend t))
      (Icc 0 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (hd.mul ?_)
    exact hf.comp hγc (fun t _ => hmem i t)
  have hint := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc hg hγc
    isOpen_univ hH (fun b _ t _ => hWmem i t b)
  refine hint.congr isOpen_univ (fun b _ => ?_)
  rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  rw [curveIntegralFun_def]
  simp only [toSpanSingleton_apply, smul_eq_mul]
  ring

/-- **Carlson's contour representation on cycles for all complex parameters** (the contour
form of 6.3-6): under the hypotheses of the cycle form of Representation 5.11-2 with nonzero
index `m`, `m⁻¹ n!/(2πi) ∫_Γ f(s) R_{-n-1}(b, s - z) ds` (continued resolvent) is the entire
regularized continuation of the derivative averages `F⁽ⁿ⁾(b, z)`. -/
theorem isRegCarlsonContinuation_cycleIntegral (n : ℕ) (z : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    (hhull : convexHull ℝ (Set.range z) ⊆ U)
    (havoid : Γ.range ⊆ (convexHull ℝ (Set.range z))ᶜ) {m : ℂ} (hm0 : m ≠ 0)
    (hm : ∀ w ∈ convexHull ℝ (Set.range z), Γ.index w = m) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    IsRegCarlsonContinuation (iteratedDeriv n f) z (fun b => m⁻¹ *
      ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun s =>
        toSpanSingleton ℂ (continuedRegCarlsonResolvent n b z s * f s)))) := by
  refine IsRegCarlsonContinuation.mk' ?_ ?_
  · intro b _
    exact analyticAt_const.mul (analyticAt_const.mul
      (analyticOnNhd_cycleIntegral_continuedRegCarlsonResolvent n z Γ hΓ havoid
        (hf.continuousOn.mono hΓU) b (mem_univ _)))
  · intro b hb
    have hcongr : Γ.integral (fun s => toSpanSingleton ℂ
        (continuedRegCarlsonResolvent n b z s * f s)) =
        Γ.integral (fun s => toSpanSingleton ℂ (regCarlsonResolvent n b z s * f s)) := by
      refine Γ.integral_congr fun s hs => ?_
      rw [continuedRegCarlsonResolvent_eq_native n hb
        (mem_carlsonResolventDomain_of_not_mem_convexHull (havoid hs))]
    simp only
    rw [hcongr, regCarlsonDirichletAverage_iteratedDeriv_eq_cycleIntegral n hb z hU Γ hΓ hΓU
      hind hhull havoid hm hf, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

end Dirichlet
