/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import Carlson.TwoVariable.Basic
public import Dirichlet.Average.CauchyCycle
public import Dirichlet.Transform.Euler

/-!
# The contour representation of the R-function

Carlson's Theorem 6.8-2 continues the R-function by the contour integral (6.8-7)
`R_{-a}(b, z)/Γ(c) = (2πi)⁻¹ ∫_γ R_{-1}(a, c - a; s - 1, s)/Γ(c) ∏ (1 - s + s zᵢ)^(-bᵢ) ds`,
where `γ` surrounds the unit segment inside the domain of the product. In the Euler strip the
R-function is the two-node Dirichlet average of the product with parameters `(a, c - a)` at the
nodes `1, 0`, and the cycle form of Representation 5.11-2 gives the contour integral. The
continued resolvent then makes both sides entire in `(a, b)`, and the identity theorem removes
the strip.

The contour is an arbitrary `C¹` cycle homologous to zero in the domain of the product, avoiding
the unit segment and with nonzero index `m` on it; Carlson's positively oriented ellipse with
foci `0, 1` has `m = 1`.

## Main results

* `Carlson.TwoVariable.regCarlsonDirichletAverage_pair_eq`: two-node averages as Euler integrals.
* `Carlson.regCarlsonR_neg_eq_regCarlsonDirichletAverage`: the R-function as a two-node average
  in the Euler strip.
* `Carlson.regCarlsonR_neg_eq_cycleIntegral_native`: formula (6.8-7) in the Euler strip.
* `Carlson.regCarlsonR_neg_eq_cycleIntegral`: formula (6.8-7) for all complex `a, b`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.8.
-/

open Dirichlet
open Set MeasureTheory Filter ContinuousLinearMap Complex
open scoped unitInterval Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The regularized Dirichlet average over two nodes is an Euler integral. -/
theorem regCarlsonDirichletAverage_pair_eq (a a' X Y : ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage (pair a a') (pair X Y) f =
      regEulerIntegral a a' (fun u : ℝ => f ((u : ℂ) * X + (1 - u : ℂ) * Y)) := by
  rw [← regDirichletIntegral_fin_two]
  unfold regCarlsonDirichletAverage
  apply regDirichletIntegral_congr
  intro u hu
  have hs := (Convexity.StdSimplex.mem_coordinateSet.mp hu).2
  simp only [Fin.sum_univ_two] at hs
  simp only [carlsonAffineForm, Fin.sum_univ_two, pair_zero, pair_one]
  rw [show (u 1 : ℂ) = 1 - u 0 by rw [show u 1 = 1 - u 0 by linarith]; push_cast; ring]

/-- The convex hull of the two nodes `1, 0` is the unit segment. -/
theorem convexHull_range_pair_one_zero :
    convexHull ℝ (Set.range (pair (1 : ℂ) 0)) = segment ℝ (0 : ℂ) 1 := by
  have h : Set.range (pair (1 : ℂ) 0) = {1, 0} := by
    ext x; simp [pair, or_comm]
  rw [h, convexHull_pair, segment_symm]

end Carlson.TwoVariable

namespace Carlson
open TwoVariable
variable {ι : Type*} [Fintype ι]

/-- The holomorphy domain of the product `∏ (1 - s + s zᵢ)^(-bᵢ)` in `s`. -/
def carlsonSegmentDomain (z : ι → ℂ) : Set ℂ := {s | ∀ i, 1 - s + s * z i ∈ slitPlane}

/-- The segment domain is open. -/
theorem isOpen_carlsonSegmentDomain (z : ι → ℂ) : IsOpen (carlsonSegmentDomain z) := by
  rw [show carlsonSegmentDomain z = ⋂ i, {s | 1 - s + s * z i ∈ slitPlane} by
    ext s; simp [carlsonSegmentDomain]]
  exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)

omit [Fintype ι] in
/-- For slit-plane nodes the segment domain contains the unit segment. -/
theorem segment_subset_carlsonSegmentDomain {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    segment ℝ (0 : ℂ) 1 ⊆ carlsonSegmentDomain z := by
  intro s hs i
  rw [segment_eq_image] at hs
  obtain ⟨θ, hθ, rfl⟩ := hs
  have h := carlsonRSegment_mem_slitPlane hz hθ i
  simpa [Complex.real_smul, sub_eq_add_neg, add_comm, add_left_comm] using h


/-- The product `∏ (1 - s + s zᵢ)^(-bᵢ)` of Carlson's single-integral representation. -/
def carlsonSegmentProduct (b z : ι → ℂ) (s : ℂ) : ℂ :=
  ∏ i, (1 - s + s * z i) ^ (-b i)

/-- The segment product is holomorphic on the segment domain. -/
theorem differentiableOn_carlsonSegmentProduct (b z : ι → ℂ) :
    DifferentiableOn ℂ (carlsonSegmentProduct b z) (carlsonSegmentDomain z) := by
  intro s hs
  refine (DifferentiableAt.differentiableWithinAt ?_)
  unfold carlsonSegmentProduct
  refine DifferentiableAt.fun_finsetProd fun i _ => ?_
  exact ((differentiableAt_const _).sub differentiableAt_id |>.add
    (differentiableAt_id.mul (differentiableAt_const _))).cpow (differentiableAt_const _) (hs i)

/-- In the Euler strip, the regularized R-function is the two-node Dirichlet average of the
segment product with parameters `(a, c - a)` at the nodes `1, 0` (Carlson (6.8-2)). -/
theorem regCarlsonR_neg_eq_regCarlsonDirichletAverage {a : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (hca : 0 < (∑ i, b i - a).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR (-a) b z =
      regCarlsonDirichletAverage (pair a (∑ i, b i - a)) (pair 1 0)
          (carlsonSegmentProduct b z) := by
  rw [regCarlsonR_eq_unitIntervalIntegral (by simpa using ha)
    (by rw [← sub_eq_add_neg]; exact hca) hz, regCarlsonDirichletAverage_pair_eq,
    regEulerIntegral, neg_neg, ← sub_eq_add_neg, carlsonRUnitIntervalIntegral]
  rw [mul_inv]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [carlsonSegmentProduct, mul_one, mul_zero, add_zero]

/-- **Theorem 6.8-2, formula (7)** in regularized form on `C¹` cycles, in the Euler strip: for
slit-plane nodes and a `C¹` cycle homologous to zero in the domain of the segment product,
avoiding the unit segment and with index `m ≠ 0` on it,
`R_{-a}(b, z)/Γ(c) = (2πi m)⁻¹ ∫_Γ R_{-1}(a, c - a; s - 1, s)/Γ(c) ∏ (1 - s + s zᵢ)^(-bᵢ) ds`. -/
theorem regCarlsonR_neg_eq_cycleIntegral_native {a : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (hca : 0 < (∑ i, b i - a).re) (hz : z ∈ carlsonRSlitDomain)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ carlsonSegmentDomain z)
    (hind : ∀ w, w ∉ carlsonSegmentDomain z → Γ.index w = 0)
    (havoid : Γ.range ⊆ (segment ℝ (0 : ℂ) 1)ᶜ) {m : ℂ} (hm0 : m ≠ 0)
    (hm : ∀ w ∈ segment ℝ (0 : ℂ) 1, Γ.index w = m) :
    regCarlsonR (-a) b z = m⁻¹ * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun s =>
      toSpanSingleton ℂ (regCarlsonResolvent 0 (pair a (∑ i, b i - a)) (pair 1 0) s *
        carlsonSegmentProduct b z s))) := by
  have hbc : pair a (∑ i, b i - a) ∈ mvBetaConvergent := fun i => by
    fin_cases i
    · exact ha
    · exact hca
  have h := regCarlsonDirichletAverage_iteratedDeriv_eq_cycleIntegral 0 hbc (pair 1 0)
    (isOpen_carlsonSegmentDomain z) Γ hΓ hΓU hind
    (by rw [convexHull_range_pair_one_zero]; exact segment_subset_carlsonSegmentDomain hz)
    (by rw [convexHull_range_pair_one_zero]; exact havoid)
    (fun w hw => hm w (by rwa [convexHull_range_pair_one_zero] at hw))
    (differentiableOn_carlsonSegmentProduct b z)
  rw [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at h
  rw [regCarlsonR_neg_eq_regCarlsonDirichletAverage ha hca hz, h, ← mul_assoc,
    inv_mul_cancel₀ hm0, one_mul]


/-- **Theorem 6.8-2, formula (7)**, for all complex `a` and `b`, in regularized form on `C¹`
cycles: with the continued resolvent,
`R_{-a}(b, z)/Γ(c) = (2πi m)⁻¹ ∫_Γ R_{-1}(a, c - a; s - 1, s)/Γ(c) ∏ (1 - s + s zᵢ)^(-bᵢ) ds`,
for slit-plane nodes and a `C¹` cycle homologous to zero in the domain of the segment product,
avoiding the unit segment and with index `m ≠ 0` on it. -/
theorem regCarlsonR_neg_eq_cycleIntegral [Nonempty ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ carlsonSegmentDomain z)
    (hind : ∀ w, w ∉ carlsonSegmentDomain z → Γ.index w = 0)
    (havoid : Γ.range ⊆ (segment ℝ (0 : ℂ) 1)ᶜ) {m : ℂ} (hm0 : m ≠ 0)
    (hm : ∀ w ∈ segment ℝ (0 : ℂ) 1, Γ.index w = m) :
    regCarlsonR (-a) b z = m⁻¹ * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun s =>
      toSpanSingleton ℂ (continuedRegCarlsonResolvent 0 (pair a (∑ i, b i - a)) (pair 1 0) s *
        carlsonSegmentProduct b z s))) := by
  set E := ℂ × (ι → ℂ)
  have havoid' : Γ.range ⊆ (convexHull ℝ (Set.range (pair (1 : ℂ) 0)))ᶜ := by
    rw [convexHull_range_pair_one_zero]; exact havoid
  -- the right side is entire in `(a, b)`
  set W : Set (E × ℂ) := {q | (q.2, pair (1 : ℂ) 0) ∈ carlsonResolventDomain ∧
    q.2 ∈ carlsonSegmentDomain z}
  have hH : AnalyticOnNhd ℂ (fun q : E × ℂ => continuedRegCarlsonResolvent 0
      (pair q.1.1 (∑ i, q.1.2 i - q.1.1)) (pair 1 0) q.2 * carlsonSegmentProduct q.1.2 z q.2)
          W := by
    intro q hq
    have ha : AnalyticAt ℂ (fun q : E × ℂ => q.1.1) q :=
      ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).comp (ContinuousLinearMap.fst ℂ E ℂ)).analyticAt q
    have hb : ∀ i, AnalyticAt ℂ (fun q : E × ℂ => q.1.2 i) q := fun i =>
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).comp (ContinuousLinearMap.fst ℂ E ℂ)).analyticAt q
    have hpar : AnalyticAt ℂ (fun q : E × ℂ => pair q.1.1 (∑ i, q.1.2 i - q.1.1)) q := by
      apply analyticAt_pi_iff.mpr
      intro i; fin_cases i
      · exact ha
      · exact (Finset.analyticAt_fun_sum _ fun i _ => hb i).sub ha
    have h1 := (analyticOnNhd_continuedRegCarlsonResolvent 0
      (pair q.1.1 (∑ i, q.1.2 i - q.1.1), q.2, pair (1 : ℂ) 0) ⟨mem_univ _, hq.1⟩).comp_of_eq
      (hpar.prod (analyticAt_snd.prod analyticAt_const)) rfl
    have h2 : AnalyticAt ℂ (fun q : E × ℂ => carlsonSegmentProduct q.1.2 z q.2) q := by
      unfold carlsonSegmentProduct
      refine Finset.analyticAt_fun_prod _ fun i _ => ?_
      exact ((analyticAt_const.sub analyticAt_snd).add (analyticAt_snd.mul analyticAt_const)).cpow
        (hb i).neg (hq.2 i)
    exact h1.mul h2
  have hmem : ∀ i (t : ℝ), (Γ.loop i).2.extend t ∈ Γ.range := fun i t =>
    Γ.loop_extend_mem_range i t
  have hWmem : ∀ i (t : ℝ), ∀ x : E, (x, (Γ.loop i).2.extend t) ∈ W := fun i t x =>
    ⟨mem_carlsonResolventDomain_of_not_mem_convexHull (havoid' (hmem i t)), hΓU (hmem i t)⟩
  have hG : AnalyticOnNhd ℂ (fun x : E => m⁻¹ * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Γ.integral (fun s => toSpanSingleton ℂ (continuedRegCarlsonResolvent 0
        (pair x.1 (∑ i, x.2 i - x.1)) (pair 1 0) s * carlsonSegmentProduct x.2 z s)))) univ := by
    refine fun x hx => analyticAt_const.mul (analyticAt_const.mul ?_)
    unfold Cycle.integral
    refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
    set γ := (Γ.loop i).2
    have hγc : ContinuousOn γ.extend (Icc (0 : ℝ) 1) := γ.continuous_extend.continuousOn
    have hd : ContinuousOn (fun t => derivWithin γ.extend I t) (Icc (0 : ℝ) 1) :=
      (hΓ i).continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
    have hg : IntegrableOn (fun t : ℝ => derivWithin γ.extend I t) (Icc 0 1) :=
      hd.integrableOn_compact isCompact_Icc
    have hint := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc hg hγc
      isOpen_univ hH (fun x _ t _ => hWmem i t x)
    refine (hint x hx).congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
    rw [curveIntegralFun_def]
    simp only [toSpanSingleton_apply, smul_eq_mul]
  have hF : AnalyticOnNhd ℂ (fun x : E => regCarlsonR (-x.1) x.2 z) univ := fun x _ =>
    analyticAt_regCarlsonR_comp analyticAt_fst.neg analyticAt_snd analyticAt_const hz
  -- agreement on the Euler strip
  set O : Set E := {x | 0 < x.1.re ∧ 0 < (∑ i, x.2 i - x.1).re}
  have hO : IsOpen O := by
    refine (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp ?_))
    exact (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd).sub
      continuous_fst
  set x₀ : E := (1, fun _ => 2)
  have hx₀ : x₀ ∈ O := by
    refine ⟨by simp [x₀], ?_⟩
    have hcard : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    simp [x₀, Finset.sum_const]
    linarith
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_univ (mem_univ x₀) (by
    filter_upwards [hO.mem_nhds hx₀] with x hx
    rw [regCarlsonR_neg_eq_cycleIntegral_native hx.1 hx.2 hz Γ hΓ hΓU hind havoid hm0 hm]
    congr 2
    refine Γ.integral_congr fun s hs => ?_
    rw [continuedRegCarlsonResolvent_eq_native 0 (fun i => by fin_cases i; exacts [hx.1, hx.2])
      (mem_carlsonResolventDomain_of_not_mem_convexHull (havoid' hs))])
  exact heq (mem_univ (a, b))

end Carlson
