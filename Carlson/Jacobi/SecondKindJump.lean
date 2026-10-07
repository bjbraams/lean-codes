/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexSecondKind
public import Dirichlet.Average.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.Convex

/-!
# The jump of the second-kind functions for all parameters

Carlson proves the jump (7.8-5) of `qₙ` across the segment for `1 + α, 1 + β ∈ ℂ_>` and states
that it holds on `U₂` "by the permanence of functional relations". We prove it for all complex
`α, β`. Above and below the segment `[0, 1]` the regularized second-kind function is the
continuation, by Carlson's Theorem 8 (simply connected case), of the Dirichlet average of
`w ↦ w^{-n-1}` over the nodes `z - 1, z` on the rotated slit planes `i ℂ₀` and `-i ℂ₀`. These
continuations have boundary values at the cut that are entire in the Dirichlet parameters, so
their difference, known in the convergence range, is identified everywhere by the identity
theorem.

Carlson also sketches how orthogonality on the segment follows from biorthogonality by
collapsing the contour onto the cut. With the Cauchy representation (7.8-8) this becomes an
exchange of the circle and segment integrals followed by Cauchy's formula for `pₘ`.

## Main results

* `Carlson.TwoVariable.tendsto_jacobiSecondKind_sub_all`: the jump (7.8-5) on `[0, 1]` for all
  complex `α, β`.
* `Carlson.TwoVariable.tendsto_jacobiSecondKind_sub_all_affine`: the same at distinct complex
  endpoints.
* `Carlson.TwoVariable.jacobiCauchyCoefficient_mul_integral_eq_of_biorthogonality`: Carlson's
  deduction of orthogonality on the segment from biorthogonality on a contour around it.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.8,
  equation (5).
-/

open Complex Set Filter Dirichlet Polynomial MeasureTheory
open scoped Topology Pointwise

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- A rotated slit plane `c ℂ₀` is simply connected. -/
theorem isSimplyConnected_smul_slitPlane {c : ℂ} (hc : c ≠ 0) :
    IsSimplyConnected (c • slitPlane) := by
  rw [isSimplyConnected_smul_set₀_iff hc]
  have := starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
  exact (inferInstance : SimplyConnectedSpace slitPlane)

/-- Membership in a rotated slit plane. -/
theorem mem_smul_slitPlane {c z : ℂ} (hc : c ≠ 0) : z ∈ c • slitPlane ↔ c⁻¹ * z ∈ slitPlane := by
  rw [mem_smul_set_iff_inv_smul_mem₀ hc, smul_eq_mul]

/-- The joint continuation of the average of `w ↦ w^{-n-1}` on a rotated slit plane. -/
theorem exists_side_continuation {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    ∃ G : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ,
      IsJointRegCarlsonContinuationOn (c • slitPlane) (fun w => w ^ (-(n + 1 : ℤ))) G := by
  refine exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected
    (isOpen_slitPlane.smul₀ hc) (isSimplyConnected_smul_slitPlane hc) ?_ (Fin 2)
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mem_smul_slitPlane hc, mul_zero] at hw
    exact slitPlane_ne_zero hw rfl
  exact analyticAt_id.zpow hw0

/-- Off the segment, the continued resolvent with nodes `1, 0` is the side continuation at the
nodes `z - 1, z`, whenever that segment lies in the domain of the side continuation. -/
theorem continuedRegCarlsonResolvent_eq_side {D : Set ℂ} {n : ℕ}
    {G : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ}
    (hG : IsJointRegCarlsonContinuationOn D (fun w => w ^ (-(n + 1 : ℤ))) G) {z : ℂ}
    (hz : z ∉ segment ℝ (1 : ℂ) 0) (hD : segment ℝ (z - 1) z ⊆ D) (b : Fin 2 → ℂ) :
    continuedRegCarlsonResolvent n b (pair 1 0) z = G (b, pair (z - 1) z) := by
  have hdom : (z, pair (1 : ℂ) 0) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair])
  have h1 := isRegCarlsonContinuation_continuedRegCarlsonResolvent n hdom
  have hG2 := hG.isRegCarlsonContinuation (z := pair (z - 1) z)
    (by rwa [convexHull_range_pair])
  have h2 : IsRegCarlsonContinuation (fun w => (z - w) ^ (-(n + 1 : ℤ))) (pair 1 0)
      (fun b => G (b, pair (z - 1) z)) := by
    refine ⟨hG2.1, fun b hb => ?_⟩
    rw [hG2.2 hb]
    show regDirichletIntegral b _ = regDirichletIntegral b _
    apply regDirichletIntegral_congr
    intro u hu
    have h := carlsonAffineForm_affine hu (-1) z (pair 1 0)
    have hp : (fun i => -1 * pair (1 : ℂ) 0 i + z) = pair (z - 1) z := by
      funext i; fin_cases i <;> simp [pair]; ring
    rw [hp] at h
    simp only [h]
    ring_nf
  exact congrFun (h1.eq h2) b

/-- Points of the upper half-plane lie in `i ℂ₀`. -/
theorem mem_I_smul_slitPlane {w : ℂ} (hw : 0 < w.im ∨ (w.im = 0 ∧ w ≠ 0)) :
    w ∈ I • slitPlane := by
  rw [mem_smul_slitPlane I_ne_zero, inv_I, mem_slitPlane_iff]
  rcases hw with hw | ⟨hw, hw0⟩
  · left; simpa using hw
  · right
    have : w.re ≠ 0 := fun h => hw0 (Complex.ext h hw)
    simpa using this

/-- Points of the lower half-plane lie in `-i ℂ₀`. -/
theorem mem_neg_I_smul_slitPlane {w : ℂ} (hw : w.im < 0 ∨ (w.im = 0 ∧ w ≠ 0)) :
    w ∈ (-I) • slitPlane := by
  rw [mem_smul_slitPlane (neg_ne_zero.mpr I_ne_zero), inv_neg, inv_I, neg_neg,
    mem_slitPlane_iff]
  rcases hw with hw | ⟨hw, hw0⟩
  · left; simpa using hw
  · right
    have : w.re ≠ 0 := fun h => hw0 (Complex.ext h hw)
    simpa using this

/-- An entire function of one variable is determined by its values on `re z > -1`. -/
theorem eq_of_differentiable_of_re_gt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ z : ℂ, -1 < z.re → f z = g z) : f = g := by
  have hfa := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hev : f =ᶠ[𝓝 0] g := by
    have ho : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [ho.mem_nhds (by simp)] with z hz using h z hz
  funext z
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ (mem_univ 0) hev
    (mem_univ z)

/-- The jump density `-2πi (-1)ⁿ/(Γ(α + n + 1) Γ(β + n + 1)) x^α (1 - x)^β p̂ₙ(x)`, the
Gamma-regularized right side of (7.8-5). -/
def jacobiJumpDensity (α β : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) * I * ((-1 : ℂ) ^ n * ((Gamma (α + n + 1))⁻¹ * (Gamma (β + n + 1))⁻¹)) *
    (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ))

/-- The right side of (7.8-5) is `Γ(α + β + 2n + 2)` times the regularized jump density. -/
theorem jacobiCauchy_jump_eq (α β : ℂ) (n : ℕ) (x : ℝ) :
    -2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n *
        (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ)) =
      Gamma (α + n + 1 + (β + n + 1)) * jacobiJumpDensity α β n x := by
  simp only [jacobiCauchyCoefficient, jacobiJumpDensity, div_eq_mul_inv, mul_inv]
  ring

/-- The jump density is entire in `α`. -/
theorem differentiable_jacobiJumpDensity_left (β : ℂ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun α => jacobiJumpDensity α β n x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
  have hG : Differentiable ℂ fun α : ℂ => (Gamma (α + n + 1))⁻¹ :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold jacobiJumpDensity complexJacobiWeight shiftedJacobi jacobiCoeff
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  intro α
  have hc : DifferentiableAt ℂ (fun α : ℂ => (x : ℂ) ^ α) α :=
    (differentiableAt_id).const_cpow (Or.inl hx0)
  have hG' := hG α
  fun_prop

/-- The jump density is entire in `β`. -/
theorem differentiable_jacobiJumpDensity_right (α : ℂ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun β => jacobiJumpDensity α β n x := by
  have hx1 : (1 : ℂ) - x ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg re h; simp at this; linarith [hx.2]
  have hG : Differentiable ℂ fun β : ℂ => (Gamma (β + n + 1))⁻¹ :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold jacobiJumpDensity complexJacobiWeight shiftedJacobi jacobiCoeff
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  intro β
  have hc : DifferentiableAt ℂ (fun β : ℂ => (1 - (x : ℂ)) ^ β) β :=
    (differentiableAt_id).const_cpow (Or.inl hx1)
  have hG' := hG β
  fun_prop

/-- **The jump (7.8-5) for all complex parameters**: for every `α, β ∈ ℂ` and `x ∈ (0, 1)`,
`qₙ(x + iε) - qₙ(x - iε) → -2πi (-1)ⁿ Γ(α + β + 2n + 2)/(Γ(α + n + 1) Γ(β + n + 1))
x^α (1 - x)^β p̂ₙ(x)` as `ε → 0⁺`, where `p̂ₙ = shiftedJacobi α β n` and the second-kind
function has endpoints `1, 0`. -/
theorem tendsto_jacobiSecondKind_sub_all (α β : ℂ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β 1 0 n ((x : ℂ) + (c⁻¹ : ℝ) * I) -
      jacobiSecondKind α β 1 0 n ((x : ℂ) - (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (-2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n *
        (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ)))) := by
  obtain ⟨Gp, hGp⟩ := exists_side_continuation (c := I) I_ne_zero n
  obtain ⟨Gm, hGm⟩ := exists_side_continuation (c := -I) (neg_ne_zero.mpr I_ne_zero) n
  set P : Fin 2 → ℂ := pair ((x : ℂ) - 1) x
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
  have hx1 : (x : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg re h; simp at this; linarith [hx.2]
  have hPp : Set.range P ⊆ I • slitPlane := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact mem_I_smul_slitPlane (Or.inr ⟨by simp [P, pair], hx1⟩)
    · exact mem_I_smul_slitPlane (Or.inr ⟨by simp [P, pair], hx0⟩)
  have hPm : Set.range P ⊆ (-I) • slitPlane := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact mem_neg_I_smul_slitPlane (Or.inr ⟨by simp [P, pair], hx1⟩)
    · exact mem_neg_I_smul_slitPlane (Or.inr ⟨by simp [P, pair], hx0⟩)
  -- the boundary values
  set Δ : ℂ → ℂ → ℂ := fun a b => Gp (pair (a + n + 1) (b + n + 1), P) -
    Gm (pair (a + n + 1) (b + n + 1), P)
  -- the side limits for all parameters
  have hlim (a b : ℂ) : Tendsto (fun c : ℝ =>
      jacobiSecondKind a b 1 0 n ((x : ℂ) + (c⁻¹ : ℝ) * I) -
      jacobiSecondKind a b 1 0 n ((x : ℂ) - (c⁻¹ : ℝ) * I)) atTop
      (𝓝 (Gamma (a + n + 1 + (b + n + 1)) * Δ a b)) := by
    set B : Fin 2 → ℂ := pair (a + n + 1) (b + n + 1)
    let φ : ℂ → (Fin 2 → ℂ) × (Fin 2 → ℂ) := fun w => (B, pair ((x : ℂ) + w - 1) (x + w))
    have hφ : Continuous φ := by
      refine continuous_const.prodMk (continuous_pi fun i => ?_)
      fin_cases i <;> simp [pair] <;> fun_prop
    have hφ0 : φ 0 = (B, P) := by simp [φ, P]
    have ht : Tendsto (fun c : ℝ => ((c⁻¹ : ℝ) : ℂ) * I) atTop (𝓝 0) := by
      have := ((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).mul_const I
      simpa using this
    have htm : Tendsto (fun c : ℝ => -(((c⁻¹ : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      simpa using ht.neg
    have hp := ((hGp.1 (B, P) hPp).continuousAt.tendsto.comp
      (hφ0 ▸ hφ.continuousAt.tendsto.comp ht))
    have hm := ((hGm.1 (B, P) hPm).continuousAt.tendsto.comp
      (hφ0 ▸ hφ.continuousAt.tendsto.comp htm))
    refine ((hp.sub hm).const_mul (Gamma (a + n + 1 + (b + n + 1)))).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    set zp : ℂ := (x : ℂ) + (c⁻¹ : ℝ) * I
    set zm : ℂ := (x : ℂ) - (c⁻¹ : ℝ) * I
    have hzp : zp.im = c⁻¹ := by simp [zp]
    have hzm : zm.im = -c⁻¹ := by simp [zm]
    have hsegp : segment ℝ (zp - 1) zp ⊆ I • slitPlane := fun w hw =>
      mem_I_smul_slitPlane (Or.inl ((convex_halfSpace_im_gt (r := 0)).segment_subset
        (show 0 < (zp - 1).im by simp [hzp, hcpos]) (show 0 < zp.im by simp [hzp, hcpos]) hw))
    have hsegm : segment ℝ (zm - 1) zm ⊆ (-I) • slitPlane := fun w hw =>
      mem_neg_I_smul_slitPlane (Or.inl ((convex_halfSpace_im_lt (r := 0)).segment_subset
        (show (zm - 1).im < 0 by simp [hzm, hcpos]) (show zm.im < 0 by simp [hzm, hcpos]) hw))
    have hnp : zp ∉ segment ℝ (1 : ℂ) 0 :=
      not_mem_unitSegment_of_im_ne_zero (by rw [hzp]; exact hcpos.ne')
    have hnm : zm ∉ segment ℝ (1 : ℂ) 0 :=
      not_mem_unitSegment_of_im_ne_zero (by rw [hzm]; exact neg_ne_zero.mpr hcpos.ne')
    simp only [Function.comp_apply, φ]
    rw [jacobiSecondKind, jacobiSecondKind,
      continuedRegCarlsonResolvent_eq_side hGp hnp hsegp,
      continuedRegCarlsonResolvent_eq_side hGm hnm hsegm]
    simp only [zp, zm, B]
    ring_nf
  -- the boundary values in the convergence range
  have hconv (a b : ℂ) (ha : -1 < a.re) (hb : -1 < b.re) :
      Δ a b = jacobiJumpDensity a b n x := by
    have h1 := tendsto_jacobiSecondKind_sub_complex ha hb n hx
    rw [jacobiCauchy_jump_eq] at h1
    have huniq := tendsto_nhds_unique (hlim a b) h1
    have hre : 0 < (a + n + 1 + (b + n + 1)).re := by
      simp only [add_re, natCast_re, one_re]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact mul_left_cancel₀ (Gamma_ne_zero_of_re_pos hre) huniq
  -- analyticity of the boundary values in each parameter
  have hΔa (b : ℂ) : Differentiable ℂ fun a => Δ a b := by
    intro a
    have hp := (hGp.1 (pair (a + n + 1) (b + n + 1), P) hPp).differentiableAt
    have hm := (hGm.1 (pair (a + n + 1) (b + n + 1), P) hPm).differentiableAt
    have hpair : DifferentiableAt ℂ (fun a : ℂ => (pair (a + n + 1) (b + n + 1), P)) a := by
      refine DifferentiableAt.prodMk ?_ (differentiableAt_const _)
      refine differentiableAt_pi.mpr fun i => ?_
      fin_cases i <;> simp [pair]
    exact (hp.comp a hpair).sub (hm.comp a hpair)
  have hΔb (a : ℂ) : Differentiable ℂ fun b => Δ a b := by
    intro b
    have hp := (hGp.1 (pair (a + n + 1) (b + n + 1), P) hPp).differentiableAt
    have hm := (hGm.1 (pair (a + n + 1) (b + n + 1), P) hPm).differentiableAt
    have hpair : DifferentiableAt ℂ (fun b : ℂ => (pair (a + n + 1) (b + n + 1), P)) b := by
      refine DifferentiableAt.prodMk ?_ (differentiableAt_const _)
      refine differentiableAt_pi.mpr fun i => ?_
      fin_cases i <;> simp [pair]
    exact (hp.comp b hpair).sub (hm.comp b hpair)
  -- extension by the identity theorem, first in `α`, then in `β`
  have hall : Δ α β = jacobiJumpDensity α β n x := by
    have hstep1 (b : ℂ) (hb : -1 < b.re) : (fun a => Δ a b) = fun a => jacobiJumpDensity a b n x :=
      eq_of_differentiable_of_re_gt (hΔa b) (differentiable_jacobiJumpDensity_left b n hx)
        fun a ha => hconv a b ha hb
    have hstep2 : (fun b => Δ α b) = fun b => jacobiJumpDensity α b n x :=
      eq_of_differentiable_of_re_gt (hΔb α) (differentiable_jacobiJumpDensity_right α n hx)
        fun b hb => congrFun (hstep1 b hb) α
    exact congrFun hstep2 β
  rw [jacobiCauchy_jump_eq, ← hall]
  exact hlim α β

/-- **The jump (7.8-5) for all complex parameters at distinct complex endpoints**, with a
perpendicular approach to the segment. -/
theorem tendsto_jacobiSecondKind_sub_all_affine (α β : ℂ) (n : ℕ) {r s : ℂ} (hrs : r ≠ s)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun c : ℝ =>
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) + (c⁻¹ : ℝ) * I) + s) -
      jacobiSecondKind α β r s n ((r - s) * ((x : ℂ) - (c⁻¹ : ℝ) * I) + s)) atTop
      (𝓝 ((r - s) ^ (-(n + 1 : ℤ)) *
        (-2 * (Real.pi : ℂ) * I * jacobiCauchyCoefficient α β n *
          (complexJacobiWeight α β x * (shiftedJacobi α β n).eval (x : ℂ))))) := by
  have h := (tendsto_jacobiSecondKind_sub_all α β n hx).const_mul ((r - s) ^ (-(n + 1 : ℤ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hp : ((x : ℂ) + (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have hm : ((x : ℂ) - (c⁻¹ : ℝ) * I).im ≠ 0 := by simp [hc.ne']
  have he {z : ℂ} (hz : z.im ≠ 0) :
      jacobiSecondKind α β r s n ((r - s) * z + s) =
        (r - s) ^ (-(n + 1 : ℤ)) * jacobiSecondKind α β 1 0 n z := by
    simpa using jacobiSecondKind_affine α β 1 0 (r - s) s n (sub_ne_zero.mpr hrs)
      (not_mem_unitSegment_of_im_ne_zero hz)
  rw [he hp, he hm, mul_sub]

/-- A continuous kernel on a circle times `[0, 1]` may be integrated in either order against an
integrable density on `[0, 1]`. -/
theorem circleIntegral_intervalIntegral_swap {ρ : ℝ → ℂ} (hρ : IntervalIntegrable ρ volume 0 1)
    (c : ℂ) {R : ℝ} {F : ℂ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (Metric.sphere c R ×ˢ Icc 0 1))
    (hR : 0 ≤ R) :
    (∮ z in C(c, R), ∫ t in (0 : ℝ)..1, ρ t * F z t) =
      ∫ t in (0 : ℝ)..1, ρ t * ∮ z in C(c, R), F z t := by
  have hρI : IntegrableOn ρ (Icc 0 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hρ.1
  have hbase : IntegrableOn (fun p : ℝ × ℝ => ρ p.2) (Icc 0 (2 * Real.pi) ×ˢ Icc 0 1)
      (volume.prod volume) := by
    rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using
      (integrableOn_const isCompact_Icc.measure_ne_top :
        IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc 0 (2 * Real.pi))).mul_prod hρI
  have hkernel : ContinuousOn (fun p : ℝ × ℝ =>
      deriv (circleMap c R) p.1 * F (circleMap c R p.1) p.2)
      (Icc 0 (2 * Real.pi) ×ˢ Icc 0 1) := by
    apply ContinuousOn.mul
    · simp only [deriv_circleMap]
      fun_prop
    · exact hF.comp
        (((continuous_circleMap c R).comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨circleMap_mem_sphere c hR p.1, hp.2⟩)
  have hint := hbase.mul_continuousOn hkernel (isCompact_Icc.prod isCompact_Icc)
  rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict] at hint
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun θ t => ρ t * (deriv (circleMap c R) θ * F (circleMap c R θ) t)) hint
  simp only [circleIntegral_def_Icc, intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, smul_eq_mul,
    ← MeasureTheory.integral_const_mul]
  simpa only [mul_left_comm] using hswap

/-- **Orthogonality from biorthogonality** (Carlson §7.8, the cut-contour argument): for
`re α, re β > -1` and `α + β + 2` Gamma-regular, the biorthogonality of `pₘ` and `qₙ` on a circle
around `[0, 1]` (Theorem 7.2-1), together with the Cauchy representation (7.8-8) of `qₙ`, gives
`K_n ∫₀¹ t^α (1 - t)^β p̂ₙ(t) pₘ(t) dt = δₘₙ`, where `K_n = jacobiCauchyCoefficient α β n`.
Collapsing the circle onto the cut appears here as an exchange of the circle and segment
integrals followed by Cauchy's formula for `pₘ`. -/
theorem jacobiCauchyCoefficient_mul_integral_eq_of_biorthogonality {α β : ℂ}
    (hα : -1 < α.re) (hβ : -1 < β.re) (hc : IsGammaRegular (α + β + 2)) (m n : ℕ) :
    jacobiCauchyCoefficient α β n * ∫ t in (0 : ℝ)..1, complexJacobiWeight α β t *
        (shiftedJacobi α β n).eval (t : ℂ) * (jacobiOn α β 1 0 m).eval (t : ℂ) =
      if m = n then 1 else 0 := by
  set K := jacobiCauchyCoefficient α β n
  set ρ : ℝ → ℂ := fun t => complexJacobiWeight α β t * (shiftedJacobi α β n).eval (t : ℂ)
  set p := jacobiOn α β 1 0 m
  have hρ : IntervalIntegrable ρ volume 0 1 :=
    (intervalIntegrable_complexJacobiWeight hα hβ).mul_continuousOn
      ((shiftedJacobi α β n).continuous.comp continuous_ofReal).continuousOn
  have hz : Set.range (pair (1 : ℂ) 0) ⊆ Metric.ball (1 / 2) 1 := by
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [pair, Metric.mem_ball, dist_eq] <;> norm_num
  have hb := circleIntegral_jacobiOn_mul_jacobiSecondKind α β 1 0 hc m n one_pos hz
  -- points of `[0, 1]` lie strictly inside the circle
  have hin {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (t : ℂ) ∈ Metric.ball (1 / 2 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq, show (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hsep {z : ℂ} (hz : z ∈ Metric.sphere (1 / 2 : ℂ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      z - t ≠ 0 := by
    intro h
    have h1 := Metric.mem_sphere.mp hz
    have h2 := Metric.mem_ball.mp (hin ht)
    rw [sub_eq_zero.mp h] at h1
    linarith
  have hout {z : ℂ} (hz : z ∈ Metric.sphere (1 / 2 : ℂ) 1) : z ∉ segment ℝ (1 : ℂ) 0 := by
    intro hs
    have hmem := (convex_closedBall (1 / 2 : ℂ) (1 / 2)).segment_subset
      (by rw [Metric.mem_closedBall, dist_eq]; norm_num)
      (by rw [Metric.mem_closedBall, dist_eq]; norm_num) hs
    rw [Metric.mem_closedBall] at hmem
    rw [Metric.mem_sphere] at hz
    linarith
  -- the integrand on the circle through the Cauchy representation of `qₙ`
  set F : ℂ → ℝ → ℂ := fun z t => K * p.eval z * (z - t)⁻¹
  have hcongr : (∮ z in C(1 / 2, 1), p.eval z * jacobiSecondKind α β 1 0 n z) =
      ∮ z in C(1 / 2, 1), ∫ t in (0 : ℝ)..1, ρ t * F z t := by
    apply circleIntegral.integral_congr zero_le_one
    intro z hzs
    dsimp only
    rw [jacobiSecondKind_eq_complexCauchyIntegral hα hβ n (hout hzs),
      ← intervalIntegral.integral_const_mul K, ← intervalIntegral.integral_const_mul (p.eval z)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [F, ρ]
    ring
  have hF : ContinuousOn (fun q : ℂ × ℝ => F q.1 q.2) (Metric.sphere (1 / 2) 1 ×ˢ Icc 0 1) := by
    apply ContinuousOn.mul
    · exact (continuous_const.mul ((p.continuous).comp continuous_fst)).continuousOn
    · exact (continuous_fst.sub (continuous_ofReal.comp continuous_snd)).continuousOn.inv₀
        fun q hq => hsep hq.1 hq.2
  rw [hcongr, circleIntegral_intervalIntegral_swap hρ (1 / 2) hF zero_le_one] at hb
  have hinner : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ρ t * (∮ z in C(1 / 2, 1), F z t) =
      2 * (Real.pi : ℂ) * I * (K * (complexJacobiWeight α β t *
        (shiftedJacobi α β n).eval (t : ℂ) * p.eval (t : ℂ))) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hcf := (p.differentiable.diffContOnCl
      (s := Metric.ball (1 / 2 : ℂ) 1)).circleIntegral_sub_inv_smul (hin ht)
    simp only [smul_eq_mul] at hcf
    have : (∮ z in C(1 / 2, 1), F z t) = K * ∮ z in C(1 / 2, 1), (z - t)⁻¹ * p.eval z := by
      rw [← circleIntegral.integral_const_mul]
      congr 1; funext z; simp only [F]; ring
    rw [this, hcf]
    simp only [ρ]
    ring
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hb
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  rw [← hb]
  field_simp

end Carlson.TwoVariable
