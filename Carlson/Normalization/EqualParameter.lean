/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.GammaPoles
public import Carlson.R.Explicit
public import Carlson.R.SlitPlane
public import Carlson.RPolynomial.TaylorContinuation
public import Dirichlet.Average.JointContinuation
public import SeveralComplexVariables.SeparateAnalytic

/-!
# Equal parameters: removable Gamma singularities

When all `k` Dirichlet parameters equal `β`, the regularized functions `F(β, …, β; z)/Γ(kβ)`
vanish at `β = 0, -1, -2, …`, so multiplication by `Γ(β)` produces removable singularities
only. This is Carlson's Theorem 6.2-6 for R-polynomials, Corollary 6.3-7 for continued
Dirichlet averages on convex domains, and Theorem 6.8-4 for the R-function on the product slit
plane. The strengthened normalization matters because the Bessel, Legendre, and Gegenbauer
functions are averages with equal parameters.

The vanishing is proved as in Carlson: for R-polynomials each Pochhammer term vanishes either
through a Pochhammer factor `(-p)ₘ` with `m > p` or through `1/Γ` at a nonpositive integer; for
averages it follows from the R-polynomial Taylor series (Theorem 6.3-1) near a diagonal node
and the identity theorem on `Ωᵏ`; for the R-function from right-half-plane nodes by the
identity theorem on the slit domain.

The removal itself needs only the one exceptional variable `β`: along each line in `β` the
singularity is removable by `Complex.exists_analyticAt_Gamma_mul_iff`, the filled-in value is
the Gamma residue times the `β`-derivative, and joint analyticity in all variables follows
from Hartogs' theorem on separate analyticity (`Complex.analyticOnNhd_GammaRemovedValue`, in
`Dirichlet.GammaPoles`). No division along a general analytic hypersurface is needed.

## Main definitions

* `Carlson.equalRPolynomial`: the entire function `Γ(β) Rₙ(β, …, β; z)/Γ(kβ)`.
* `Carlson.equalR`: the function `Γ(β) R_t(β, …, β; z)/Γ(kβ)`.

## Main results

* `Carlson.regCarlsonRPolynomial_const_neg_nat`, `analyticOnNhd_equalRPolynomial`: Theorem 6.2-6.
* `Dirichlet.IsRegCarlsonContinuation.eq_zero_const_neg_nat`,
  `Carlson.exists_analyticOnNhd_Gamma_mul_equalParameter`: Corollary 6.3-7.
* `Carlson.regCarlsonR_const_neg_nat`, `Carlson.analyticOnNhd_equalR`: Theorem 6.8-4.
* `Carlson.tendsto_equalRPolynomial`, `Carlson.tendsto_equalR`: the removed values are limits.

## Implementation notes

The exceptional parameter `β` is the `none` coordinate of `Option ι → ℂ` (and the exponent `t`
is the `some none` coordinate of `Option (Option ι) → ℂ`), which is the form required by
Hartogs' theorem. Corollary 6.3-7 and Theorem 6.8-4 assume a nonempty index type, as Carlson's
`k ≥ 1` does.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§6.2, 6.3,
  6.8.
-/

open Filter Set Function
open scoped Topology
@[expose] public noncomputable section

namespace Carlson
open Complex
variable {ι : Type*} [Fintype ι]

/-- **Carlson 6.2-6, vanishing**: with all parameters equal to a nonpositive integer `-p`, the
regularized R-polynomial `Rₙ(b, z)/Γ(kβ)` vanishes. -/
theorem regCarlsonRPolynomial_const_neg_nat (n p : ℕ) (z : ι → ℂ) :
    regCarlsonRPolynomial n (fun _ => -(p : ℂ)) z = 0 := by
  rw [regCarlsonRPolynomial_eq_pochhammer_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h : ∃ i, p < m i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ascPochhammer_eval_neg_coe_nat_of_lt hi)]
    simp
  · push Not at h
    have hs : ∑ i, (-(p : ℂ) + m i) = -((∑ i, (p - m i) : ℕ) : ℂ) := by
      push_cast [Finset.sum_sub_distrib, h]
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]; ring
    rw [hs, Gamma_neg_nat_eq_zero]
    simp

/-- **Carlson 6.3-7, vanishing**: a continued regularized average with all parameters equal to a
nonpositive integer vanishes, for nodes in a convex open holomorphy domain. -/
theorem _root_.Dirichlet.IsRegCarlsonContinuation.eq_zero_const_neg_nat [Nonempty ι]
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : ∀ i, z i ∈ Ω) {G : (ι → ℂ) → ℂ}
    (hG : Dirichlet.IsRegCarlsonContinuation f z G) (p : ℕ) :
    G (fun _ => -(p : ℂ)) = 0 := by
  obtain ⟨J, hJ, hJc⟩ := Dirichlet.exists_joint_isRegCarlsonContinuation hΩo hΩc hf (ι := ι)
  set V : Set (ι → ℂ) := univ.pi fun _ => Ω
  have hmemV : ∀ w, w ∈ V ↔ Set.range w ⊆ Ω := fun w => by
    simp [V, Set.range_subset_iff]
  have hφ : AnalyticOnNhd ℂ (fun w => J (fun _ => -(p : ℂ), w)) V := fun w hw =>
    (hJ _ ((hmemV w).mp hw)).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hVc : IsPreconnected V := (convex_pi fun _ _ => hΩc).isPreconnected
  set c₀ := z (Classical.arbitrary ι)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩo c₀ (hz _)
  have hloc : (fun w => J (fun _ => -(p : ℂ), w)) =ᶠ[𝓝 (fun _ : ι => c₀)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (fun _ : ι => c₀) hr] with w hw
    have hwn : ‖fun i => w i - c₀‖ < r := by
      rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
    have hwi : ∀ i, w i ∈ Ω := fun i => hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (norm_le_pi_norm (fun i => w i - c₀) i).trans_lt hwn)
    have hs := (hJc w ((hmemV w).mp (Set.mem_univ_pi.mpr hwi))).hasSum_taylor
      (hf.mono hball) hwn (fun _ => -(p : ℂ))
    simp only [regCarlsonRPolynomial_const_neg_nat, mul_zero] at hs
    exact hs.unique hasSum_zero
  have h0 := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVc
    (Set.mem_univ_pi.mpr fun _ => hball (Metric.mem_ball_self hr)) hloc
    (Set.mem_univ_pi.mpr hz)
  rw [hG.eq (hJc z ((hmemV z).mp (Set.mem_univ_pi.mpr hz)))]
  exact h0

/-- **Carlson 6.8-4, vanishing**: the regularized R-function with all parameters equal to a
nonpositive integer vanishes, for every exponent and all nodes in the product slit plane. -/
theorem regCarlsonR_const_neg_nat [Nonempty ι] (t : ℂ) (p : ℕ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t (fun _ => -(p : ℂ)) z = 0 := by
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ => w ^ t) Dirichlet.carlsonRightHalfPlane :=
    fun w hw => analyticAt_id.cpow analyticAt_const (carlsonRightHalfPlane_subset_slitPlane hw)
  have hEq : Set.EqOn (fun z : ι → ℂ => regCarlsonR t (fun _ => -(p : ℂ)) z) 0
      carlsonRVariableDomain := fun w hw =>
    (isRegCarlsonRContinuation_regCarlsonR t hw).eq_zero_const_neg_nat
      Dirichlet.isOpen_carlsonRightHalfPlane Dirichlet.convex_carlsonRightHalfPlane hpow hw p
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonR t _)
    analyticOnNhd_const hEq hz

omit [Fintype ι] in
/-- The point of `Option ι → ℂ` with `none`-coordinate `β` and remaining coordinates `z`. -/
def optionPoint (β : ℂ) (z : ι → ℂ) : Option ι → ℂ := fun o => o.elim β z

omit [Fintype ι] in
/-- The `none` coordinate of `optionPoint β z` is `β`. -/
@[simp] theorem optionPoint_none (β : ℂ) (z : ι → ℂ) : optionPoint β z none = β := rfl

omit [Fintype ι] in
/-- The `some i` coordinate of `optionPoint β z` is `z i`. -/
@[simp] theorem optionPoint_some (β : ℂ) (z : ι → ℂ) (i : ι) : optionPoint β z (some i) = z i :=
  rfl

omit [Fintype ι] in
/-- Every point of `Option ι → ℂ` is an `optionPoint`. -/
theorem optionPoint_eta (q : Option ι → ℂ) : optionPoint (q none) (fun i => q (some i)) = q := by
  funext o; cases o <;> rfl

/-- **Carlson's Theorem 6.2-6**: the entire function `Γ(β) Rₙ(β, …, β; z)/Γ(kβ)`, with the
removable singularities at `β = 0, -1, -2, …` filled in. -/
def equalRPolynomial [DecidableEq ι] (n : ℕ) (β : ℂ) (z : ι → ℂ) : ℂ :=
  GammaRemovedValue (fun q : Option ι → ℂ =>
    regCarlsonRPolynomial n (fun _ => q none) (fun i => q (some i))) (optionPoint β z)

/-- Away from the poles of `Γ(β)`, `equalRPolynomial` is the product `Γ(β) Rₙ/Γ(kβ)`. -/
theorem equalRPolynomial_of_ne [DecidableEq ι] (n : ℕ) {β : ℂ} (hβ : ∀ m : ℕ, β ≠ -m) (z : ι → ℂ) :
    equalRPolynomial n β z = Gamma β * regCarlsonRPolynomial n (fun _ => β) z := by
  rw [equalRPolynomial, GammaRemovedValue_of_ne _ (by simpa using hβ)]; rfl

/-- **Carlson's Theorem 6.2-6**: `Γ(β) Rₙ(β, …, β; z)/Γ(kβ)` is entire in `β` and `z` jointly;
the parameter is the `none` coordinate. -/
theorem analyticOnNhd_equalRPolynomial [DecidableEq ι] (n : ℕ) :
    AnalyticOnNhd ℂ (fun q : Option ι → ℂ => equalRPolynomial n (q none) (fun i => q (some i)))
      univ := by
  simp only [equalRPolynomial, optionPoint_eta]
  refine analyticOnNhd_GammaRemovedValue isOpen_univ (fun q _ => ?_) (fun q _ hq => ?_)
  · exact analyticAt_regCarlsonRPolynomial_comp
      (b := fun q : Option ι → ℂ => fun _ => q none) (z := fun q => fun i => q (some i))
      (fun _ => (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt q)
      (fun i => (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt q) n
  · obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hq
    simp only [hm]
    exact regCarlsonRPolynomial_const_neg_nat n m _

/-- **Carlson's Corollary 6.3-7**: for `f` holomorphic on a convex open set `Ω`, the continued
average `Γ(β) F(β, …, β; z)/Γ(kβ)` is holomorphic in `(β, z)` on `ℂ × Ωᵏ`; the parameter is the
`none` coordinate and `F/Γ(kβ)` is the regularized continuation. -/
theorem exists_analyticOnNhd_Gamma_mul_equalParameter [Nonempty ι] {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    ∃ K : (Option ι → ℂ) → ℂ, AnalyticOnNhd ℂ K {q | ∀ i, q (some i) ∈ Ω} ∧
      ∀ (β : ℂ) (z : ι → ℂ), (∀ i, z i ∈ Ω) → (∀ m : ℕ, β ≠ -m) →
        ∀ G, Dirichlet.IsRegCarlsonContinuation f z G →
          K (optionPoint β z) = Gamma β * G (fun _ => β) := by
  classical
  obtain ⟨J, hJ, hJc⟩ := Dirichlet.exists_joint_isRegCarlsonContinuation hΩo hΩc hf (ι := ι)
  have hrange : ∀ w : ι → ℂ, (∀ i, w i ∈ Ω) → Set.range w ⊆ Ω := fun w hw =>
    Set.range_subset_iff.mpr hw
  set U : Set (Option ι → ℂ) := {q | ∀ i, q (some i) ∈ Ω}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hΩo.preimage (continuous_apply _)
  set G' : (Option ι → ℂ) → ℂ := fun q => J (fun _ => q none, fun i => q (some i))
  refine ⟨GammaRemovedValue G', analyticOnNhd_GammaRemovedValue hU (fun q hq => ?_)
    (fun q hq hpole => ?_), fun β z hz hβ G hG => ?_⟩
  · have hmap : AnalyticAt ℂ (fun q : Option ι → ℂ => ((fun _ => q none : ι → ℂ),
        (fun i => q (some i) : ι → ℂ))) q :=
      (analyticAt_pi_iff.mpr fun _ =>
        (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt q).prod
      (analyticAt_pi_iff.mpr fun i =>
        (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt q)
    exact (hJ _ (hrange (fun i => q (some i)) hq)).comp_of_eq hmap rfl
  · obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hpole
    simp only [G', hm]
    exact (hJc _ (hrange (fun i => q (some i)) hq)).eq_zero_const_neg_nat hΩo hΩc hf hq m
  · rw [GammaRemovedValue_of_ne _ (by simpa using hβ), hG.eq (hJc z (hrange z hz))]
    rfl

/-- **Carlson's Theorem 6.8-4**: the function `Γ(β) R_t(β, …, β; z)/Γ(kβ)`, with the removable
singularities at `β = 0, -1, -2, …` filled in. -/
def equalR [DecidableEq ι] (t β : ℂ) (z : ι → ℂ) : ℂ :=
  GammaRemovedValue (fun q : Option (Option ι) → ℂ =>
    regCarlsonR (q (some none)) (fun _ => q none) (fun i => q (some (some i))))
    (optionPoint β (optionPoint t z))

/-- Away from the poles of `Γ(β)`, `equalR` is the product `Γ(β) R_t/Γ(kβ)`. -/
theorem equalR_of_ne [DecidableEq ι] (t : ℂ) {β : ℂ} (hβ : ∀ m : ℕ, β ≠ -m) (z : ι → ℂ) :
    equalR t β z = Gamma β * regCarlsonR t (fun _ => β) z := by
  rw [equalR, GammaRemovedValue_of_ne _ (by simpa using hβ)]; rfl

/-- **Carlson's Theorem 6.8-4**: `Γ(β) R_t(β, …, β; z)/Γ(kβ)` is holomorphic in `(t, β, z)` on
`ℂ² × ℂ₀ᵏ`. The parameter is the `none` coordinate, the exponent the `some none` coordinate. -/
theorem analyticOnNhd_equalR [DecidableEq ι] [Nonempty ι] :
    AnalyticOnNhd ℂ (fun q : Option (Option ι) → ℂ =>
      equalR (q (some none)) (q none) (fun i => q (some (some i))))
      {q | (fun i => q (some (some i))) ∈ carlsonRSlitDomain} := by
  have heta : ∀ q : Option (Option ι) → ℂ,
      optionPoint (q none) (optionPoint (q (some none)) fun i => q (some (some i))) = q := by
    intro q; funext o; rcases o with _ | _ | i <;> rfl
  simp only [equalR, heta]
  have hproj : ∀ o : Option (Option ι), AnalyticOnNhd ℂ (fun q : Option (Option ι) → ℂ => q o)
      univ := fun o q _ =>
    (ContinuousLinearMap.proj o : (Option (Option ι) → ℂ) →L[ℂ] ℂ).analyticAt q
  refine analyticOnNhd_GammaRemovedValue ?_ ?_ (fun q hq hpole => ?_)
  · exact isOpen_carlsonRSlitDomain.preimage (continuous_pi fun i => continuous_apply _)
  · exact analyticOnNhd_regCarlsonR_comp
      (isOpen_carlsonRSlitDomain.preimage (continuous_pi fun i => continuous_apply _))
      ((hproj _).mono (subset_univ _))
      (fun q _ => analyticAt_pi_iff.mpr fun _ => hproj none q (mem_univ _))
      (fun q _ => analyticAt_pi_iff.mpr fun i => hproj (some (some i)) q (mem_univ _))
      (fun q hq => hq)
  · obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hpole
    simp only [hm]
    exact regCarlsonR_const_neg_nat _ m hq

/-- At every `β₀`, including the removable singularities, `Γ(β) Rₙ(β, …, β; z)/Γ(kβ)` tends to
`equalRPolynomial n β₀ z` as `β → β₀`. -/
theorem tendsto_equalRPolynomial [DecidableEq ι] (n : ℕ) (β₀ : ℂ) (z : ι → ℂ) :
    Tendsto (fun β => Gamma β * regCarlsonRPolynomial n (fun _ => β) z) (𝓝[≠] β₀)
      (𝓝 (equalRPolynomial n β₀ z)) := by
  have hK := analyticOnNhd_equalRPolynomial (ι := ι) n
  simp only [equalRPolynomial, optionPoint_eta] at hK
  have h := tendsto_GammaRemovedValue hK (mem_univ (optionPoint β₀ z))
  simp only [optionPoint_none] at h
  refine h.congr fun β => ?_
  congr 2

/-- At every `β₀`, including the removable singularities, `Γ(β) R_t(β, …, β; z)/Γ(kβ)` tends to
`equalR t β₀ z` as `β → β₀`. -/
theorem tendsto_equalR [DecidableEq ι] [Nonempty ι] (t β₀ : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    Tendsto (fun β => Gamma β * regCarlsonR t (fun _ => β) z) (𝓝[≠] β₀)
      (𝓝 (equalR t β₀ z)) := by
  have hK := analyticOnNhd_equalR (ι := ι)
  have heta : ∀ q : Option (Option ι) → ℂ,
      optionPoint (q none) (optionPoint (q (some none)) fun i => q (some (some i))) = q := by
    intro q; funext o; rcases o with _ | _ | i <;> rfl
  simp only [equalR, heta] at hK
  have h := tendsto_GammaRemovedValue hK (p := optionPoint β₀ (optionPoint t z)) hz
  simp only [optionPoint_none] at h
  refine h.congr fun β => ?_
  congr 2

end Carlson
end
