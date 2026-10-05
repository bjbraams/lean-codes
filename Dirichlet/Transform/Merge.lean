/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Merge
public import Dirichlet.Transform.Joint

/-!
# The merging identity for the regularized Dirichlet transform

Merging two coordinates `a ≠ a'` of the simplex (`Dirichlet.Merge`) writes the regularized
Dirichlet transform of an arbitrary kernel `g` as a two-coordinate transform, with parameters
`(b a, b a')`, of the transform with merged parameters of `y ↦ g (mergeMap v y)`:

`T_b[g] = Γ(b a + b a') · T_(b a, b a')[v ↦ T_(merged b)[y ↦ g (mergeMap v y)]]`.

For positive parameters this is the iterated-integral form of the merging identity for
Dirichlet measures. As an identity of entire functions of `b` it is stated with the factor
`Γ(b a + b a')⁻¹` on the left, where both sides are entire; the inner transform must then
depend holomorphically on the proportions `v`, which holds for kernels holomorphic near the
simplex. Iterating the identity is the stick-breaking representation of the transform as an
iterated two-coordinate (Euler) transform.

## Main results

* `Dirichlet.regDirichletIntegral_ofReal_eq_merge`: the native identity for positive parameters
  and a kernel continuous on the simplex.
* `Dirichlet.IsRegDirichletContinuation.inv_Gamma_mul_eq_merge`: the identity of entire
  functions, given a jointly holomorphic inner continuation.
* `Dirichlet.IsRegDirichletContinuation.eq_Gamma_mul_merge`: the same, away from the Gamma poles
  of the merged parameter, without the reciprocal factor.
* `Dirichlet.exists_merge_continuation`: for a kernel holomorphic near the simplex the inner and
  outer continuations exist.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, equation (4.21).
-/

open Complex MeasureTheory ProbabilityTheory Set
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a a' : ι}

/-- **The native merging identity.** For positive parameters and a kernel continuous on the
simplex, the regularized Dirichlet integral is `Γ(b a + b a')` times the two-coordinate
integral of the merged integrals. -/
theorem regDirichletIntegral_ofReal_eq_merge (h : a ≠ a') {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral (fun i => (b i : ℂ)) g =
      Gamma ((b a : ℂ) + b a') *
        regDirichletIntegral (pairParam a a' fun i => (b i : ℂ))
          (fun v => regDirichletIntegral (mergeParam a a' fun i => (b i : ℂ))
            (fun y => g (mergeMap h v y))) := by
  have : Nonempty ι := ⟨a⟩
  have : Nonempty {i : ι // i ≠ a'} := ⟨mergeIndex h⟩
  have h2 := pairParam_mem_mvRealBetaDomain (a := a) (a' := a') hb
  have h' := mergeParam_mem_mvRealBetaDomain (a := a) (a' := a') hb
  have hpair : pairParam a a' (fun i => (b i : ℂ)) = fun i => ((pairParam a a' b i : ℝ) : ℂ) := by
    funext i; fin_cases i <;> rfl
  have hmerge : mergeParam a a' (fun i => (b i : ℂ)) =
      fun j => ((mergeParam a a' b j : ℝ) : ℂ) := by
    funext j; unfold mergeParam; split_ifs <;> push_cast <;> rfl
  have hsum : ∑ j, ((mergeParam a a' b j : ℝ) : ℂ) = ∑ i, (b i : ℂ) := by
    rw [sum_eq_merge h, sum_merged_eq h, mergeParam_apply_merge]
    simp_rw [mergeParam_apply_other]
    push_cast; ring
  have hsum2 : ∑ i, ((pairParam a a' b i : ℝ) : ℂ) = (b a : ℂ) + b a' := by
    simp [pairParam, Fin.sum_univ_two]
  have hG : Gamma ((b a : ℂ) + b a') ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simpa using add_pos (hb a) (hb a'))
  rw [hpair, hmerge, regDirichletIntegral_ofReal hb, regDirichletIntegral_ofReal h2, hsum2,
    integral_dirichletMeasure_eq_merge h hb hg]
  simp_rw [regDirichletIntegral_ofReal h', hsum]
  rw [integral_div]
  field_simp

omit [DecidableEq ι] in
/-- Evaluation at a coordinate is analytic. -/
theorem analyticAt_apply_coord (i : ι) (b : ι → ℂ) : AnalyticAt ℂ (fun b : ι → ℂ => b i) b :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b

omit [DecidableEq ι] in
/-- The two-coordinate parameters depend analytically on the parameters. -/
theorem analyticAt_pairParam (b : ι → ℂ) :
    AnalyticAt ℂ (fun b : ι → ℂ => pairParam a a' b) b := by
  rw [analyticAt_pi_iff]
  intro k
  fin_cases k
  · exact analyticAt_apply_coord a b
  · exact analyticAt_apply_coord a' b

/-- The merged parameters depend analytically on the parameters. -/
theorem analyticAt_mergeParam (b : ι → ℂ) :
    AnalyticAt ℂ (fun b : ι → ℂ => mergeParam a a' b) b := by
  rw [analyticAt_pi_iff]
  intro j
  unfold mergeParam
  split_ifs
  · exact (analyticAt_apply_coord a b).add (analyticAt_apply_coord a' b)
  · exact analyticAt_apply_coord _ b

omit [Fintype ι] [DecidableEq ι] in
/-- The two-coordinate parameters of positive parameters are in the convergence region. -/
theorem pairParam_ofReal_mem {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    pairParam a a' (fun i => (b i : ℂ)) ∈ mvBetaConvergent := by
  intro k
  fin_cases k
  · simpa [pairParam] using hb a
  · simpa [pairParam] using hb a'

omit [Fintype ι] in
/-- The merged parameters of positive parameters are in the convergence region. -/
theorem mergeParam_ofReal_mem {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    mergeParam a a' (fun i => (b i : ℂ)) ∈ mvBetaConvergent := by
  intro j
  unfold mergeParam
  split_ifs
  · simpa using add_pos (hb a) (hb a')
  · simpa using hb j

/-- **The merging identity for the entire transform.** Let `F` be the entire transform of a
kernel `g` continuous on the simplex, let `M (c, v)` be jointly holomorphic for `v` near the
two-coordinate simplex and, for real proportions `v`, the entire transform in the merged
parameters `c` of `y ↦ g (mergeMap v y)`, and let `P (·, c)` be the entire transform of
`v ↦ M (c, v)`. Then `Γ(b a + b a')⁻¹ F(b) = P(b_pair, b_merged)` for all parameters `b`. -/
theorem IsRegDirichletContinuation.inv_Gamma_mul_eq_merge (h : a ≠ a') {g : (ι → ℝ) → ℂ}
    {F : (ι → ℂ) → ℂ} (hF : IsRegDirichletContinuation g F)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {V : Set (Fin 2 → ℂ)} (hV : IsOpen V)
    (hΔV : ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2), (fun k => (v k : ℂ)) ∈ V)
    {M : (({i : ι // i ≠ a'} → ℂ) × (Fin 2 → ℂ)) → ℂ} (hM : AnalyticOnNhd ℂ M (univ ×ˢ V))
    (hMc : ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2),
      IsRegDirichletContinuation (fun y => g (mergeMap h v y))
        (fun c => M (c, fun k => (v k : ℂ))))
    {P : ((Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ)) → ℂ}
    (hP : ∀ c, IsRegDirichletContinuation (fun v => M (c, fun k => (v k : ℂ)))
      (fun β => P (β, c)))
    (b : ι → ℂ) :
    (Gamma (b a + b a'))⁻¹ * F b = P (pairParam a a' b, mergeParam a a' b) := by
  have hPan : AnalyticOnNhd ℂ P (univ ×ˢ univ) :=
    analyticOnNhd_joint_of_isRegDirichletContinuation isOpen_univ (isOpen_univ.prod hV) hM
      (fun _ _ v hv => ⟨mem_univ _, hΔV v hv⟩) (fun c _ => hP c)
  refine congrFun (analyticOnNhd_eq_of_eqOn_realDirichletDomain
    (G := fun b => (Gamma (b a + b a'))⁻¹ * F b)
    (H := fun b => P (pairParam a a' b, mergeParam a a' b)) ?_ ?_ ?_) b
  · intro b _
    have hinv : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) (b a + b a') :=
      differentiable_one_div_Gamma.analyticAt _
    exact (hinv.comp_of_eq ((analyticAt_apply_coord a b).add (analyticAt_apply_coord a' b))
      rfl).mul (hF.1 b (mem_univ _))
  · intro b _
    exact (hPan _ ⟨mem_univ _, mem_univ _⟩).comp_of_eq
      ((analyticAt_pairParam b).prod (analyticAt_mergeParam b)) rfl
  · intro b hb
    have hβ := pairParam_ofReal_mem (a := a) (a' := a') hb
    have hc := mergeParam_ofReal_mem (a := a) (a' := a') hb
    have hb' : (fun i => (b i : ℂ)) ∈ mvBetaConvergent := fun i => by simpa using hb i
    have hG : Gamma ((b a : ℂ) + b a') ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simpa using add_pos (hb a) (hb a'))
    simp only
    rw [(hP _).eq_native hβ, hF.eq_native hb', regDirichletIntegral_ofReal_eq_merge h hb hg,
      ← mul_assoc, inv_mul_cancel₀ hG, one_mul]
    refine regDirichletIntegral_congr _ fun v hv => ?_
    exact ((hMc v hv).eq_native hc).symm

/-- **The merging identity away from Gamma poles.** If `b a + b a'` is not a nonpositive
integer, then `F(b) = Γ(b a + b a') P(b_pair, b_merged)`. -/
theorem IsRegDirichletContinuation.eq_Gamma_mul_merge (h : a ≠ a') {g : (ι → ℝ) → ℂ}
    {F : (ι → ℂ) → ℂ} (hF : IsRegDirichletContinuation g F)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    {V : Set (Fin 2 → ℂ)} (hV : IsOpen V)
    (hΔV : ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2), (fun k => (v k : ℂ)) ∈ V)
    {M : (({i : ι // i ≠ a'} → ℂ) × (Fin 2 → ℂ)) → ℂ} (hM : AnalyticOnNhd ℂ M (univ ×ˢ V))
    (hMc : ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2),
      IsRegDirichletContinuation (fun y => g (mergeMap h v y))
        (fun c => M (c, fun k => (v k : ℂ))))
    {P : ((Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ)) → ℂ}
    (hP : ∀ c, IsRegDirichletContinuation (fun v => M (c, fun k => (v k : ℂ)))
      (fun β => P (β, c)))
    {b : ι → ℂ} (hb : ∀ m : ℕ, b a + b a' ≠ -m) :
    F b = Gamma (b a + b a') * P (pairParam a a' b, mergeParam a a' b) := by
  rw [← hF.inv_Gamma_mul_eq_merge h hg hV hΔV hM hMc hP b, ← mul_assoc,
    mul_inv_cancel₀ (Gamma_ne_zero hb), one_mul]

/-- The merging map is jointly analytic in the proportions and the merged coordinates. -/
theorem analyticAt_mergeMap (h : a ≠ a') (p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ)) :
    AnalyticAt ℂ (fun p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ) => mergeMap h p.1 p.2) p := by
  have hfst (k : Fin 2) : AnalyticAt ℂ
      (fun p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ) => p.1 k) p :=
    ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _)).analyticAt p
  have hsnd (j : {i : ι // i ≠ a'}) : AnalyticAt ℂ
      (fun p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ) => p.2 j) p :=
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)).analyticAt p
  rw [analyticAt_pi_iff]
  intro i
  unfold mergeMap
  split_ifs
  · exact (hfst 1).mul (hsnd _)
  · exact (hfst 0).mul (hsnd _)
  · exact hsnd _

omit [Fintype ι] in
/-- Complexifying the arguments of the merging map complexifies its values. -/
theorem mergeMap_ofReal (h : a ≠ a') (v : Fin 2 → ℝ) (y : {i : ι // i ≠ a'} → ℝ) :
    mergeMap h (fun k => (v k : ℂ)) (fun j => (y j : ℂ)) = fun i => ((mergeMap h v y i : ℝ) : ℂ) :=
  mergeMap_map Complex.ofRealHom h v y

/-- **Existence of the merged continuations.** For a kernel holomorphic on a neighborhood of the
real simplex, the inner continuation `M`, holomorphic in the proportions near the
two-coordinate simplex, and the outer continuation `P` of the merging identity exist. -/
theorem exists_merge_continuation (h : a ≠ a') {Ω : Set (ι → ℂ)} (hΩ : IsOpen Ω)
    {f : (ι → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hΔ : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, (fun i => (u i : ℂ)) ∈ Ω) :
    ∃ (V : Set (Fin 2 → ℂ)) (M : (({i : ι // i ≠ a'} → ℂ) × (Fin 2 → ℂ)) → ℂ)
      (P : ((Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ)) → ℂ),
      IsOpen V ∧
      (∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2), (fun k => (v k : ℂ)) ∈ V) ∧
      AnalyticOnNhd ℂ M (univ ×ˢ V) ∧
      (∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2),
        IsRegDirichletContinuation (fun y => f (fun i => ((mergeMap h v y i : ℝ) : ℂ)))
          (fun c => M (c, fun k => (v k : ℂ)))) ∧
      ∀ c, IsRegDirichletContinuation (fun v => M (c, fun k => (v k : ℂ)))
        (fun β => P (β, c)) := by
  set Δm := Convexity.StdSimplex.coordinateSet ℝ {i : ι // i ≠ a'}
  have hcont : Continuous (fun p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℂ) => mergeMap h p.1 p.2) :=
    continuous_iff_continuousAt.mpr fun p => (analyticAt_mergeMap h p).continuousAt
  -- The proportions whose merged simplex is mapped into `Ω`.
  set V : Set (Fin 2 → ℂ) := {v | ∀ y ∈ Δm, mergeMap h v (fun j => (y j : ℂ)) ∈ Ω}
  have hV : IsOpen V := by
    rw [isOpen_iff_forall_mem_open]
    intro v₀ hv₀
    have hemb : Continuous fun p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℝ) =>
        (p.1, fun j => (p.2 j : ℂ)) :=
      continuous_fst.prodMk
        (continuous_pi fun j => continuous_ofReal.comp ((continuous_apply j).comp continuous_snd))
    have hn : IsOpen {p : (Fin 2 → ℂ) × ({i : ι // i ≠ a'} → ℝ) |
        mergeMap h p.1 (fun j => (p.2 j : ℂ)) ∈ Ω} :=
      hΩ.preimage (hcont.comp hemb)
    obtain ⟨u, w, hu, -, hvu, hΔw, huw⟩ := generalized_tube_lemma isCompact_singleton
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ {i : ι // i ≠ a'}) hn
      (fun p hp => by
        obtain ⟨hp1, hp2⟩ := hp
        rw [mem_singleton_iff] at hp1
        simpa [hp1] using hv₀ p.2 hp2)
    exact ⟨u, fun v hv y hy => huw (show (v, y) ∈ u ×ˢ w from ⟨hv, hΔw hy⟩), hu, hvu rfl⟩
  have hΔV : ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2), (fun k => (v k : ℂ)) ∈ V := by
    intro v hv y hy
    rw [mergeMap_ofReal]
    exact hΔ _ (mergeMap_mem_coordinateSet h hv hy)
  -- The inner continuation, with the proportions as auxiliary parameters.
  obtain ⟨M, hM⟩ := exists_isJointRegDirichletContinuation (κ := Fin 2) hV
    (hΩ.preimage hcont) (H := fun p => f (mergeMap h p.1 p.2))
    (fun p hp => (hf _ hp).comp_of_eq (analyticAt_mergeMap h p) rfl)
    (fun v hv y hy => hv y hy)
  -- The outer continuation, with the merged parameters as auxiliary parameters.
  obtain ⟨P, hP⟩ := exists_isJointRegDirichletContinuation (κ := {i : ι // i ≠ a'})
    (ι := Fin 2) isOpen_univ (isOpen_univ.prod hV) (H := M) hM.1
    (fun _ _ v hv => ⟨mem_univ _, hΔV v hv⟩)
  refine ⟨V, M, P, hV, hΔV, hM.1, fun v hv => ?_, fun c => hP.2 c (mem_univ _)⟩
  have := hM.2 _ (hΔV v hv)
  simpa only [mergeMap_ofReal] using this

end Dirichlet

end
