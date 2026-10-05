/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.TwoNode
public import Dirichlet.Average.Merge
public import Dirichlet.Average.HolomorphicDomain
public import Dirichlet.GammaPoles

/-!
# Dirichlet averages on simply connected domains (Carlson 1969, Theorem 8)

Let `f` be holomorphic on a simply connected open set `D ⊆ ℂ`. Carlson (1977, p. 156) asks
whether the Dirichlet average of `f`, defined natively when the convex hull of the nodes lies in
`D`, continues analytically to all nodes in `D`, and refers to Carlson (1969), Theorem 8. We
prove the simply connected case: the Gamma-regularized average has a continuation that is entire
in the Dirichlet parameters and holomorphic in all nodes in `D`, including coincident nodes.

The proof is by induction on the number of nodes. Two nodes `a ≠ a'` are merged: by the merging
identity (`Dirichlet.regCarlsonDirichletAverage_ofReal_eq_merge`) the average is `Γ(b a + b a')`
times the two-node average, over the segment from `z a` to `z a'`, of the average in which the
two nodes are replaced by one moving node with parameter `b a + b a'`. By induction the inner
average continues to all nodes in `D`, and the parametric two-node theorem
(`Dirichlet.exists_twoNode_continuation`) continues the outer average. The factor
`Γ(b a + b a')` has poles; the continued two-node average vanishes there, first for node tuples
with convex hull in `D` by comparison with the native continuation, and then for all node tuples
by the identity theorem along each exceptional hyperplane. The poles are therefore removable
(`Complex.analyticOnNhd_GammaRemovedValue`).

The case of one node, and of no nodes, is the integral-domain continuation, since the convex hull
of at most one point is the point itself.

Carlson's proof uses contour integrals with contour-adapted branches of the R-function. Ours uses
a convex chart of `D` from the Riemann mapping theorem instead. The multiply connected case and
the Riemann-surface case of Theorem 8, with continuation along arcs avoiding the coincidence
diagonals, are not treated.

## Main results

* `Dirichlet.exists_isJointRegCarlsonContinuationOn_merge`: the induction step.
* `Dirichlet.exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected`: **Carlson (1969),
  Theorem 8, simply connected case.**

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, Theorem 8.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.8.
-/

open Complex Set Filter Function ProbabilityTheory
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- With at most one node, the native node domain is the full node domain. -/
theorem exists_isJointRegCarlsonContinuationOn_of_card_le_one (hι : Fintype.card ι ≤ 1)
    {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ, IsJointRegCarlsonContinuationOn D f G := by
  obtain ⟨N, hN, hNeq⟩ := exists_joint_isRegCarlsonContinuation_on_integralDomain (ι := ι) hDo hf
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hι
  have hhull : ∀ z : ι → ℂ, convexHull ℝ (range z) = range z := fun z =>
    (Set.subsingleton_range z).convex.convexHull_eq
  have hdom : ∀ z : ι → ℂ, range z ⊆ D → z ∈ carlsonIntegralNodeDomain D := fun z hz => by
    change convexHull ℝ (range z) ⊆ D
    rwa [hhull]
  refine ⟨N, fun p hp => hN p ⟨mem_univ _, hdom p.2 hp⟩, fun z hz b hb => ?_⟩
  exact (hNeq z hz).eq_native hb

variable [DecidableEq ι] {a a' : ι}

omit [Fintype ι] in
/-- Replacing the merged node by `w` is the merged node vector. -/
theorem update_eq_mergeNodes {α : Type*} (h : a ≠ a') (z : ι → α) (w : α) :
    update (fun j : {i : ι // i ≠ a'} => z j) (mergeIndex h) w = mergeNodes a a' z w := by
  funext j
  by_cases hj : (j : ι) = a
  · have : j = mergeIndex h := Subtype.ext hj
    subst this
    simp [mergeNodes, mergeIndex]
  · have : j ≠ mergeIndex h := fun e => hj (by rw [e]; rfl)
    simp [mergeNodes, hj, this]

omit [Fintype ι] in
/-- The merged node vector, with a point of the convex hull, has convex hull inside the convex
hull of the original nodes. -/
theorem convexHull_mergeNodes_subset {E : Type*} [AddCommGroup E] [Module ℝ E] (z : ι → E)
    {w : E} (hw : w ∈ convexHull ℝ (range z)) :
    convexHull ℝ (range (mergeNodes a a' z w)) ⊆ convexHull ℝ (range z) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨j, rfl⟩
  unfold mergeNodes
  split_ifs
  · exact hw
  · exact subset_convexHull ℝ _ ⟨j, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The two merged nodes lie in the convex hull of all nodes. -/
theorem convexHull_pairParam_subset {E : Type*} [AddCommGroup E] [Module ℝ E] (z : ι → E) :
    convexHull ℝ (range (pairParam a a' z)) ⊆ convexHull ℝ (range z) := by
  apply convexHull_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨a, rfl⟩
  · exact ⟨a', rfl⟩

/-- **The induction step.** If the average with `a` and `a'` merged into one node has a joint
continuation on a simply connected domain, so does the original average. -/
theorem exists_isJointRegCarlsonContinuationOn_merge {D : Set ℂ} (hDo : IsOpen D)
    (hDs : IsSimplyConnected D) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (h : a ≠ a')
    {G' : (({i : ι // i ≠ a'} → ℂ) × ({i : ι // i ≠ a'} → ℂ)) → ℂ}
    (hG' : IsJointRegCarlsonContinuationOn D f G') :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ, IsJointRegCarlsonContinuationOn D f G := by
  classical
  -- The two-node data: the merged parameters and the remaining nodes are external parameters.
  let bq : ({i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} → ℂ) → {i : ι // i ≠ a'} → ℂ :=
    fun q j => q (Sum.inl j)
  let zq : ({i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} → ℂ) → {i : ι // i ≠ a'} → ℂ :=
    fun q j => q (Sum.inr j)
  let P : Set ({i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} → ℂ) := {q | ∀ j, zq q j ∈ D}
  let g : ℂ × ({i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} → ℂ) → ℂ :=
    fun r => G' (bq r.2, update (zq r.2) (mergeIndex h) r.1)
  have hP : IsOpen P := by
    simp only [P, ofPred_forall]
    exact isOpen_iInter_of_finite fun j => hDo.preimage (continuous_apply _)
  have hg : AnalyticOnNhd ℂ g (D ×ˢ P) := by
    rintro ⟨w, q⟩ ⟨hw, hq⟩
    have hmem : (bq q, update (zq q) (mergeIndex h) w) ∈
        {p : ({i : ι // i ≠ a'} → ℂ) × ({i : ι // i ≠ a'} → ℂ) | range p.2 ⊆ D} := by
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = mergeIndex h
      · subst hj; simpa using hw
      · simpa [update_of_ne hj] using hq j
    refine (hG'.1 _ hmem).comp_of_eq ?_ rfl
    refine AnalyticAt.prod ?_ ?_
    · exact analyticAt_pi_iff.mpr fun j => ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : {i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} => ℂ) (Sum.inl j)).analyticAt _).comp
          analyticAt_snd
    · refine analyticAt_pi_iff.mpr fun j => ?_
      by_cases hj : j = mergeIndex h
      · subst hj; simpa using analyticAt_fst
      · simp only [update_of_ne hj]
        exact ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : {i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} => ℂ) (Sum.inr j)).analyticAt _).comp
            analyticAt_snd
  obtain ⟨Gtwo, hGtwo, hGtwoEq⟩ := exists_twoNode_continuation hDo hDs hP hg
  -- The continued two-node average of the merged continuation.
  let encq : (ι → ℂ) → (ι → ℂ) → {i : ι // i ≠ a'} ⊕ {i : ι // i ≠ a'} → ℂ :=
    fun b z => Sum.elim (mergeParam a a' b) (fun j => z j)
  let Φ : (ι → ℂ) × (ι → ℂ) → ℂ := fun p =>
    Gtwo ((pairParam a a' p.1, pairParam a a' p.2), encq p.1 p.2)
  have hΦ : AnalyticOnNhd ℂ Φ {p : (ι → ℂ) × (ι → ℂ) | range p.2 ⊆ D} := by
    rintro ⟨b, z⟩ hz
    have hpair (π : (ι → ℂ) × (ι → ℂ) → ι → ℂ) (hπ : ∀ i, AnalyticAt ℂ (fun p => π p i) (b, z)) :
        AnalyticAt ℂ (fun p => pairParam a a' (π p)) (b, z) := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i
      · simpa [pairParam] using hπ a
      · simpa [pairParam] using hπ a'
    have hb : ∀ i, AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ℂ) => p.1 i) (b, z) := fun i =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt _).comp analyticAt_fst
    have hzz : ∀ i, AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ℂ) => p.2 i) (b, z) := fun i =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt _).comp analyticAt_snd
    have henc : AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ℂ) => encq p.1 p.2) (b, z) := by
      refine analyticAt_pi_iff.mpr fun k => ?_
      rcases k with j | j
      · simp only [Sum.elim_inl, mergeParam]
        split_ifs
        · exact (hb a).add (hb a')
        · exact hb j
      · simpa [encq] using hzz j
    have hmem : ((pairParam a a' b, pairParam a a' z), encq b z) ∈
        (univ ×ˢ pairDomain D) ×ˢ P := by
      refine ⟨⟨mem_univ _, ?_, ?_⟩, fun j => ?_⟩
      · simpa [pairParam] using hz ⟨a, rfl⟩
      · simpa [pairParam] using hz ⟨a', rfl⟩
      · simpa [zq, encq] using hz ⟨j, rfl⟩
    exact (hGtwo _ hmem).comp_of_eq (((hpair _ hb).prod (hpair _ hzz)).prod henc) rfl
  -- The native continuation on the integral node domain.
  obtain ⟨N, hN, hNeq⟩ := exists_joint_isRegCarlsonContinuation_on_integralDomain (ι := ι) hDo hf
  have hSsub : ∀ z ∈ carlsonIntegralNodeDomain (ι := ι) D, range z ⊆ D := fun z hz =>
    (subset_convexHull ℝ _).trans hz
  -- For node tuples with convex hull in `D` and positive real parameters, the merging identity.
  have hreal : ∀ z ∈ carlsonIntegralNodeDomain (ι := ι) D, ∀ c : ι → ℝ, c ∈ mvRealBetaDomain →
      Φ ((fun i => (c i : ℂ)), z) * Gamma ((c a : ℂ) + c a') = N ((fun i => (c i : ℂ)), z) := by
    intro z hz c hc
    set b : ι → ℂ := fun i => (c i : ℂ)
    have hb : b ∈ mvBetaConvergent := fun i => by simpa [b] using hc i
    have hpb : pairParam a a' b ∈ mvBetaConvergent := by
      intro i; fin_cases i
      · simpa [pairParam, b] using hc a
      · simpa [pairParam, b] using hc a'
    have hmb : mergeParam a a' b ∈ mvBetaConvergent := by
      intro j; unfold mergeParam; split_ifs
      · simpa [b] using add_pos (hc a) (hc a')
      · simpa [b] using hc j
    have hencP : encq b z ∈ P := fun j => by simpa [zq, encq] using hSsub z hz ⟨j, rfl⟩
    have h1 := hGtwoEq (encq b z) hencP (pairParam a a' z)
      ((convexHull_pairParam_subset z).trans hz) (pairParam a a' b) hpb
    have hinner : regCarlsonDirichletAverage (pairParam a a' b) (pairParam a a' z)
        (fun w => g (w, encq b z)) =
        regCarlsonDirichletAverage (pairParam a a' b) (pairParam a a' z)
          (fun w => regCarlsonDirichletAverage (mergeParam a a' b) (mergeNodes a a' z w) f) := by
      apply regDirichletIntegral_congr
      intro u hu
      have hw : carlsonAffineForm (pairParam a a' z) u ∈ convexHull ℝ (range z) :=
        convexHull_pairParam_subset z (carlsonAffineForm_mem_convexHull _ hu)
      simp only [g, bq, zq, encq, Sum.elim_inl, Sum.elim_inr]
      rw [update_eq_mergeNodes h]
      exact hG'.2 _ ((convexHull_mergeNodes_subset z hw).trans hz) hmb
    have hfc : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι) := by
      intro u hu
      exact ((hf _ (hz (carlsonAffineForm_mem_convexHull z hu))).continuousAt.comp
        (continuous_carlsonAffineForm z).continuousAt).continuousWithinAt
    have hmerge := regCarlsonDirichletAverage_ofReal_eq_merge h hc z hfc
    change Gtwo ((pairParam a a' b, pairParam a a' z), encq b z) * Gamma (b a + b a') = _
    rw [h1, hinner, (hNeq z hz).eq_native hb, hmerge]
    ring
  -- Hence for node tuples with convex hull in `D`, at every parameter.
  have hall : ∀ z ∈ carlsonIntegralNodeDomain (ι := ι) D, ∀ b : ι → ℂ,
      Φ (b, z) = N (b, z) * (Gamma (b a + b a'))⁻¹ := by
    intro z hz
    have hrecip : AnalyticOnNhd ℂ (fun b : ι → ℂ => (Gamma (b a + b a'))⁻¹) univ := by
      intro b _
      have := (differentiable_one_div_Gamma.analyticAt (b a + b a')).comp_of_eq
        ((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) a).analyticAt b)).add
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) a').analyticAt b)) rfl
      simpa [Function.comp_def, one_div] using this
    have hΦz : AnalyticOnNhd ℂ (fun b => Φ (b, z)) univ := fun b _ =>
      (hΦ (b, z) (hSsub z hz)).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have hNz : AnalyticOnNhd ℂ (fun b => N (b, z)) univ := fun b _ =>
      (hN (b, z) ⟨mem_univ _, hz⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    intro b
    refine congrFun (analyticOnNhd_eq_of_eqOn_realDirichletDomain hΦz (hNz.mul hrecip) ?_) b
    intro c hc
    have hG : Gamma ((c a : ℂ) + c a') ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simpa using add_pos (hc a) (hc a'))
    rw [← hreal z hz c hc]
    field_simp
  -- The continued two-node average vanishes on the exceptional hyperplanes.
  have hzero : ∀ (m : ℕ) (b z : ι → ℂ), range z ⊆ D → b a + b a' = -m → Φ (b, z) = 0 := by
    intro m b z hz hm
    obtain ⟨x₀, hx₀⟩ := hDs.nonempty
    let χ : (ι → ℂ) × (ι → ℂ) → ℂ := fun p => Φ (update p.1 a' (-m - p.1 a), p.2)
    have hupd : AnalyticOnNhd ℂ (fun c : ι → ℂ => update c a' (-m - c a)) univ := by
      intro c _
      refine analyticAt_pi_iff.mpr fun i => ?_
      by_cases hi : i = a'
      · subst hi
        simpa using (analyticAt_const (v := (-(m : ℂ)))).fun_sub (analyticAt_apply_coord a c)
      · simpa [update_of_ne hi] using analyticAt_apply_coord i c
    have hχ : AnalyticOnNhd ℂ χ (univ ×ˢ {z : ι → ℂ | range z ⊆ D}) := by
      rintro ⟨c, z'⟩ ⟨-, hz'⟩
      have hmap : AnalyticAt ℂ
          (fun p : (ι → ℂ) × (ι → ℂ) => (update p.1 a' (-m - p.1 a), p.2)) (c, z') :=
        ((hupd c trivial).comp (analyticAt_fst (p := ((c, z') : (ι → ℂ) × (ι → ℂ))))).prod
          (analyticAt_snd (p := ((c, z') : (ι → ℂ) × (ι → ℂ))))
      exact (hΦ (update c a' (-m - c a), z') hz').comp_of_eq hmap rfl
    have hconn : IsPreconnected ((univ : Set (ι → ℂ)) ×ˢ {z : ι → ℂ | range z ⊆ D}) := by
      refine (isPreconnected_univ (α := ι → ℂ)).prod ?_
      have hDc : IsPreconnected D := (isPathConnected_iff_pathConnectedSpace.mpr
        (by have := hDs.simplyConnectedSpace; infer_instance)).isConnected.isPreconnected
      convert isPreconnected_univ_pi (fun _ : ι => hDc) using 1
      ext z'
      simp [Set.range_subset_iff]
    have hS0 : (fun _ : ι => x₀) ∈ carlsonIntegralNodeDomain (ι := ι) D := by
      change convexHull ℝ (range fun _ : ι => x₀) ⊆ D
      exact (convexHull_min (by rintro _ ⟨_, rfl⟩; exact singleton_subset_iff.mpr rfl rfl)
        (convex_singleton x₀)).trans (singleton_subset_iff.mpr hx₀)
    have hev : χ =ᶠ[𝓝 ((0 : ι → ℂ), fun _ : ι => x₀)] 0 := by
      have hS := (isOpen_carlsonIntegralNodeDomain (ι := ι) hDo).mem_nhds hS0
      filter_upwards [(continuous_snd.continuousAt
        (x := ((0 : ι → ℂ), fun _ : ι => x₀))).preimage_mem_nhds hS] with p hp
      simp only [Pi.zero_apply, χ]
      rw [hall p.2 hp, update_of_ne h, update_self]
      have : p.1 a + (-(m : ℂ) - p.1 a) = -m := by ring
      rw [this, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    have hχ0 := hχ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
      ⟨mem_univ _, by rintro _ ⟨_, rfl⟩; exact hx₀⟩ hev
    have := hχ0 (show (b, z) ∈ (univ : Set (ι → ℂ)) ×ˢ {z : ι → ℂ | range z ⊆ D} from
      ⟨mem_univ _, hz⟩)
    simp only [χ, Pi.zero_apply] at this
    rwa [show update b a' (-m - b a) = b by
      rw [update_eq_self_iff]; linear_combination -hm] at this
  -- Removal of the Gamma poles.
  let κ := {i : ι // i ≠ a'} ⊕ ι
  let E : (ι → ℂ) × (ι → ℂ) → Option κ → ℂ := fun p o =>
    o.elim (p.1 a + p.1 a') (Sum.elim (fun j => p.1 j) p.2)
  let bOf : (Option κ → ℂ) → ι → ℂ := fun q i =>
    if hi : i = a' then q none - q (some (Sum.inl (mergeIndex h))) else q (some (Sum.inl ⟨i, hi⟩))
  let zOf : (Option κ → ℂ) → ι → ℂ := fun q i => q (some (Sum.inr i))
  let Φt : (Option κ → ℂ) → ℂ := fun q => Φ (bOf q, zOf q)
  let Ut : Set (Option κ → ℂ) := {q | ∀ i, zOf q i ∈ D}
  have hUt : IsOpen Ut := by
    simp only [Ut, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hDo.preimage (continuous_apply _)
  have hbOf : ∀ q, AnalyticAt ℂ bOf q := by
    intro q
    refine analyticAt_pi_iff.mpr fun i => ?_
    by_cases hi : i = a'
    · subst hi
      simpa [bOf] using (analyticAt_apply_coord none q).fun_sub
        (analyticAt_apply_coord (some (Sum.inl (mergeIndex h))) q)
    · simpa [bOf, hi] using analyticAt_apply_coord (some (Sum.inl ⟨i, hi⟩)) q
  have hzOf : ∀ q, AnalyticAt ℂ zOf q := fun q => analyticAt_pi_iff.mpr fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option κ => ℂ) (some (Sum.inr i))).analyticAt q
  have hΦt : AnalyticOnNhd ℂ Φt Ut := fun q hq =>
    (hΦ (bOf q, zOf q) (by rintro _ ⟨i, rfl⟩; exact hq i)).comp_of_eq ((hbOf q).prod (hzOf q)) rfl
  have hΦt0 : ∀ q ∈ Ut, Gamma (q none) = 0 → Φt q = 0 := by
    intro q hq hΓ
    obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hΓ
    apply hzero m _ _ (by rintro _ ⟨i, rfl⟩; exact hq i)
    simp only [bOf, h, dite_false, dite_true]
    have : (⟨a, h⟩ : {i : ι // i ≠ a'}) = mergeIndex h := rfl
    rw [this, ← hm]; ring
  have hK := Complex.analyticOnNhd_GammaRemovedValue hUt hΦt hΦt0
  have hbE : ∀ p, bOf (E p) = p.1 := by
    intro p; funext i
    by_cases hi : i = a'
    · subst hi; simp [bOf, E, mergeIndex]
    · simp [bOf, E, hi]
  have hzE : ∀ p, zOf (E p) = p.2 := fun p => rfl
  have hE : ∀ p, AnalyticAt ℂ E p := by
    intro p
    refine analyticAt_pi_iff.mpr fun o => ?_
    rcases o with _ | j | i
    · exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) a).analyticAt _).comp
        analyticAt_fst).add (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ)
          a').analyticAt _).comp analyticAt_fst)
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt _).comp
        analyticAt_fst
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt _).comp
        analyticAt_snd
  refine ⟨fun p => Complex.GammaRemovedValue Φt (E p), ?_, ?_⟩
  · intro p hp
    exact (hK (E p) (fun i => hp ⟨i, rfl⟩)).comp_of_eq (hE p) rfl
  · intro z hz
    have hGz : AnalyticOnNhd ℂ (fun b => Complex.GammaRemovedValue Φt (E (b, z))) univ :=
      fun b _ => (hK (E (b, z)) (fun i => (hSsub z hz) ⟨i, rfl⟩)).comp_of_eq
        ((hE (b, z)).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl) rfl
    have hcont : IsRegCarlsonContinuation f z
        (fun b => Complex.GammaRemovedValue Φt (E (b, z))) := by
      refine IsRegCarlsonContinuation.mk_of_eqOn_realDirichletDomain hGz (hNeq z hz) ?_
      intro c hc
      have hpos : ∀ m : ℕ, E ((fun i => (c i : ℂ)), z) none ≠ -m := by
        intro m hm
        have := congrArg re hm
        simp only [E, Option.elim, add_re, ofReal_re, neg_re, natCast_re] at this
        linarith [hc a, hc a', (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      rw [Complex.GammaRemovedValue_of_ne _ hpos]
      change Gamma ((c a : ℂ) + c a') * Φ (bOf (E _), zOf (E _)) = _
      rw [hbE, hzE, ← hreal z hz c hc]
      ring
    exact fun b hb => hcont.eq_native hb

/-- **Carlson (1969), Theorem 8, simply connected case.** Let `f` be holomorphic on a simply
connected open set `D ⊆ ℂ`. The Gamma-regularized Dirichlet average of `f` has a continuation
that is entire in the Dirichlet parameters and holomorphic in all nodes in `D`, coincident nodes
included, and that agrees with the native average whenever the convex hull of the nodes lies in
`D` and the Dirichlet parameters have positive real parts. Any finite number of nodes is
allowed. -/
theorem exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected {D : Set ℂ}
    (hDo : IsOpen D) (hDs : IsSimplyConnected D) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D)
    (ι : Type*) [Fintype ι] :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ, IsJointRegCarlsonContinuationOn D f G := by
  induction h : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
    classical
    by_cases hn : n ≤ 1
    · exact exists_isJointRegCarlsonContinuationOn_of_card_le_one (h ▸ hn) hDo hf
    obtain ⟨a, a', hne⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card ι)
    have hcard : Fintype.card {i : ι // i ≠ a'} < n := by
      rw [← h]; simp; omega
    obtain ⟨G', hG'⟩ := ih _ hcard {i : ι // i ≠ a'} rfl
    exact exists_isJointRegCarlsonContinuationOn_merge hDo hDs hf hne hG'

end Dirichlet

end
