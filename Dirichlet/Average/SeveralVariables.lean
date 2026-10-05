/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.SimplyConnected
public import Dirichlet.Average.FibreContinuation

/-!
# Dirichlet averages of functions of several variables on non-convex domains

Let `h` be holomorphic on an open set `D ⊆ ℂ^σ`. The regularized Dirichlet average of `h` with
vector nodes `Z i ∈ ℂ^σ`,

`R_b(Z; h) = T_b[u ↦ h (∑ i, u i • Z i)]`,

is defined natively when the convex hull of the nodes lies in `D`. We show that it continues
analytically to all nodes in `D`, entire in the Dirichlet parameters, provided the complex-line
sections `{t : ℂ | t • x + (1 - t) • y ∈ D}` of `D` through any two of its points are simply
connected (`Dirichlet.HasSimplyConnectedLineSections`). Convex domains, and (for `σ` a single
coordinate) simply connected planar domains, have this property, so the theorem contains
Carlson's (1969) Theorem 8 in the simply connected case; domains of `ℂⁿ` all of whose
intersections with complex lines are connected and simply connected are the `ℂ`-convex domains.

This is the fibrewise deformation theorem of the Dirichlet-transform programme: the merging
identity (`Dirichlet.Transform.Merge`) reduces the number of nodes; the merged node moves on the
complex line through the two merged nodes, where the kernel is holomorphic on the line section;
and the continuation of Euler integrals over simply connected fibres
(`Dirichlet.exists_regEulerIntegral_continuation_of_fibres`) continues the outer two-node
average. The Gamma factor of the merged parameter is removed as in the planar proof.

## Main definitions

* `Dirichlet.vecAffineForm`: the point `∑ i, u i • Z i`.
* `Dirichlet.regVecDirichletAverage`: the regularized Dirichlet average with vector nodes.
* `Dirichlet.IsJointRegVecContinuationOn`: a joint continuation to all nodes in `D`.
* `Dirichlet.HasSimplyConnectedLineSections`: the hypothesis on `D`.

## Main results

* `Dirichlet.regVecDirichletAverage_ofReal_eq_merge`: the merging identity.
* `Dirichlet.exists_isJointRegVecContinuationOn`: **the continuation theorem**.
* `Convex.hasSimplyConnectedLineSections`, `IsSimplyConnected.hasSimplyConnectedLineSections`:
  convex domains and planar simply connected domains have simply connected line sections.
* `Dirichlet.exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected_of_lineSections`:
  Carlson's Theorem 8 (simply connected case) recovered as the case of one coordinate.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, Theorem 8.
* M. Andersson, M. Passare, R. Sigurdsson, *Complex Convexity and Analytic Functionals*,
  Birkhäuser, 2004 (`ℂ`-convex domains).
-/

open Complex Set Filter Function ProbabilityTheory
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

/-- The point `∑ i, u i • Z i` of `ℂ^σ` with vector nodes `Z` and simplex weights `u`. -/
def vecAffineForm (Z : ι → σ → ℂ) (u : ι → ℝ) : σ → ℂ := ∑ i, (u i : ℂ) • Z i

/-- The regularized Dirichlet average of a function of several variables with vector nodes. -/
def regVecDirichletAverage (b : ι → ℂ) (Z : ι → σ → ℂ) (h : (σ → ℂ) → ℂ) : ℂ :=
  regDirichletIntegral b (fun u => h (vecAffineForm Z u))

/-- A joint continuation of the regularized average to all nodes in `D`: holomorphic in the
Dirichlet parameters and nodes, and equal to the native average whenever the convex hull of the
nodes lies in `D`. -/
def IsJointRegVecContinuationOn (D : Set (σ → ℂ)) (h : (σ → ℂ) → ℂ)
    (G : (ι → ℂ) × (ι → σ → ℂ) → ℂ) : Prop :=
  AnalyticOnNhd ℂ G {p | ∀ i, p.2 i ∈ D} ∧
    ∀ Z : ι → σ → ℂ, convexHull ℝ (range Z) ⊆ D →
      EqOn (fun b => G (b, Z)) (fun b => regVecDirichletAverage b Z h) mvBetaConvergent

/-- The sections of `D` by the complex lines through any two of its points are simply
connected. -/
def HasSimplyConnectedLineSections (D : Set (σ → ℂ)) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, IsSimplyConnected {t : ℂ | t • x + (1 - t) • y ∈ D}

omit [Fintype σ] in
/-- The weighted point of a simplex point lies in the convex hull of the nodes. -/
theorem vecAffineForm_mem_convexHull (Z : ι → σ → ℂ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    vecAffineForm Z u ∈ convexHull ℝ (range Z) := by
  have h := (convex_convexHull ℝ (range Z)).sum_mem (t := Finset.univ) (w := u) (z := Z)
    (fun i _ => hu.1 i) (by simpa using hu.2) (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  convert h using 1
  unfold vecAffineForm
  refine Finset.sum_congr rfl fun i _ => ?_
  ext s
  simp

omit [Fintype σ] in
/-- The weighted point is continuous in the weights. -/
theorem continuous_vecAffineForm (Z : ι → σ → ℂ) : Continuous (vecAffineForm Z) := by
  unfold vecAffineForm
  fun_prop

omit [Fintype σ] in
/-- Merging two nodes: the weighted point of the merged weights is the weighted point of the
merged nodes, the merged node being the weighted point of the two merged nodes. -/
theorem vecAffineForm_mergeMap [DecidableEq ι] {a a' : ι} (h : a ≠ a') (Z : ι → σ → ℂ)
    (v : Fin 2 → ℝ) (y : {i : ι // i ≠ a'} → ℝ) :
    vecAffineForm Z (mergeMap h v y) =
      vecAffineForm (mergeNodes a a' Z (vecAffineForm (pairParam a a' Z) v)) y := by
  unfold vecAffineForm
  rw [sum_eq_merge h, sum_merged_eq h, mergeMap_apply_right, mergeMap_apply_left]
  simp_rw [mergeMap_apply_other]
  have hk : ∀ k : {j : {i : ι // i ≠ a'} // j ≠ mergeIndex h},
      mergeNodes a a' Z (∑ i, (v i : ℂ) • pairParam a a' Z i) k.1 = Z k.1.1 := by
    intro k
    have h2 : (k.1 : ι) ≠ a := fun e => k.2 (Subtype.ext e)
    simp [mergeNodes, h2]
  simp_rw [hk]
  simp only [mergeNodes, mergeIndex, ite_true, Fin.sum_univ_two, pairParam,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  simp only [smul_add, smul_smul, mul_comm ((y ⟨a, h⟩ : ℝ) : ℂ)]
  abel

omit [Fintype σ] in
/-- **The merging identity for averages with vector nodes**, for positive parameters. -/
theorem regVecDirichletAverage_ofReal_eq_merge [DecidableEq ι] {a a' : ι} (h : a ≠ a')
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (Z : ι → σ → ℂ) {f : (σ → ℂ) → ℂ}
    (hf : ContinuousOn (fun u => f (vecAffineForm Z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regVecDirichletAverage (fun i => (b i : ℂ)) Z f =
      Gamma ((b a : ℂ) + b a') *
        regVecDirichletAverage (pairParam a a' (fun i => (b i : ℂ))) (pairParam a a' Z)
          (fun w => regVecDirichletAverage (mergeParam a a' (fun i => (b i : ℂ)))
            (mergeNodes a a' Z w) f) := by
  unfold regVecDirichletAverage
  rw [regDirichletIntegral_ofReal_eq_merge h hb hf]
  simp_rw [vecAffineForm_mergeMap h]

omit [Fintype σ] in
/-- A two-node average with vector nodes is a regularized Euler integral along the segment. -/
theorem regVecDirichletAverage_fin_two (b : Fin 2 → ℂ) (Z : Fin 2 → σ → ℂ)
    (f : (σ → ℂ) → ℂ) :
    regVecDirichletAverage b Z f =
      regEulerIntegral (b 0) (b 1) (fun t : ℝ => f ((t : ℂ) • Z 0 + (1 - (t : ℂ)) • Z 1)) := by
  have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
  unfold regVecDirichletAverage
  rw [regDirichletIntegral_congr b
    (g := fun u => (fun t : ℝ => f ((t : ℂ) • Z 0 + (1 - (t : ℂ)) • Z 1)) (u 0))]
  · have h := regDirichletIntegral_fin_two (b 0) (b 1)
      (fun t : ℝ => f ((t : ℂ) • Z 0 + (1 - (t : ℂ)) • Z 1))
    rwa [← hb] at h
  · intro u hu
    have h1 : u 1 = 1 - u 0 := by
      have := hu.2; simp only [Fin.sum_univ_two] at this; linarith
    simp only [vecAffineForm, Fin.sum_univ_two, h1]
    push_cast
    rfl

/-- Evaluation of a node coordinate is analytic. -/
theorem analyticAt_node_apply (i : ι) (s : σ) (Z : ι → σ → ℂ) :
    AnalyticAt ℂ (fun Z : ι → σ → ℂ => Z i s) Z :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => σ → ℂ) i)).analyticAt Z

/-- **Native continuation for fixed nodes.** If the convex hull of the nodes lies in the open
domain of holomorphy, the regularized average has an entire continuation in the Dirichlet
parameters. -/
theorem exists_isRegDirichletContinuation_vecAverage {D : Set (σ → ℂ)} (hDo : IsOpen D)
    {f : (σ → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f D) {Z : ι → σ → ℂ}
    (hZ : convexHull ℝ (range Z) ⊆ D) :
    ∃ F : (ι → ℂ) → ℂ, IsRegDirichletContinuation (fun u => f (vecAffineForm Z u)) F := by
  let A : (ι → ℂ) → σ → ℂ := fun w => ∑ i, w i • Z i
  have hA : ∀ w, AnalyticAt ℂ A w := fun w =>
    analyticAt_pi_iff.mpr fun s => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        (analyticAt_apply_coord i w).mul analyticAt_const
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun w => (hA w).continuousAt
  obtain ⟨F, hF⟩ := exists_isJointRegDirichletContinuation (κ := Fin 0) (U := univ) isOpen_univ
    (W := {q : (Fin 0 → ℂ) × (ι → ℂ) | A q.2 ∈ D}) (hDo.preimage (hAc.comp continuous_snd))
    (H := fun q => f (A q.2))
    (fun q hq => (hf _ hq).comp_of_eq ((hA q.2).comp analyticAt_snd) rfl)
    (fun _ _ u hu => hZ (vecAffineForm_mem_convexHull Z hu))
  exact ⟨fun b => F (b, 0), (hF.2 0 (mem_univ _))⟩

/-- **At most one node.** With at most one node the convex hull of the nodes is the set of
nodes, and the integral-domain continuation is a joint continuation to all nodes in `D`. -/
theorem exists_isJointRegVecContinuationOn_of_card_le_one (hι : Fintype.card ι ≤ 1)
    {D : Set (σ → ℂ)} (hDo : IsOpen D) {f : (σ → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f D) :
    ∃ G : (ι → ℂ) × (ι → σ → ℂ) → ℂ, IsJointRegVecContinuationOn D f G := by
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hι
  -- The nodes are auxiliary parameters, indexed by `ι × σ`.
  let unflat : (ι × σ → ℂ) → ι → σ → ℂ := fun q i s => q (i, s)
  let A : (ι × σ → ℂ) × (ι → ℂ) → σ → ℂ := fun q => ∑ i, q.2 i • unflat q.1 i
  have hA : ∀ q, AnalyticAt ℂ A q := fun q =>
    analyticAt_pi_iff.mpr fun s => by
      simp only [unflat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        ((analyticAt_apply_coord i q.2).comp analyticAt_snd).mul
          ((analyticAt_apply_coord (i, s) q.1).comp analyticAt_fst)
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun q => (hA q).continuousAt
  let U : Set (ι × σ → ℂ) := {q | ∀ i, unflat q i ∈ D}
  have hU : IsOpen U := by
    simp only [U, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hDo.preimage
      (continuous_pi fun s => continuous_apply (i, s))
  obtain ⟨F, hF⟩ := exists_isJointRegDirichletContinuation hU
    (W := A ⁻¹' D) (hDo.preimage hAc) (H := fun q => f (A q))
    (fun q hq => (hf _ hq).comp_of_eq (hA q) rfl) (fun q hq u hu => by
      obtain ⟨i⟩ : Nonempty ι := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        simpa using hu.2
      have hsum : u i = 1 := by
        have := hu.2
        rwa [Fintype.sum_subsingleton _ i] at this
      simp only [mem_preimage, A, unflat]
      rw [Fintype.sum_subsingleton _ i, hsum, ofReal_one, one_smul]
      exact hq i)
  let flat : (ι → σ → ℂ) → ι × σ → ℂ := fun Z k => Z k.1 k.2
  have hflat : ∀ Z, AnalyticAt ℂ flat Z := fun Z =>
    analyticAt_pi_iff.mpr fun k => analyticAt_node_apply k.1 k.2 Z
  refine ⟨fun p => F (p.1, flat p.2), fun p hp => ?_, fun Z hZh b hb => ?_⟩
  · exact (hF.1 _ ⟨mem_univ _, fun i => hp i⟩).comp_of_eq (analyticAt_fst.prod ((hflat p.2).comp
      analyticAt_snd)) rfl
  · have hZ : flat Z ∈ U := fun i => hZh (subset_convexHull ℝ _ ⟨i, rfl⟩)
    exact (hF.2 _ hZ).eq_native hb

omit [Fintype σ] in
/-- A domain with simply connected line sections is preconnected: two of its points are joined
inside the image of the line section through them. -/
theorem HasSimplyConnectedLineSections.isPreconnected {D : Set (σ → ℂ)}
    (hD : HasSimplyConnectedLineSections D) : IsPreconnected D := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  set S := {t : ℂ | t • x + (1 - t) • y ∈ D}
  refine ⟨(fun t : ℂ => t • x + (1 - t) • y) '' S, ?_, ⟨1, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · simpa [S] using hx
  · simp
  · simpa [S] using hy
  · simp
  · exact (hD x hx y hy).isPathConnected.isConnected.isPreconnected.image _
      (by fun_prop : Continuous fun t : ℂ => t • x + (1 - t) • y).continuousOn

/-- **The induction step.** If the average with the nodes `a` and `a'` merged has a joint
continuation on a domain with simply connected line sections, so does the original average. -/
theorem exists_isJointRegVecContinuationOn_merge [DecidableEq ι] {a a' : ι}
    {D : Set (σ → ℂ)} (hDo : IsOpen D) (hDl : HasSimplyConnectedLineSections D)
    {f : (σ → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f D) (h : a ≠ a')
    {G' : ({i : ι // i ≠ a'} → ℂ) × ({i : ι // i ≠ a'} → σ → ℂ) → ℂ}
    (hG' : IsJointRegVecContinuationOn D f G') :
    ∃ G : (ι → ℂ) × (ι → σ → ℂ) → ℂ, IsJointRegVecContinuationOn D f G := by
  classical
  -- The parameters of the Euler integral: all Dirichlet parameters and all nodes.
  let bOf : (ι ⊕ ι × σ → ℂ) → ι → ℂ := fun p i => p (Sum.inl i)
  let ZOf : (ι ⊕ ι × σ → ℂ) → ι → σ → ℂ := fun p i s => p (Sum.inr (i, s))
  let enc : (ι → ℂ) × (ι → σ → ℂ) → ι ⊕ ι × σ → ℂ := fun q =>
    Sum.elim q.1 (fun k => q.2 k.1 k.2)
  let lp : ℂ × (ι ⊕ ι × σ → ℂ) → σ → ℂ := fun r => r.1 • ZOf r.2 a + (1 - r.1) • ZOf r.2 a'
  let P : Set (ι ⊕ ι × σ → ℂ) := {p | ∀ i, ZOf p i ∈ D}
  let 𝒲 : Set (ℂ × (ι ⊕ ι × σ → ℂ)) := {r | r.2 ∈ P ∧ lp r ∈ D}
  let g : ℂ × (ι ⊕ ι × σ → ℂ) → ℂ := fun r =>
    G' (mergeParam a a' (bOf r.2), update (fun j => ZOf r.2 j) (mergeIndex h) (lp r))
  have hZOfc : ∀ i, Continuous fun p => ZOf p i := fun i =>
    continuous_pi fun s => continuous_apply (Sum.inr (i, s))
  have hP : IsOpen P := by
    simp only [P, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hDo.preimage (hZOfc i)
  have hlpc : Continuous lp := by
    simp only [lp]
    exact (continuous_fst.smul ((hZOfc a).comp continuous_snd)).add
      ((continuous_const.sub continuous_fst).smul ((hZOfc a').comp continuous_snd))
  have h𝒲 : IsOpen 𝒲 := (hP.preimage continuous_snd).inter (hDo.preimage hlpc)
  -- Analyticity of the parameter accessors.
  have hbOf : ∀ p, AnalyticAt ℂ bOf p := fun p =>
    analyticAt_pi_iff.mpr fun i => analyticAt_apply_coord (Sum.inl i) p
  have hZOf : ∀ (i : ι) (r : ℂ × (ι ⊕ ι × σ → ℂ)),
      AnalyticAt ℂ (fun r : ℂ × (ι ⊕ ι × σ → ℂ) => ZOf r.2 i) r := fun i r =>
    analyticAt_pi_iff.mpr fun s => (analyticAt_apply_coord (Sum.inr (i, s)) r.2).comp
      analyticAt_snd
  have hlp : ∀ r, AnalyticAt ℂ lp r := fun r =>
    (analyticAt_fst.smul (hZOf a r)).add ((analyticAt_const.sub analyticAt_fst).smul (hZOf a' r))
  have hg : AnalyticOnNhd ℂ g 𝒲 := by
    rintro r ⟨hrP, hrl⟩
    have hmem : (mergeParam a a' (bOf r.2),
        update (fun j : {i : ι // i ≠ a'} => ZOf r.2 j) (mergeIndex h) (lp r)) ∈
        {q : ({i : ι // i ≠ a'} → ℂ) × ({i : ι // i ≠ a'} → σ → ℂ) | ∀ j, q.2 j ∈ D} := by
      intro j
      by_cases hj : j = mergeIndex h
      · subst hj; simpa using hrl
      · simpa [update_of_ne hj] using hrP j
    refine (hG'.1 _ hmem).comp_of_eq (AnalyticAt.prod ?_ ?_) rfl
    · exact (analyticAt_mergeParam _).comp ((hbOf r.2).comp analyticAt_snd)
    · refine analyticAt_pi_iff.mpr fun j => ?_
      by_cases hj : j = mergeIndex h
      · subst hj; simpa using hlp r
      · simpa [update_of_ne hj] using hZOf j r
  have hsc : ∀ p ∈ P, IsSimplyConnected {t : ℂ | (t, p) ∈ 𝒲} := by
    intro p hp
    have := hDl _ (hp a) _ (hp a')
    convert this using 1
    ext t
    simp [𝒲, hp, lp]
  obtain ⟨E, hE, hEeq⟩ := exists_regEulerIntegral_continuation_of_fibres h𝒲 hP hg hsc
  -- The continued outer two-node average.
  let Φ : (ι → ℂ) × (ι → σ → ℂ) → ℂ := fun q => E (pairParam a a' q.1, enc q)
  have henc : ∀ q, AnalyticAt ℂ enc q := fun q => analyticAt_pi_iff.mpr fun k => by
    rcases k with i | ⟨i, s⟩
    · exact (analyticAt_apply_coord i q.1).comp analyticAt_fst
    · exact (analyticAt_node_apply i s q.2).comp analyticAt_snd
  have hencP : ∀ Z : ι → σ → ℂ, (∀ i, Z i ∈ D) → ∀ b, enc (b, Z) ∈ P :=
    fun Z hZ b i => hZ i
  have hΦ : AnalyticOnNhd ℂ Φ {q | ∀ i, q.2 i ∈ D} := by
    rintro ⟨b, Z⟩ hZ
    have hmem : (pairParam a a' b, enc (b, Z)) ∈
        {q : (Fin 2 → ℂ) × (ι ⊕ ι × σ → ℂ) | q.2 ∈ P ∧ ((1 : ℂ), q.2) ∈ 𝒲 ∧
          ((0 : ℂ), q.2) ∈ 𝒲} := by
      refine ⟨hencP Z hZ b, ⟨hencP Z hZ b, ?_⟩, ⟨hencP Z hZ b, ?_⟩⟩
      · simpa [lp, ZOf, enc] using hZ a
      · simpa [lp, ZOf, enc] using hZ a'
    have hpq : AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → σ → ℂ) => pairParam a a' q.1) (b, Z) :=
      (analyticAt_pairParam (a := a) (a' := a') b).comp
        (analyticAt_fst (p := ((b, Z) : (ι → ℂ) × (ι → σ → ℂ))))
    exact (hE _ hmem).comp_of_eq (hpq.prod (henc (b, Z))) rfl
  -- For node tuples with convex hull in `D` and positive real parameters, the merging identity.
  have hreal : ∀ Z : ι → σ → ℂ, convexHull ℝ (range Z) ⊆ D →
      ∀ {F : (ι → ℂ) → ℂ}, IsRegDirichletContinuation (fun u => f (vecAffineForm Z u)) F →
      ∀ c : ι → ℝ, c ∈ mvRealBetaDomain →
        Φ ((fun i => (c i : ℂ)), Z) * Gamma ((c a : ℂ) + c a') = F (fun i => (c i : ℂ)) := by
    intro Z hZ F hF c hc
    set b : ι → ℂ := fun i => (c i : ℂ)
    have hZD : ∀ i, Z i ∈ D := fun i => hZ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    have hb : b ∈ mvBetaConvergent := fun i => by simpa [b] using hc i
    have hmb := mergeParam_ofReal_mem (a := a) (a' := a') hc
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ), enc (b, Z)) ∈ 𝒲 := by
      intro t ht
      refine ⟨hencP Z hZD b, hZ ?_⟩
      have hcomb := (convex_convexHull ℝ (range Z)) (subset_convexHull ℝ _ ⟨a, rfl⟩)
        (subset_convexHull ℝ _ ⟨a', rfl⟩) ht.1 (sub_nonneg.mpr ht.2) (add_sub_cancel t 1)
      convert hcomb using 1
      ext s
      simp [lp, ZOf, enc]
    have h1 := hEeq (enc (b, Z)) (hencP Z hZD b) hseg (pairParam a a' b)
      (pairParam_ofReal_mem hc)
    have hfc : ContinuousOn (fun u => f (vecAffineForm Z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι) := fun u hu =>
      ((hf _ (hZ (vecAffineForm_mem_convexHull Z hu))).continuousAt.comp
        (continuous_vecAffineForm Z).continuousAt).continuousWithinAt
    have hinner : regVecDirichletAverage (pairParam a a' b) (pairParam a a' Z)
        (fun w => G' (mergeParam a a' b,
          update (fun j : {i : ι // i ≠ a'} => Z j) (mergeIndex h) w)) =
        regVecDirichletAverage (pairParam a a' b) (pairParam a a' Z)
          (fun w => regVecDirichletAverage (mergeParam a a' b) (mergeNodes a a' Z w) f) := by
      apply regDirichletIntegral_congr
      intro u hu
      have hw : vecAffineForm (pairParam a a' Z) u ∈ convexHull ℝ (range Z) :=
        convexHull_pairParam_subset Z (vecAffineForm_mem_convexHull _ hu)
      simp only
      rw [update_eq_mergeNodes h]
      exact hG'.2 _ ((convexHull_mergeNodes_subset Z hw).trans hZ) hmb
    have hfin := regVecDirichletAverage_fin_two (pairParam a a' b) (pairParam a a' Z)
      (fun w => G' (mergeParam a a' b, update (fun j : {i : ι // i ≠ a'} => Z j) (mergeIndex h) w))
    have hmerge := regVecDirichletAverage_ofReal_eq_merge h hc Z hfc
    change E (pairParam a a' b, enc (b, Z)) * Gamma (b a + b a') = _
    rw [h1, hF.eq_native hb]
    change _ = regVecDirichletAverage b Z f
    rw [hmerge, ← hinner, hfin]
    simp only [pairParam, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [mul_comm]
    rfl
  -- Hence, for such node tuples, at every parameter.
  have hall : ∀ Z : ι → σ → ℂ, convexHull ℝ (range Z) ⊆ D →
      ∃ F : (ι → ℂ) → ℂ, IsRegDirichletContinuation (fun u => f (vecAffineForm Z u)) F ∧
        ∀ b, Φ (b, Z) = F b * (Gamma (b a + b a'))⁻¹ := by
    intro Z hZ
    obtain ⟨F, hF⟩ := exists_isRegDirichletContinuation_vecAverage hDo hf hZ
    refine ⟨F, hF, fun b => ?_⟩
    have hZD : ∀ i, Z i ∈ D := fun i => hZ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    have hrecip : AnalyticOnNhd ℂ (fun b : ι → ℂ => (Gamma (b a + b a'))⁻¹) univ := fun b _ =>
      (differentiable_one_div_Gamma.analyticAt (b a + b a')).comp_of_eq
        ((analyticAt_apply_coord a b).add (analyticAt_apply_coord a' b)) rfl
    have hΦZ : AnalyticOnNhd ℂ (fun b => Φ (b, Z)) univ := fun b _ =>
      (hΦ (b, Z) hZD).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    refine congrFun (analyticOnNhd_eq_of_eqOn_realDirichletDomain hΦZ (hF.1.mul hrecip) ?_) b
    intro c hc
    have hG : Gamma ((c a : ℂ) + c a') ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simpa using add_pos (hc a) (hc a'))
    simp only
    rw [← hreal Z hZ hF c hc]
    field_simp
  -- The continued two-node average vanishes on the exceptional hyperplanes.
  have hzero : ∀ (m : ℕ) (b : ι → ℂ) (Z : ι → σ → ℂ), (∀ i, Z i ∈ D) →
      b a + b a' = -m → Φ (b, Z) = 0 := by
    intro m b Z hZ hm
    set x₀ := Z a
    have hx₀ : x₀ ∈ D := hZ a
    let χ : (ι → ℂ) × (ι → σ → ℂ) → ℂ := fun q => Φ (update q.1 a' (-m - q.1 a), q.2)
    have hupd : ∀ c : ι → ℂ, AnalyticAt ℂ (fun c : ι → ℂ => update c a' (-m - c a)) c := by
      intro c
      refine analyticAt_pi_iff.mpr fun i => ?_
      by_cases hi : i = a'
      · subst hi
        simpa using (analyticAt_const (v := (-(m : ℂ)))).fun_sub (analyticAt_apply_coord a c)
      · simpa [update_of_ne hi] using analyticAt_apply_coord i c
    have hχ : AnalyticOnNhd ℂ χ (univ ×ˢ univ.pi fun _ : ι => D) := by
      rintro ⟨c, Z'⟩ ⟨-, hZ'⟩
      exact (hΦ (update c a' (-m - c a), Z') fun i => hZ' i (mem_univ i)).comp_of_eq
        (((hupd c).comp (analyticAt_fst (p := ((c, Z') : (ι → ℂ) × (ι → σ → ℂ))))).prod
          (analyticAt_snd (p := ((c, Z') : (ι → ℂ) × (ι → σ → ℂ))))) rfl
    have hconn : IsPreconnected ((univ : Set (ι → ℂ)) ×ˢ univ.pi fun _ : ι => D) :=
      isPreconnected_univ.prod (isPreconnected_univ_pi fun _ => hDl.isPreconnected)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hDo x₀ hx₀
    have hev : χ =ᶠ[𝓝 ((0 : ι → ℂ), fun _ : ι => x₀)] 0 := by
      have hnear : ∀ᶠ q : (ι → ℂ) × (ι → σ → ℂ) in 𝓝 ((0 : ι → ℂ), fun _ : ι => x₀),
          ∀ i, q.2 i ∈ Metric.ball x₀ r := by
        refine eventually_all.mpr fun i => ?_
        exact ((continuous_apply i).comp continuous_snd).continuousAt.preimage_mem_nhds
          (Metric.isOpen_ball.mem_nhds (by simpa using hr))
      filter_upwards [hnear] with q hq
      have hhull : convexHull ℝ (range q.2) ⊆ D :=
        (convexHull_min (by rintro _ ⟨i, rfl⟩; exact hq i) (convex_ball x₀ r)).trans hball
      obtain ⟨F, -, hFΦ⟩ := hall q.2 hhull
      simp only [Pi.zero_apply, χ]
      rw [hFΦ, update_of_ne h, update_self]
      have : q.1 a + (-(m : ℂ) - q.1 a) = -m := by ring
      rw [this, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    have hχ0 := hχ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
      ⟨mem_univ _, fun _ _ => hx₀⟩ hev
    have := hχ0 (show (b, Z) ∈ (univ : Set (ι → ℂ)) ×ˢ univ.pi fun _ : ι => D from
      ⟨mem_univ _, fun i _ => hZ i⟩)
    simp only [χ, Pi.zero_apply] at this
    rwa [show update b a' (-m - b a) = b by
      rw [update_eq_self_iff]; linear_combination -hm] at this
  -- Removal of the Gamma poles.
  let κ := {i : ι // i ≠ a'} ⊕ ι × σ
  let Ep : (ι → ℂ) × (ι → σ → ℂ) → Option κ → ℂ := fun q o =>
    o.elim (q.1 a + q.1 a') (Sum.elim (fun j => q.1 j) (fun k => q.2 k.1 k.2))
  let bOf' : (Option κ → ℂ) → ι → ℂ := fun q i =>
    if hi : i = a' then q none - q (some (Sum.inl (mergeIndex h)))
    else q (some (Sum.inl ⟨i, hi⟩))
  let zOf' : (Option κ → ℂ) → ι → σ → ℂ := fun q i s => q (some (Sum.inr (i, s)))
  let Φt : (Option κ → ℂ) → ℂ := fun q => Φ (bOf' q, zOf' q)
  let Ut : Set (Option κ → ℂ) := {q | ∀ i, zOf' q i ∈ D}
  have hUt : IsOpen Ut := by
    simp only [Ut, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hDo.preimage
      (continuous_pi fun s => continuous_apply (some (Sum.inr (i, s))))
  have hbOf' : ∀ q, AnalyticAt ℂ bOf' q := by
    intro q
    refine analyticAt_pi_iff.mpr fun i => ?_
    by_cases hi : i = a'
    · subst hi
      simpa [bOf'] using (analyticAt_apply_coord none q).fun_sub
        (analyticAt_apply_coord (some (Sum.inl (mergeIndex h))) q)
    · simpa [bOf', hi] using analyticAt_apply_coord (some (Sum.inl ⟨i, hi⟩)) q
  have hzOf' : ∀ q, AnalyticAt ℂ zOf' q := fun q => analyticAt_pi_iff.mpr fun i =>
    analyticAt_pi_iff.mpr fun s => analyticAt_apply_coord (some (Sum.inr (i, s))) q
  have hΦt : AnalyticOnNhd ℂ Φt Ut := fun q hq =>
    (hΦ (bOf' q, zOf' q) hq).comp_of_eq ((hbOf' q).prod (hzOf' q)) rfl
  have hΦt0 : ∀ q ∈ Ut, Gamma (q none) = 0 → Φt q = 0 := by
    intro q hq hΓ
    obtain ⟨m, hm⟩ := (Gamma_eq_zero_iff _).mp hΓ
    apply hzero m _ _ hq
    simp only [bOf', h, dite_false, dite_true]
    have : (⟨a, h⟩ : {i : ι // i ≠ a'}) = mergeIndex h := rfl
    rw [this, ← hm]; ring
  have hK := Complex.analyticOnNhd_GammaRemovedValue hUt hΦt hΦt0
  have hbE : ∀ q, bOf' (Ep q) = q.1 := by
    intro q; funext i
    by_cases hi : i = a'
    · subst hi; simp [bOf', Ep, mergeIndex]
    · simp [bOf', Ep, hi]
  have hzE : ∀ q, zOf' (Ep q) = q.2 := fun q => rfl
  have hEp : ∀ q, AnalyticAt ℂ Ep q := by
    intro q
    refine analyticAt_pi_iff.mpr fun o => ?_
    rcases o with _ | j | ⟨i, s⟩
    · exact ((analyticAt_apply_coord a q.1).comp analyticAt_fst).add
        ((analyticAt_apply_coord a' q.1).comp analyticAt_fst)
    · exact (analyticAt_apply_coord (j : ι) q.1).comp analyticAt_fst
    · exact (analyticAt_node_apply i s q.2).comp analyticAt_snd
  refine ⟨fun q => Complex.GammaRemovedValue Φt (Ep q), fun q hq => ?_, fun Z hZ => ?_⟩
  · exact (hK (Ep q) hq).comp_of_eq (hEp q) rfl
  · have hZD : ∀ i, Z i ∈ D := fun i => hZ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    obtain ⟨F, hF, -⟩ := hall Z hZ
    have hGZ : AnalyticOnNhd ℂ (fun b => Complex.GammaRemovedValue Φt (Ep (b, Z))) univ :=
      fun b _ => (hK (Ep (b, Z)) hZD).comp_of_eq
        ((hEp (b, Z)).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl) rfl
    have hcont : IsRegDirichletContinuation (fun u => f (vecAffineForm Z u))
        (fun b => Complex.GammaRemovedValue Φt (Ep (b, Z))) := by
      refine IsRegDirichletContinuation.mk_of_eqOn_realDirichletDomain hGZ hF ?_
      intro c hc
      have hpos : ∀ m : ℕ, Ep ((fun i => (c i : ℂ)), Z) none ≠ -m := by
        intro m hm
        have := congrArg re hm
        simp only [Ep, Option.elim, add_re, ofReal_re, neg_re, natCast_re] at this
        linarith [hc a, hc a', (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      rw [Complex.GammaRemovedValue_of_ne _ hpos]
      change Gamma ((c a : ℂ) + c a') * Φ (bOf' (Ep _), zOf' (Ep _)) = _
      rw [hbE, hzE, ← hreal Z hZ hF c hc]
      ring
    exact fun b hb => hcont.eq_native hb

/-- **Continuation of Dirichlet averages of functions of several variables.** Let `f` be
holomorphic on an open set `D ⊆ ℂ^σ` whose sections by the complex lines through any two of its
points are simply connected. The regularized Dirichlet average of `f` with any finite number of
vector nodes has a continuation that is entire in the Dirichlet parameters and holomorphic in
all nodes in `D`, coincident nodes included, and that agrees with the native average whenever
the convex hull of the nodes lies in `D` and the Dirichlet parameters have positive real
parts. -/
theorem exists_isJointRegVecContinuationOn {D : Set (σ → ℂ)} (hDo : IsOpen D)
    (hDl : HasSimplyConnectedLineSections D) {f : (σ → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f D)
    (ι : Type*) [Fintype ι] :
    ∃ G : (ι → ℂ) × (ι → σ → ℂ) → ℂ, IsJointRegVecContinuationOn D f G := by
  induction h : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
    classical
    by_cases hn : n ≤ 1
    · exact exists_isJointRegVecContinuationOn_of_card_le_one (h ▸ hn) hDo hf
    obtain ⟨a, a', hne⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card ι)
    have hcard : Fintype.card {i : ι // i ≠ a'} < n := by
      rw [← h]; simp; omega
    obtain ⟨G', hG'⟩ := ih _ hcard {i : ι // i ≠ a'} rfl
    exact exists_isJointRegVecContinuationOn_merge hDo hDl hf hne hG'

/-! ### Examples: convex domains and planar simply connected domains -/

omit [Fintype σ] in
/-- A convex open domain has simply connected (indeed convex) line sections. -/
theorem _root_.Convex.hasSimplyConnectedLineSections {D : Set (σ → ℂ)} (hD : Convex ℝ D) :
    HasSimplyConnectedLineSections D := by
  intro x hx y hy
  have hconv : Convex ℝ {t : ℂ | t • x + (1 - t) • y ∈ D} := by
    intro t₁ ht₁ t₂ ht₂ α β hα hβ hαβ
    show (α • t₁ + β • t₂) • x + (1 - (α • t₁ + β • t₂)) • y ∈ D
    convert hD ht₁ ht₂ hα hβ hαβ using 1
    have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
    ext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    linear_combination (-(y s)) * hαβ'
  have hne : {t : ℂ | t • x + (1 - t) • y ∈ D}.Nonempty := ⟨0, by simpa using hy⟩
  have : ContractibleSpace {t : ℂ | t • x + (1 - t) • y ∈ D} := hconv.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- A planar domain, viewed in `ℂ^Unit`. -/
def planarDomain (D : Set ℂ) : Set (Unit → ℂ) := {x | x () ∈ D}

/-- A simply connected planar domain has simply connected line sections: each section is an
affine preimage of the domain, or the whole plane. -/
theorem _root_.IsSimplyConnected.hasSimplyConnectedLineSections {D : Set ℂ}
    (hD : IsSimplyConnected D) : HasSimplyConnectedLineSections (planarDomain D) := by
  intro x hx y hy
  by_cases hxy : x () = y ()
  · have huniv : {t : ℂ | t • x + (1 - t) • y ∈ planarDomain D} = univ := by
      ext t
      simp only [planarDomain, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxy,
        mem_univ, iff_true]
      have hy' : y () ∈ D := hy
      convert hy' using 1
      ring
    rw [huniv]
    have : ContractibleSpace (univ : Set ℂ) := convex_univ.contractibleSpace univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  · let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (x () - y ()) (sub_ne_zero.mpr hxy)).trans
      (Homeomorph.addLeft (y ()))
    have he : {t : ℂ | t • x + (1 - t) • y ∈ planarDomain D} = e ⁻¹' D := by
      ext t
      simp only [planarDomain, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        mem_preimage, e, Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀,
        Homeomorph.coe_addLeft]
      ring_nf
    rw [he, e.isSimplyConnected_preimage]
    exact hD

/-- **Carlson (1969), Theorem 8, simply connected case, recovered** from the several-variables
theorem with a single coordinate. This is a second proof of
`Dirichlet.exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected`, through the merging
identity for general kernels and the continuation of Euler integrals over simply connected
fibres. -/
theorem exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected_of_lineSections
    {D : Set ℂ} (hDo : IsOpen D) (hDs : IsSimplyConnected D) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (ι : Type*) [Fintype ι] :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ, IsJointRegCarlsonContinuationOn D f G := by
  have hD₁o : IsOpen (planarDomain D) := hDo.preimage (continuous_apply ())
  have hf₁ : AnalyticOnNhd ℂ (fun x : Unit → ℂ => f (x ())) (planarDomain D) := fun x hx =>
    (hf _ hx).comp_of_eq (analyticAt_apply_coord () x) rfl
  obtain ⟨Gv, hGv⟩ := exists_isJointRegVecContinuationOn hD₁o
    hDs.hasSimplyConnectedLineSections hf₁ ι
  let L : (ι → ℂ) → ι → Unit → ℂ := fun z i _ => z i
  have hL : ∀ z, AnalyticAt ℂ L z := fun z =>
    analyticAt_pi_iff.mpr fun i => analyticAt_pi_iff.mpr fun _ => analyticAt_apply_coord i z
  refine ⟨fun p => Gv (p.1, L p.2), fun p hp => ?_, fun z hz b hb => ?_⟩
  · exact (hGv.1 _ fun i => hp ⟨i, rfl⟩).comp_of_eq
      (analyticAt_fst.prod ((hL p.2).comp analyticAt_snd)) rfl
  · let ℓ : ℂ →ₗ[ℝ] (Unit → ℂ) :=
      { toFun := fun w _ => w, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hrange : range (L z) = ℓ '' range z := by
      ext x
      simp only [mem_range, mem_image, exists_exists_eq_and]
      rfl
    have hhull : convexHull ℝ (range (L z)) ⊆ planarDomain D := by
      rw [hrange, ← ℓ.image_convexHull]
      rintro _ ⟨w, hw, rfl⟩
      exact hz hw
    rw [hGv.2 (L z) hhull hb]
    show regDirichletIntegral b _ = regDirichletIntegral b _
    congr 1
    funext u
    simp [vecAffineForm, carlsonAffineForm, L, Finset.sum_apply]

end Dirichlet

end
