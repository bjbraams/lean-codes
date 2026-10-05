/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.TwoNode

/-!
# Two-node continuation over simply connected fibres

Let `g (w, p)` be holomorphic on an open set `𝒲 ⊆ ℂ × P` whose fibres `D_p = {w | (w, p) ∈ 𝒲}`
are simply connected. The regularized two-node Dirichlet average of `g (·, p)`, equivalently the
regularized Euler integral of `t ↦ g (t x + (1 - t) y, p)`, is defined natively when the segment
joining the nodes `x, y` lies in `D_p`. We show that it continues to a function holomorphic in
the Dirichlet parameters, the nodes and the parameter on the whole open set where both nodes lie
in the fibre: continuation is possible as long as the endpoints stay in the simply connected
fibre, however the fibre moves with the parameter.

For a product `𝒲 = D × P` this is `Dirichlet.exists_twoNode_continuation`. In general a single
convex chart of all fibres is not available. The continuation is defined fibre by fibre, with a
Riemann chart of each fibre; near a given parameter it agrees, by the identity theorem in the
Dirichlet parameters and the nodes, with the continuation built on a relatively compact chart
piece of one fibre, which lies in all nearby fibres. This gives holomorphy in the parameter.

## Main results

* `Dirichlet.IsConvexChart.exists_restrict`: a relatively compact chart piece containing two
  given points.
* `Dirichlet.exists_twoNode_continuation_of_fibres`: the continuation over simply connected
  fibres.
* `Dirichlet.exists_regEulerIntegral_continuation_of_fibres`: the same for Euler integrals with
  fixed endpoints `0` and `1`.

## References

* B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), 116–148, Theorem 8.
-/

open Complex Set Filter Metric
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

/-- **Relatively compact chart pieces.** Two points of the target of a convex chart lie in the
target of a restricted convex chart whose target is contained in a compact subset of the
original target. The source of the restricted chart is a thickening of the segment joining the
two chart coordinates. -/
theorem IsConvexChart.exists_restrict {D V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hC : IsConvexChart D V φ ψ) {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) :
    ∃ (V' D' K : Set ℂ), IsConvexChart D' V' φ ψ ∧ x ∈ D' ∧ y ∈ D' ∧ IsCompact K ∧
      D' ⊆ K ∧ K ⊆ D := by
  have hseg : segment ℝ (ψ x) (ψ y) ⊆ V :=
    hC.convex_source.segment_subset (hC.mapsTo_inv hx) (hC.mapsTo_inv hy)
  have hcs : IsCompact (segment ℝ (ψ x) (ψ y)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨r, hr, hsub⟩ := hcs.exists_cthickening_subset_open hC.isOpen_source hseg
  set V' := thickening r (segment ℝ (ψ x) (ψ y))
  have hV'V : V' ⊆ V := (thickening_subset_cthickening _ _).trans hsub
  have hmem {s : ℂ} (hs : s ∈ segment ℝ (ψ x) (ψ y)) : s ∈ V' := self_subset_thickening hr _ hs
  refine ⟨V', D ∩ ψ ⁻¹' V', φ '' cthickening r (segment ℝ (ψ x) (ψ y)), ⟨isOpen_thickening,
    (convex_segment _ _).thickening r, ⟨ψ x, hmem (left_mem_segment ℝ _ _)⟩,
    hC.analyticOnNhd_inv.continuousOn.isOpen_inter_preimage hC.isOpen_target isOpen_thickening,
    hC.analyticOnNhd.mono hV'V, hC.analyticOnNhd_inv.mono inter_subset_left,
    fun s hs => ⟨hC.mapsTo (hV'V hs), by simpa [hC.left_inv s (hV'V hs)] using hs⟩,
    fun w hw => hw.2, fun s hs => hC.left_inv s (hV'V hs), fun w hw => hC.right_inv w hw.1⟩,
    ⟨hx, hmem (left_mem_segment ℝ _ _)⟩, ⟨hy, hmem (right_mem_segment ℝ _ _)⟩,
    hcs.cthickening.image_of_continuousOn
      (hC.analyticOnNhd.continuousOn.mono hsub), ?_, ?_⟩
  · intro w hw
    exact ⟨ψ w, thickening_subset_cthickening _ _ hw.2, hC.right_inv w hw.1⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hC.mapsTo (hsub hs)

/-- The pairs of points of the target of a convex chart form a preconnected set. -/
theorem IsConvexChart.isPreconnected_pairDomain {D V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hC : IsConvexChart D V φ ψ) : IsPreconnected (pairDomain D) := by
  have himage : (fun c : Fin 2 → ℂ => fun i => φ (c i)) '' pairDomain V = pairDomain D := by
    refine Subset.antisymm ?_ fun z hz => ⟨fun i => ψ (z i), ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨hC.mapsTo hc.1, hC.mapsTo hc.2⟩
    · exact ⟨hC.mapsTo_inv hz.1, hC.mapsTo_inv hz.2⟩
    · funext i
      fin_cases i
      · exact hC.right_inv _ hz.1
      · exact hC.right_inv _ hz.2
  rw [← himage]
  refine (convex_pairDomain hC.convex_source).isPreconnected.image _ ?_
  refine continuousOn_pi.mpr fun i => ?_
  refine hC.analyticOnNhd.continuousOn.comp (continuous_apply i).continuousOn fun c hc => ?_
  fin_cases i
  · exact hc.1
  · exact hc.2

/-- The fibre of an open set of `ℂ × (σ → ℂ)` over a parameter is open. -/
theorem isOpen_fibre {σ : Type*} {𝒲 : Set (ℂ × (σ → ℂ))} (h𝒲 : IsOpen 𝒲) (p : σ → ℂ) :
    IsOpen {w : ℂ | (w, p) ∈ 𝒲} :=
  h𝒲.preimage (continuous_id.prodMk continuous_const)

/-- **Two-node continuation over simply connected fibres.** Let `g` be holomorphic on an open set
`𝒲 ⊆ ℂ × (σ → ℂ)` whose fibres over the open parameter set `P` are simply connected. There is a
function of the Dirichlet parameters, the two nodes and the parameter, holomorphic wherever the
parameter lies in `P` and both nodes lie in its fibre, that agrees with the regularized two-node
average of `g (·, p)` whenever the segment of the nodes lies in the fibre and the Dirichlet
parameters have positive real parts. -/
theorem exists_twoNode_continuation_of_fibres {σ : Type*} [Fintype σ]
    {𝒲 : Set (ℂ × (σ → ℂ))} (h𝒲 : IsOpen 𝒲) {P : Set (σ → ℂ)} (hP : IsOpen P)
    {g : ℂ × (σ → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g 𝒲)
    (hsc : ∀ p ∈ P, IsSimplyConnected {w : ℂ | (w, p) ∈ 𝒲}) :
    ∃ G : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) × (σ → ℂ) → ℂ,
      AnalyticOnNhd ℂ G {q | q.2 ∈ P ∧ ∀ i, (q.1.2 i, q.2) ∈ 𝒲} ∧
      ∀ p ∈ P, ∀ z : Fin 2 → ℂ, convexHull ℝ (range z) ⊆ {w : ℂ | (w, p) ∈ 𝒲} →
        ∀ b ∈ mvBetaConvergent,
          G ((b, z), p) = regCarlsonDirichletAverage b z (fun w => g (w, p)) := by
  set D : (σ → ℂ) → Set ℂ := fun p => {w : ℂ | (w, p) ∈ 𝒲}
  -- The fibrewise continuation, from a Riemann chart of each fibre.
  have hfib (p : σ → ℂ) : ∃ Gp : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ, p ∈ P →
      AnalyticOnNhd ℂ Gp (univ ×ˢ pairDomain (D p)) ∧
      ∀ z : Fin 2 → ℂ, convexHull ℝ (range z) ⊆ D p → ∀ b ∈ mvBetaConvergent,
        Gp (b, z) = regCarlsonDirichletAverage b z (fun w => g (w, p)) := by
    by_cases hp : p ∈ P
    · have hgp : AnalyticOnNhd ℂ (fun q : ℂ × (σ → ℂ) => g (q.1, p)) (D p ×ˢ univ) :=
        fun q hq => (hg _ hq.1).comp_of_eq (analyticAt_fst.prod analyticAt_const) rfl
      obtain ⟨G₀, hG₀, hG₀eq⟩ := exists_twoNode_continuation (isOpen_fibre h𝒲 p) (hsc p hp)
        isOpen_univ hgp
      refine ⟨fun c => G₀ (c, 0), fun _ => ⟨fun c hc => ?_, fun z hz b hb => ?_⟩⟩
      · exact (hG₀ (c, 0) ⟨hc, mem_univ _⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
      · exact hG₀eq 0 (mem_univ _) z hz b hb
    · exact ⟨0, fun h => absurd h hp⟩
  choose Gf hGf using hfib
  refine ⟨fun q => Gf q.2 q.1, ?_, fun p hp z hz b hb => (hGf p hp).2 z hz b hb⟩
  rintro ⟨⟨b₀, z₀⟩, p₀⟩ ⟨hp₀, hz₀⟩
  -- A relatively compact chart piece of the fibre over `p₀` containing both nodes.
  obtain ⟨V, φ, ψ, hC⟩ :=
    IsConvexChart.exists_of_isSimplyConnected (isOpen_fibre h𝒲 p₀) (hsc p₀ hp₀)
  obtain ⟨V', D', K, hC', hx, hy, hK, hD'K, hKD⟩ := hC.exists_restrict (hz₀ 0) (hz₀ 1)
  -- The compact set lies in all nearby fibres.
  obtain ⟨u, N, -, hN, hKu, hpN, huN⟩ := generalized_tube_lemma hK isCompact_singleton h𝒲
    (fun q hq => by
      obtain ⟨hq1, hq2⟩ := hq
      rw [mem_singleton_iff] at hq2
      rw [← Prod.mk.eta (p := q), hq2]
      exact hKD hq1)
  have hKN : ∀ w ∈ K, ∀ p ∈ N, (w, p) ∈ 𝒲 := fun w hw p hp => huN ⟨hKu hw, hp⟩
  have hp₀N : p₀ ∈ N := hpN rfl
  -- The local continuation on the chart piece, holomorphic in the parameter.
  have hgl : AnalyticOnNhd ℂ g (D' ×ˢ (P ∩ N)) := fun q hq =>
    hg q (by simpa using hKN q.1 (hD'K hq.1) q.2 hq.2.2)
  obtain ⟨Gl, hGl, hGleq⟩ := exists_twoNode_continuation_of_chart hC' (hP.inter hN) hgl
  -- On the chart piece the local and fibrewise continuations agree.
  have hagree : ∀ p ∈ P ∩ N, ∀ c ∈ univ ×ˢ pairDomain D', Gl (c, p) = Gf p c := by
    intro p hp
    have hD'p : D' ⊆ D p := fun w hw => hKN w (hD'K hw) p hp.2
    have hA : AnalyticOnNhd ℂ (fun c => Gl (c, p)) (univ ×ˢ pairDomain D') := fun c hc =>
      (hGl (c, p) ⟨hc, hp⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have hB : AnalyticOnNhd ℂ (Gf p) (univ ×ˢ pairDomain D') := fun c hc =>
      (hGf p hp.1).1 c ⟨mem_univ _, hD'p hc.2.1, hD'p hc.2.2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hC'.isOpen_target _ hx
    set c₀ : (Fin 2 → ℂ) × (Fin 2 → ℂ) := (fun _ => 1, ![z₀ 0, z₀ 0])
    have hc₀ : c₀ ∈ univ ×ˢ pairDomain D' := ⟨mem_univ _, hx, hx⟩
    have hev : ∀ᶠ c in 𝓝 c₀, c.1 ∈ mvBetaConvergent ∧ c.2 0 ∈ ball (z₀ 0) ε ∧
        c.2 1 ∈ ball (z₀ 0) ε := by
      have hco (i : Fin 2) : Continuous fun c : (Fin 2 → ℂ) × (Fin 2 → ℂ) => c.2 i :=
        (continuous_apply i).comp continuous_snd
      refine ((isOpen_mvBetaConvergent.preimage continuous_fst).inter
        ((isOpen_ball.preimage (hco 0)).inter (isOpen_ball.preimage (hco 1)))).mem_nhds ?_
      refine ⟨fun i => by simp [c₀], ?_, ?_⟩ <;> simp [c₀, hε]
    refine hA.eqOn_of_preconnected_of_eventuallyEq hB
      (isPreconnected_univ.prod hC'.isPreconnected_pairDomain) hc₀ ?_
    filter_upwards [hev] with c hc
    have hhull : convexHull ℝ (range c.2) ⊆ D' := by
      refine (convexHull_min ?_ (convex_ball (z₀ 0) ε)).trans hball
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hc.2.1
      · exact hc.2.2
    rw [← Prod.mk.eta (p := c), hGleq p hp c.2 hhull c.1 hc.1,
      (hGf p hp.1).2 c.2 (hhull.trans hD'p) c.1 hc.1]
  -- Hence the fibrewise continuation is holomorphic near `((b₀, z₀), p₀)`.
  have hq₀ : ((b₀, z₀), p₀) ∈ (univ ×ˢ pairDomain D') ×ˢ (P ∩ N) :=
    ⟨⟨mem_univ _, hx, hy⟩, hp₀, hp₀N⟩
  refine (hGl _ hq₀).congr ?_
  filter_upwards [((isOpen_univ.prod (isOpen_pairDomain hC'.isOpen_target)).prod
    (hP.inter hN)).mem_nhds hq₀] with q hq
  exact hagree q.2 hq.2 q.1 hq.1

/-- **Euler integrals over simply connected fibres.** Let `g (t, p)` be holomorphic on an open
set `𝒲 ⊆ ℂ × (σ → ℂ)` whose fibres over the open parameter set `P` are simply connected. The
regularized Euler integral `(Γ(α) Γ(β))⁻¹ ∫₀¹ t^(α - 1) (1 - t)^(β - 1) g (t, p) dt` continues
to a function entire in `(α, β)` and holomorphic in `p` wherever `p ∈ P` and the endpoints `0`
and `1` lie in the fibre over `p`. -/
theorem exists_regEulerIntegral_continuation_of_fibres {σ : Type*} [Fintype σ]
    {𝒲 : Set (ℂ × (σ → ℂ))} (h𝒲 : IsOpen 𝒲) {P : Set (σ → ℂ)} (hP : IsOpen P)
    {g : ℂ × (σ → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g 𝒲)
    (hsc : ∀ p ∈ P, IsSimplyConnected {w : ℂ | (w, p) ∈ 𝒲}) :
    ∃ E : (Fin 2 → ℂ) × (σ → ℂ) → ℂ,
      AnalyticOnNhd ℂ E {q | q.2 ∈ P ∧ ((1 : ℂ), q.2) ∈ 𝒲 ∧ ((0 : ℂ), q.2) ∈ 𝒲} ∧
      ∀ p ∈ P, (∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ), p) ∈ 𝒲) → ∀ b ∈ mvBetaConvergent,
        E (b, p) = regEulerIntegral (b 0) (b 1) (fun t : ℝ => g ((t : ℂ), p)) := by
  obtain ⟨G, hG, hGeq⟩ := exists_twoNode_continuation_of_fibres h𝒲 hP hg hsc
  refine ⟨fun q => G ((q.1, ![1, 0]), q.2), fun q hq => ?_, fun p hp hseg b hb => ?_⟩
  · refine (hG _ ⟨hq.1, fun i => ?_⟩).comp_of_eq
      ((analyticAt_fst.prod analyticAt_const).prod analyticAt_snd) rfl
    fin_cases i
    · exact hq.2.1
    · exact hq.2.2
  · have hhull : convexHull ℝ (range (![1, 0] : Fin 2 → ℂ)) ⊆ {w : ℂ | (w, p) ∈ 𝒲} := by
      rw [show range (![1, 0] : Fin 2 → ℂ) = {1, 0} by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, union_empty,
          singleton_union], convexHull_pair, segment_eq_image]
      rintro _ ⟨θ, hθ, rfl⟩
      have h := hseg (1 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
      simpa using h
    simp only
    rw [hGeq p hp _ hhull b hb, regCarlsonDirichletAverage_fin_two]
    simp

end Dirichlet

end
