/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Polygon
public import ComplexAnalysis.HolomorphicInverse
public import ToMathlib.Topology.ProperCovering

/-!
# The Schwarz–Christoffel mapping theorem (Carlson's Theorem 8.2-1)

For distinct real nodes `xᵢ`, exponents `0 < bᵢ < 1` and `0 < a ≤ 1` with `a + 1 = ∑ bᵢ`, the map
`w(z) = R_{-a}(b; z - x)` maps the open upper half-plane conformally and one-to-one onto the open
convex polygon `scPolygon a b x`. Its vertices are the boundary values `w(xᵢ)` and `w(∞) = 0`,
and its inner angles are `(1 - bᵢ)π` and `aπ`.

Carlson refers to Markushevich for the proof that the mapping is one-to-one and onto. The proof
here is topological. The map `w` sends the upper half-plane into the polygon (module
`Carlson.Elliptic.Polygon`). It is a local homeomorphism because `w' ≠ 0`. It is proper, because it
extends continuously to the closed half-plane with `w(∞) = 0`, and the real axis and `∞` map to
the boundary of the polygon. A proper local homeomorphism is a covering map, and a covering of the
simply connected convex polygon by the connected half-plane is injective. The image is open and
closed in the connected polygon, hence all of it. The inverse map is holomorphic.

## Main results

* `Carlson.injOn_scMap`, `Carlson.image_scMap`, `Carlson.bijOn_scMap`: Theorem 8.2-1.
* `Carlson.scMapInv`, `Carlson.differentiableOn_scMapInv`: the holomorphic inverse map.
* `Carlson.scAngle_sub_scAngle`: the turning angles of the polygon.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
* A. I. Markushevich, *Theory of Functions of a Complex Variable*, Vol. 2, 1965.
-/

open Complex Set Filter Topology
open scoped Real
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι] {a : ℝ} {b x : ι → ℝ}

/-- The open upper half-plane as a set. -/
abbrev upperHalfPlaneSet' : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperHalfPlaneSet' : IsOpen upperHalfPlaneSet' :=
  isOpen_lt continuous_const continuous_im

/-- The Schwarz–Christoffel map as a map from the upper half-plane to its polygon. -/
def scMapRestrict (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) :
    upperHalfPlaneSet' → scPolygon a b x :=
  fun z => ⟨scMap a b x z, scMap_mem_scPolygon h ha1 z.2⟩

section Restrict

variable (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1)
include h ha1

theorem continuous_scMapRestrict : Continuous (scMapRestrict h ha1) := by
  refine Continuous.subtype_mk ?_ _
  exact ((continuousOn_scMap h).mono fun z (hz : 0 < z.im) =>
    (le_of_lt hz : 0 ≤ z.im)).comp_continuous
    continuous_subtype_val fun z => z.2

theorem isOpenMap_scMapRestrict : IsOpenMap (scMapRestrict h ha1) := by
  intro O hO
  have hO' : IsOpen (Subtype.val '' O : Set ℂ) :=
    isOpen_upperHalfPlaneSet'.isOpenMap_subtype_val O hO
  have himg := isOpen_image_scMap h hO' (by rintro _ ⟨z, _, rfl⟩; exact z.2)
  have heq : scMapRestrict h ha1 '' O =
      Subtype.val ⁻¹' (scMap a b x '' (Subtype.val '' O)) := by
    ext ⟨ζ, hζ⟩
    simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
      scMapRestrict, Subtype.mk.injEq]
  rw [heq]
  exact himg.preimage continuous_subtype_val

theorem locallyInjective_scMapRestrict (z : upperHalfPlaneSet') :
    ∃ U ∈ 𝓝 z, InjOn (scMapRestrict h ha1) U := by
  have hd := hasStrictDerivAt_scMap h z.2
  have hne := neg_mul_scIntegrand_ne_zero h z.2
  have hev := hd.eventually_left_inverse hne
  refine ⟨Subtype.val ⁻¹' {w | hd.localInverse _ _ _ hne (scMap a b x w) = w},
    continuous_subtype_val.continuousAt.preimage_mem_nhds hev, ?_⟩
  intro u hu v hv huv
  have huv' : scMap a b x u = scMap a b x v := congrArg Subtype.val huv
  have hu' : _ = (u : ℂ) := hu
  have hv' : _ = (v : ℂ) := hv
  exact Subtype.ext (by rw [← hu', ← hv', huv'])

theorem isLocalHomeomorph_scMapRestrict : IsLocalHomeomorph (scMapRestrict h ha1) :=
  isLocalHomeomorph_of_isOpenMap_of_injOn (continuous_scMapRestrict h ha1)
    (isOpenMap_scMapRestrict h ha1) (locallyInjective_scMapRestrict h ha1)

omit ha1 in
/-- The compact subsets of the polygon have compact preimages in the upper half-plane. -/
theorem isCompact_preimage_scMap {K : Set ℂ} (hK : IsCompact K) (hKP : K ⊆ scPolygon a b x) :
    IsCompact (closedUpperHalfPlane ∩ scMap a b x ⁻¹' K) ∧
      closedUpperHalfPlane ∩ scMap a b x ⁻¹' K ⊆ upperHalfPlaneSet' := by
  have hclosed : IsClosed (closedUpperHalfPlane ∩ scMap a b x ⁻¹' K) :=
    (continuousOn_scMap h).preimage_isClosed_of_isClosed isClosed_closedUpperHalfPlane hK.isClosed
  have h0 : (0 : ℂ) ∉ K := fun h0 => zero_notMem_scPolygon (hKP h0)
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 closedUpperHalfPlane, scMap a b x z ∉ K :=
    (tendsto_scMap_cobounded h).eventually (hK.isClosed.isOpen_compl.mem_nhds h0)
  rw [eventually_inf_principal] at hev
  obtain ⟨R, -, hR⟩ := (Filter.hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp hev
  have hbdd : Bornology.IsBounded (closedUpperHalfPlane ∩ scMap a b x ⁻¹' K) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    rintro z ⟨hz, hzK⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc
    exact hR (le_of_lt (not_le.mp hc)) hz hzK
  refine ⟨Metric.isCompact_of_isClosed_isBounded hclosed hbdd, ?_⟩
  rintro z ⟨hz, hzK⟩
  rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [heq.symm])
    rw [mem_preimage, hz'] at hzK
    exact scMap_ofReal_notMem_scPolygon h z.re (hKP hzK)

theorem isProperMap_scMapRestrict : IsProperMap (scMapRestrict h ha1) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_scMapRestrict h ha1, fun K hK => ?_⟩
  set K' : Set ℂ := Subtype.val '' K
  have hK' : IsCompact K' := hK.image continuous_subtype_val
  have hK'P : K' ⊆ scPolygon a b x := by rintro _ ⟨ζ, _, rfl⟩; exact ζ.2
  obtain ⟨hc, hsub⟩ := isCompact_preimage_scMap h hK' hK'P
  rw [Subtype.isCompact_iff]
  convert hc using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨show (0 : ℝ) ≤ (w : ℂ).im from le_of_lt w.2, ⟨_, hw, rfl⟩⟩
  · rintro ⟨hz, ⟨ζ, hζ, hζz⟩⟩
    have hzH : 0 < z.im := hsub ⟨hz, ⟨ζ, hζ, hζz⟩⟩
    refine ⟨⟨z, hzH⟩, ?_, rfl⟩
    show scMapRestrict h ha1 ⟨z, hzH⟩ ∈ K
    convert hζ
    exact Subtype.ext hζz.symm

theorem scPolygon_nonempty : (scPolygon a b x).Nonempty :=
  ⟨_, scMap_mem_scPolygon h ha1 (z := I) (by simp)⟩

theorem injective_scMapRestrict : Function.Injective (scMapRestrict h ha1) := by
  have : PathConnectedSpace upperHalfPlaneSet' := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact (convex_halfSpace_im_gt 0).isPathConnected ⟨I, by simp⟩
  have : ContractibleSpace (scPolygon a b x) :=
    convex_scPolygon.contractibleSpace (scPolygon_nonempty h ha1)
  exact (isLocalHomeomorph_scMapRestrict h ha1).injective_of_isProperMap
    (isProperMap_scMapRestrict h ha1)

theorem surjective_scMapRestrict : Function.Surjective (scMapRestrict h ha1) := by
  have : PreconnectedSpace (scPolygon a b x) := by
    rw [← isPreconnected_iff_preconnectedSpace]
    exact convex_scPolygon.isPreconnected
  have hclopen : IsClopen (range (scMapRestrict h ha1)) :=
    ⟨(isProperMap_scMapRestrict h ha1).isClosedMap.isClosed_range,
      (isOpenMap_scMapRestrict h ha1).isOpen_range⟩
  have hne : (range (scMapRestrict h ha1)).Nonempty := ⟨_, ⟨⟨I, by simp⟩, rfl⟩⟩
  exact range_eq_univ.mp (hclopen.eq_univ hne)

end Restrict

/-- **Carlson's Theorem 8.2-1, one-to-one**: for `0 < a ≤ 1` the Schwarz–Christoffel map is
injective on the open upper half-plane. -/
theorem injOn_scMap (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) :
    InjOn (scMap a b x) upperHalfPlaneSet' := by
  intro u hu v hv huv
  have := injective_scMapRestrict h ha1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) (Subtype.ext huv)
  exact congrArg Subtype.val this

/-- **Carlson's Theorem 8.2-1, onto**: the image of the open upper half-plane is the open polygon
`scPolygon a b x`. -/
theorem image_scMap (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) :
    scMap a b x '' upperHalfPlaneSet' = scPolygon a b x := by
  refine Subset.antisymm ?_ fun ζ hζ => ?_
  · rintro _ ⟨z, hz, rfl⟩; exact scMap_mem_scPolygon h ha1 hz
  · obtain ⟨z, hz⟩ := surjective_scMapRestrict h ha1 ⟨ζ, hζ⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩

/-- **Carlson's Theorem 8.2-1**: for distinct real nodes `xᵢ`, exponents `0 < bᵢ < 1` and
`0 < a ≤ 1` with `a + 1 = ∑ bᵢ`, the map `w(z) = R_{-a}(b; z - x)` is a bijection from the open
upper half-plane onto the open convex polygon `scPolygon a b x`, holomorphic with nonvanishing
derivative. -/
theorem bijOn_scMap (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) :
    BijOn (scMap a b x) upperHalfPlaneSet' (scPolygon a b x) := by
  refine ⟨fun z hz => scMap_mem_scPolygon h ha1 hz, injOn_scMap h ha1, ?_⟩
  rw [← image_scMap h ha1]
  exact subset_rfl

/-- The inverse of the Schwarz–Christoffel map, from the polygon to the upper half-plane. -/
def scMapInv (a : ℝ) (b x : ι → ℝ) : ℂ → ℂ := Function.invFunOn (scMap a b x) upperHalfPlaneSet'

theorem scMapInv_mem (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) {ζ : ℂ}
    (hζ : ζ ∈ scPolygon a b x) : 0 < (scMapInv a b x ζ).im := by
  rw [← image_scMap h ha1] at hζ
  exact Function.invFunOn_mem hζ

theorem scMap_scMapInv (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) {ζ : ℂ}
    (hζ : ζ ∈ scPolygon a b x) : scMap a b x (scMapInv a b x ζ) = ζ := by
  rw [← image_scMap h ha1] at hζ
  exact Function.invFunOn_eq hζ

theorem scMapInv_scMap (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) {z : ℂ}
    (hz : 0 < z.im) : scMapInv a b x (scMap a b x z) = z :=
  (injOn_scMap h ha1).leftInvOn_invFunOn hz

/-- The inverse map is holomorphic on the polygon, with derivative `1/w'`. -/
theorem hasDerivAt_scMapInv (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) {z : ℂ}
    (hz : 0 < z.im) :
    HasDerivAt (scMapInv a b x) (-(a : ℂ) * scIntegrand b x z)⁻¹ (scMap a b x z) := by
  have := Complex.hasDerivAt_invFunOn_of_injOn isOpen_upperHalfPlaneSet'
    (differentiableOn_scMap h) (injOn_scMap h ha1) hz
  rwa [(hasDerivAt_scMap h hz).deriv] at this

theorem differentiableOn_scMapInv (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) :
    DifferentiableOn ℂ (scMapInv a b x) (scPolygon a b x) := by
  rw [← image_scMap h ha1]
  exact Complex.differentiableOn_invFunOn_of_injOn isOpen_upperHalfPlaneSet'
    (differentiableOn_scMap h) (injOn_scMap h ha1)

/-- **The turning angles of the polygon**: the direction `θ` of the boundary derivative increases
by `π ∑_{t < xᵢ ≤ s} bᵢ` from `t` to `s`; in particular it jumps by `π bᵢ` at `xᵢ`, where the
inner angle is `(1 - bᵢ)π`. -/
theorem scAngle_sub_scAngle (b x : ι → ℝ) {s t : ℝ} (hts : t ≤ s) :
    scAngle b x s - scAngle b x t =
      π * ∑ i ∈ Finset.univ.filter (fun i => t < x i ∧ x i ≤ s), b i := by
  classical
  unfold scAngle
  have hsplit : Finset.univ.filter (fun i => t < x i) =
      Finset.univ.filter (fun i => s < x i) ∪ Finset.univ.filter (fun i => t < x i ∧ x i ≤ s) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hi
      by_cases his : s < x i
      · exact Or.inl his
      · exact Or.inr ⟨hi, not_lt.mp his⟩
    · rintro (hi | hi)
      · linarith
      · exact hi.1
  have hdisj : Disjoint (Finset.univ.filter (fun i => s < x i))
      (Finset.univ.filter (fun i => t < x i ∧ x i ≤ s)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    linarith [h2.2]
  rw [hsplit, Finset.sum_union hdisj]
  ring

end Carlson
