/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.VertexLimits
public import ToMathlib.Analysis.UpperHalfPlaneMaximum

/-!
# The polygon of a Schwarz–Christoffel map (Carlson §8.2)

On the real axis the Schwarz–Christoffel map `w = scMap a b x` has derivative
`-a ∏ (t - xᵢ)^{-bᵢ} = a ∏ |t - xᵢ|^{-bᵢ} e^{iθ(t)}` with Carlson's direction
`θ(t) = π (1 - ∑_{xᵢ > t} bᵢ)`. The direction is constant between the nodes and increases by
`π bᵢ` at `xᵢ`, so the boundary curve is a polygon. This module proves that for `a ≤ 1` the
polygon is convex: `w(t)` lies to the left of every side line, for every real `t`. The proof
uses only the monotonicity of `θ`, its range `[-π a, π]` of length at most `2π`, and the closure
of the polygon. The minimum principle for harmonic functions then puts `w` of the upper
half-plane into the open polygon, which is the intersection of the open half-planes to the left
of the side lines.

## Main results

* `Carlson.scAngle`: Carlson's direction `θ` of the boundary derivative.
* `Carlson.scIntegrand_ofReal`: the boundary integrand in polar form.
* `Carlson.hasDerivAt_scMap`: `w' = -a ∏ (z - xᵢ)^{-bᵢ}` on the upper half-plane.
* `Carlson.im_mul_scMap_sub_nonneg`: convexity, `w(t)` lies to the left of every side line.
* `Carlson.scPolygon`: the open polygon, cut out by the side lines.
* `Carlson.scMap_mem_scPolygon`: `w` maps the upper half-plane into the polygon.
* `Carlson.scMap_ofReal_notMem_scPolygon`: the real axis maps to the boundary.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι] {a : ℝ} {b x : ι → ℝ}

/-- Carlson's direction of the boundary derivative of the Schwarz–Christoffel map,
`θ(σ) = π (1 - ∑_{xᵢ > σ} bᵢ)`. -/
def scAngle (b x : ι → ℝ) (σ : ℝ) : ℝ :=
  π * (1 - ∑ i ∈ Finset.univ.filter (fun i => σ < x i), b i)

theorem scAngle_mono (hb : ∀ i, 0 ≤ b i) : Monotone (scAngle b x) := by
  intro σ τ hστ
  unfold scAngle
  have : ∑ i ∈ Finset.univ.filter (fun i => τ < x i), b i ≤
      ∑ i ∈ Finset.univ.filter (fun i => σ < x i), b i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hb i
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  nlinarith [Real.pi_pos]

theorem scAngle_le (hb : ∀ i, 0 ≤ b i) (σ : ℝ) : scAngle b x σ ≤ π := by
  unfold scAngle
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ.filter (fun i => σ < x i)) => hb i
  nlinarith [Real.pi_pos]

theorem neg_mul_le_scAngle (h : SchwarzChristoffelParams a b x) (σ : ℝ) :
    -(π * a) ≤ scAngle b x σ := by
  unfold scAngle
  have : ∑ i ∈ Finset.univ.filter (fun i => σ < x i), b i ≤ ∑ i, b i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => (h.pos i).le
  have hs := h.sum_eq
  nlinarith [Real.pi_pos]

/-- To the left of all nodes the direction is `-π a`. -/
theorem scAngle_of_lt (h : SchwarzChristoffelParams a b x) {σ : ℝ} (hσ : ∀ i, σ < x i) :
    scAngle b x σ = -(π * a) := by
  unfold scAngle
  rw [Finset.filter_true_of_mem fun i _ => hσ i, ← h.sum_eq]
  ring

/-- The boundary integrand in polar form: `∏ (σ - xᵢ)^{-bᵢ} = -∏ |σ - xᵢ|^{-bᵢ} e^{iθ(σ)}`. -/
theorem scIntegrand_ofReal (b x : ι → ℝ) (σ : ℝ) :
    scIntegrand b x σ = -((scDensity b x σ : ℝ) : ℂ) * exp (scAngle b x σ * I) := by
  have h := prod_ofReal_sub_cpow (fun i => (b i : ℂ)) x σ
  have hl : scIntegrand b x σ = ∏ i, (((σ - x i : ℝ)) : ℂ) ^ (-(b i : ℂ)) := by
    simp [scIntegrand]
  rw [hl, h]
  have hd : (∏ i, ((|σ - x i| : ℝ) : ℂ) ^ (-(b i : ℂ))) = ((scDensity b x σ : ℝ) : ℂ) := by
    rw [scDensity, ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofReal_cpow (abs_nonneg _)]
    push_cast
    rfl
  rw [hd, scAngle]
  have hexp : exp (((π * (1 - ∑ i ∈ Finset.univ.filter (fun i => σ < x i), b i) : ℝ) : ℂ) * I) =
      -exp (-(π * I) * ∑ i ∈ Finset.univ.filter (fun i => σ < x i), (b i : ℂ)) := by
    push_cast
    rw [show (π : ℂ) * (1 - ∑ i ∈ Finset.univ.filter (fun i => σ < x i), (b i : ℂ)) * I =
      π * I + -(π * I) * ∑ i ∈ Finset.univ.filter (fun i => σ < x i), (b i : ℂ) by ring,
      exp_add, exp_pi_mul_I]
    ring
  rw [hexp]
  ring

/-- **The Schwarz–Christoffel differential equation for `scMap`**: on the upper half-plane
`w'(z) = -a ∏ (z - xᵢ)^{-bᵢ}`. -/
theorem hasDerivAt_scMap (h : SchwarzChristoffelParams a b x) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (scMap a b x) (-(a : ℂ) * scIntegrand b x z) z := by
  have hsum : (a : ℂ) + 1 = ∑ i, (b i : ℂ) := by exact_mod_cast h.sum_eq
  have hΓ : ∀ m : ℕ, (a : ℂ) + 1 ≠ -m := by
    intro m hm
    have := congrArg re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [h.a_pos]
  have hs : ∀ i, z - (x i : ℂ) ∈ slitPlane := fun i => Or.inr (by simp [hz.ne'])
  have hd := hasDerivAt_carlsonR_sub (a : ℂ) (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) hsum hΓ hs
  have hev : scMap a b x =ᶠ[𝓝 z]
      fun z => carlsonR (-(a : ℂ)) (fun i => (b i : ℂ)) (fun i => z - x i) := by
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with w hw
    exact scMap_eq_carlsonR h hw
  exact hd.congr_of_eventuallyEq hev

theorem differentiableOn_scMap (h : SchwarzChristoffelParams a b x) :
    DifferentiableOn ℂ (scMap a b x) {z | 0 < z.im} := fun _ hz =>
  (hasDerivAt_scMap h hz).differentiableAt.differentiableWithinAt

theorem scIntegrand_ne_zero {z : ℂ} (hz : 0 < z.im) : scIntegrand b x z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  have hne : z - (x i : ℂ) ≠ 0 := by
    intro h0
    have := congrArg im h0
    simp at this
    linarith
  rw [cpow_def_of_ne_zero hne]
  exact exp_ne_zero _

/-! ### Convexity of the polygon -/

section Convexity

variable (b x) in
/-- The imaginary part of the rotated boundary integrand, `-∏ |σ - xᵢ|^{-bᵢ} sin (θ(σ) - θ₀)`. -/
def scRotIm (θ₀ σ : ℝ) : ℝ := (exp (-(θ₀ : ℂ) * I) * scIntegrand b x σ).im

theorem scRotIm_eq (θ₀ σ : ℝ) :
    scRotIm b x θ₀ σ = -(scDensity b x σ * Real.sin (scAngle b x σ - θ₀)) := by
  rw [scRotIm, scIntegrand_ofReal, show exp (-(θ₀ : ℂ) * I) * (-((scDensity b x σ : ℝ) : ℂ) *
      exp (scAngle b x σ * I)) = -(((scDensity b x σ : ℝ) : ℂ) *
      exp (((scAngle b x σ - θ₀ : ℝ) : ℂ) * I)) by
    push_cast
    rw [show ((scAngle b x σ : ℂ) - θ₀) * I = -(θ₀ : ℂ) * I + scAngle b x σ * I by ring, exp_add]
    ring]
  rw [neg_im, im_ofReal_mul, exp_ofReal_mul_I_im]

theorem integrable_scIntegrand_ofReal (h : SchwarzChristoffelParams a b x) :
    Integrable fun σ : ℝ => scIntegrand b x σ := by
  simpa using integrable_scIntegrand_line h 0

theorem scMap_ofReal (t : ℝ) : scMap a b x t = a * ∫ σ in Ioi t, scIntegrand b x σ := by
  simp [scMap]

theorem integrable_scRotIm (h : SchwarzChristoffelParams a b x) (θ₀ : ℝ) :
    Integrable (scRotIm b x θ₀) :=
  ((integrable_scIntegrand_ofReal h).const_mul (exp (-(θ₀ : ℂ) * I))).im

/-- `im (e^{-iθ₀} w(t)) = a ∫_{Ioi t} im (e^{-iθ₀} ∏ (σ - xᵢ)^{-bᵢ}) dσ`. -/
theorem im_mul_scMap_eq (h : SchwarzChristoffelParams a b x) (θ₀ t : ℝ) :
    (exp (-(θ₀ : ℂ) * I) * scMap a b x t).im = a * ∫ σ in Ioi t, scRotIm b x θ₀ σ := by
  have hi : Integrable (fun σ : ℝ => exp (-(θ₀ : ℂ) * I) * scIntegrand b x σ)
      (volume.restrict (Ioi t)) :=
    ((integrable_scIntegrand_ofReal h).const_mul (exp (-(θ₀ : ℂ) * I))).integrableOn
  have := integral_im hi
  rw [scMap_ofReal, show exp (-(θ₀ : ℂ) * I) * ((a : ℂ) * ∫ σ in Ioi t, scIntegrand b x σ) =
      (a : ℂ) * ∫ σ in Ioi t, exp (-(θ₀ : ℂ) * I) * scIntegrand b x σ by
    rw [integral_const_mul]; ring]
  rw [im_ofReal_mul]
  congr 1
  exact this.symm

/-- The same quantity as an integral over `Iic t`, by closure of the polygon. -/
theorem im_mul_scMap_eq_Iic (h : SchwarzChristoffelParams a b x) (θ₀ t : ℝ) :
    (exp (-(θ₀ : ℂ) * I) * scMap a b x t).im = -(a * ∫ σ in Iic t, scRotIm b x θ₀ σ) := by
  have hint := integrable_scRotIm h θ₀
  have htot : ∫ σ, scRotIm b x θ₀ σ = 0 := by
    have hi := (integrable_scIntegrand_ofReal h).const_mul (exp (-(θ₀ : ℂ) * I))
    have := integral_im hi
    rw [show (fun σ => scRotIm b x θ₀ σ) = fun σ : ℝ => RCLike.im
      (exp (-(θ₀ : ℂ) * I) * scIntegrand b x σ) from rfl, this, integral_const_mul,
      integral_scIntegrand_eq_zero h, mul_zero]
    rfl
  have hsplit := setIntegral_union (s := Iic t) (t := Ioi t) (f := scRotIm b x θ₀)
    (Set.disjoint_left.mpr fun σ h1 h2 => not_lt.mpr h1 h2) measurableSet_Ioi
    hint.integrableOn hint.integrableOn
  rw [Iic_union_Ioi, setIntegral_univ, htot] at hsplit
  rw [im_mul_scMap_eq h, show ∫ σ in Ioi t, scRotIm b x θ₀ σ = -∫ σ in Iic t, scRotIm b x θ₀ σ by
    linarith]
  ring

/-- Differences of the rotated imaginary part along the real axis. -/
theorem im_mul_scMap_sub_eq (h : SchwarzChristoffelParams a b x) (θ₀ : ℝ) {s t : ℝ}
    (hst : s ≤ t) : (exp (-(θ₀ : ℂ) * I) * scMap a b x t).im -
      (exp (-(θ₀ : ℂ) * I) * scMap a b x s).im = -(a * ∫ σ in Ioc s t, scRotIm b x θ₀ σ) := by
  have hint := integrable_scRotIm h θ₀
  have hsplit := setIntegral_union (s := Ioc s t) (t := Ioi t) (f := scRotIm b x θ₀)
    (Set.disjoint_left.mpr fun σ h1 h2 => not_lt.mpr h1.2 h2) measurableSet_Ioi
    hint.integrableOn hint.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hst] at hsplit
  rw [im_mul_scMap_eq h, im_mul_scMap_eq h, hsplit]
  ring

private theorem sin_nonneg_of_mem {ψ : ℝ} (h : ψ ∈ Icc 0 π ∨ ψ ∈ Icc (-(2 * π)) (-π)) :
    0 ≤ Real.sin ψ := by
  rcases h with h | h
  · exact Real.sin_nonneg_of_nonneg_of_le_pi h.1 h.2
  · rw [← Real.sin_add_two_pi]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [h.1]) (by linarith [h.2])

private theorem sin_nonpos_of_mem {ψ : ℝ} (h : ψ ∈ Icc (-π) 0 ∨ ψ ∈ Icc π (2 * π)) :
    Real.sin ψ ≤ 0 := by
  rcases h with h | h
  · exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h.2 h.1
  · rw [← Real.sin_sub_two_pi]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [h.2]) (by linarith [h.1])

/-- **Convexity of the Schwarz–Christoffel polygon** (Carlson §8.2): for `a ≤ 1`, every boundary
point `w(t)` lies in the closed half-plane to the left of the side line through `w(s)` with
direction `θ(s)`, and so does the vertex `w(∞) = 0`. -/
theorem im_mul_scMap_sub_nonneg_and (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1)
    (s : ℝ) : (∀ t : ℝ, 0 ≤ (exp (-(scAngle b x s : ℂ) * I) *
      (scMap a b x t - scMap a b x s)).im) ∧
      0 ≤ (exp (-(scAngle b x s : ℂ) * I) * (0 - scMap a b x s)).im := by
  set θ₀ := scAngle b x s
  set P : ℝ → ℝ := fun t => (exp (-(θ₀ : ℂ) * I) * scMap a b x t).im with hP
  have hsub : ∀ t : ℝ,
      (exp (-(θ₀ : ℂ) * I) * (scMap a b x t - scMap a b x s)).im = P t - P s := by
    intro t; simp only [P, mul_sub, sub_im]
  have hzero : (exp (-(θ₀ : ℂ) * I) * (0 - scMap a b x s)).im = -P s := by
    simp only [P, zero_sub, mul_neg, neg_im]
  simp_rw [hsub, hzero]
  have ha := h.a_pos
  have hb0 : ∀ i, 0 ≤ b i := fun i => (h.pos i).le
  have hmono := scAngle_mono (x := x) hb0
  have hle := scAngle_le (x := x) hb0
  have hge := neg_mul_le_scAngle h
  have hπ := Real.pi_pos
  have hπa : π * a ≤ π := by nlinarith
  -- the sign of the integrand is governed by `ψ(σ) = θ(σ) - θ₀`
  have hk : ∀ σ, scRotIm b x θ₀ σ = -(scDensity b x σ * Real.sin (scAngle b x σ - θ₀)) :=
    scRotIm_eq θ₀
  have hD := fun σ => scDensity_nonneg (b := b) (x := x) σ
  have kle : ∀ σ, 0 ≤ Real.sin (scAngle b x σ - θ₀) → scRotIm b x θ₀ σ ≤ 0 := fun σ hs => by
    rw [hk]; have := mul_nonneg (hD σ) hs; linarith
  have kge : ∀ σ, Real.sin (scAngle b x σ - θ₀) ≤ 0 → 0 ≤ scRotIm b x θ₀ σ := fun σ hs => by
    rw [hk]; have := mul_nonpos_of_nonneg_of_nonpos (hD σ) hs; linarith
  have hIoi : ∀ t, P t = a * ∫ σ in Ioi t, scRotIm b x θ₀ σ := im_mul_scMap_eq h θ₀
  have hIic : ∀ t, P t = -(a * ∫ σ in Iic t, scRotIm b x θ₀ σ) := im_mul_scMap_eq_Iic h θ₀
  have hdiff : ∀ u v : ℝ, u ≤ v → P v - P u = -(a * ∫ σ in Ioc u v, scRotIm b x θ₀ σ) :=
    fun u v huv => im_mul_scMap_sub_eq h θ₀ huv
  by_cases hA : ∀ σ, s < σ → scAngle b x σ - θ₀ ≤ π
  · -- Case A: the integrand is nonpositive to the right of `s`
    have hright : ∀ σ ∈ Ioi s, scRotIm b x θ₀ σ ≤ 0 := fun σ hσ =>
      kle σ (sin_nonneg_of_mem (Or.inl ⟨by linarith [hmono (le_of_lt hσ)], hA σ hσ⟩))
    have hPs : P s ≤ 0 := by
      have := setIntegral_nonpos (μ := volume) measurableSet_Ioi hright
      rw [hIoi]; nlinarith
    refine ⟨fun t => ?_, by linarith⟩
    rcases le_total s t with hst | hts
    · have := setIntegral_nonpos (μ := volume) (s := Ioc s t) measurableSet_Ioc
        fun σ hσ => hright σ hσ.1
      have hd := hdiff _ _ hst
      nlinarith
    · by_cases hψ : -π ≤ scAngle b x t - θ₀
      · have hmid : ∀ σ ∈ Ioc t s, 0 ≤ scRotIm b x θ₀ σ := fun σ hσ =>
          kge σ (sin_nonpos_of_mem (Or.inl ⟨by linarith [hmono hσ.1.le],
            by linarith [hmono hσ.2]⟩))
        have := setIntegral_nonneg (μ := volume) measurableSet_Ioc hmid
        have hd := hdiff _ _ hts
        nlinarith
      · push Not at hψ
        have hleft : ∀ σ ∈ Iic t, scRotIm b x θ₀ σ ≤ 0 := fun σ hσ =>
          kle σ (sin_nonneg_of_mem (Or.inr ⟨by linarith [hge σ, hle s],
            by linarith [hmono (show σ ≤ t from hσ)]⟩))
        have := setIntegral_nonpos (μ := volume) measurableSet_Iic hleft
        have hPt : 0 ≤ P t := by rw [hIic]; nlinarith
        linarith
  · -- Case B: the integrand is nonnegative to the left of `s`
    push Not at hA
    obtain ⟨σ₁, hσ₁, hψ₁⟩ := hA
    have hB : ∀ σ, σ ≤ s → -π ≤ scAngle b x σ - θ₀ := by
      intro σ hσ
      by_contra hc
      push Not at hc
      have := hle σ₁
      have := hge σ
      linarith
    have hleft : ∀ σ ∈ Iic s, 0 ≤ scRotIm b x θ₀ σ := fun σ hσ =>
      kge σ (sin_nonpos_of_mem (Or.inl ⟨hB σ hσ, by linarith [hmono (show σ ≤ s from hσ)]⟩))
    have hPs : P s ≤ 0 := by
      have := setIntegral_nonneg (μ := volume) measurableSet_Iic hleft
      rw [hIic]; nlinarith
    refine ⟨fun t => ?_, by linarith⟩
    rcases le_total t s with hts | hst
    · have := setIntegral_nonneg (μ := volume) (s := Ioc t s) measurableSet_Ioc
        fun σ hσ => hleft σ hσ.2
      have hd := hdiff _ _ hts
      nlinarith
    · by_cases hψ : scAngle b x t - θ₀ ≤ π
      · have hmid : ∀ σ ∈ Ioc s t, scRotIm b x θ₀ σ ≤ 0 := fun σ hσ =>
          kle σ (sin_nonneg_of_mem (Or.inl ⟨by linarith [hmono hσ.1.le],
            by linarith [hmono hσ.2]⟩))
        have := setIntegral_nonpos (μ := volume) measurableSet_Ioc hmid
        have hd := hdiff _ _ hst
        nlinarith
      · push Not at hψ
        have hright : ∀ σ ∈ Ioi t, 0 ≤ scRotIm b x θ₀ σ := fun σ hσ =>
          kge σ (sin_nonpos_of_mem (Or.inr ⟨by linarith [hmono (le_of_lt (show t < σ from hσ))],
            by linarith [hle σ, hge s]⟩))
        have := setIntegral_nonneg (μ := volume) measurableSet_Ioi hright
        have hPt : 0 ≤ P t := by rw [hIoi]; nlinarith
        linarith

/-- Points on the same side have the same side line. -/
theorem im_mul_scMap_sub_eq_zero (h : SchwarzChristoffelParams a b x) {s t : ℝ} (hst : s ≤ t)
    (hθ : ∀ σ ∈ Ioc s t, scAngle b x σ = scAngle b x s) :
    (exp (-(scAngle b x s : ℂ) * I) * (scMap a b x t - scMap a b x s)).im = 0 := by
  rw [mul_sub, sub_im, im_mul_scMap_sub_eq h _ hst]
  have : ∫ σ in Ioc s t, scRotIm b x (scAngle b x s) σ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    rw [scRotIm_eq, hθ σ hσ, sub_self, Real.sin_zero, mul_zero, neg_zero]
  rw [this, mul_zero, neg_zero]

/-- To the left of all nodes, `w(t)` lies on the line through `0` with direction `-π a`. -/
theorem im_mul_scMap_eq_zero_of_lt (h : SchwarzChristoffelParams a b x) {t : ℝ}
    (ht : ∀ i, t < x i) : (exp ((π * a : ℝ) * I) * scMap a b x t).im = 0 := by
  have hθ := scAngle_of_lt h ht
  have := im_mul_scMap_eq_Iic h (scAngle b x t) t
  rw [hθ] at this
  push_cast at this ⊢
  rw [neg_neg] at this
  rw [this]
  have : ∫ σ in Iic t, scRotIm b x (-(π * a)) σ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    have hσ' : ∀ i, σ < x i := fun i => lt_of_le_of_lt hσ (ht i)
    rw [scRotIm_eq, scAngle_of_lt h hσ', sub_self, Real.sin_zero, mul_zero, neg_zero]
  rw [this, mul_zero, neg_zero]

end Convexity

/-! ### The polygon -/

/-- **The open Schwarz–Christoffel polygon**: the intersection of the open half-planes to the left
of the side lines, namely the line through `0` with direction `-π a`, and for each node `xᵢ` the
line through the vertex `w(xᵢ)` with direction `θ(xᵢ)`. -/
def scPolygon (a : ℝ) (b x : ι → ℝ) : Set ℂ :=
  {ζ | 0 < (exp ((π * a : ℝ) * I) * ζ).im ∧
    ∀ i, 0 < (exp (-(scAngle b x (x i) : ℂ) * I) * (ζ - scMap a b x (x i))).im}

theorem isOpen_scPolygon : IsOpen (scPolygon a b x) := by
  refine (isOpen_lt continuous_const
    (continuous_im.comp (continuous_const.mul continuous_id))).inter ?_
  have hi : ∀ i : ι, IsOpen {ζ : ℂ |
      0 < (exp (-(scAngle b x (x i) : ℂ) * I) * (ζ - scMap a b x (x i))).im} := fun i =>
    isOpen_lt continuous_const
      (continuous_im.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  refine (congrArg IsOpen ?_).mp (isOpen_iInter_of_finite hi)
  ext ζ
  simp only [mem_iInter, mem_ofPred_eq]
  rfl

theorem convex_scPolygon : Convex ℝ (scPolygon a b x) := by
  intro u hu v hv s t hs ht hst
  have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
  have key : ∀ (c d : ℂ), 0 < (c * (u - d)).im → 0 < (c * (v - d)).im →
      0 < (c * (s • u + t • v - d)).im := by
    intro c d hu hv
    have hlin : c * (s • u + t • v - d) = (s : ℂ) * (c * (u - d)) + (t : ℂ) * (c * (v - d)) := by
      simp only [Complex.real_smul]
      linear_combination (c * d) * hst'
    rw [hlin, add_im, im_ofReal_mul, im_ofReal_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · have := mul_pos hs' hu
      have := mul_nonneg ht hv.le
      linarith
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using hv
  refine ⟨?_, fun i => key _ _ (hu.2 i) (hv.2 i)⟩
  have := key (exp ((π * a : ℝ) * I)) 0 (by simpa using hu.1) (by simpa using hv.1)
  simpa using this

/-- An open set inside a closed half-plane lies in the open half-plane. -/
theorem lt_im_of_isOpen {U : Set ℂ} (hU : IsOpen U) {c d : ℂ} (hc : c ≠ 0)
    (hsub : ∀ ζ ∈ U, 0 ≤ (c * (ζ - d)).im) {ζ : ℂ} (hζ : ζ ∈ U) : 0 < (c * (ζ - d)).im := by
  rcases (hsub ζ hζ).lt_or_eq with h | h
  · exact h
  exfalso
  have hopen : IsOpen {ε : ℝ | ζ - (ε : ℂ) * I / c ∈ U} :=
    hU.preimage (by fun_prop)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa using hζ)
  have hmem : ζ - ((δ / 2 : ℝ) : ℂ) * I / c ∈ U :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have := hsub _ hmem
  have hcalc : c * (ζ - ((δ / 2 : ℝ) : ℂ) * I / c - d) = c * (ζ - d) - ((δ / 2 : ℝ) : ℂ) * I := by
    field_simp
    ring
  rw [hcalc, sub_im, ← h] at this
  simp at this
  linarith

/-- The derivative of `w` on the upper half-plane is a strict derivative. -/
theorem hasStrictDerivAt_scMap (h : SchwarzChristoffelParams a b x) {z : ℂ} (hz : 0 < z.im) :
    HasStrictDerivAt (scMap a b x) (-(a : ℂ) * scIntegrand b x z) z := by
  have han : AnalyticAt ℂ (scMap a b x) z :=
    (differentiableOn_scMap h).analyticAt ((isOpen_lt continuous_const continuous_im).mem_nhds hz)
  have := han.hasStrictDerivAt
  rwa [(hasDerivAt_scMap h hz).deriv] at this

theorem neg_mul_scIntegrand_ne_zero (h : SchwarzChristoffelParams a b x) {z : ℂ}
    (hz : 0 < z.im) : -(a : ℂ) * scIntegrand b x z ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast h.a_pos.ne')) (scIntegrand_ne_zero hz)

/-- `w` is an open map on the upper half-plane. -/
theorem isOpen_image_scMap (h : SchwarzChristoffelParams a b x) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ {z | 0 < z.im}) : IsOpen (scMap a b x '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hmap := (hasStrictDerivAt_scMap h (hUH hz)).map_nhds_eq
    (neg_mul_scIntegrand_ne_zero h (hUH hz))
  rw [← hmap]
  exact image_mem_map (hU.mem_nhds hz)

/-- A point strictly to the left of all nodes. -/
private theorem exists_lt_nodes (x : ι → ℝ) : ∃ s₀ : ℝ, ∀ i, s₀ < x i := by
  refine ⟨-(∑ i, |x i|) - 1, fun i => ?_⟩
  have := Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg (x i))
    (Finset.mem_univ i)
  have := neg_abs_le (x i)
  linarith

/-- On the real axis, `w(t)` lies to the left of the side line through `0`. -/
theorem im_mul_scMap_nonneg_first (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) (t : ℝ) :
    0 ≤ (exp ((π * a : ℝ) * I) * scMap a b x t).im := by
  obtain ⟨s₀, hs₀⟩ := exists_lt_nodes x
  have h1 := (im_mul_scMap_sub_nonneg_and h ha1 s₀).1 t
  have h2 := im_mul_scMap_eq_zero_of_lt h hs₀
  rw [scAngle_of_lt h hs₀] at h1
  push_cast at h1 h2 ⊢
  rw [neg_neg, mul_sub, sub_im] at h1
  linarith

/-- **`w` maps the upper half-plane into the polygon** (Carlson §8.2), for `a ≤ 1`: the minimum
principle for the harmonic functions `im (e^{-iθ} (w - w(s)))`, whose boundary values are
nonnegative by convexity, and the open mapping property. -/
theorem scMap_mem_scPolygon (h : SchwarzChristoffelParams a b x) (ha1 : a ≤ 1) {z : ℂ}
    (hz : 0 < z.im) : scMap a b x z ∈ scPolygon a b x := by
  have hopen := isOpen_image_scMap h (isOpen_lt continuous_const continuous_im) subset_rfl
  have hmem : scMap a b x z ∈ scMap a b x '' {z | 0 < z.im} := ⟨z, hz, rfl⟩
  -- the minimum principle for one side line
  have hside : ∀ c d : ℂ, c ≠ 0 → (∀ t : ℝ, 0 ≤ (c * (scMap a b x t - d)).im) →
      0 ≤ (c * (0 - d)).im → 0 < (c * (scMap a b x z - d)).im := by
    intro c d hc hb hL
    refine lt_im_of_isOpen hopen hc ?_ hmem
    rintro _ ⟨w, hw, rfl⟩
    refine Complex.im_nonneg_of_boundary_upperHalfPlane (f := fun w => c * (scMap a b x w - d))
      (L := c * (0 - d)) ?_ ?_ ?_ hL hb hw
    · exact (differentiableOn_const c).mul
        ((differentiableOn_scMap h).sub (differentiableOn_const d))
    · exact continuousOn_const.mul ((continuousOn_scMap h).sub continuousOn_const)
    · exact tendsto_const_nhds.mul ((tendsto_scMap_cobounded h).sub tendsto_const_nhds)
  refine ⟨?_, fun i => ?_⟩
  · have := hside (exp ((π * a : ℝ) * I)) 0 (exp_ne_zero _)
      (fun t => by simpa using im_mul_scMap_nonneg_first h ha1 t) (by simp)
    simpa using this
  · exact hside _ _ (exp_ne_zero _) (im_mul_scMap_sub_nonneg_and h ha1 (x i)).1
      (im_mul_scMap_sub_nonneg_and h ha1 (x i)).2

/-- **The real axis maps to the boundary of the polygon**: `w(t) ∉ P` for real `t`. -/
theorem scMap_ofReal_notMem_scPolygon (h : SchwarzChristoffelParams a b x) (t : ℝ) :
    scMap a b x t ∉ scPolygon a b x := by
  classical
  rintro ⟨h1, h2⟩
  by_cases hall : ∀ i, t < x i
  · rw [im_mul_scMap_eq_zero_of_lt h hall] at h1
    exact lt_irrefl _ h1
  · push Not at hall
    set S := Finset.univ.filter fun i : ι => x i ≤ t
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hall
      exact ⟨i, by simp [S, hi]⟩
    obtain ⟨i, hiS, hmax⟩ := S.exists_max_image x hS
    have hit : x i ≤ t := (Finset.mem_filter.mp hiS).2
    have hθ : ∀ σ ∈ Ioc (x i) t, scAngle b x σ = scAngle b x (x i) := by
      intro σ hσ
      have hf : Finset.univ.filter (fun j => σ < x j) =
          Finset.univ.filter (fun j => x i < x j) := by
        refine Finset.filter_congr fun j _ => ?_
        constructor
        · intro hj; linarith [hσ.1]
        · intro hj
          by_contra hc
          push Not at hc
          have : j ∈ S := by simp [S]; linarith [hσ.2]
          have := hmax j this
          linarith
      unfold scAngle
      rw [hf]
    have := im_mul_scMap_sub_eq_zero h hit hθ
    have h2i := h2 i
    rw [this] at h2i
    exact lt_irrefl _ h2i

/-- The vertex `w(∞) = 0` is not in the open polygon. -/
theorem zero_notMem_scPolygon : (0 : ℂ) ∉ scPolygon a b x := fun h => by
  simpa using h.1

/-! ### Boundary values along the sides -/

section Sides

/-- `w(t) - w(s) = -a ∫_s^t ∏ (σ - xᵢ)^{-bᵢ} dσ` along the real axis. -/
theorem scMap_sub_ofReal (h : SchwarzChristoffelParams a b x) {s t : ℝ} (hst : s ≤ t) :
    scMap a b x t - scMap a b x s = -(a * ∫ σ in Ioc s t, scIntegrand b x σ) := by
  have hint := integrable_scIntegrand_ofReal h
  have hsplit := setIntegral_union (s := Ioc s t) (t := Ioi t)
    (f := fun σ : ℝ => scIntegrand b x σ)
    (Set.disjoint_left.mpr fun σ h1 h2 => not_lt.mpr h1.2 h2) measurableSet_Ioi
    hint.integrableOn hint.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hst] at hsplit
  rw [scMap_ofReal, scMap_ofReal, hsplit]
  ring

/-- `w(t) = -a ∫_{-∞}^t ∏ (σ - xᵢ)^{-bᵢ} dσ`, by closure of the polygon. -/
theorem scMap_ofReal_eq_Iic (h : SchwarzChristoffelParams a b x) (t : ℝ) :
    scMap a b x t = -(a * ∫ σ in Iic t, scIntegrand b x σ) := by
  have hint := integrable_scIntegrand_ofReal h
  have hsplit := setIntegral_union (s := Iic t) (t := Ioi t)
    (f := fun σ : ℝ => scIntegrand b x σ)
    (Set.disjoint_left.mpr fun σ h1 h2 => not_lt.mpr h1 h2) measurableSet_Ioi
    hint.integrableOn hint.integrableOn
  rw [Iic_union_Ioi, setIntegral_univ, integral_scIntegrand_eq_zero h] at hsplit
  rw [scMap_ofReal, show ∫ σ in Ioi t, scIntegrand b x σ = -∫ σ in Iic t, scIntegrand b x σ by
    linear_combination (-1 : ℂ) * hsplit]
  ring

theorem scIntegrand_of_scAngle_eq {σ c : ℝ} (hθ : scAngle b x σ = c) :
    scIntegrand b x σ = -((scDensity b x σ : ℝ) : ℂ) * exp (c * I) := by
  rw [scIntegrand_ofReal, hθ]

private theorem integral_neg_density_mul {S : Set ℝ} (c : ℝ) :
    ∫ σ in S, -((scDensity b x σ : ℝ) : ℂ) * exp (c * I) =
      -(((∫ σ in S, scDensity b x σ : ℝ)) : ℂ) * exp (c * I) := by
  rw [integral_mul_const, integral_neg, integral_complex_ofReal]

/-- **A side of the polygon**: if the direction is `c` between `s` and `t`, then
`w(t) - w(s) = a e^{ic} ∫_s^t ∏ |σ - xᵢ|^{-bᵢ} dσ`. -/
theorem scMap_sub_of_scAngle (h : SchwarzChristoffelParams a b x) {s t c : ℝ} (hst : s ≤ t)
    (hθ : ∀ σ ∈ Ioo s t, scAngle b x σ = c) :
    scMap a b x t - scMap a b x s =
      a * exp (c * I) * (((∫ σ in Ioo s t, scDensity b x σ : ℝ)) : ℂ) := by
  rw [scMap_sub_ofReal h hst, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo fun σ hσ => scIntegrand_of_scAngle_eq (hθ σ hσ),
    integral_neg_density_mul]
  ring

/-- The last side, from `w(t)` to `w(∞) = 0`. -/
theorem scMap_of_scAngle_Ioi {t c : ℝ}
    (hθ : ∀ σ ∈ Ioi t, scAngle b x σ = c) :
    scMap a b x t = -(a * exp (c * I) * (((∫ σ in Ioi t, scDensity b x σ : ℝ)) : ℂ)) := by
  rw [scMap_ofReal,
    setIntegral_congr_fun measurableSet_Ioi fun σ hσ => scIntegrand_of_scAngle_eq (hθ σ hσ),
    integral_neg_density_mul]
  ring

/-- The first side, from `w(-∞) = 0` to `w(t)`. -/
theorem scMap_of_scAngle_Iio (h : SchwarzChristoffelParams a b x) {t c : ℝ}
    (hθ : ∀ σ ∈ Iio t, scAngle b x σ = c) :
    scMap a b x t = a * exp (c * I) * (((∫ σ in Iio t, scDensity b x σ : ℝ)) : ℂ) := by
  rw [scMap_ofReal_eq_Iic h, integral_Iic_eq_integral_Iio,
    setIntegral_congr_fun measurableSet_Iio fun σ hσ => scIntegrand_of_scAngle_eq (hθ σ hσ),
    integral_neg_density_mul]
  ring

end Sides

end Carlson
