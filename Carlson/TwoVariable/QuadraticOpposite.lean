/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.TwoVariable.ParameterSymmetry
public import Carlson.R.SmallVariableContinuation
public import Carlson.R.Homogeneity

/-!
# The first quadratic transformation for nodes in opposite half-planes

The first quadratic transformation (6.9-3) is proved in `Carlson.TwoVariable.QuadraticSlit` for
nodes `x, y` in the right half-plane. Both sides are holomorphic in `(x, y)` on the convex open set
`im x > 0 > im y`, `re (x + y) > 0`, where all nodes and transformed nodes lie in the slit plane,
and that set meets the right half-plane; the identity theorem extends the transformation to it.

Letting `y → -x` inside this set, along `y = -x (1 + iδ)`, the transformed nodes are
`((x + y)/2)² → 0` and `xy → -x²`. Homogeneity reduces the right side to an `R`-function with
nodes `((x + y)/2)²/(xy) → 0` (through the right half-plane) and `1`, and the small-variable
limit (Theorem 8.3-2) evaluates it. This gives Carlson's Exercise 8.3-9: the average of `w^{2t}`
over the segment joining `x` and `-x` (continued through the origin) is an elementary multiple
of `(-x²)^t`.

## Main results

* `Carlson.TwoVariable.regR_firstQuadratic_of_im`: the first quadratic transformation for
  `im x > 0 > im y`, `re (x + y) > 0`, all complex `t, β`.
* `Carlson.TwoVariable.regCarlsonR_pair_neg`, `Carlson.TwoVariable.carlsonR_pair_neg`:
  Exercise 8.3-9, regularized for all `t, β`, and in Carlson's normalization.
-/

open Dirichlet
open Complex Set Filter
open scoped Topology Real
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- A number in the open upper half-plane times one in the open lower half-plane avoids the cut
`(-∞, 0]`. -/
theorem mul_mem_slitPlane_of_im {x y : ℂ} (hx : 0 < x.im) (hy : y.im < 0) :
    x * y ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  simp only [not_or, not_lt, not_not] at h
  obtain ⟨hre, him⟩ := h
  rw [mul_re] at hre
  rw [mul_im] at him
  have key : x.im * (x.re * y.re - x.im * y.im) = -y.im * (x.re ^ 2 + x.im ^ 2) := by
    linear_combination x.re * him
  have hpos : 0 < -y.im * (x.re ^ 2 + x.im ^ 2) :=
    mul_pos (neg_pos.2 hy) (by positivity)
  nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hx.le, hre⟩)]

/-- The open set of node pairs with `x` in the upper and `y` in the lower half-plane and
`re (x + y) > 0`. -/
def oppositeNodeDomain : Set (Fin 2 → ℂ) :=
  {w | 0 < (w 0).im ∧ (w 1).im < 0 ∧ 0 < (w 0 + w 1).re}

theorem convex_oppositeNodeDomain : Convex ℝ oppositeNodeDomain := by
  intro z hz w hw a b ha hb hab
  simp only [oppositeNodeDomain, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, add_re, add_im,
    smul_re, smul_im, smul_eq_mul] at hz hw ⊢
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp at hab; subst hab; simp; exact ⟨hw0, hw1, hw2⟩
  refine ⟨by nlinarith [mul_pos ha' hz0, mul_nonneg hb hw0.le],
    by nlinarith [mul_pos ha' (neg_pos.2 hz1), mul_nonneg hb (neg_pos.2 hw1).le],
    by nlinarith [mul_pos ha' hz2, mul_nonneg hb hw2.le]⟩

theorem isOpen_oppositeNodeDomain : IsOpen oppositeNodeDomain := by
  have h0 : Continuous fun w : Fin 2 → ℂ => (w 0).im := by fun_prop
  have h1 : Continuous fun w : Fin 2 → ℂ => (w 1).im := by fun_prop
  have h2 : Continuous fun w : Fin 2 → ℂ => (w 0 + w 1).re := by fun_prop
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h1 continuous_const).inter
    (isOpen_lt continuous_const h2))

/-- On the opposite-node domain the nodes and both transformed mean squares lie in the slit
plane. -/
theorem slitDomains_of_oppositeNodeDomain {w : Fin 2 → ℂ} (hw : w ∈ oppositeNodeDomain) :
    w ∈ carlsonRSlitDomain ∧
      pair (arithmeticMeanSq (w 0) (w 1)) (geometricMeanSq (w 0) (w 1)) ∈ carlsonRSlitDomain := by
  obtain ⟨h0, h1, h2⟩ := hw
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact mem_slitPlane_iff.2 (Or.inr h0.ne')
    · exact mem_slitPlane_iff.2 (Or.inr h1.ne)
  · fin_cases i
    · apply sq_mem_slitPlane_of_re_pos
      simp only [div_ofNat_re]
      positivity
    · exact mul_mem_slitPlane_of_im h0 h1

/-- **The first quadratic transformation for nodes in opposite half-planes**: for
`im x > 0 > im y` and `re (x + y) > 0`, and all complex `t, β`,
`R̃_{2t}(β, β; x, y) = q(β) R̃_t(β + t, 1/2 - t; ((x + y)/2)², xy)`. -/
theorem regR_firstQuadratic_of_im (t β x y : ℂ) (hx : 0 < x.im) (hy : y.im < 0)
    (hxy : 0 < (x + y).re) :
    regCarlsonR (2 * t) (pair β β) (pair x y) =
      quadraticGammaRatio β * regCarlsonR t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  let F := fun w : Fin 2 → ℂ => regCarlsonR (2 * t) (pair β β) w
  let G := fun w : Fin 2 → ℂ => quadraticGammaRatio β *
    regCarlsonR t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq (w 0) (w 1)) (geometricMeanSq (w 0) (w 1)))
  have hF : AnalyticOnNhd ℂ F oppositeNodeDomain := fun w hw =>
    analyticOnNhd_regCarlsonR _ _ w (slitDomains_of_oppositeNodeDomain hw).1
  have hG : AnalyticOnNhd ℂ G oppositeNodeDomain := fun w hw =>
    analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_meanSquares w) (slitDomains_of_oppositeNodeDomain hw).2)
  -- the base point `(1 + i, 1 - i)` lies in both domains
  set p : Fin 2 → ℂ := pair (1 + I) (1 - I)
  have hp : p ∈ oppositeNodeDomain := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [p, pair]
  have hpR : p ∈ carlsonRVariableDomain := by
    intro i; fin_cases i <;> simp [p, pair, carlsonRightHalfPlane]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    convex_oppositeNodeDomain.isPreconnected hp ?_
  · exact heq (show pair x y ∈ oppositeNodeDomain from ⟨hx, hy, hxy⟩)
  · filter_upwards [isOpen_carlsonRVariableDomain.eventually_mem hpR] with w hw
    change regCarlsonR (2 * t) (pair β β) w = _
    conv_lhs => rw [← pair_eta w]
    exact regRSlit_firstQuadratic t β (w 0) (w 1) (hw 0) (hw 1)

/-- For non-real `x`, `-x²` lies in the slit plane. -/
theorem neg_sq_mem_slitPlane {x : ℂ} (hx : x.im ≠ 0) : -x ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases ha : x.re = 0
  · left
    rw [neg_re, sq, mul_re, ha]
    have := mul_self_pos.2 hx
    linarith
  · right
    rw [neg_im, sq, mul_im]
    intro h
    apply mul_ne_zero ha hx
    linarith

private theorem tendsto_arg_of_tendsto {E : Type*} {l : Filter E} {f : E → ℂ} {z : ℂ}
    (hz : z ∈ slitPlane) (hf : Tendsto f l (𝓝 z)) : Tendsto (fun e => arg (f e)) l (𝓝 (arg z)) :=
  (continuousAt_arg hz).tendsto.comp hf

/-- **Carlson's Exercise 8.3-9**, regularized, for `im x > 0`. -/
theorem regCarlsonR_pair_neg_of_im_pos (t β x : ℂ) (hx : 0 < x.im) :
    regCarlsonR (2 * t) (pair β β) (pair x (-x)) =
      quadraticGammaRatio β * Gamma (1 / 2) * (Gamma (β + 1 / 2 + t))⁻¹ *
        (Gamma (1 / 2 - t))⁻¹ * (-x ^ 2) ^ t := by
  set b : Fin 2 → ℂ := pair (β + t) (1 / 2 - t)
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδc : Tendsto (fun n => (δ n : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp hδ
    rwa [ofReal_zero] at this
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  set y : ℕ → ℂ := fun n => -x * (1 + I * δ n)
  set w : ℕ → ℂ := fun n => ((δ n) ^ 2 / 4 : ℝ) * (1 + I * δ n)⁻¹
  set G : ℕ → ℂ := fun n => geometricMeanSq x (y n)
  have hone : ∀ n, (1 + I * (δ n : ℂ)) ≠ 0 := fun n h => by
    have := congrArg re h; simp at this
  have hG : ∀ n, G n = -x ^ 2 * (1 + I * δ n) := fun n => by
    simp only [G, y, geometricMeanSq]; ring
  have hAG : ∀ n, arithmeticMeanSq x (y n) = G n * w n := fun n => by
    have h1 : arithmeticMeanSq x (y n) = -x ^ 2 * ((δ n : ℂ) ^ 2 / 4) := by
      simp only [arithmeticMeanSq, y]
      linear_combination (x ^ 2 * (δ n : ℂ) ^ 2 / 4) * I_sq
    have h2 : G n * w n = -x ^ 2 * ((δ n : ℂ) ^ 2 / 4) := by
      rw [hG]
      simp only [w]
      push_cast
      field_simp [hone n]
    rw [h1, h2]
  have hwre : ∀ n, 0 < (w n).re := fun n => by
    simp only [w, re_ofReal_mul]
    apply mul_pos (by positivity)
    rw [inv_re]; apply div_pos (by simp) (normSq_pos.2 (hone n))
  -- the path lies eventually in the opposite-node domain
  have hyim : ∀ᶠ n in atTop, (y n).im < 0 := by
    have hyi : ∀ n, (y n).im = -x.im - x.re * δ n := fun n => by
      simp [y, mul_im, mul_re]; ring
    have : Tendsto (fun n => (y n).im) atTop (𝓝 (-x.im)) := by
      rw [show (fun n => (y n).im) = fun n => -x.im - x.re * δ n from funext hyi]
      simpa using (tendsto_const_nhds (x := -x.im)).sub ((tendsto_const_nhds (x := x.re)).mul hδ)
    exact this.eventually (eventually_lt_nhds (by linarith))
  have hsum : ∀ n, 0 < (x + y n).re := fun n => by
    simp [y]; nlinarith [hδpos n]
  -- limits of the pieces
  have hyl : Tendsto y atTop (𝓝 (-x)) := by
    simpa [y] using (tendsto_const_nhds (x := -x)).mul
      ((tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := I)).mul hδc))
  have hGl : Tendsto G atTop (𝓝 (-x ^ 2)) := by
    rw [show G = fun n => -x ^ 2 * (1 + I * (δ n : ℂ)) from funext hG]
    simpa using (tendsto_const_nhds (x := -x ^ 2)).mul
      ((tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := I)).mul hδc))
  have hslit := neg_sq_mem_slitPlane hx.ne'
  have hargG := tendsto_arg_of_tendsto hslit hGl
  have hinv : Tendsto (fun n => (1 + I * (δ n : ℂ))⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℂ))).add
      ((tendsto_const_nhds (x := I)).mul hδc)).inv₀ (by simp)
  have hargw : ∀ n, arg (w n) = arg ((1 + I * (δ n : ℂ))⁻¹) := fun n => by
    simp only [w]; exact arg_real_mul _ (by positivity)
  have hargwl : Tendsto (fun n => arg (w n)) atTop (𝓝 0) := by
    simp only [hargw]
    simpa using tendsto_arg_of_tendsto one_mem_slitPlane hinv
  have hargmem : arg (-x ^ 2) ∈ Ioo (-π) π :=
    ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (slitPlane_arg_ne_pi hslit)⟩
  have hev1 : ∀ᶠ n in atTop, arg (G n) + arg (w n) ∈ Ioo (-π) π := by
    have := hargG.add hargwl
    rw [add_zero] at this
    exact this.eventually (isOpen_Ioo.mem_nhds hargmem)
  have hev2 : ∀ᶠ n in atTop, arg (G n) ∈ Ioo (-π) π :=
    hargG.eventually (isOpen_Ioo.mem_nhds hargmem)
  -- equality along the path
  have heq : ∀ᶠ n in atTop, regCarlsonR (2 * t) (pair β β) (pair x (y n)) =
      quadraticGammaRatio β * (G n ^ t * regCarlsonR t b (pair (w n) 1)) := by
    filter_upwards [hyim, hev1, hev2] with n hn h1 h2
    rw [regR_firstQuadratic_of_im t β x (y n) hx hn (hsum n), hAG]
    congr 1
    have hGs : G n ∈ slitPlane := mul_mem_slitPlane_of_im hx hn
    have hz : pair (w n) 1 ∈ carlsonRSlitDomain := by
      intro i; fin_cases i
      · exact mem_slitPlane_iff.2 (Or.inl (hwre n))
      · exact one_mem_slitPlane
    have hh := regCarlsonR_mul_of_arg_add t b hz hGs (fun i => by
      fin_cases i
      · exact h1
      · simpa [pair] using h2)
    rw [← hh]
    congr 1
    funext i; fin_cases i <;> simp [pair, G]
  -- the left side converges to the value at `(x, -x)`
  have hxs : x ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hx.ne')
  have hxs' : -x ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by simp; exact hx.ne'))
  have hpair : pair x (-x) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hxs
    · exact hxs'
  have hLl : Tendsto (fun n => regCarlsonR (2 * t) (pair β β) (pair x (y n))) atTop
      (𝓝 (regCarlsonR (2 * t) (pair β β) (pair x (-x)))) := by
    refine ((analyticOnNhd_regCarlsonR _ _ _ hpair).continuousAt.tendsto).comp ?_
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact tendsto_const_nhds
    · simpa [pair] using hyl
  -- the right side converges by the small-variable limit (Theorem 8.3-2)
  have hwl : Tendsto w atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => (δ n) ^ 2 / 4) atTop (𝓝 0) := by
      simpa using (hδ.pow 2).div_const 4
    have h1 : Tendsto (fun n => (((δ n) ^ 2 / 4 : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).comp h0
      rwa [ofReal_zero] at this
    have := h1.mul hinv
    rwa [zero_mul] at this
  have hbsum : -t + (β + 1 / 2 + t) = ∑ j, b j := by simp [b]
  have hbk : 0 < (β + 1 / 2 + t - b 0).re := by simp [b, pair]
  have hz1 : (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain :=
    fun _ => by simp [carlsonRightHalfPlane]
  have hlim := tendsto_regCarlsonR_update_zero (0 : Fin 2) hbsum hbk hz1 ⟨1, by decide⟩ hwre hwl
  have hupd : ∀ n, Function.update (fun _ : Fin 2 => (1 : ℂ)) 0 (w n) = pair (w n) 1 := fun n => by
    funext i; fin_cases i <;> simp [pair]
  simp only [hupd, neg_neg] at hlim
  have hGt := ((continuousAt_cpow_const (b := t) hslit).tendsto).comp hGl
  have hR := (hGt.mul hlim).const_mul (quadraticGammaRatio β)
  have huniq := tendsto_nhds_unique hLl (hR.congr' (by
    filter_upwards [heq] with n hn
    exact hn.symm))
  rw [huniq]
  have herase : eraseCarlsonVariable (0 : Fin 2) (fun _ : Fin 2 => (1 : ℂ)) = fun _ => 1 := rfl
  have hs : ∑ i, eraseCarlsonParameter (0 : Fin 2) b i = 1 / 2 - t := by
    have h := sum_eraseCarlsonParameter (0 : Fin 2) b
    rw [sum_pair] at h
    convert h using 1
    · congr!
    · simp [b, pair]
  rw [herase, regCarlsonR_const_node _ _ one_mem_slitPlane, one_cpow, hs,
    show β + 1 / 2 + t - b 0 = 1 / 2 by simp [b, pair]]
  ring

/-- **Carlson's Exercise 8.3-9**, regularized: for non-real `x` and all complex `t, β`,
`R̃_{2t}(β, β; x, -x) = q(β) Γ(1/2) Γ(β + 1/2 + t)⁻¹ Γ(1/2 - t)⁻¹ (-x²)^t`, where
`q(β) = 2^{1-2β} √π / Γ(β)`. -/
theorem regCarlsonR_pair_neg (t β x : ℂ) (hx : x.im ≠ 0) :
    regCarlsonR (2 * t) (pair β β) (pair x (-x)) =
      quadraticGammaRatio β * Gamma (1 / 2) * (Gamma (β + 1 / 2 + t))⁻¹ *
        (Gamma (1 / 2 - t))⁻¹ * (-x ^ 2) ^ t := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hxs : x ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hx)
    have hxs' : -x ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by simpa using hx))
    have h := regCarlsonR_pair_neg_of_im_pos t β (-x) (by simpa using hneg)
    rw [neg_neg] at h
    rw [← regCarlsonR_pair_swap (2 * t) β β hxs hxs', h]
    ring_nf
  · exact regCarlsonR_pair_neg_of_im_pos t β x hpos

/-- **Carlson's Exercise 8.3-9**: for non-real `x`, complex `t`, and `β` not a nonpositive
integer, `R_{2t}(β, β; x, -x) = π^{1/2} Γ(β + 1/2) / (Γ(1/2 - t) Γ(β + 1/2 + t)) (-x²)^t`
(with `1/Γ` read as the entire reciprocal Gamma function). For `2t ∈ ℕ` this is Theorem
6.9-1. -/
theorem carlsonR_pair_neg (t β x : ℂ) (hx : x.im ≠ 0) (hβ : ∀ n : ℕ, β ≠ -n) :
    carlsonR (2 * t) (pair β β) (pair x (-x)) =
      (Real.sqrt π : ℂ) * Gamma (β + 1 / 2) * (Gamma (1 / 2 - t))⁻¹ *
        (Gamma (β + 1 / 2 + t))⁻¹ * (-x ^ 2) ^ t := by
  have hG : Gamma β ≠ 0 := Gamma_ne_zero hβ
  have hdup := Gamma_mul_Gamma_add_half β
  unfold carlsonR
  have hg : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
      Real.Gamma_one_half_eq]
  rw [sum_pair, show β + β = 2 * β by ring, regCarlsonR_pair_neg t β x hx, quadraticGammaRatio,
    hg]
  have h2 : Gamma (2 * β) * (2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt π : ℂ) * (Gamma β)⁻¹ =
      Gamma (β + 1 / 2) := by
    rw [← hdup]; field_simp
  linear_combination (Real.sqrt π * (Gamma (β + 1 / 2 + t))⁻¹ * (Gamma (1 / 2 - t))⁻¹ *
    (-x ^ 2) ^ t) * h2

end Carlson.TwoVariable
