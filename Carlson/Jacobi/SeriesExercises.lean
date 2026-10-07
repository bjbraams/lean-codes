/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipticExpansion
public import Carlson.Jacobi.EllipseCoefficient
public import Carlson.R.LogContour
public import Carlson.Jacobi.GegenbauerAddition
public import Carlson.Jacobi.FourierCosine

/-!
# Jacobi series of particular analytic functions (Exercises 7.6-2 – 7.7-15)

Applications of Theorem 7.6-2 with explicit coefficients: the coefficients are continued
Dirichlet averages of derivatives, identified here with R-functions or with native averages.

## Main results

* `Carlson.TwoVariable.hasSum_affine_cpow_jacobiOn`: Exercise 7.7-14, the Jacobi series of
  `(A - Bx)^{-λ}`.
* `Carlson.TwoVariable.hasSum_gegenbauer_expansion`: Exercise 7.6-2, the Gegenbauer series of
  `f(A + Bx)`.
* `Carlson.TwoVariable.hasSum_gegenbauer_dist_cpow`: Exercise 7.7-15, the Gegenbauer series of
  `|r - r'|^{-2λ}`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§7.6, 7.7.
-/

open Complex Polynomial Set Filter Dirichlet
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Iterated derivatives of `w ↦ (A - Bw)^t` where `A - Bw` lies in the slit plane:
`(-B)ⁿ (t)ₙ↓ (A - Bw)^{t-n}`, with the falling factorial `(t)ₙ↓`. -/
theorem iteratedDeriv_affine_cpow (A B t : ℂ) (n : ℕ) {w : ℂ} (hw : A - B * w ∈ slitPlane) :
    iteratedDeriv n (fun u : ℂ => (A - B * u) ^ t) w =
      (-B) ^ n * (descPochhammer ℂ n).eval t * (A - B * w) ^ (t - n) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have hopen : IsOpen {u : ℂ | A - B * u ∈ slitPlane} :=
      isOpen_slitPlane.preimage (by fun_prop)
    have he : iteratedDeriv n (fun u : ℂ => (A - B * u) ^ t) =ᶠ[𝓝 w]
        fun u => (-B) ^ n * (descPochhammer ℂ n).eval t * (A - B * u) ^ (t - n) := by
      filter_upwards [hopen.mem_nhds hw] with u hu using ih hu
    have hd : HasDerivAt (fun u : ℂ => A - B * u) (-B) w := by
      simpa using ((hasDerivAt_id w).const_mul B).const_sub A
    have hd2 := (hd.cpow_const (c := t - n) hw).const_mul ((-B) ^ n * (descPochhammer ℂ n).eval t)
    rw [iteratedDeriv_succ, he.deriv_eq, hd2.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

/-- The continued average of `w ↦ C (A - Bw)^t` over the nodes `r, s` is
`C R_t(b; A - Br, A - Bs)` (regularized) when the image segment lies in the slit plane. -/
theorem isRegCarlsonContinuation_affine_cpow (C A B t r s : ℂ)
    (hseg : ∀ w ∈ segment ℝ r s, A - B * w ∈ slitPlane) :
    IsRegCarlsonContinuation (fun w => C * (A - B * w) ^ t) (pair r s)
      (fun b => C * regCarlsonR t b (pair (A - B * r) (A - B * s))) := by
  have hhull : convexHull ℝ (Set.range (pair (A - B * r) (A - B * s))) ⊆ slitPlane := by
    have hr : Set.range (pair (A - B * r) (A - B * s)) = {A - B * r, A - B * s} := by
      ext v; simp [pair]; tauto
    rw [hr, convexHull_pair]
    rintro v ⟨a, c, ha, hc, hac, rfl⟩
    have hmem : a • r + c • s ∈ segment ℝ r s := ⟨a, c, ha, hc, hac, rfl⟩
    have := hseg _ hmem
    convert this using 1
    simp only [real_smul]
    have hac' : (a : ℂ) + c = 1 := by exact_mod_cast hac
    linear_combination A * hac'
  have hR := isRegCarlsonRContinuation_regCarlsonR_of_convexHull t hhull
  refine IsRegCarlsonContinuation.mk' (fun b _ => analyticAt_const.mul
    (hR.analyticOnNhd b (Set.mem_univ _))) fun b hb => ?_
  simp only
  rw [regCarlsonDirichletAverage_const_mul, hR.eq_native hb]
  congr 1
  have h := regCarlsonDirichletAverage_comp_affine b (pair r s) (fun u : ℂ => u ^ t) (-B) A
  have hz : (fun i => -B * pair r s i + A) = pair (A - B * r) (A - B * s) := by
    funext i; fin_cases i <;> simp [pair] <;> ring
  rw [hz] at h
  rw [← h]
  congr 1; funext w; ring_nf

/-- **Exercise 7.7-14**: the Jacobi series of `(A - Bx)^{-λ}`,
`(A - Bx)^{-λ} = ∑ₙ (λ)ₙ/n! Bⁿ R_{-λ-n}(1 + α + n, 1 + β + n; A - Br, A - Bs) pₙ(x)`, for `x` inside
an elliptic disk with foci `r, s` on which `A - Bw` stays in the slit plane (principal branch).
`R` is written as `Γ(c)` times the regularized function. -/
theorem hasSum_affine_cpow_jacobiOn (α β r s A B lam : ℂ) (hc : IsGammaRegular (α + β + 2))
    {τ : ℝ} (hD : ∀ w ∈ jacobiEllipseDisk r s τ, A - B * w ∈ slitPlane) {x : ℂ}
    (hx : jacobiEllipseRadius r s x < τ) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval lam / n.factorial * B ^ n *
        (Gamma (α + n + 1 + (β + n + 1)) * regCarlsonR (-lam - n) (pair (α + n + 1) (β + n + 1))
          (pair (A - B * r) (A - B * s))) * (jacobiOn α β r s n).eval x)
      ((A - B * x) ^ (-lam)) := by
  set f : ℂ → ℂ := fun w => (A - B * w) ^ (-lam)
  have hμx := le_jacobiEllipseRadius r s x
  set σ : ℝ := (jacobiEllipseRadius r s x + τ) / 2
  have hσx : jacobiEllipseRadius r s x < σ := by simp only [σ]; linarith
  have hστ : σ < τ := by simp only [σ]; linarith
  have hσ : ‖r - s‖ / 4 < σ := lt_of_le_of_lt hμx hσx
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ) := fun w hw =>
    (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).cpow
      (differentiableAt_const _) (hD w hw)).differentiableWithinAt
  have h := hasSum_jacobiContourCoefficient_jacobiEllipseCycle α β r s hc hf hσ0 hσ hστ hσx
  refine h.congr_fun fun n => ?_
  have hseg : ∀ w ∈ segment ℝ r s, A - B * w ∈ slitPlane := fun w hw =>
    hD w (segment_subset_jacobiEllipseDisk r s (hσ.trans hστ) hw)
  set C : ℂ := (ascPochhammer ℂ n).eval lam * B ^ n
  have hg := isRegCarlsonContinuation_affine_cpow C A B (-lam - n) r s hseg
  have hcont : IsRegCarlsonContinuation (iteratedDeriv n f) (pair r s)
      (fun b => C * regCarlsonR (-lam - n) b (pair (A - B * r) (A - B * s))) := by
    refine IsRegCarlsonContinuation.mk' hg.analyticOnNhd fun b hb => ?_
    rw [hg.eq_native hb]
    refine regCarlsonDirichletAverage_congr_convexHull fun w hw => ?_
    have hw' : w ∈ segment ℝ r s := by
      have hr : Set.range (pair r s) = {r, s} := by ext v; simp [pair]; tauto
      rwa [hr, convexHull_pair] at hw
    simp only [f]
    rw [iteratedDeriv_affine_cpow A B (-lam) n (hseg w hw')]
    have hdesc : (descPochhammer ℂ n).eval (-lam) = (-1) ^ n * (ascPochhammer ℂ n).eval lam := by
      have := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) (-lam) n
      rw [neg_neg] at this
      rw [this, ← mul_assoc, ← mul_pow]; norm_num
    rw [hdesc, neg_pow B]
    simp only [C]
    have h11 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(B ^ n) * (ascPochhammer ℂ n).eval lam * (A - B * w) ^ (-lam - n)) * h11
  rw [jacobiContourCoefficient_jacobiEllipseCycle_eq_continuation α β r s n hf hσ0 hσ hστ hcont]
  simp only [C]
  have hf' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 7.6-2**: the Gegenbauer series of `f(A + Bx)`. If `ν` is not a nonpositive integer,
`re (ν + 1/2) > 0`, and `f` is holomorphic on an elliptic disk with foci `A ∓ B` containing
`A + Bx`, then `f(A + Bx) = ∑ₙ (B/2)ⁿ/(ν)ₙ F⁽ⁿ⁾(1/2 + ν + n, 1/2 + ν + n; A - B, A + B) Cₙ^ν(x)`. -/
theorem hasSum_gegenbauer_expansion {ν : ℂ} (hν : ∀ m : ℕ, (ascPochhammer ℂ m).eval ν ≠ 0)
    (hre : 0 < (ν + 1 / 2).re) (A B : ℂ) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk (A - B) (A + B) τ)) {x : ℂ}
    (hx : jacobiEllipseRadius (A - B) (A + B) (A + B * x) < τ) :
    HasSum (fun n : ℕ => (B / 2) ^ n / (ascPochhammer ℂ n).eval ν *
        carlsonDirichletAverage (pair (ν + 1 / 2 + n) (ν + 1 / 2 + n)) (pair (A - B) (A + B))
          (iteratedDeriv n f) * (gegenbauer ν n).eval x)
      (f (A + B * x)) := by
  set α : ℂ := ν - 1 / 2
  have hre' : 0 < ν.re + 1 / 2 := by simpa using hre
  have hc : IsGammaRegular (α + α + 2) := by
    intro k hk
    have := congrArg re hk
    simp [α] at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hre']
  have hμx := le_jacobiEllipseRadius (A - B) (A + B) (A + B * x)
  set σ : ℝ := (jacobiEllipseRadius (A - B) (A + B) (A + B * x) + τ) / 2
  have hσx : jacobiEllipseRadius (A - B) (A + B) (A + B * x) < σ := by simp only [σ]; linarith
  have hστ : σ < τ := by simp only [σ]; linarith
  have hσ : ‖A - B - (A + B)‖ / 4 < σ := lt_of_le_of_lt hμx hσx
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have h := hasSum_jacobiContourCoefficient_jacobiEllipseCycle α α (A - B) (A + B) hc hf hσ0 hσ
    hστ hσx
  refine h.congr_fun fun n => ?_
  have hpos : 0 < (α + n + 1).re := by
    simp [α]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [jacobiContourCoefficient_jacobiEllipseCycle_eq_average α α (A - B) (A + B) n hpos hpos hf
    hσ0 hσ hστ]
  have hP : (ascPochhammer ℂ n).eval (α + α + n + 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    apply ascPochhammer_eval_ne_zero_of_re_pos
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp [α]; linarith
  rw [eval_jacobiOn_affine_monicJacobi α α A B x n hP]
  have hm := eval_jacobiOn_affine_monicJacobi α α 0 1 x n hP
  simp only [zero_sub, zero_add, one_mul, one_pow] at hm
  have hg := eval_jacobiOn_gegenbauer (ν + 1 / 2) x n (by
      rw [show ν + 1 / 2 - 1 / 2 = ν by ring]; exact hν n)
    (ascPochhammer_eval_ne_zero_of_re_pos hre n)
  rw [show ν + 1 / 2 - 1 = α by simp only [α]; ring, show ν + 1 / 2 - 1 / 2 = ν by ring, hm] at hg
  rw [show α + n + 1 = ν + 1 / 2 + n by simp only [α]; ring]
  have hf' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have hνn := hν n
  have hmono : (monicJacobi α α n).eval x =
      (n.factorial : ℂ) * (gegenbauer ν n).eval x / (2 ^ n * (ascPochhammer ℂ n).eval ν) := by
    rw [eq_div_iff (mul_ne_zero h2 hνn)]; exact hg
  rw [hmono, div_pow]
  field_simp

/-- On real points of the segment `[-1, 1]` the mean radius of the ellipses with foci `∓1`
is `1/2`. -/
theorem jacobiEllipseRadius_neg_one_one_of_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    jacobiEllipseRadius (-1) 1 x = 1 / 2 := by
  have h1 : ‖(x : ℂ) - -1‖ = x + 1 := by
    rw [sub_neg_eq_add, show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by linarith [abs_le.mp hx])]
  have h2 : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonpos (by linarith [abs_le.mp hx])]; ring
  have h3 : ‖(-1 : ℂ) - 1‖ = 2 := by norm_num
  unfold jacobiEllipseRadius
  rw [h1, h2, h3, show x + 1 + (1 - x) = 2 by ring]
  norm_num

/-- **Exercise 7.7-15**: the Gegenbauer series of `|r - r'|^{-2λ}`. For lengths `a ≠ b` of the
two vectors and `x = cos θ ∈ [-1, 1]`, with `ν` and `ν + 1/2` not nonpositive integers and
`2ν + 1` Gamma-regular,
`(a² + b² - 2abx)^{-λ} = ∑ₙ (λ)ₙ/(ν)ₙ (ab)ⁿ R_{-λ-n}(ν + 1/2 + n, ν + 1/2 + n; (a + b)², (a - b)²)
Cₙ^ν(x)`. -/
theorem hasSum_gegenbauer_dist_cpow {ν : ℂ} (hν : ∀ m : ℕ, (ascPochhammer ℂ m).eval ν ≠ 0)
    (hν' : ∀ m : ℕ, (ascPochhammer ℂ m).eval (ν + 1 / 2) ≠ 0) (h2ν : IsGammaRegular (2 * ν + 1))
    (lam : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval lam / (ascPochhammer ℂ n).eval ν *
        ((a * b : ℝ) : ℂ) ^ n * carlsonR (-lam - n) (pair (ν + 1 / 2 + n) (ν + 1 / 2 + n))
          (pair (((a + b) ^ 2 : ℝ) : ℂ) (((a - b) ^ 2 : ℝ) : ℂ)) * (gegenbauer ν n).eval (x : ℂ))
      ((((a ^ 2 + b ^ 2 - 2 * a * b * x : ℝ)) : ℂ) ^ (-lam)) := by
  set A : ℂ := ((a ^ 2 + b ^ 2 : ℝ) : ℂ)
  set B : ℂ := ((2 * a * b : ℝ) : ℂ)
  have hB : 0 < 2 * a * b := by positivity
  set τ : ℝ := (a ^ 2 + b ^ 2) / (2 * (2 * a * b))
  have hc : IsGammaRegular (ν - 1 / 2 + (ν - 1 / 2) + 2) := by
    rw [show ν - 1 / 2 + (ν - 1 / 2) + 2 = 2 * ν + 1 by ring]; exact h2ν
  have hD : ∀ w ∈ jacobiEllipseDisk (-1) 1 τ, A - B * w ∈ slitPlane := by
    intro w hw
    rw [mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    have hwim : w.im = 0 := by
      simp only [A, B, sub_im, ofReal_im, mul_im, ofReal_re, zero_mul, zero_sub, neg_eq_zero,
        add_zero] at him
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h hB.ne'
      · exact h
    have hwre : (a ^ 2 + b ^ 2) / (2 * a * b) ≤ w.re := by
      simp only [A, B, sub_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero] at hre
      rw [div_le_iff₀ hB]; linarith
    have hw1 : 1 ≤ w.re := by
      refine le_trans ?_ hwre
      rw [le_div_iff₀ hB]; nlinarith [sq_nonneg (a - b)]
    have hwr : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hwim]
    have hd : ‖w - -1‖ + ‖w - 1‖ = 2 * w.re := by
      rw [hwr, sub_neg_eq_add, show (w.re : ℂ) + 1 = ((w.re + 1 : ℝ) : ℂ) by push_cast; ring,
        show (w.re : ℂ) - 1 = ((w.re - 1 : ℝ) : ℂ) by push_cast; ring, norm_real, norm_real,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
      simp only [ofReal_re]; ring
    have hrad : (‖w - -1‖ + ‖w - 1‖) / 4 ≤ jacobiEllipseRadius (-1) 1 w := by
      unfold jacobiEllipseRadius
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        (by norm_num)
    have hlt : jacobiEllipseRadius (-1) 1 w < τ := hw
    rw [hd] at hrad
    have : τ ≤ 2 * w.re / 4 := by
      simp only [τ]
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hB] at hwre
      nlinarith
    linarith
  have hxτ : jacobiEllipseRadius (-1) 1 (x : ℂ) < τ := by
    rw [jacobiEllipseRadius_neg_one_one_of_abs_le hx]
    simp only [τ]
    rw [lt_div_iff₀ (by positivity)]
    have : 0 < (a - b) ^ 2 := by
      have : a - b ≠ 0 := sub_ne_zero.mpr hab
      positivity
    nlinarith
  have H := hasSum_affine_cpow_jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 A B lam hc hD hxτ
  convert H using 1
  · funext n
    have hJ := eval_jacobiOn_gegenbauer (ν + 1 / 2) (x : ℂ) n
      (by rw [show ν + 1 / 2 - 1 / 2 = ν by ring]; exact hν n) (hν' n)
    rw [show ν + 1 / 2 - 1 = ν - 1 / 2 by ring, show ν + 1 / 2 - 1 / 2 = ν by ring] at hJ
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have hνn := hν n
    have hp : (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 n).eval (x : ℂ) =
        n.factorial * (gegenbauer ν n).eval (x : ℂ) / (2 ^ n * (ascPochhammer ℂ n).eval ν) := by
      rw [eq_div_iff (mul_ne_zero h2 hνn)]; exact hJ
    rw [hp, carlsonR, sum_pair,
      show ν - 1 / 2 + n + 1 = ν + 1 / 2 + n by ring,
      show A - B * -1 = (((a + b) ^ 2 : ℝ) : ℂ) by simp only [A, B]; push_cast; ring,
      show A - B * 1 = (((a - b) ^ 2 : ℝ) : ℂ) by simp only [A, B]; push_cast; ring]
    simp only [B]
    push_cast
    field_simp
    ring
  · simp only [A, B]; push_cast; ring_nf

end Carlson.TwoVariable
