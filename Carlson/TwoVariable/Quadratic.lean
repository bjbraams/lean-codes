/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.TwoVariable.RPolynomial
public import Carlson.TwoVariable.PolynomialDifferential
public import Carlson.TwoVariable.R
public import Carlson.TwoVariable.S

/-!
# Quadratic transformations of two-variable Carlson functions

This is the home for Carlson's Sections 6.9 and 6.10.  Their polynomial forms will be proved
before the branch-sensitive complex-power forms.  In particular, the hypotheses `x,y ∈ C₀`
in Carlson's statements must be translated into an explicit square-root branch domain rather
than suppressed by notation.
-/

open Complex Set Filter
open scoped Classical Topology
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The squared arithmetic mean occurring in Carlson's first quadratic transformation. -/
def arithmeticMeanSq (x y : ℂ) : ℂ := ((x + y) / 2) ^ 2

/-- The squared geometric mean occurring in Carlson's first quadratic transformation. -/
def geometricMeanSq (x y : ℂ) : ℂ := x * y

/-- The arithmetic mean is symmetric in its arguments. -/
theorem arithmeticMeanSq_comm (x y : ℂ) : arithmeticMeanSq x y = arithmeticMeanSq y x := by
  simp [arithmeticMeanSq, add_comm]

/-- The squared geometric mean is symmetric in its arguments. -/
theorem geometricMeanSq_comm (x y : ℂ) : geometricMeanSq x y = geometricMeanSq y x := by
  simp [geometricMeanSq, mul_comm]

private lemma numerator₂_zero_right (n : ℕ) (p q x : ℂ) :
    carlsonRPolynomialNumerator₂ n p q x 0 = (ascPochhammer ℂ n).eval p * x ^ n := by
  rw [← carlsonRPolynomialNumerator_pair]
  convert! carlsonRPolynomialNumerator_single n (0 : Fin 2) (pair p q) x using 1
  congr 1
  ext i
  fin_cases i <;> simp [pair]

private lemma eq_of_translate_sub_deriv_zero (F G : ℂ → ℂ → ℂ)
    (hzero : ∀ x, F x 0 = G x 0)
    (hd : ∀ x y w, HasDerivAt (fun t => F (x + t) (y + t) - G (x + t) (y + t)) 0 w)
    (x y : ℂ) : F x y = G x y := by
  have H := is_const_of_deriv_eq_zero (fun w => (hd x y w).differentiableAt)
    (fun w => (hd x y w).deriv) 0 (-y)
  simpa only [add_zero, add_neg_cancel, hzero, sub_self, sub_eq_zero] using H

private lemma hasDerivAt_numerator₂_quadratic_translate (n : ℕ) (p q x y w : ℂ) :
    HasDerivAt (fun t => carlsonRPolynomialNumerator₂ (n + 1) p q
      (arithmeticMeanSq (x + t) (y + t)) (geometricMeanSq (x + t) (y + t)))
      ((n + 1 : ℂ) * (p + q + n) *
        carlsonRPolynomialNumerator₂ n p q
          (arithmeticMeanSq (x + w) (y + w)) (geometricMeanSq (x + w) (y + w)) *
        (x + y + 2 * w)) w := by
  let d := ((x - y) / 2) ^ 2
  let s := fun t : ℂ => ((x + y) / 2 + t) ^ 2
  have hs : HasDerivAt s (x + y + 2 * w) w := by
    convert! (((hasDerivAt_id w).const_add ((x + y) / 2)).pow 2) using 1
    simp only [id_eq]
    ring
  have H := (hasDerivAt_carlsonRPolynomialNumerator₂_translate n p q 0 (-d) (s w)).comp w hs
  have hA (t : ℂ) : 0 + s t = arithmeticMeanSq (x + t) (y + t) := by
    dsimp [s, arithmeticMeanSq]; ring
  have hG (t : ℂ) : -d + s t = geometricMeanSq (x + t) (y + t) := by
    dsimp [d, s, geometricMeanSq]; ring
  simpa only [Function.comp_def, hA, hG] using! H

private lemma meanSq_zero_pow (n : ℕ) (x : ℂ) :
    4 ^ n * arithmeticMeanSq x 0 ^ n = x ^ (2 * n) := by
  rw [← mul_pow, pow_mul]
  congr 1
  dsimp [arithmeticMeanSq]
  ring

set_option maxRecDepth 2048 in
/-- Polynomial quadratic transformations before inserting redundant Pochhammer factors. -/
private theorem numerator₂_firstQuadratic (n : ℕ) (β x y : ℂ) :
    carlsonRPolynomialNumerator₂ (2 * n) β β x y =
        4 ^ n * (ascPochhammer ℂ n).eval β *
          carlsonRPolynomialNumerator₂ n (β + n) (1 / 2 - n)
            (arithmeticMeanSq x y) (geometricMeanSq x y) ∧
    carlsonRPolynomialNumerator₂ (2 * n + 1) β β x y =
        2 * 4 ^ n * (ascPochhammer ℂ (n + 1)).eval β * ((x + y) / 2) *
          carlsonRPolynomialNumerator₂ n (1 + β + n) (-1 / 2 - n)
            (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  induction n generalizing β x y with
  | zero =>
    simp [carlsonRPolynomialNumerator₂, Finset.Nat.antidiagonal_succ]
    ring
  | succ n ih =>
    have heven (x y : ℂ) : carlsonRPolynomialNumerator₂ (2 * (n + 1)) β β x y =
        4 ^ (n + 1) * (ascPochhammer ℂ (n + 1)).eval β *
          carlsonRPolynomialNumerator₂ (n + 1) (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ))
            (arithmeticMeanSq x y) (geometricMeanSq x y) := by
      apply eq_of_translate_sub_deriv_zero
      · intro v
        rw [numerator₂_zero_right, geometricMeanSq, mul_zero, numerator₂_zero_right,
          show 2 * (n + 1) = (n + 1) + (n + 1) by omega,
          ascPochhammer_add_eval β (n + 1) (n + 1)]
        have H := meanSq_zero_pow (n + 1) v
        rw [show (n + 1) + (n + 1) = 2 * (n + 1) by omega]
        linear_combination
          -(ascPochhammer ℂ (n + 1)).eval β *
            (ascPochhammer ℂ (n + 1)).eval (β + (n + 1 : ℕ)) * H
      · intro u v w
        have hl := hasDerivAt_carlsonRPolynomialNumerator₂_translate (2 * n + 1) β β u v w
        have hr := (hasDerivAt_numerator₂_quadratic_translate n
          (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ)) u v w).const_mul
            (4 ^ (n + 1) * (ascPochhammer ℂ (n + 1)).eval β)
        convert! hl.sub hr using 1
        rw [(ih β (u + w) (v + w)).2]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, pow_succ]
        have hp : β + ((n : ℂ) + 1) = 1 + β + n := by ring
        have hq : (1 : ℂ) / 2 - ((n : ℂ) + 1) = -1 / 2 - n := by ring
        rw [hp, hq]
        ring
    refine ⟨heven x y, ?_⟩
    apply eq_of_translate_sub_deriv_zero
    · intro v
      rw [numerator₂_zero_right, geometricMeanSq, mul_zero, numerator₂_zero_right,
        show 2 * (n + 1) + 1 = ((n + 1) + 1) + (n + 1) by omega,
        ascPochhammer_add_eval β ((n + 1) + 1) (n + 1)]
      have hp : 1 + β + (n + 1 : ℕ) = β + ((n + 1) + 1 : ℕ) := by push_cast; ring
      rw [hp]
      have H := meanSq_zero_pow (n + 1) v
      simp only [add_zero]
      rw [show ((n + 1) + 1) + (n + 1) = 2 * (n + 1) + 1 by omega, pow_succ]
      linear_combination
        -(ascPochhammer ℂ ((n + 1) + 1)).eval β *
          (ascPochhammer ℂ (n + 1)).eval (β + ((n + 1) + 1 : ℕ)) * v * H
    · intro u v w
      have hl := hasDerivAt_carlsonRPolynomialNumerator₂_translate (2 * (n + 1)) β β u v w
      have hm : HasDerivAt (fun t : ℂ => ((u + t) + (v + t)) / 2) 1 w := by
        convert! (((hasDerivAt_id w).const_add u).add
          ((hasDerivAt_id w).const_add v)).div_const 2 using 1
        norm_num
      have hr := (hm.mul (hasDerivAt_numerator₂_quadratic_translate n
        (1 + β + (n + 1 : ℕ)) (-1 / 2 - (n + 1 : ℕ)) u v w)).const_mul
          (2 * 4 ^ (n + 1) * (ascPochhammer ℂ ((n + 1) + 1)).eval β)
      have hc := carlsonRPolynomialNumerator₂_contiguous n
        (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ))
          (arithmeticMeanSq (u + w) (v + w)) (geometricMeanSq (u + w) (v + w))
      convert! hl.sub hr using 1
      · funext t
        dsimp only [Pi.sub_apply, Pi.mul_apply]
        ring
      · rw [heven (u + w) (v + w)]
        simp only [ascPochhammer_succ_eval, Nat.cast_add, Nat.cast_mul,
          Nat.cast_one, Nat.cast_ofNat] at hc ⊢
        have hp : β + ((n : ℂ) + 1) + 1 = 1 + β + ((n : ℂ) + 1) := by ring
        have hq : (1 : ℂ) / 2 - ((n : ℂ) + 1) - 1 = -1 / 2 - ((n : ℂ) + 1) := by ring
        rw [hp, hq] at hc
        dsimp only [arithmeticMeanSq] at hc ⊢
        linear_combination
          4 * 4 ^ (n + 1) * (ascPochhammer ℂ n).eval β *
            (β + n) * (β + ((n : ℂ) + 1)) * hc

/-- The even moments on opposite nodes, in division-free form. -/
private lemma numerator₂_even_opposite (n : ℕ) (β w : ℂ) :
    carlsonRPolynomialNumerator₂ (2 * n) β β w (-w) =
      4 ^ n * (ascPochhammer ℂ n).eval β *
        (ascPochhammer ℂ n).eval (1 / 2) * w ^ (2 * n) := by
  rw [(numerator₂_firstQuadratic n β w (-w)).1]
  have hA : arithmeticMeanSq w (-w) = 0 := by simp [arithmeticMeanSq]
  rw [hA, ← carlsonRPolynomialNumerator₂_swap,
    numerator₂_zero_right]
  have hp : (1 : ℂ) / 2 - n = 1 - 1 / 2 - n := by ring
  rw [hp, ascPochhammer_eval_reflect]
  rw [show geometricMeanSq w (-w) = -(w ^ 2) by dsimp [geometricMeanSq]; ring,
    neg_pow]
  rw [pow_mul]
  ring_nf
  simp

private lemma pochhammer_ne_zero_of_re_pos {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval c ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨k, _, hk⟩
  have h := congrArg Complex.re hk
  simp only [natCast_re, neg_re] at h
  linarith

private lemma Gamma_mul_regRPolynomial (n : ℕ) (p q x y : ℂ)
    (hc : 0 < (p + q).re) :
    Gamma (p + q) * regRPolynomial n p q x y =
      carlsonRPolynomialNumerator₂ n p q x y /
        (ascPochhammer ℂ n).eval (p + q) := by
  have hreg (k : ℕ) : p + q ≠ -(k : ℂ) := by
    intro h
    have h' := congrArg Complex.re h
    simp only [neg_re, natCast_re] at h'
    linarith
  have hG := Gamma_add_nat_div_Gamma_eq (n := n) (p + q) hreg
  have hG0 := Gamma_ne_zero_of_re_pos hc
  have hp0 := pochhammer_ne_zero_of_re_pos hc n
  have hG' : Gamma (p + q + n) =
      (ascPochhammer ℂ n).eval (p + q) * Gamma (p + q) :=
    (div_eq_iff hG0).mp hG
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma, hG']
  field_simp

private lemma Gamma_mul_regRPolynomial_even_opposite
    (n : ℕ) {β : ℂ} (hβ : 0 < β.re) (w : ℂ) :
    Gamma (β + β) * regRPolynomial (2 * n) β β w (-w) =
      (ascPochhammer ℂ n).eval (1 / 2) /
        (ascPochhammer ℂ n).eval (β + 1 / 2) * w ^ (2 * n) := by
  have hb : 0 < (β + β).re := by simpa using add_pos hβ hβ
  rw [Gamma_mul_regRPolynomial _ _ _ _ _ hb,
    numerator₂_even_opposite, show β + β = 2 * β by ring,
    ascPochhammer_eval_double]
  have hp := pochhammer_ne_zero_of_re_pos hβ n
  have hq := pochhammer_ne_zero_of_re_pos (c := β + 1 / 2) (by
    simp only [add_re, div_ofNat_re, one_re]; linarith) n
  field_simp

private lemma rIntegral_firstQuadratic_near_one (t β w : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hw : ‖w‖ < 1) :
    rIntegral (2 * t) β β (1 - w) (1 + w) =
      rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) := by
  let L : ℕ → ℂ := fun n => Gamma (β + β) *
    ((ascPochhammer ℂ n).eval (-(2 * t)) / (n.factorial : ℂ) *
      regRPolynomial n β β w (-w))
  let R : ℕ → ℂ := fun n => Gamma ((β + t) + (1 / 2 - t)) *
    ((ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) *
      regRPolynomial n (β + t) (1 / 2 - t) 0 (w ^ 2))
  have hl : HasSum L (rIntegral (2 * t) β β (1 - w) (1 + w)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-(2 * t))
      (pair β β) (pair w (-w)) hbleft (by
        intro i; fin_cases i <;> simpa [pair] using hw)).mul_left (Gamma (β + β))
    have hnodes : (fun i => 1 - pair w (-w) i) = pair (1 - w) (1 + w) := by
      ext i; fin_cases i <;> simp [pair]
    simpa only [hnodes, neg_neg, carlsonRIntegral, sum_pair, L] using H
  have hr : HasSum R (rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-t)
      (pair (β + t) (1 / 2 - t)) (pair 0 (w ^ 2)) hbright (by
        intro i; fin_cases i
        · simp [pair]
        · simpa [pair, norm_pow] using pow_lt_one₀ (norm_nonneg w) hw (by decide : 2 ≠ 0)
      )).mul_left (Gamma ((β + t) + (1 / 2 - t)))
    have hnodes : (fun i => 1 - pair 0 (w ^ 2) i) = pair 1 (1 - w ^ 2) := by
      ext i; fin_cases i <;> simp [pair]
    simpa only [hnodes, neg_neg, carlsonRIntegral, sum_pair, R] using H
  have hodd (n : ℕ) (hn : n ∉ Set.range (fun m : ℕ => 2 * m)) : L n = 0 := by
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · exact (hn ⟨m, hm.symm⟩).elim
    · subst n
      simp [L, regRPolynomial_eq_zero_of_odd _ (by exact ⟨m, rfl⟩)]
  have hi : Function.Injective (fun m : ℕ => 2 * m) := by
    intro i j h
    dsimp only at h
    omega
  have he := (hi.hasSum_iff hodd).mpr hl
  have hβ : 0 < β.re := hbleft 0
  have hc : 0 < (β + 1 / 2).re := by
    simp only [add_re, div_ofNat_re, one_re]; linarith
  have heq (n : ℕ) : L (2 * n) = R n := by
    have hfac : ((2 * n).factorial : ℂ) =
        4 ^ n * (ascPochhammer ℂ n).eval (1 / 2) * (n.factorial : ℂ) := by
      have H := ascPochhammer_eval_double (1 / 2 : ℂ) n
      norm_num [ascPochhammer_eval_one] at H ⊢
      exact H
    have hhalf := pochhammer_ne_zero_of_re_pos (c := (1 / 2 : ℂ)) (by norm_num) n
    have hsum : β + t + (1 / 2 - t) = β + 1 / 2 := by ring
    have hsingle : Gamma ((β + t) + (1 / 2 - t)) *
        regRPolynomial n (β + t) (1 / 2 - t) 0 (w ^ 2) =
        (ascPochhammer ℂ n).eval (1 / 2 - t) * (w ^ 2) ^ n /
          (ascPochhammer ℂ n).eval (β + 1 / 2) := by
      rw [Gamma_mul_regRPolynomial _ _ _ _ _ (by rwa [hsum]), hsum,
        ← carlsonRPolynomialNumerator₂_swap, numerator₂_zero_right]
    dsimp only [L, R]
    rw [show Gamma (β + β) *
        ((ascPochhammer ℂ (2 * n)).eval (-(2 * t)) / ((2 * n).factorial : ℂ) *
          regRPolynomial (2 * n) β β w (-w)) =
        (ascPochhammer ℂ (2 * n)).eval (-(2 * t)) / ((2 * n).factorial : ℂ) *
          (Gamma (β + β) * regRPolynomial (2 * n) β β w (-w)) by ring]
    rw [Gamma_mul_regRPolynomial_even_opposite n hβ w,
      show -(2 * t) = 2 * (-t) by ring, ascPochhammer_eval_double, hfac]
    have hrw := congrArg (fun v : ℂ => (ascPochhammer ℂ n).eval (-t) /
      (n.factorial : ℂ) * v) hsingle
    rw [show -t + (1 : ℂ) / 2 = 1 / 2 - t by ring]
    convert! hrw.symm using 1 <;> field_simp
    all_goals ring
  have hs : HasSum R (rIntegral (2 * t) β β (1 - w) (1 + w)) := by
    simpa only [Function.comp_def, heq] using he
  exact hs.unique hr

/-- Branch-safe domain for Carlson's first quadratic transformation 6.9-3. -/
def FirstQuadraticDomain (x y : ℂ) : Prop :=
  pair x y ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

/-- Branch-safe domain for Carlson's second quadratic transformation 6.10-1. -/
def SecondQuadraticDomain (x y : ℂ) : Prop :=
  pair (x ^ 2) (y ^ 2) ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

private lemma rIntegral_smul_of_re_pos (t p q x y : ℂ) {m : ℂ} (hm : 0 < m.re)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    rIntegral t p q (m * x) (m * y) = m ^ t * rIntegral t p q x y := by
  change carlsonRIntegral t (pair p q) (pair (m * x) (m * y)) = _
  rw [show pair (m * x) (m * y) = (fun i => m * pair x y i) by
    ext i; fin_cases i <;> rfl]
  exact carlsonRIntegral_smul_of_re_pos t hm hz

private lemma rIntegral_firstQuadratic_of_normalized (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hm : 0 < ((x + y) / 2).re) (hm2 : 0 < (arithmeticMeanSq x y).re)
    (hw : ‖(y - x) / (x + y)‖ < 1) :
    rIntegral (2 * t) β β x y =
      rIntegral t (β + t) (1 / 2 - t) (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  let m := (x + y) / 2
  let w := (y - x) / (x + y)
  have hsub {v : ℂ} (hv : ‖v‖ < 1) : 0 < (1 - v).re := by
    have h := re_le_norm v
    simp only [sub_re, one_re]
    linarith
  have hl : pair (1 - w) (1 + w) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hsub hw
    · change 0 < (1 + w).re
      simpa only [sub_neg_eq_add] using
        hsub (v := -w) (by simpa only [norm_neg] using (hw : ‖w‖ < 1))
  have hr : pair 1 (1 - w ^ 2) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · norm_num [pair, carlsonRightHalfPlane]
    · exact hsub (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw (by decide))
  have hsum : x + y ≠ 0 := by
    intro h
    simp [h] at hm
  have hx : m * (1 - w) = x := by dsimp [m, w]; field_simp; ring
  have hy : m * (1 + w) = y := by dsimp [m, w]; field_simp; ring
  have hg : m ^ 2 * (1 - w ^ 2) = geometricMeanSq x y := by
    dsimp [m, w, geometricMeanSq]; field_simp; ring
  have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hm))
  have hpow : (m ^ (2 : ℕ)) ^ t = m ^ (2 * t) := by
    symm
    exact cpow_ofNat_mul' (by linarith [harg.1]) (by linarith [harg.2]) t
  have H := rIntegral_firstQuadratic_near_one t β w hbleft hbright hw
  have Hleft := rIntegral_smul_of_re_pos (2 * t) β β (1 - w) (1 + w) hm hl
  have Hright := rIntegral_smul_of_re_pos t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) hm2 hr
  rw [hx, hy, H] at Hleft
  change rIntegral t (β + t) (1 / 2 - t) (m ^ 2 * 1) (m ^ 2 * (1 - w ^ 2)) =
    (m ^ (2 : ℕ)) ^ t * rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) at Hright
  rw [mul_one, hg, hpow] at Hright
  exact Hleft.trans Hright.symm

private lemma re_affine_prod_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hxy : 0 < (x * y).re) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (((1 - s : ℂ) + s * x) * ((1 - s : ℂ) + s * y)).re := by
  have heq : (((1 - s : ℂ) + s * x) * ((1 - s : ℂ) + s * y)).re =
      (1 - s) ^ 2 + s * (1 - s) * (x.re + y.re) + s ^ 2 * (x * y).re := by
    simp [mul_re, sub_re, add_re]
    ring
  rw [heq]
  have hmiddle : 0 ≤ s * (1 - s) * (x.re + y.re) := by positivity
  by_cases hs : s = 1
  · subst s; simpa using hxy
  · have : 0 < (1 - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hs))
    positivity

/-- The branch-safe domain is preserved along the segment from the all-one nodes. -/
theorem FirstQuadraticDomain.affine {x y : ℂ} (hz : FirstQuadraticDomain x y)
    {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    FirstQuadraticDomain (1 - (r : ℂ) + r * x) (1 - (r : ℂ) + r * y) := by
  have hpos {v : ℂ} (hv : 0 < v.re) : 0 < (1 - (r : ℂ) + r * v).re := by
    have H := convex_carlsonRightHalfPlane (by norm_num [carlsonRightHalfPlane] : (1 : ℂ) ∈ carlsonRightHalfPlane)
      hv (sub_nonneg.mpr hr.2) hr.1 (by ring : 1 - r + r = 1)
    simpa [Complex.real_smul, carlsonRightHalfPlane] using H
  have hm : 0 < ((x + y) / 2).re := by
    have hx := hz.1 0
    have hy := hz.1 1
    change 0 < x.re at hx
    change 0 < y.re at hy
    simp only [div_ofNat_re, add_re]
    positivity
  have hA := re_affine_prod_pos hm hm (by
    have hh := hz.2 0
    change 0 < (((x + y) / 2) ^ 2).re at hh
    simpa only [pow_two] using hh) hr.1 hr.2
  have heq : arithmeticMeanSq ((1 - (r : ℂ) + r * x)) ((1 - (r : ℂ) + r * y)) =
      (1 - (r : ℂ) + r * ((x + y) / 2)) *
        (1 - (r : ℂ) + r * ((x + y) / 2)) := by
    dsimp [arithmeticMeanSq]; ring
  constructor
  · intro i; fin_cases i
    · exact hpos (hz.1 0)
    · exact hpos (hz.1 1)
  · intro i; fin_cases i
    · change 0 < (arithmeticMeanSq _ _).re
      rw [heq]
      exact hA
    · exact re_affine_prod_pos (hz.1 0) (hz.1 1) (hz.2 1) hr.1 hr.2

/-- Carlson's first quadratic transformation 6.9-3 on a common native integral domain.

The extra convergence hypotheses make both sides genuine Dirichlet integrals.  The book's
larger parameter domain is obtained afterward from continuation in the Dirichlet parameters. -/
theorem rIntegral_firstQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hz : FirstQuadraticDomain x y) :
    rIntegral (2 * t) β β x y =
      rIntegral t (β + t) (1 / 2 - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  let X : ℂ → ℂ := fun s => 1 - s + s * x
  let Y : ℂ → ℂ := fun s => 1 - s + s * y
  let S : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hX (s : ℂ) : AnalyticAt ℂ X s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hY (s : ℂ) : AnalyticAt ℂ Y s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hpath (s : ℂ) (hs : s ∈ S) : FirstQuadraticDomain (X s) (Y s) := by
    obtain ⟨r, hr, rfl⟩ := hs
    exact hz.affine hr
  have hleft : AnalyticOnNhd ℂ (fun s => rIntegral (2 * t) β β (X s) (Y s)) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral (2 * t) hbleft _ (hpath s hs).1).comp
      (f := fun u => pair (X u) (Y u))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact hX s
    · exact hY s
  have hright : AnalyticOnNhd ℂ (fun s => rIntegral t (β + t) (1 / 2 - t)
      (arithmeticMeanSq (X s) (Y s)) (geometricMeanSq (X s) (Y s))) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral t hbright _ (hpath s hs).2).comp
      (f := fun u => pair (arithmeticMeanSq (X u) (Y u)) (geometricMeanSq (X u) (Y u)))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (((hX s).add (hY s)).div_const (c := 2)).pow 2
    · exact (hX s).mul (hY s)
  have hS : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have h0 : (0 : ℂ) ∈ S := ⟨0, by norm_num, by simp⟩
  have h1 : (1 : ℂ) ∈ S := ⟨1, by norm_num, by simp⟩
  have hlocal : (fun s => rIntegral (2 * t) β β (X s) (Y s)) =ᶠ[𝓝 0]
      (fun s => rIntegral t (β + t) (1 / 2 - t)
        (arithmeticMeanSq (X s) (Y s)) (geometricMeanSq (X s) (Y s))) := by
    have hm := (Complex.continuous_re.continuousAt.comp
      (((hX 0).continuousAt.add (hY 0).continuousAt).div_const 2)).eventually_const_lt
      (by norm_num [X, Y] : (0 : ℝ) < (((X 0 + Y 0) / 2 : ℂ)).re)
    have hm2 := (Complex.continuous_re.continuousAt.comp
      ((((hX 0).continuousAt.add (hY 0).continuousAt).div_const 2).pow 2)).eventually_const_lt
      (by norm_num [X, Y] : (0 : ℝ) < ((((X 0 + Y 0) / 2 : ℂ) ^ 2)).re)
    have hw := ((((hY 0).continuousAt.sub (hX 0).continuousAt).div
      ((hX 0).continuousAt.add (hY 0).continuousAt) (by norm_num [X, Y])).norm).eventually_lt_const
      (by norm_num [X, Y] : ‖(Y 0 - X 0) / (X 0 + Y 0)‖ < 1)
    filter_upwards [hm, hm2, hw] with s hs hs2 hw
    exact rIntegral_firstQuadratic_of_normalized t β (X s) (Y s) hbleft hbright hs hs2 hw
  have H := hleft.eqOn_of_preconnected_of_eventuallyEq hright hS h0 hlocal h1
  simpa [X, Y] using H

/-- Carlson's second quadratic transformation 6.10-1 on a common native integral domain. -/
theorem rIntegral_secondQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent)
    (hz : SecondQuadraticDomain x y) :
    rIntegral t β β (x ^ 2) (y ^ 2) =
      rIntegral t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  sorry

/-- Division-free polynomial form of the even-degree first quadratic transformation 6.9-8.
It is valid at exceptional parameters because no Pochhammer symbol is divided out. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_even
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n) β β x y =
      (ascPochhammer ℂ (2 * n)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (β + n) (1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  rw [(numerator₂_firstQuadratic n β x y).1, ascPochhammer_eval_double]
  ring

/-- Division-free polynomial form of the odd-degree first quadratic transformation 6.9-9. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_odd
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n + 1) β β x y =
      ((x + y) / 2) * (ascPochhammer ℂ (2 * n + 1)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (1 + β + n) (-1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  rw [(numerator₂_firstQuadratic n β x y).2, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval, ascPochhammer_eval_double]
  push_cast
  ring

private lemma numerator₂_rotated_quadratic (n : ℕ) (p q x y : ℂ) :
    carlsonRPolynomialNumerator₂ n (1 - p - q - n) q
      (arithmeticMeanSq ((x + y) ^ 2) ((x - y) ^ 2))
      (geometricMeanSq ((x + y) ^ 2) ((x - y) ^ 2)) =
    4 ^ n * (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n p q
      (arithmeticMeanSq (x ^ 2) (y ^ 2)) (geometricMeanSq (x ^ 2) (y ^ 2)) := by
  have hA : arithmeticMeanSq ((x + y) ^ 2) ((x - y) ^ 2) =
      4 * arithmeticMeanSq (x ^ 2) (y ^ 2) := by dsimp [arithmeticMeanSq]; ring
  have hG : geometricMeanSq ((x + y) ^ 2) ((x - y) ^ 2) =
      4 * (arithmeticMeanSq (x ^ 2) (y ^ 2) - geometricMeanSq (x ^ 2) (y ^ 2)) := by
    dsimp [arithmeticMeanSq, geometricMeanSq]; ring
  rw [hA, hG, carlsonRPolynomialNumerator₂_smul,
    carlsonRPolynomialNumerator₂_transform n p q]
  rw [mul_assoc, ← mul_assoc ((-1 : ℂ) ^ n), ← mul_pow]
  simp

/-- Regression check: the version of the second quadratic identity with unsquared
right-hand nodes is false, already for `n = β = 1`, `x = 2`, `y = 0`. -/
theorem secondQuadratic_unsquared_counterexample :
    (ascPochhammer ℂ 1).eval (1 - 2 * 1 - 2 * 1) *
        carlsonRPolynomialNumerator₂ 1 1 1 (2 ^ 2) (0 ^ 2) ≠
      (ascPochhammer ℂ 1).eval 1 *
        carlsonRPolynomialNumerator₂ 1 (1 / 2 - 1 - 1) (1 / 2 - 1 - 1)
          (2 + 0) (2 - 0) := by
  norm_num [carlsonRPolynomialNumerator₂, Finset.Nat.antidiagonal_succ]

/-- Division-free polynomial form of Carlson's involutive transformation 6.10-3.
Both transformed nodes must be squared: both sides are homogeneous of degree `2 * n`
in `x,y`.  Omitting the squares gives the false identity refuted above. -/
theorem carlsonRPolynomialNumerator₂_secondQuadratic
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (1 - 2 * β - 2 * n) *
        carlsonRPolynomialNumerator₂ n β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ n).eval β *
        carlsonRPolynomialNumerator₂ n (1 / 2 - β - n) (1 / 2 - β - n)
          ((x + y) ^ 2) ((x - y) ^ 2) := by
  obtain ⟨m, rfl | rfl⟩ := n.even_or_odd'
  · let γ : ℂ := 1 / 2 - β - (2 * m : ℕ)
    have hg : 1 - 2 * β - 2 * (2 * m : ℕ) = 2 * γ := by dsimp [γ]; push_cast; ring
    have hp : γ + m = 1 - (β + m) - (1 / 2 - m) - m := by
      dsimp [γ]; push_cast; ring
    have hr : γ + 1 / 2 = 1 - (β + m) - m := by dsimp [γ]; push_cast; ring
    change (ascPochhammer ℂ (2 * m)).eval (1 - 2 * β - 2 * (2 * m : ℕ)) *
      carlsonRPolynomialNumerator₂ (2 * m) β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ (2 * m)).eval β *
        carlsonRPolynomialNumerator₂ (2 * m) γ γ ((x + y) ^ 2) ((x - y) ^ 2)
    rw [hg, (numerator₂_firstQuadratic m β (x ^ 2) (y ^ 2)).1,
      (numerator₂_firstQuadratic m γ ((x + y) ^ 2) ((x - y) ^ 2)).1,
      hp, numerator₂_rotated_quadratic, ascPochhammer_eval_double,
      show 2 * m = m + m by omega, ascPochhammer_add_eval β m m, hr, ascPochhammer_eval_reflect]
    ring
  · let γ : ℂ := 1 / 2 - β - (2 * m + 1 : ℕ)
    have hg : 1 - 2 * β - 2 * (2 * m + 1 : ℕ) = 2 * γ := by dsimp [γ]; push_cast; ring
    have hp : 1 + γ + m = 1 - (1 + β + m) - (-1 / 2 - m) - m := by
      dsimp [γ]; push_cast; ring
    have hr : γ + 1 / 2 = 1 - (β + (m + 1 : ℕ)) - m := by dsimp [γ]; push_cast; ring
    have hM : (((x + y) ^ 2 + (x - y) ^ 2) / 2 : ℂ) = 2 * ((x ^ 2 + y ^ 2) / 2) := by ring
    change (ascPochhammer ℂ (2 * m + 1)).eval (1 - 2 * β - 2 * (2 * m + 1 : ℕ)) *
      carlsonRPolynomialNumerator₂ (2 * m + 1) β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ (2 * m + 1)).eval β *
        carlsonRPolynomialNumerator₂ (2 * m + 1) γ γ ((x + y) ^ 2) ((x - y) ^ 2)
    have hd : (ascPochhammer ℂ (2 * m + 1)).eval (2 * γ) =
        2 * 4 ^ m * (ascPochhammer ℂ (m + 1)).eval γ *
          (ascPochhammer ℂ m).eval (γ + 1 / 2) := by
      rw [ascPochhammer_succ_eval, ascPochhammer_eval_double, ascPochhammer_succ_eval]
      push_cast
      ring
    rw [hg, (numerator₂_firstQuadratic m β (x ^ 2) (y ^ 2)).2,
      (numerator₂_firstQuadratic m γ ((x + y) ^ 2) ((x - y) ^ 2)).2,
      hp, numerator₂_rotated_quadratic, hd,
      show 2 * m + 1 = (m + 1) + m by omega, ascPochhammer_add_eval β (m + 1) m,
      hr, ascPochhammer_eval_reflect, hM]
    have hparam : β + (m + 1 : ℕ) = 1 + β + m := by push_cast; ring
    rw [hparam]
    ring

/- The corresponding identities for a future concrete globally continued R-function should
be derived from `rIntegral_firstQuadratic` and `rIntegral_secondQuadratic` by uniqueness of
continuation.  No Legendre, Chebyshev, Gegenbauer, or elliptic-integral specialization belongs
in this file. -/

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
