/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.SEqualParameter
public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.TwoVariable.RPolynomial.SpecialValues
public import Carlson.RPolynomial.PolygonSpecial

/-!
# S- and R-functions with three nodes in arithmetic progression (Exercises 6.9-5, 6.9-15)

For the nodes `x, y, (x + y)/2` the third node is the midpoint. After translating by the
midpoint it becomes `0`, so its parameter drops out of the R-polynomial numerators, and only the
even R-polynomials with opposite nodes survive (Theorem 6.9-1). The S-function (6.9-15) and the
R-function about the midpoint (6.9-5, via the Taylor expansion 6.3-1) are then hypergeometric
series `₁F₂` and `₃F₂`.

## Main results

* `Carlson.TwoVariable.hasSum_carlsonS_arithmetic`: Exercise 6.9-15.
* `Carlson.TwoVariable.hasSum_carlsonR_arithmetic`: Exercise 6.9-5.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- A zero node contributes only in degree zero: `Nₖ(β; 0) = δ_{k0}` for one node. -/
theorem carlsonRPolynomialNumerator_fin_one_zero (k : ℕ) (β : ℂ) :
    carlsonRPolynomialNumerator k (fun _ : Fin 1 => β) (fun _ => 0) = if k = 0 then 1 else 0 := by
  classical
  have h := carlsonRPolynomialNumerator_single k (0 : Fin 1) (fun _ => β) 0
  have h' : carlsonRPolynomialNumerator k (fun _ : Fin 1 => β) (fun _ => 0) =
      (ascPochhammer ℂ k).eval β * 0 ^ k := by
    convert h using 2
    funext i; simp
  rw [h']
  split_ifs with hk <;> simp [hk]

/-- Appending a zero node leaves the Pochhammer numerator unchanged. -/
theorem carlsonRPolynomialNumerator_sumElim_zero (n : ℕ) (b z : Fin 2 → ℂ) (β : ℂ) :
    carlsonRPolynomialNumerator n (Sum.elim b fun _ : Fin 1 => β) (Sum.elim z fun _ => 0) =
      carlsonRPolynomialNumerator n b z := by
  have h := carlsonRPolynomialNumerator_sumElim n b z (fun _ : Fin 1 => β) (fun _ => 0)
  rw [sum_eq_single n (fun m hm hmn => by
      rw [carlsonRPolynomialNumerator_fin_one_zero, ite_eq_right_iff.mpr (fun h => absurd h (by
        have := Nat.lt_succ_iff.mp (mem_range.mp hm); omega))]; simp)
    (fun h => absurd (mem_range.mpr (Nat.lt_succ_self n)) h),
    Nat.sub_self, carlsonRPolynomialNumerator_fin_one_zero] at h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [ite_true, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at h
  rwa [div_left_inj' hf] at h

/-- **Exercise 6.9-15**: if `2β + 2β'` is not a nonpositive integer, then
`S(β, β, 2β'; x, y, (x + y)/2) = e^{(x+y)/2} ₁F₂[β; β + β', β + β' + ½; ((x - y)/4)²]`, with
`₁F₂[a; c, d; t] = ∑ (a)ₖ tᵏ/((c)ₖ (d)ₖ k!)`. The three nodes are indexed by `Fin 2 ⊕ Fin 1`. -/
theorem hasSum_carlsonS_arithmetic {β β' : ℂ} (hc : ∀ m : ℕ, 2 * β + 2 * β' ≠ -m) (x y : ℂ) :
    HasSum (fun k : ℕ => exp ((x + y) / 2) * ((ascPochhammer ℂ k).eval β *
        (((x - y) / 4) ^ 2) ^ k / ((ascPochhammer ℂ k).eval (β + β') *
          (ascPochhammer ℂ k).eval (β + β' + 1 / 2) * k.factorial)))
      (carlsonS (Sum.elim (pair β β) fun _ : Fin 1 => 2 * β')
        (Sum.elim (pair x y) fun _ : Fin 1 => (x + y) / 2)) := by
  set w := (x - y) / 2
  set a := (x + y) / 2
  set c := 2 * β + 2 * β'
  set b : Fin 2 ⊕ Fin 1 → ℂ := Sum.elim (pair β β) fun _ => 2 * β'
  set z' : Fin 2 ⊕ Fin 1 → ℂ := Sum.elim (pair w (-w)) fun _ => 0
  have hz : (Sum.elim (pair x y) fun _ : Fin 1 => (x + y) / 2) = fun i => z' i + a := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [z', pair, w, a] <;> ring
    · simp [z', a]
  have hbsum : ∑ i, b i = c := by
    simp [b, Fintype.sum_sum_type, pair, c]; ring
  unfold carlsonS regCarlsonS
  rw [hz, regCarlsonSSeries_add_const, hbsum]
  have hser := hasSum_regCarlsonSSeries z' b
  have hterm : ∀ n : ℕ, (n.factorial : ℂ)⁻¹ * regCarlsonRPolynomial n b z' =
      (n.factorial : ℂ)⁻¹ * (carlsonRPolynomialNumerator₂ n β β w (-w) *
        (Gamma (c + n))⁻¹) := fun n => by
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hbsum,
      carlsonRPolynomialNumerator_sumElim_zero, carlsonRPolynomialNumerator_pair]
  simp_rw [hterm] at hser
  have hodd : ∀ m ∉ Set.range (fun n : ℕ => 2 * n),
      (m.factorial : ℂ)⁻¹ * (carlsonRPolynomialNumerator₂ m β β w (-w) *
        (Gamma (c + m))⁻¹) = 0 := by
    intro m hm
    have hmo : Odd m := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by show 2 * k = m; omega⟩ hm
      · exact h
    rw [carlsonRPolynomialNumerator₂_eq_zero_of_odd m hmo, zero_mul, mul_zero]
  have heven := (Function.Injective.hasSum_iff (fun a b h => by omega) hodd).mpr hser
  refine ((heven.mul_left (exp a)).mul_left (Gamma c)).congr_fun fun k => ?_
  simp only [Function.comp_apply]
  rw [numerator₂_even_opposite]
  -- Pochhammer and Gamma bookkeeping
  have hΓ : ∀ j : ℕ, Gamma (c + j) = (ascPochhammer ℂ j).eval c * Gamma c := fun j => by
    rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ (Gamma_ne_zero hc)]
  have hdouble := ascPochhammer_eval_double (β + β') k
  rw [show 2 * (β + β') = c by simp only [c]; ring] at hdouble
  have hfac := four_pow_mul_ascPochhammer_half k
  have hck : (ascPochhammer ℂ (2 * k)).eval c ≠ 0 := by
    intro h0
    have := hΓ (2 * k)
    rw [h0, zero_mul] at this
    exact Gamma_ne_zero
      (fun m hm => hc (m + 2 * k) (by push_cast at hm ⊢; linear_combination hm)) this
  have hp1 : (ascPochhammer ℂ k).eval (β + β') ≠ 0 := fun h0 => hck (by rw [hdouble, h0]; ring)
  have hp2 : (ascPochhammer ℂ k).eval (β + β' + 1 / 2) ≠ 0 :=
    fun h0 => hck (by rw [hdouble, h0]; ring)
  have hΓc := Gamma_ne_zero hc
  have hhalf : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) k
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [hΓ, hdouble, ← hfac]
  have hw : (((x - y) / 4) ^ 2) ^ k = w ^ (2 * k) / 4 ^ k := by
    rw [pow_mul, ← div_pow]; congr 1; simp only [w]; ring
  rw [hw]
  field_simp

/-- **Exercise 6.9-5**: for three nodes `x, y, (x + y)/2` in arithmetic progression with
parameters `β, β, δ`, if `2β + δ` is not a nonpositive integer and the nodes lie in a disk about
`(x + y)/2` inside the slit plane, then `R_t(β, β, δ; x, y, (x + y)/2) =
((x + y)/2)^t ₃F₂[-t/2, (1 - t)/2, β; β + δ/2, β + (δ + 1)/2; ((x - y)/(x + y))²]`.
The three nodes are indexed by `Fin 2 ⊕ Fin 1`. -/
theorem hasSum_carlsonR_arithmetic {β δ : ℂ} (hc : ∀ m : ℕ, 2 * β + δ ≠ -m) (t : ℂ) {x y : ℂ}
    {R : ℝ} (hball : Metric.ball ((x + y) / 2) R ⊆ slitPlane) (hxy : ‖(x - y) / 2‖ < R) :
    HasSum (fun m : ℕ => ((x + y) / 2) ^ t * ((ascPochhammer ℂ m).eval (-t / 2) *
        (ascPochhammer ℂ m).eval ((1 - t) / 2) * (ascPochhammer ℂ m).eval β *
          (((x - y) / (x + y)) ^ 2) ^ m / ((ascPochhammer ℂ m).eval (β + δ / 2) *
            (ascPochhammer ℂ m).eval (β + (δ + 1) / 2) * m.factorial)))
      (carlsonR t (Sum.elim (pair β β) fun _ : Fin 1 => δ)
        (Sum.elim (pair x y) fun _ : Fin 1 => (x + y) / 2)) := by
  set a := (x + y) / 2
  set w := (x - y) / 2
  set c := 2 * β + δ
  set b : Fin 2 ⊕ Fin 1 → ℂ := Sum.elim (pair β β) fun _ => δ
  set z : Fin 2 ⊕ Fin 1 → ℂ := Sum.elim (pair x y) fun _ => a
  have hR : 0 < R := (norm_nonneg w).trans_lt hxy
  have ha : a ∈ slitPlane := hball (Metric.mem_ball_self hR)
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have hz' : (fun i => z i - a) = Sum.elim (pair w (-w)) fun _ => 0 := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [z, pair, w, a] <;> ring
    · simp [z]
  have hnorm : ‖fun i => z i - a‖ < R := by
    rw [hz']
    refine (pi_norm_lt_iff hR).mpr fun i => ?_
    rcases i with i | i
    · fin_cases i <;> simpa [pair] using hxy
    · simpa using hR
  have hzball : Set.range z ⊆ Metric.ball a R := by
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact ((norm_le_pi_norm (fun i => z i - a) i).trans_lt hnorm)
  have hhull : convexHull ℝ (Set.range z) ⊆ slitPlane :=
    (convexHull_min hzball (convex_ball a R)).trans hball
  have hG := isRegCarlsonRContinuation_regCarlsonR_of_convexHull t hhull
  have hf : AnalyticOnNhd ℂ (fun u : ℂ => u ^ t) (Metric.ball a R) := fun u hu =>
    analyticAt_id.cpow analyticAt_const (hball hu)
  have h := hG.hasSum_taylor hf hnorm b
  have hbsum : ∑ i, b i = c := by
    simp [b, Fintype.sum_sum_type, pair, c]; ring
  have hterm : ∀ n : ℕ, iteratedDeriv n (fun u : ℂ => u ^ t) a / n.factorial *
      regCarlsonRPolynomial n b (fun i => z i - a) =
        (descPochhammer ℂ n).eval t * a ^ (t - n) / n.factorial *
          (carlsonRPolynomialNumerator₂ n β β w (-w) * (Gamma (c + n))⁻¹) := fun n => by
    rw [iteratedDeriv_cpow_const_of_mem_slitPlane _ _ ha,
      regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hbsum, hz',
      carlsonRPolynomialNumerator_sumElim_zero, carlsonRPolynomialNumerator_pair]
  simp_rw [hterm] at h
  have hodd : ∀ m ∉ Set.range (fun n : ℕ => 2 * n),
      (descPochhammer ℂ m).eval t * a ^ (t - m) / m.factorial *
        (carlsonRPolynomialNumerator₂ m β β w (-w) * (Gamma (c + m))⁻¹) = 0 := by
    intro m hm
    have hmo : Odd m := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by show 2 * k = m; omega⟩ hm
      · exact h
    rw [carlsonRPolynomialNumerator₂_eq_zero_of_odd m hmo, zero_mul, mul_zero]
  have heven := (Function.Injective.hasSum_iff (fun a b h => by omega) hodd).mpr h
  unfold carlsonR
  rw [hbsum]
  refine (heven.mul_left (Gamma c)).congr_fun fun k => ?_
  simp only [Function.comp_apply]
  rw [numerator₂_even_opposite]
  have hΓ : ∀ j : ℕ, Gamma (c + j) = (ascPochhammer ℂ j).eval c * Gamma c := fun j => by
    rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ (Gamma_ne_zero hc)]
  have hdouble := ascPochhammer_eval_double (β + δ / 2) k
  rw [show 2 * (β + δ / 2) = c by simp only [c]; ring,
    show β + δ / 2 + 1 / 2 = β + (δ + 1) / 2 by ring] at hdouble
  have hdesc : (descPochhammer ℂ (2 * k)).eval t =
      4 ^ k * (ascPochhammer ℂ k).eval (-t / 2) * (ascPochhammer ℂ k).eval ((1 - t) / 2) := by
    have h1 := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) t (2 * k)
    have h2 := ascPochhammer_eval_double (-t / 2) k
    rw [show 2 * (-t / 2) = -t by ring, show -t / 2 + 1 / 2 = (1 - t) / 2 by ring] at h2
    rw [h2, pow_mul] at h1
    norm_num at h1
    exact h1.symm
  have hfac := four_pow_mul_ascPochhammer_half k
  have hck : (ascPochhammer ℂ (2 * k)).eval c ≠ 0 := by
    intro h0
    have := hΓ (2 * k)
    rw [h0, zero_mul] at this
    exact Gamma_ne_zero
      (fun m hm => hc (m + 2 * k) (by push_cast at hm ⊢; linear_combination hm)) this
  have hp1 : (ascPochhammer ℂ k).eval (β + δ / 2) ≠ 0 := fun h0 => hck (by rw [hdouble, h0]; ring)
  have hp2 : (ascPochhammer ℂ k).eval (β + (δ + 1) / 2) ≠ 0 :=
    fun h0 => hck (by rw [hdouble, h0]; ring)
  have hΓc := Gamma_ne_zero hc
  have hhalf : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) k
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have ha2k : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha0
  rw [hΓ, hdouble, hdesc, ← hfac, show t - ((2 * k : ℕ) : ℂ) = t - ((2 * k : ℕ) : ℂ) from rfl,
    cpow_sub _ _ ha0, cpow_natCast]
  have hxy0 : x + y ≠ 0 := fun h0 => ha0 (by simp only [a, h0, zero_div])
  have hw : (((x - y) / (x + y)) ^ 2) ^ k = w ^ (2 * k) / a ^ (2 * k) := by
    rw [show (x - y) / (x + y) = w / a by simp only [w, a]; field_simp, ← pow_mul, div_pow]
  rw [hw]
  generalize Gamma c = G at hΓc ⊢
  field_simp

end Carlson.TwoVariable
