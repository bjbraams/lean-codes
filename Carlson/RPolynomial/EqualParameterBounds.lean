/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.SharpEstimates
public import Carlson.RPolynomial.SmallParameters
import Pochhammer.Vandermonde
public import ToMathlib.Analysis.SpecialFunctions.GammaBounds

/-!
# Estimates for R-polynomials with equal parameters (Exercises 6.2-10 – 6.2-12)

For `b = (β, …, β)` on `k` nodes, some multi-index entry is at least `s = ⌈n/k⌉`, and splitting
off `(β)ₛ` from that Pochhammer factor gives Carlson's bound
`|(kβ)ₙ Rₙ(b, z)| ≤ |(β)ₛ|/s! (k|β| + k)ₙ |z|ⁿ` (6.2-10). With the Gamma estimates
`|Γ(s)| ≤ Γ(re s)`, `Γ(x)/|Γ(x + iy)| ≤ e^{π|y|/2}` and the monotonicity of `Γ(x + r)/Γ(x)`, this
gives the explicit bound 6.2-12, and polynomial growth of its coefficients gives 6.2-11.

## Main results

* `Carlson.norm_carlsonRPolynomialNumerator_const_le`,
  `Carlson.norm_Gamma_mul_regCarlsonRPolynomial_const_le`: Exercise 6.2-10.
* `Carlson.eventually_norm_Gamma_mul_regCarlsonRPolynomial_const_le`: Exercise 6.2-11.
* `Carlson.norm_Gamma_mul_regCarlsonRPolynomial_const_le_exp`: Exercise 6.2-12.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.2.
-/

open Complex Finset Polynomial Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- Real Pochhammer symbols are monotone in a nonnegative argument. -/
theorem ascPochhammer_eval_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (ascPochhammer ℝ n).eval y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (by linarith) (add_nonneg hx (Nat.cast_nonneg n))
      (ascPochhammer_eval_nonneg_of_nonneg (hx.trans hxy) n)

/-- `(x)_{s+t} = (x)_s (x + s)_t`. -/
theorem ascPochhammer_eval_add {R : Type*} [CommSemiring R] (x : R) (s t : ℕ) :
    (ascPochhammer R (s + t)).eval x =
      (ascPochhammer R s).eval x * (ascPochhammer R t).eval (x + s) := by
  rw [← ascPochhammer_mul, eval_mul, eval_comp]
  simp

/-- For `s ≤ m`, `s! ‖(β)ₘ‖ ≤ ‖(β)ₛ‖ (‖β‖ + 1)ₘ`. -/
theorem norm_ascPochhammer_mul_factorial_le (β : ℂ) {s m : ℕ} (hsm : s ≤ m) :
    ‖(ascPochhammer ℂ m).eval β‖ * s.factorial ≤
      ‖(ascPochhammer ℂ s).eval β‖ * (ascPochhammer ℝ m).eval (‖β‖ + 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hsm
  have hb : 0 ≤ ‖β‖ := norm_nonneg β
  rw [ascPochhammer_eval_add, ascPochhammer_eval_add, norm_mul]
  have h1 : ‖(ascPochhammer ℂ t).eval (β + s)‖ ≤ (ascPochhammer ℝ t).eval (‖β‖ + s) :=
    norm_ascPochhammer_eval_le_ascPochhammer _ _ (by
      calc ‖β + s‖ ≤ ‖β‖ + ‖(s : ℂ)‖ := norm_add_le _ _
        _ = ‖β‖ + s := by rw [Complex.norm_natCast])
  have h2 : (s.factorial : ℝ) ≤ (ascPochhammer ℝ s).eval (‖β‖ + 1) := by
    rw [← ascPochhammer_eval_one]; exact ascPochhammer_eval_le_of_le zero_le_one (by linarith) s
  have h3 : (ascPochhammer ℝ t).eval (‖β‖ + s) ≤ (ascPochhammer ℝ t).eval (‖β‖ + 1 + s) :=
    ascPochhammer_eval_le_of_le (by positivity) (by linarith) t
  have h4 : 0 ≤ (ascPochhammer ℝ t).eval (‖β‖ + s) :=
    ascPochhammer_eval_nonneg_of_nonneg (by positivity) t
  calc ‖(ascPochhammer ℂ s).eval β‖ * ‖(ascPochhammer ℂ t).eval (β + s)‖ * s.factorial
      ≤ ‖(ascPochhammer ℂ s).eval β‖ * ((ascPochhammer ℝ t).eval (‖β‖ + s) * s.factorial) := by
        rw [mul_assoc]; gcongr
    _ ≤ ‖(ascPochhammer ℂ s).eval β‖ * ((ascPochhammer ℝ t).eval (‖β‖ + 1 + s) *
          (ascPochhammer ℝ s).eval (‖β‖ + 1)) := by
        gcongr
        exact ascPochhammer_eval_nonneg_of_nonneg (by positivity) t
    _ = _ := by ring

/-- If `∑ mᵢ = n` over `k` indices, some `mⱼ` is at least `s = ⌈n/k⌉`, written `(n + k - 1)/k`. -/
theorem exists_le_of_sum_eq [Nonempty ι] {m : ι → ℕ} {n : ℕ} (hm : ∑ i, m i = n) :
    ∃ j, (n + Fintype.card ι - 1) / Fintype.card ι ≤ m j := by
  set k := Fintype.card ι
  have hk : 0 < k := Fintype.card_pos
  set s := (n + k - 1) / k
  by_contra! h
  have hle : n ≤ k * (s - 1) := by
    rw [← hm]
    calc ∑ i, m i ≤ ∑ _i : ι, (s - 1) := sum_le_sum fun i _ => by have := h i; omega
      _ = k * (s - 1) := by simp [k]
  have hs : s * k ≤ n + k - 1 := Nat.div_mul_le_self _ _
  have hs0 : 1 ≤ s := by obtain ⟨j⟩ := ‹Nonempty ι›; have := h j; omega
  have hPk : k ≤ s * k := Nat.le_mul_of_pos_left k hs0
  rw [Nat.mul_sub_one, mul_comm] at hle
  generalize s * k = P at hle hs hPk
  omega

/-- **Exercise 6.2-10, first inequality**: for equal parameters `b = (β, …, β)` on `k` nodes,
`|(kβ)ₙ Rₙ(b, z)| ≤ |(β)ₛ|/s! (k|β| + k)ₙ |z|ⁿ` with `s - 1 = ⌊(n - 1)/k⌋`, i.e. `s = ⌈n/k⌉`,
in numerator form and with `|z| ≤ r` for every node. -/
theorem norm_carlsonRPolynomialNumerator_const_le [Nonempty ι] (n : ℕ) (β : ℂ) (z : ι → ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) :
    ‖carlsonRPolynomialNumerator n (fun _ => β) z‖ ≤
      ‖(ascPochhammer ℂ ((n + Fintype.card ι - 1) / Fintype.card ι)).eval β‖ /
          ((n + Fintype.card ι - 1) / Fintype.card ι).factorial *
        (ascPochhammer ℝ n).eval (Fintype.card ι * ‖β‖ + Fintype.card ι) * r ^ n := by
  classical
  set k := Fintype.card ι
  set s := (n + k - 1) / k
  set A := ‖(ascPochhammer ℂ s).eval β‖ / s.factorial
  have hsf : (0 : ℝ) < s.factorial := by exact_mod_cast s.factorial_pos
  have hA : 0 ≤ A := by positivity
  rw [carlsonRPolynomialNumerator_eq_sum_piAntidiag, carlsonGeneratingCoeff]
  have hkey : (k : ℝ) * ‖β‖ + k = ∑ _i : ι, (‖β‖ + 1) := by simp [k]
  rw [hkey, ascPochhammer_eval_sum, mul_sum, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
  have hsum : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
  obtain ⟨j, hj⟩ := exists_le_of_sum_eq hsum
  have hnodes : ‖∏ i, z i ^ m i‖ ≤ r ^ n := by
    rw [Complex.norm_prod]
    calc _ ≤ ∏ i, r ^ m i := prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _)
      _ = _ := by rw [prod_pow_eq_pow_sum, hsum]
  have hparams : ‖∏ i, (ascPochhammer ℂ (m i)).eval β‖ ≤
      A * ∏ i, (ascPochhammer ℝ (m i)).eval (‖β‖ + 1) := by
    rw [Complex.norm_prod, ← mul_prod_erase _ _ (mem_univ j),
      ← mul_prod_erase _ _ (mem_univ j)]
    have hj' := norm_ascPochhammer_mul_factorial_le β hj
    have hrest : ∏ i ∈ univ.erase j, ‖(ascPochhammer ℂ (m i)).eval β‖ ≤
        ∏ i ∈ univ.erase j, (ascPochhammer ℝ (m i)).eval (‖β‖ + 1) :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
        norm_ascPochhammer_eval_le_ascPochhammer _ _ (by linarith)
    have hnn : 0 ≤ ∏ i ∈ univ.erase j, ‖(ascPochhammer ℂ (m i)).eval β‖ :=
      prod_nonneg fun _ _ => norm_nonneg _
    have hj'' : ‖(ascPochhammer ℂ (m j)).eval β‖ ≤
        A * (ascPochhammer ℝ (m j)).eval (‖β‖ + 1) := by
      simp only [A]; rw [div_mul_eq_mul_div, le_div_iff₀ hsf]; exact hj'
    calc _ ≤ A * (ascPochhammer ℝ (m j)).eval (‖β‖ + 1) *
          ∏ i ∈ univ.erase j, (ascPochhammer ℝ (m i)).eval (‖β‖ + 1) :=
          mul_le_mul hj'' hrest hnn (mul_nonneg hA
            (ascPochhammer_eval_nonneg_of_nonneg (by positivity) _))
      _ = _ := by ring
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  calc _ ≤ (Nat.multinomial univ m : ℝ) * r ^ n *
        (A * ∏ i, (ascPochhammer ℝ (m i)).eval (‖β‖ + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnodes (by positivity)) hparams
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Exercise 6.2-10, second inequality**:
`|Γ(β) Rₙ(b, z)/Γ(kβ)| ≤ |Γ(β + s)| (k|β| + k)ₙ/(s! |Γ(kβ + n)|) |z|ⁿ`, stated for the
regularized polynomial `Rₙ(b, z)/Γ(kβ)`. At the poles of `Γ` both sides use Mathlib's
convention `Γ(-m) = 0`. -/
theorem norm_Gamma_mul_regCarlsonRPolynomial_const_le [Nonempty ι] (n : ℕ) (β : ℂ)
    (z : ι → ℂ) {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) :
    ‖Gamma β * regCarlsonRPolynomial n (fun _ => β) z‖ ≤
      ‖Gamma (β + ((n + Fintype.card ι - 1) / Fintype.card ι : ℕ))‖ *
          (ascPochhammer ℝ n).eval (Fintype.card ι * ‖β‖ + Fintype.card ι) /
        (((n + Fintype.card ι - 1) / Fintype.card ι).factorial *
          ‖Gamma (Fintype.card ι * β + n)‖) * r ^ n := by
  set k := Fintype.card ι
  set s := (n + k - 1) / k
  have hsf : (0 : ℝ) < s.factorial := by exact_mod_cast s.factorial_pos
  by_cases hβ : ∀ m : ℕ, β ≠ -m
  · have hG : Gamma (β + s) = Gamma β * (ascPochhammer ℂ s).eval β := by
      rw [← Gamma_add_nat_div_Gamma_eq β hβ, mul_div_cancel₀ _ (Gamma_ne_zero hβ)]
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
    have hsumβ : ∑ _i : ι, β = k * β := by simp [k]
    rw [hsumβ, hG, norm_mul, norm_mul, norm_mul, norm_inv]
    have hN := norm_carlsonRPolynomialNumerator_const_le n β z hr hz
    have hB := ascPochhammer_eval_nonneg_of_nonneg
      (by positivity : (0 : ℝ) ≤ k * ‖β‖ + k) n
    calc ‖Gamma β‖ * (‖carlsonRPolynomialNumerator n (fun _ => β) z‖ *
          ‖Gamma (k * β + n)‖⁻¹)
        ≤ ‖Gamma β‖ * ((‖(ascPochhammer ℂ s).eval β‖ / s.factorial *
          (ascPochhammer ℝ n).eval (k * ‖β‖ + k) * r ^ n) * ‖Gamma (k * β + n)‖⁻¹) := by
          gcongr
      _ = _ := by field_simp
  · push Not at hβ
    obtain ⟨m, hm⟩ := hβ
    rw [(Gamma_eq_zero_iff β).mpr ⟨m, hm⟩, zero_mul, norm_zero]
    have hB := ascPochhammer_eval_nonneg_of_nonneg
      (by positivity : (0 : ℝ) ≤ k * ‖β‖ + k) n
    positivity

/-- The integer `s = ⌈n/k⌉` of Exercise 6.2-10 lies between `n/k` and `(n - 1)/k + 1`. -/
theorem ceilDiv_bounds {n k : ℕ} (hk : 0 < k) :
    (n : ℝ) / k ≤ ((n + k - 1) / k : ℕ) ∧ (((n + k - 1) / k : ℕ) : ℝ) ≤ ((n : ℝ) - 1) / k + 1 ∨
      n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · right; rfl
  left
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set s := (n + k - 1) / k
  have h1 : s * k ≤ n + k - 1 := Nat.div_mul_le_self _ _
  have h2 : n + k - 1 < (s + 1) * k := by
    have : n + k - 1 < s * k + k := Nat.lt_div_mul_add hk
    rw [add_mul, one_mul]; exact this
  have h1' : (s : ℝ) * k ≤ n + k - 1 := by
    have : ((s * k : ℕ) : ℝ) ≤ ((n + k - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast [Nat.cast_sub (by omega : 1 ≤ n + k)] at this; linarith
  have h2' : (n : ℝ) + k - 1 < (s + 1) * k := by
    have : ((n + k - 1 : ℕ) : ℝ) < (((s + 1) * k : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast [Nat.cast_sub (by omega : 1 ≤ n + k)] at this; linarith
  constructor
  · rw [div_le_iff₀ hkR]
    have : (n : ℝ) ≤ s * k := by
      have h3 : n ≤ s * k := by
        by_contra h; push Not at h
        have : (s + 1) * k ≤ n + k - 1 := by rw [add_mul, one_mul]; omega
        omega
      exact_mod_cast h3
    linarith
  · rw [show ((n : ℝ) - 1) / k + 1 = ((n : ℝ) - 1 + k) / k by field_simp, le_div_iff₀ hkR]
    linarith

/-- **Exercise 6.2-12**: for equal parameters `b = (β, …, β)` on `k` nodes with `|zᵢ| ≤ ρ`, and
`|β| ≤ r ≤ (n - k - 1)/k`,
`|Γ(β) Rₙ(b, z)/Γ(kβ)| ≤ e^{πkr/2} ((n - 1)/k + 1, r) (kr + k)ₙ/Γ(n - kr) ρⁿ`, where
`(a, r) = Γ(a + r)/Γ(a)`. -/
theorem norm_Gamma_mul_regCarlsonRPolynomial_const_le_exp [Nonempty ι] (n : ℕ) (β : ℂ)
    (z : ι → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : ∀ i, ‖z i‖ ≤ ρ) {r : ℝ} (hβr : ‖β‖ ≤ r)
    (hrn : r ≤ ((n : ℝ) - Fintype.card ι - 1) / Fintype.card ι) :
    ‖Gamma β * regCarlsonRPolynomial n (fun _ => β) z‖ ≤
      Real.exp (Real.pi * Fintype.card ι * r / 2) *
        (Real.Gamma (((n : ℝ) - 1) / Fintype.card ι + 1 + r) /
          Real.Gamma (((n : ℝ) - 1) / Fintype.card ι + 1)) *
        (ascPochhammer ℝ n).eval (Fintype.card ι * r + Fintype.card ι) /
          Real.Gamma (n - Fintype.card ι * r) * ρ ^ n := by
  set k := Fintype.card ι
  have hk : 0 < k := Fintype.card_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := (norm_nonneg β).trans hβr
  have hnk : (k : ℝ) * r + k + 1 ≤ n := by
    have := (le_div_iff₀ hkR).mp hrn; linarith
  have hn1 : (1 : ℝ) ≤ n := by nlinarith
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn1
  set s := (n + k - 1) / k
  obtain ⟨hs1, hs2⟩ := (ceilDiv_bounds (n := n) hk).resolve_right hn0
  set a : ℝ := ((n : ℝ) - 1) / k + 1
  have hsr : r + 1 < s := by
    have : r + 1 + 1 / k ≤ (n : ℝ) / k := by
      rw [le_div_iff₀ hkR]; field_simp; nlinarith
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  have hs2' : (2 : ℝ) ≤ s := by
    have : (1 : ℝ) < s := by linarith
    have h : 1 < s := by exact_mod_cast this
    exact_mod_cast h
  have hsa : (s : ℝ) ≤ a := hs2
  -- the bound of Exercise 6.2-10
  have h10 := norm_Gamma_mul_regCarlsonRPolynomial_const_le n β z hρ hz
  -- (B1)-(B2): the Gamma factor at `β + s`
  have hre : 1 ≤ β.re + s := by
    have := neg_abs_le β.re
    have := abs_re_le_norm β
    linarith
  have hB1 : ‖Gamma (β + s)‖ ≤ Real.Gamma (r + s) := by
    refine (Complex.norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
    simp only [add_re, natCast_re]
    exact Real.Gamma_le_Gamma_of_one_le hre (by linarith [re_le_norm β]) (by linarith)
  have hsf : (s.factorial : ℝ) = Real.Gamma (s + 1) := by
    rw [Real.Gamma_nat_eq_factorial]
  have hGs : Real.Gamma s ≤ Real.Gamma (s + 1) := by
    rw [Real.Gamma_add_one (by positivity)]
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < s by linarith)
    nlinarith
  have hB2 : Real.Gamma (r + s) / s.factorial ≤ Real.Gamma (a + r) / Real.Gamma a := by
    rw [hsf]
    have hpos : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
    calc Real.Gamma (r + s) / Real.Gamma (s + 1) ≤ Real.Gamma (s + r) / Real.Gamma s := by
          rw [add_comm r]
          exact div_le_div_of_nonneg_left (Real.Gamma_pos_of_pos (by linarith)).le hpos hGs
      _ ≤ _ := Real.Gamma_add_div_Gamma_le (by linarith) hsa hr0
  -- (B3): the Pochhammer factor
  have hB3 : (ascPochhammer ℝ n).eval (k * ‖β‖ + k) ≤ (ascPochhammer ℝ n).eval (k * r + k) :=
    ascPochhammer_eval_le_of_le (by positivity) (by nlinarith) n
  -- (B4): the reciprocal Gamma factor at `kβ + n`
  set x : ℝ := k * β.re + n
  set y : ℝ := k * β.im
  have hxy : (k : ℂ) * β + n = x + y * I := by
    apply Complex.ext <;> simp [x, y]
  have hx1 : (n : ℝ) - k * r ≤ x := by
    have := neg_abs_le β.re; have := abs_re_le_norm β
    simp only [x]; nlinarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx2 : (2 : ℝ) ≤ n - k * r := by linarith
  have hy : |y| ≤ k * r := by
    simp only [y, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left ((abs_im_le_norm β).trans hβr) hkR.le
  have hB4 : (‖Gamma ((k : ℂ) * β + n)‖)⁻¹ ≤
      Real.exp (Real.pi * k * r / 2) / Real.Gamma (n - k * r) := by
    rw [hxy]
    have hG := Complex.Gamma_div_norm_Gamma_le_exp (x := x) (by linarith) y
    have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
    have hGn : 0 < Real.Gamma (n - k * r) := Real.Gamma_pos_of_pos (by linarith)
    have hmono : Real.Gamma (n - k * r) ≤ Real.Gamma x :=
      Real.Gamma_le_Gamma_of_one_le (by linarith) hx1 (by linarith)
    have hnorm : 0 < ‖Gamma (x + y * I)‖ :=
      norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by simp; linarith))
    have hexp : Real.exp (Real.pi * |y| / 2) ≤ Real.exp (Real.pi * k * r / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    rw [div_le_iff₀ hnorm] at hG
    have hc : Real.Gamma (n - k * r) ≤ Real.exp (Real.pi * k * r / 2) * ‖Gamma (x + y * I)‖ :=
      hmono.trans (hG.trans (by gcongr))
    rw [inv_le_iff_one_le_mul₀ hnorm, div_mul_eq_mul_div, le_div_iff₀ hGn, one_mul]
    exact hc
  -- assemble
  refine h10.trans ?_
  have hP0 : 0 ≤ (ascPochhammer ℝ n).eval (k * ‖β‖ + k) :=
    ascPochhammer_eval_nonneg_of_nonneg (by positivity) n
  have hGq : 0 ≤ Real.Gamma (a + r) / Real.Gamma a :=
    div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (Real.Gamma_pos_of_pos (by linarith)).le
  calc ‖Gamma (β + s)‖ * (ascPochhammer ℝ n).eval (k * ‖β‖ + k) /
          (s.factorial * ‖Gamma (k * β + n)‖) * ρ ^ n
      = (‖Gamma (β + s)‖ / s.factorial) * (ascPochhammer ℝ n).eval (k * ‖β‖ + k) *
          (‖Gamma (k * β + n)‖)⁻¹ * ρ ^ n := by
        rw [div_mul_eq_div_div, div_eq_mul_inv _ (‖Gamma _‖)]; ring
    _ ≤ (Real.Gamma (a + r) / Real.Gamma a) * (ascPochhammer ℝ n).eval (k * r + k) *
          (Real.exp (Real.pi * k * r / 2) / Real.Gamma (n - k * r)) * ρ ^ n := by
        have hB12 : ‖Gamma (β + s)‖ / s.factorial ≤ Real.Gamma (a + r) / Real.Gamma a :=
          (div_le_div_of_nonneg_right hB1 (by positivity)).trans hB2
        gcongr
        exact mul_nonneg hGq (ascPochhammer_eval_nonneg_of_nonneg (by positivity) n)
    _ = _ := by ring

/-- A polynomial bound for the right side of Exercise 6.2-12 with `r = |β|`: for
`k|β| + k + 1 ≤ n`, `|Γ(β) Rₙ(b, z)/Γ(kβ)| ≤ e^{πk|β|/2} (n + m)ᵐ (n + M)^(M + L) ρⁿ` with
`m = ⌈|β|⌉`, `M = ⌈k|β| + k⌉`, `L = ⌈k|β|⌉`. -/
theorem norm_Gamma_mul_regCarlsonRPolynomial_const_le_poly [Nonempty ι] (β : ℂ) (z : ι → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : ∀ i, ‖z i‖ ≤ ρ) {n : ℕ}
    (hn : (Fintype.card ι : ℝ) * ‖β‖ + Fintype.card ι + 1 ≤ n) :
    ‖Gamma β * regCarlsonRPolynomial n (fun _ => β) z‖ ≤
      Real.exp (Real.pi * Fintype.card ι * ‖β‖ / 2) * ((n : ℝ) + ⌈‖β‖⌉₊) ^ ⌈‖β‖⌉₊ *
        ((n : ℝ) + ⌈Fintype.card ι * ‖β‖ + Fintype.card ι⌉₊) ^
          (⌈Fintype.card ι * ‖β‖ + Fintype.card ι⌉₊ + ⌈Fintype.card ι * ‖β‖⌉₊) * ρ ^ n := by
  set k := Fintype.card ι
  set r := ‖β‖
  set m := ⌈r⌉₊
  set M := ⌈k * r + k⌉₊
  set L := ⌈(k : ℝ) * r⌉₊
  have hk : 0 < k := Fintype.card_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := norm_nonneg β
  have hrn : r ≤ ((n : ℝ) - k - 1) / k := by rw [le_div_iff₀ hkR]; linarith
  have h12 := norm_Gamma_mul_regCarlsonRPolynomial_const_le_exp n β z hρ hz le_rfl hrn
  refine h12.trans ?_
  set a : ℝ := ((n : ℝ) - 1) / k + 1
  have ha1 : 1 ≤ a := by
    have : 0 ≤ ((n : ℝ) - 1) / k := div_nonneg (by nlinarith) hkR.le
    linarith
  have han : a ≤ n := by
    have : ((n : ℝ) - 1) / k ≤ (n : ℝ) - 1 := div_le_self (by nlinarith) hk1
    linarith
  -- (a) the ratio `Γ(a + r)/Γ(a)`
  have hA : Real.Gamma (a + r) / Real.Gamma a ≤ ((n : ℝ) + m) ^ m := by
    have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos (by linarith)
    have h1 : Real.Gamma (a + r) ≤ Real.Gamma (a + m) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have : r = 0 := le_antisymm (Nat.ceil_eq_zero.mp hm) hr0
        rw [this, hm]; simp
      · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        exact Real.Gamma_le_Gamma_of_one_le (by linarith) (by linarith [Nat.le_ceil r])
          (by linarith)
    rw [div_le_iff₀ hGa]
    calc Real.Gamma (a + r) ≤ Real.Gamma (a + m) := h1
      _ = (ascPochhammer ℝ m).eval a * Real.Gamma a := Real.Gamma_add_nat_eq (by linarith) m
      _ ≤ (a + m) ^ m * Real.Gamma a := by
          gcongr; exact Real.ascPochhammer_eval_le_pow (by linarith) m
      _ ≤ ((n : ℝ) + m) ^ m * Real.Gamma a := by gcongr
  -- (b) the ratio `(kr + k)ₙ/Γ(n - kr)`
  have hM1 : (1 : ℝ) ≤ M := by
    have := Nat.le_ceil ((k : ℝ) * r + k); nlinarith
  have hL : (L : ℝ) < k * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLge : (k : ℝ) * r ≤ L := Nat.le_ceil _
  have hnL : (1 : ℝ) ≤ n - L := by linarith
  have hB : (ascPochhammer ℝ n).eval (k * r + k) / Real.Gamma (n - k * r) ≤
      ((n : ℝ) + M) ^ (M + L) := by
    have hGnk : 0 < Real.Gamma (n - k * r) := Real.Gamma_pos_of_pos (by linarith)
    have hGnL : 0 < Real.Gamma (n - L) := Real.Gamma_pos_of_pos (by linarith)
    have hGM : 1 ≤ Real.Gamma M := by
      obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := Nat.exists_eq_succ_of_ne_zero (by
        intro h0; rw [h0] at hM1; norm_num at hM1)
      rw [hM', Nat.cast_succ, Real.Gamma_nat_eq_factorial]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero M')
    have hP : (ascPochhammer ℝ n).eval (k * r + k) ≤ Real.Gamma (M + n) := by
      calc (ascPochhammer ℝ n).eval (k * r + k) ≤ (ascPochhammer ℝ n).eval (M : ℝ) :=
            ascPochhammer_eval_le_of_le (by positivity) (Nat.le_ceil _) n
        _ ≤ (ascPochhammer ℝ n).eval (M : ℝ) * Real.Gamma M := by
            have := ascPochhammer_eval_nonneg_of_nonneg (by positivity : (0 : ℝ) ≤ M) n
            nlinarith
        _ = Real.Gamma (M + n) := (Real.Gamma_add_nat_eq (by linarith) n).symm
    have hmono : Real.Gamma (n - L) ≤ Real.Gamma (n - k * r) :=
      Real.Gamma_le_Gamma_of_one_le hnL (by linarith) (by linarith)
    have hratio : Real.Gamma (M + n) = (ascPochhammer ℝ (M + L)).eval ((n : ℝ) - L) *
        Real.Gamma (n - L) := by
      rw [← Real.Gamma_add_nat_eq (by linarith)]; push_cast; ring_nf
    rw [div_le_iff₀ hGnk]
    calc (ascPochhammer ℝ n).eval (k * r + k) ≤ Real.Gamma (M + n) := hP
      _ = (ascPochhammer ℝ (M + L)).eval ((n : ℝ) - L) * Real.Gamma (n - L) := hratio
      _ ≤ ((n : ℝ) - L + (M + L : ℕ)) ^ (M + L) * Real.Gamma (n - L) := by
          gcongr; exact Real.ascPochhammer_eval_le_pow (by linarith) _
      _ = ((n : ℝ) + M) ^ (M + L) * Real.Gamma (n - L) := by push_cast; ring_nf
      _ ≤ ((n : ℝ) + M) ^ (M + L) * Real.Gamma (n - k * r) := by gcongr
  have hE : 0 ≤ Real.exp (Real.pi * k * r / 2) := (Real.exp_pos _).le
  calc Real.exp (Real.pi * k * r / 2) * (Real.Gamma (a + r) / Real.Gamma a) *
        (ascPochhammer ℝ n).eval (k * r + k) / Real.Gamma (n - k * r) * ρ ^ n
      = Real.exp (Real.pi * k * r / 2) * (Real.Gamma (a + r) / Real.Gamma a) *
        ((ascPochhammer ℝ n).eval (k * r + k) / Real.Gamma (n - k * r)) * ρ ^ n := by ring
    _ ≤ Real.exp (Real.pi * k * r / 2) * ((n : ℝ) + m) ^ m * ((n : ℝ) + M) ^ (M + L) *
          ρ ^ n := by
        have hA0 : 0 ≤ Real.Gamma (a + r) / Real.Gamma a :=
          div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
            (Real.Gamma_pos_of_pos (by linarith)).le
        gcongr
        exact div_nonneg (ascPochhammer_eval_nonneg_of_nonneg (by positivity) n)
          (Real.Gamma_pos_of_pos (by linarith)).le

/-- **Exercise 6.2-11**: for equal parameters `b = (β, …, β)` on `k` nodes with `|zᵢ| ≤ ρ`,
`lim sup |Γ(β) Rₙ(b, z)/Γ(kβ)|^{1/n} ≤ ρ`, stated as: for every `ε > 0`, eventually
`|Γ(β) Rₙ(b, z)/Γ(kβ)| ≤ (ρ + ε)ⁿ`. -/
theorem eventually_norm_Gamma_mul_regCarlsonRPolynomial_const_le [Nonempty ι] (β : ℂ)
    (z : ι → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : ∀ i, ‖z i‖ ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖Gamma β * regCarlsonRPolynomial n (fun _ => β) z‖ ≤ (ρ + ε) ^ n := by
  set k := Fintype.card ι
  set E := Real.exp (Real.pi * k * ‖β‖ / 2)
  set m := ⌈‖β‖⌉₊
  set M := ⌈(k : ℝ) * ‖β‖ + k⌉₊
  set L := ⌈(k : ℝ) * ‖β‖⌉₊
  set D := m + M
  set K := m + (M + L)
  have hE : 0 < E := Real.exp_pos _
  have hpoly : ∀ᶠ n : ℕ in atTop, ‖Gamma β * regCarlsonRPolynomial n (fun _ => β) z‖ ≤
      E * (2 ^ K * (n : ℝ) ^ K) * ρ ^ n := by
    filter_upwards [eventually_ge_atTop ⌈(k : ℝ) * ‖β‖ + k + 1⌉₊, eventually_ge_atTop D,
      eventually_ge_atTop 1] with n hn hnD hn1
    have hn' : (k : ℝ) * ‖β‖ + k + 1 ≤ n := (Nat.ceil_le).mp hn
    refine (norm_Gamma_mul_regCarlsonRPolynomial_const_le_poly β z hρ hz hn').trans ?_
    have hnD' : (D : ℝ) ≤ n := by exact_mod_cast hnD
    have h1 : ((n : ℝ) + m) ^ m ≤ (2 * n) ^ m :=
      pow_le_pow_left₀ (by positivity) (by simp only [D] at hnD'; push_cast at hnD'; linarith) _
    have h2 : ((n : ℝ) + M) ^ (M + L) ≤ (2 * n) ^ (M + L) :=
      pow_le_pow_left₀ (by positivity) (by simp only [D] at hnD'; push_cast at hnD'; linarith) _
    calc E * ((n : ℝ) + m) ^ m * ((n : ℝ) + M) ^ (M + L) * ρ ^ n
        ≤ E * (2 * n) ^ m * (2 * n) ^ (M + L) * ρ ^ n := by gcongr
      _ = E * (2 ^ K * (n : ℝ) ^ K) * ρ ^ n := by
          simp only [K]; rw [pow_add, mul_pow, mul_pow, mul_pow]; ring
  rcases hρ.eq_or_lt with hρ0 | hρ0
  · filter_upwards [hpoly, eventually_ge_atTop 1] with n hn hn1
    rw [← hρ0, zero_pow (by omega), mul_zero] at hn
    rw [← hρ0, zero_add]
    exact hn.trans (pow_nonneg hε.le n)
  · set q := (ρ + ε) / ρ
    have hq : 1 < q := by rw [lt_div_iff₀ hρ0]; linarith
    have hlim := tendsto_pow_const_div_const_pow_of_one_lt K hq
    have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < (E * 2 ^ K)⁻¹ by positivity))
    filter_upwards [hpoly, hev] with n hn hq'
    refine hn.trans ?_
    have hqn : 0 < q ^ n := pow_pos (by linarith) n
    rw [div_lt_iff₀ hqn] at hq'
    have hρq : (ρ + ε) ^ n = q ^ n * ρ ^ n := by
      simp only [q]; rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ0.ne')]
    rw [hρq]
    have hρn : 0 < ρ ^ n := pow_pos hρ0 n
    have : E * (2 ^ K * (n : ℝ) ^ K) ≤ q ^ n := by
      have h := mul_lt_mul_of_pos_left hq' (show 0 < E * 2 ^ K by positivity)
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h
      linarith
    nlinarith

end Carlson
