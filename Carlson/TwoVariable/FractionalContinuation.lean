/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.FractionalIntegral
public import Carlson.TwoVariable.RPolynomial
public import Carlson.RPolynomial.TaylorContinuation
public import Dirichlet.Average.JointContinuation
public import Mathlib.Analysis.Complex.TaylorSeries
public import ToMathlib.Analysis.Calculus.IteratedDerivOpen

/-!
# Continuation of Carlson's fractional integral

Carlson defines `I^ν f(x) = (x - a)^ν F(1, ν; x, a)/Γ(1 + ν)` (5.5-14) and states that it
continues analytically to all `ν`, with `I^{-n} f = f⁽ⁿ⁾` (5.5-16); case (ii) is Exercise 6.3-3,
and for case (i) he refers to M. Riesz (1949).

Case (ii), `f` holomorphic on a convex open set: the continuation is `(x - a)^ν` times the
entire continuation of the regularized average. The value at `ν = -n` is computed on a Taylor
disk from the closed form `R_m(1, -n; X, Y)/Γ(m + 1 - n) = m!/(m - n)! X^(m-n) (X - Y)^n`, and
extended to the whole convex set by joint holomorphy in the nodes and the identity theorem. No
contour is used.

Case (i), `g ∈ Cⁿ` on a real interval: integration by parts in the Riemann–Liouville integral
gives `I^ν g = g(a)(x - a)^ν/Γ(ν + 1) + I^(ν+1) g'`, and iterating continues `I^ν g` to
`re ν > -n`.

## Main results

* `Carlson.TwoVariable.regRPolynomial_one_neg_nat`: the closed form above (Exercise 6.2-9).
* `Dirichlet.IsRegCarlsonContinuation.pair_one_neg_nat`: `F(1, -n; x, a)/Γ(1 - n) =
  (x - a)ⁿ f⁽ⁿ⁾(x)` for continued averages on a convex domain.
* `Carlson.TwoVariable.exists_fractionalIntegral_continuation`: case (ii), an entire continuation
  of `I^ν f(x)` with `I^{-n} f(x) = f⁽ⁿ⁾(x)`.
* `Carlson.TwoVariable.rlIntegral_eq_add`: Riesz's integration by parts.
* `Carlson.TwoVariable.exists_real_fractionalIntegral_continuation`: case (i), continuation to
  `re ν > -n` with `I^{-m} g(x) = g⁽ᵐ⁾(x)` for `m < n`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.5, §6.3.
* M. Riesz, *L'intégrale de Riemann–Liouville et le problème de Cauchy*, Acta Math. 81 (1949).
-/

open Dirichlet
open Complex Finset
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The Pochhammer numerator with parameters `(1, -n)` in degree `n + k`:
`N_{n+k}(1, -n; X, Y) = (n + k)! X^k (X - Y)^n`. -/
theorem carlsonRPolynomialNumerator₂_one_neg_nat (n k : ℕ) (X Y : ℂ) :
    carlsonRPolynomialNumerator₂ (n + k) 1 (-(n : ℂ)) X Y =
      ((n + k).factorial : ℂ) * X ^ k * (X - Y) ^ n := by
  set N := n + k
  rw [carlsonRPolynomialNumerator₂, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (N.choose i : ℂ) * (ascPochhammer ℂ i).eval 1 *
      (ascPochhammer ℂ j).eval (-(n : ℂ)) * X ^ i * Y ^ j) N]
  rw [← sum_range_reflect]
  have hterm : ∀ j ∈ range (N + 1),
      (N.choose (N + 1 - 1 - j) : ℂ) * (ascPochhammer ℂ (N + 1 - 1 - j)).eval 1 *
        (ascPochhammer ℂ (N - (N + 1 - 1 - j))).eval (-(n : ℂ)) * X ^ (N + 1 - 1 - j) *
          Y ^ (N - (N + 1 - 1 - j)) =
      (N.factorial : ℂ) * ((-1) ^ j * (n.choose j : ℂ)) * X ^ (N - j) * Y ^ j := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [show N + 1 - 1 - j = N - j by omega, show N - (N - j) = j by omega,
      ascPochhammer_eval_one, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le N j)
    rw [Nat.choose_symm hjN, Nat.sub_sub_self hjN] at h
    have h' : ((N.choose j : ℕ) : ℂ) * ((N - j).factorial : ℂ) * (j.factorial : ℂ) =
        (N.factorial : ℂ) := by exact_mod_cast h
    rw [Nat.choose_symm hjN]
    push_cast
    linear_combination ((-1) ^ j * (n.choose j : ℂ) * X ^ (N - j) * Y ^ j) * h'
  rw [sum_congr rfl hterm]
  have hsub : range (n + 1) ⊆ range (N + 1) := range_subset_range.mpr (by omega)
  rw [← sum_subset hsub fun j _ hj => by
    rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp]
  rw [show X - Y = -Y + X by ring, add_pow, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show N - j = k + (n - j) by omega, pow_add, neg_pow]
  ring

/-- The regularized two-node R-polynomial with parameters `(1, -n)`:
`R_m(1, -n; X, Y)/Γ(m + 1 - n) = m!/(m-n)! X^(m-n) (X - Y)^n` for `m ≥ n`, and `0` for `m < n`
(compare Exercise 6.2-9). -/
theorem regRPolynomial_one_neg_nat (n m : ℕ) (X Y : ℂ) :
    regRPolynomial m 1 (-(n : ℂ)) X Y =
      if n ≤ m then (m.factorial : ℂ) / ((m - n).factorial : ℂ) * X ^ (m - n) * (X - Y) ^ n
      else 0 := by
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [carlsonRPolynomialNumerator₂_one_neg_nat, Nat.add_sub_cancel_left,
      show (1 : ℂ) + -(n : ℂ) + ((n + k : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  · rw [show (1 : ℂ) + -(n : ℂ) + (m : ℂ) = -((n - m - 1 : ℕ) : ℂ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring,
      Gamma_neg_nat_eq_zero, inv_zero, mul_zero]

/-- The two-node vector `(x, a)` shifted by a center. -/
theorem pair_sub_const (x a A : ℂ) : (fun i => pair x a i - A) = pair (x - A) (a - A) := by
  funext i; fin_cases i <;> rfl

/-- **(5.5-16) on a disk.** If `f` is holomorphic on a disk containing `x` and `a`, the continued
average satisfies `F(1, -n; x, a)/Γ(1 - n) = (x - a)ⁿ f⁽ⁿ⁾(x)`. -/
theorem _root_.Dirichlet.IsRegCarlsonContinuation.pair_one_neg_nat_of_ball {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R)) {x a : ℂ} (hx : ‖x - A‖ < R)
    (ha : ‖a - A‖ < R) {G : (Fin 2 → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f (pair x a) G)
    (n : ℕ) : G (pair 1 (-(n : ℂ))) = (x - a) ^ n * iteratedDeriv n f x := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hx
  have hz : ‖fun i => pair x a i - A‖ < R := by
    rw [pair_sub_const]
    refine (pi_norm_lt_iff hR).mpr fun i => ?_
    fin_cases i
    · exact hx
    · exact ha
  have hs := hG.hasSum_taylor hf hz (pair 1 (-(n : ℂ)))
  rw [pair_sub_const] at hs
  -- Taylor series of `f⁽ⁿ⁾` about `A`.
  have hg : DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball A R) := by
    rw [iteratedDeriv_eq_iterate]; exact (hf.iterated_deriv n).differentiableOn
  have ht := Complex.hasSum_taylorSeries_on_ball hg (by simpa [dist_eq_norm] using hx)
  have hshift : ∀ k, iteratedDeriv k (iteratedDeriv n f) A = iteratedDeriv (k + n) f A := by
    intro k
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
  set term : ℕ → ℂ := fun m => iteratedDeriv m f A / (m.factorial : ℂ) *
    regCarlsonRPolynomial m (pair 1 (-(n : ℂ))) (pair (x - A) (a - A))
  have h2 : HasSum (fun k => term (k + n)) ((x - a) ^ n * iteratedDeriv n f x) := by
    refine (ht.mul_left ((x - a) ^ n)).congr_fun fun k => ?_
    simp only [term]
    rw [show regCarlsonRPolynomial (k + n) (pair 1 (-(n : ℂ))) (pair (x - A) (a - A)) =
      regRPolynomial (k + n) 1 (-(n : ℂ)) (x - A) (a - A) from rfl]
    rw [regRPolynomial_one_neg_nat, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      Nat.add_sub_cancel, hshift]
    have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : ((k + n).factorial : ℂ) ≠ 0 := by exact_mod_cast (k + n).factorial_ne_zero
    simp only [smul_eq_mul]
    field_simp
    ring
  have hzero : ∑ i ∈ range n, term i = 0 := sum_eq_zero fun i hi => by
    simp only [term]
    rw [show regCarlsonRPolynomial i (pair 1 (-(n : ℂ))) (pair (x - A) (a - A)) =
      regRPolynomial i 1 (-(n : ℂ)) (x - A) (a - A) from rfl]
    rw [regRPolynomial_one_neg_nat, ite_eq_right_of_eq_false _ _ (eq_false (by simp at hi; omega)),
      mul_zero]
  have h3 : HasSum term ((x - a) ^ n * iteratedDeriv n f x) :=
    (hasSum_nat_add_iff' n).mp (by rw [hzero, sub_zero]; exact h2)
  exact hs.unique h3

/-- **(5.5-16) and Exercise 6.3-3.** If `f` is holomorphic on a convex open set `Ω` containing
`x` and `a`, the entire continuation of `F(1, ν; x, a)/Γ(1 + ν)` takes the value
`(x - a)ⁿ f⁽ⁿ⁾(x)` at `ν = -n`. No disk containing both nodes is needed. -/
theorem _root_.Dirichlet.IsRegCarlsonContinuation.pair_one_neg_nat {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {x a : ℂ} (hx : x ∈ Ω) (ha : a ∈ Ω) {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (pair x a) G) (n : ℕ) :
    G (pair 1 (-(n : ℂ))) = (x - a) ^ n * iteratedDeriv n f x := by
  obtain ⟨J, hJ, hJc⟩ := exists_joint_isRegCarlsonContinuation hΩopen hΩconv hf (ι := Fin 2)
  have hrange : ∀ p q : ℂ, p ∈ Ω → q ∈ Ω → Set.range (pair p q) ⊆ Ω := by
    rintro p q hp hq _ ⟨i, rfl⟩
    fin_cases i
    · exact hp
    · exact hq
  have hGJ : G = fun b => J (b, pair x a) := (hG.eq (hJc _ (hrange x a hx ha)))
  set U : Set (ℂ × ℂ) := Ω ×ˢ Ω
  have hUo : IsOpen U := hΩopen.prod hΩopen
  have hUc : IsPreconnected U := (hΩconv.prod hΩconv).isPreconnected
  set Φ : ℂ × ℂ → ℂ := fun p => J (pair 1 (-(n : ℂ)), pair p.1 p.2)
  set Ψ : ℂ × ℂ → ℂ := fun p => (p.1 - p.2) ^ n * iteratedDeriv n f p.1
  have hΦ : AnalyticOnNhd ℂ Φ U := by
    intro p hp
    have hin : AnalyticAt ℂ (fun p : ℂ × ℂ => ((pair 1 (-(n : ℂ)) : Fin 2 → ℂ), pair p.1 p.2))
        p := by
      refine analyticAt_const.prod (AnalyticAt.pi fun i => ?_)
      fin_cases i
      · exact analyticAt_fst
      · exact analyticAt_snd
    exact (hJ _ (hrange _ _ hp.1 hp.2)).comp hin
  have hΨ : AnalyticOnNhd ℂ Ψ U := by
    intro p hp
    have hd : AnalyticAt ℂ (iteratedDeriv n f) p.1 := by
      rw [iteratedDeriv_eq_iterate]; exact hf.iterated_deriv n _ hp.1
    exact ((analyticAt_fst.sub analyticAt_snd).pow n).mul (hd.comp analyticAt_fst)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩopen a ha
  have hloc : Φ =ᶠ[nhds (a, a)] Ψ := by
    filter_upwards [Metric.ball_mem_nhds (a, a) hr] with p hp
    rw [Metric.mem_ball, Prod.dist_eq] at hp
    have h1 : ‖p.1 - a‖ < r := by
      rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) hp
    have h2 : ‖p.2 - a‖ < r := by
      rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_right _ _) hp
    have hp1 : p.1 ∈ Ω := hball (by simpa [dist_eq_norm] using h1)
    have hp2 : p.2 ∈ Ω := hball (by simpa [dist_eq_norm] using h2)
    exact (hJc _ (hrange _ _ hp1 hp2)).pair_one_neg_nat_of_ball
      (hf.mono hball) h1 h2 n
  have := hΦ.eqOn_of_preconnected_of_eventuallyEq hΨ hUc ⟨ha, ha⟩ hloc
    (show (x, a) ∈ U from ⟨hx, ha⟩)
  rw [hGJ]
  exact this

/-- The fractional integral `I^ν f(x) = (x - a)^ν F(1, ν; x, a)/Γ(1 + ν)` built from a continued
regularized average `G` of `f` at the nodes `(x, a)`. -/
def continuedFractionalIntegral (G : (Fin 2 → ℂ) → ℂ) (a x ν : ℂ) : ℂ :=
  (x - a) ^ ν * G (pair 1 ν)

/-- The continued fractional integral is entire in its order when `x ≠ a`. -/
theorem differentiable_continuedFractionalIntegral {f : ℂ → ℂ} {a x : ℂ} (hxa : x ≠ a)
    {G : (Fin 2 → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f (pair x a) G) :
    Differentiable ℂ (continuedFractionalIntegral G a x) := by
  intro ν
  have hpow : DifferentiableAt ℂ (fun ν : ℂ => (x - a) ^ ν) ν :=
    (hasStrictDerivAt_const_cpow (y := ν)
      (Or.inl (sub_ne_zero.mpr hxa))).hasDerivAt.differentiableAt
  have hpair : DifferentiableAt ℂ (fun ν : ℂ => (pair 1 ν : Fin 2 → ℂ)) ν := by
    refine differentiableAt_pi.mpr fun i => ?_
    fin_cases i
    · exact differentiableAt_const _
    · exact differentiableAt_id
  exact hpow.mul ((hG.analyticOnNhd _ (Set.mem_univ _)).differentiableAt.comp ν hpair)

/-- On `re ν > 0` the continued fractional integral is Carlson's (5.5-14), hence for real
`a < x` the Riemann–Liouville integral (5.5-15) by `carlsonFractionalIntegral_eq_integral`. -/
theorem continuedFractionalIntegral_eq {f : ℂ → ℂ} {a x : ℂ} {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (pair x a) G) {ν : ℂ} (hν : 0 < ν.re) :
    continuedFractionalIntegral G a x ν = carlsonFractionalIntegral ν a x f := by
  have hb : pair 1 ν ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · simp [pair]
    · simpa [pair] using hν
  rw [continuedFractionalIntegral, carlsonFractionalIntegral, hG.eq_native hb]

/-- **(5.5-16)**: at negative integer order the continued fractional integral is a derivative,
`I^{-n} f(x) = f⁽ⁿ⁾(x)`, for `f` holomorphic on a convex open set containing `a ≠ x`. -/
theorem continuedFractionalIntegral_neg_nat {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {x a : ℂ} (hx : x ∈ Ω)
    (ha : a ∈ Ω) (hxa : x ≠ a) {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (pair x a) G) (n : ℕ) :
    continuedFractionalIntegral G a x (-(n : ℂ)) = iteratedDeriv n f x := by
  rw [continuedFractionalIntegral, hG.pair_one_neg_nat hΩopen hΩconv hf hx ha n, cpow_neg,
    cpow_natCast, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (sub_ne_zero.mpr hxa)), one_mul]

/-- **Carlson's fractional integral continued in its order** (Section 5.5 and Exercise 6.3-3):
for `f` holomorphic on a convex open set containing `a ≠ x`, there is an entire function of `ν`
equal to `I^ν f(x)` (5.5-14) for `re ν > 0` and to `f⁽ⁿ⁾(x)` at `ν = -n` (5.5-16). It is unique,
being entire and determined on a half-plane. -/
theorem exists_fractionalIntegral_continuation {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {x a : ℂ} (hx : x ∈ Ω)
    (ha : a ∈ Ω) (hxa : x ≠ a) :
    ∃ J : ℂ → ℂ, Differentiable ℂ J ∧
      (∀ ν : ℂ, 0 < ν.re → J ν = carlsonFractionalIntegral ν a x f) ∧
      ∀ n : ℕ, J (-(n : ℂ)) = iteratedDeriv n f x := by
  have hrange : Set.range (pair x a) ⊆ Ω := by
    rintro _ ⟨i, rfl⟩; fin_cases i
    · exact hx
    · exact ha
  obtain ⟨G, hG⟩ := exists_isRegCarlsonContinuation hΩopen hΩconv hf hrange
  exact ⟨_, differentiable_continuedFractionalIntegral hxa hG,
    fun ν hν => continuedFractionalIntegral_eq hG hν,
    continuedFractionalIntegral_neg_nat hΩopen hΩconv hf hx ha hxa hG⟩

/-! ### Real case: Riesz's continuation -/

/-- The Riemann–Liouville fractional integral `Γ(ν)⁻¹ ∫ₐˣ g(t) (x - t)^(ν-1) dt` of a function on
the real line. -/
def rlIntegral (g : ℝ → ℂ) (a x : ℝ) (ν : ℂ) : ℂ :=
  (Gamma ν)⁻¹ * ∫ t in a..x, g t * ((x - t : ℝ) : ℂ) ^ (ν - 1)

/-- **Riesz's integration by parts**: for `re ν > 0` and `g` continuously differentiable on
`[a, x]`, `I^ν g(x) = g(a) (x - a)^ν / Γ(ν + 1) + I^(ν+1) g'(x)`. -/
theorem rlIntegral_eq_add {g g' : ℝ → ℂ} {a x : ℝ} (hax : a ≤ x)
    (hg : ∀ t ∈ Set.Icc a x, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Set.Icc a x))
    {ν : ℂ} (hν : 0 < ν.re) :
    rlIntegral g a x ν = g a * ((x - a : ℝ) : ℂ) ^ ν * (Gamma (ν + 1))⁻¹ +
      rlIntegral g' a x (ν + 1) := by
  have hν0 : ν ≠ 0 := fun h => by simp [h] at hν
  set v : ℝ → ℂ := fun t => -((x - t : ℝ) : ℂ) ^ ν / ν
  set v' : ℝ → ℂ := fun t => ((x - t : ℝ) : ℂ) ^ (ν - 1)
  have hu : ContinuousOn g (Set.uIcc a x) := by
    rw [Set.uIcc_of_le hax]; exact fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Set.uIcc a x) := by
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    refine ContinuousAt.continuousWithinAt ?_
    have hc : ContinuousAt (fun s : ℝ => ((x - s : ℝ) : ℂ)) t := by fun_prop
    have hp := continuousAt_cpow_const_of_re_pos (z := ((x - t : ℝ) : ℂ)) (w := ν)
      (Or.inl (by simp; linarith [ht.2])) hν
    exact ((hp.comp (f := fun s : ℝ => ((x - s : ℝ) : ℂ)) hc).neg).div_const ν
  have huu : ∀ t ∈ Set.Ioo (min a x) (max a x), HasDerivAt g (g' t) t := by
    intro t ht
    rw [min_eq_left hax, max_eq_right hax] at ht
    exact hg t (Set.Ioo_subset_Icc_self ht)
  have hvv : ∀ t ∈ Set.Ioo (min a x) (max a x), HasDerivAt v (v' t) t := by
    intro t ht
    rw [min_eq_left hax, max_eq_right hax] at ht
    have hpos : 0 < x - t := by linarith [ht.2]
    have hc : HasDerivAt (fun w : ℂ => w ^ ν) (ν * ((x - t : ℝ) : ℂ) ^ (ν - 1))
        ((x - t : ℝ) : ℂ) := by
      simpa using (hasDerivAt_id ((x - t : ℝ) : ℂ)).cpow_const
        (Or.inl (by simpa using hpos) : ((x - t : ℝ) : ℂ) ∈ Complex.slitPlane)
    have hc' := (hc.comp_ofReal (z := x - t)).scomp t ((hasDerivAt_id t).const_sub x)
    have := (hc'.neg).div_const ν
    convert this using 1
    · funext s; simp [v, Function.comp_def]
    · simp only [v']; field_simp; simp
  have hu' : IntervalIntegrable g' MeasureTheory.volume a x :=
    (hg'.mono (by rw [Set.uIcc_of_le hax])).intervalIntegrable
  have hv' : IntervalIntegrable v' MeasureTheory.volume a x := by
    have h0 : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ (ν - 1)) MeasureTheory.volume 0 (x - a) :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have := (h0.comp_sub_left x).symm
    simpa [v'] using this
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv huu hvv hu' hv'
  have hvx : v x = 0 := by simp [v, zero_cpow hν0]
  have hint : ∫ t in a..x, g' t * v t =
      -ν⁻¹ * ∫ t in a..x, g' t * ((x - t : ℝ) : ℂ) ^ (ν + 1 - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [v, add_sub_cancel_right]
    field_simp
  rw [rlIntegral, rlIntegral, H, hvx, hint, Gamma_add_one ν hν0]
  simp only [v]
  have hG : Gamma ν ≠ 0 := Gamma_ne_zero_of_re_pos hν
  field_simp
  ring

/-- For real `a < x`, the Riemann–Liouville integral is Carlson's fractional integral (5.5-14) of
the function `w ↦ g(re w)`. -/
theorem rlIntegral_eq_carlsonFractionalIntegral {a x : ℝ} (hax : a < x) (g : ℝ → ℂ) (ν : ℂ) :
    rlIntegral g a x ν = carlsonFractionalIntegral ν a x (fun w => g w.re) := by
  rw [carlsonFractionalIntegral_eq_integral ν hax, rlIntegral]
  simp

/-- The Riemann–Liouville integral of a continuous function is holomorphic in its order on
`re ν > 0`. -/
theorem differentiableOn_rlIntegral {a x : ℝ} (hax : a < x) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc a x)) :
    DifferentiableOn ℂ (rlIntegral g a x) {ν | 0 < ν.re} := by
  set K : (Fin 2 → ℝ) → ℂ := fun u => g (carlsonAffineForm (pair (x : ℂ) (a : ℂ)) u).re
  have hre : ∀ u : Fin 2 → ℝ, (carlsonAffineForm (pair (x : ℂ) (a : ℂ)) u).re =
      u 0 * x + u 1 * a := fun u => by simp [carlsonAffineForm, Fin.sum_univ_two, pair]
  have hK : ContinuousOn K (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
    refine hg.comp (by simp_rw [hre]; fun_prop) fun u hu => ?_
    show _ ∈ Set.Icc a x
    rw [hre]
    have h0 := hu.1 0
    have h1 := hu.1 1
    have hs : u 0 + u 1 = 1 := by simpa [Fin.sum_univ_two] using hu.2
    have p0 := mul_nonneg h0 (sub_nonneg.mpr hax.le)
    have p1 := mul_nonneg h1 (sub_nonneg.mpr hax.le)
    constructor
    · have e : u 0 * x + u 1 * a = a + u 0 * (x - a) := by
        rw [show u 1 = 1 - u 0 by linarith]; ring
      linarith
    · have e : u 0 * x + u 1 * a = x - u 1 * (x - a) := by
        rw [show u 0 = 1 - u 1 by linarith]; ring
      linarith
  have hA := isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
    (regDirichletIntegral_analyticOn hK)
  have heq : rlIntegral g a x = fun ν => ((x : ℂ) - a) ^ ν * regDirichletIntegral (pair 1 ν) K := by
    funext ν
    rw [rlIntegral_eq_carlsonFractionalIntegral hax, carlsonFractionalIntegral]
    rfl
  rw [heq]
  intro ν hν
  have hxa : (x : ℂ) - a ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hax.ne'
  have hmem : pair 1 ν ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · simp [pair]
    · simpa [pair] using hν
  have hpair : DifferentiableAt ℂ (fun ν : ℂ => (pair 1 ν : Fin 2 → ℂ)) ν := by
    refine differentiableAt_pi.mpr fun i => ?_
    fin_cases i
    · exact differentiableAt_const _
    · exact differentiableAt_id
  exact ((hasStrictDerivAt_const_cpow (y := ν) (Or.inl hxa)).hasDerivAt.differentiableAt.mul
    ((hA _ hmem).differentiableAt.comp ν hpair)).differentiableWithinAt

/-- **Riesz's continuation of the fractional integral** to `re ν > -n`, for `g ∈ Cⁿ`:
`∑_{j<n} g⁽ʲ⁾(a) (x - a)^(ν+j)/Γ(ν + j + 1) + I^(ν+n) g⁽ⁿ⁾(x)`. -/
def rieszIntegral (n : ℕ) (g : ℝ → ℂ) (a x : ℝ) (ν : ℂ) : ℂ :=
  ∑ j ∈ range n, iteratedDeriv j g a * ((x - a : ℝ) : ℂ) ^ (ν + j) * (Gamma (ν + j + 1))⁻¹ +
    rlIntegral (iteratedDeriv n g) a x (ν + n)

/-- The interval `[a, x]` lies in a convex set containing its endpoints. -/
theorem Icc_subset_of_convex {Ω : Set ℝ} (hΩc : Convex ℝ Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    Set.Icc a x ⊆ Ω :=
  hΩc.ordConnected.out ha hx

/-- Raising the order of Riesz's construction does not change it where both are defined. -/
theorem rieszIntegral_succ {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {n : ℕ} {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ (n + 1 : ℕ) g Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω) (hax : a ≤ x)
    {ν : ℂ} (hν : -(n : ℝ) < ν.re) :
    rieszIntegral (n + 1) g a x ν = rieszIntegral n g a x ν := by
  have hI := Icc_subset_of_convex hΩc ha hx
  have hstep := rlIntegral_eq_add (g := iteratedDeriv n g) (g' := iteratedDeriv (n + 1) g) hax
    (fun t ht => hg.hasDerivAt_iteratedDeriv_of_isOpen hΩo (k := n) (by norm_cast; omega) (hI ht))
    ((hg.continuousOn_iteratedDeriv_of_isOpen hΩo le_rfl).mono hI)
    (ν := ν + n) (by simp; linarith)
  rw [rieszIntegral, rieszIntegral, sum_range_succ, hstep]
  push_cast
  ring_nf

/-- On `re ν > 0` Riesz's construction is the Riemann–Liouville integral. -/
theorem rieszIntegral_eq_rlIntegral {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {n : ℕ}
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω) (hax : a ≤ x)
    {ν : ℂ} (hν : 0 < ν.re) : rieszIntegral n g a x ν = rlIntegral g a x ν := by
  induction n with
  | zero => simp [rieszIntegral]
  | succ n ih =>
    rw [rieszIntegral_succ hΩo hΩc hg ha hx hax (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
      ih (hg.of_le (by norm_cast; omega))]

/-- Riesz's constructions of different orders agree on their common half-plane. -/
theorem rieszIntegral_eq_of_le {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {n : ℕ}
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω) (hax : a ≤ x)
    {m : ℕ} (hmn : m ≤ n) {ν : ℂ} (hν : -(m : ℝ) < ν.re) :
    rieszIntegral n g a x ν = rieszIntegral m g a x ν := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [rieszIntegral_succ hΩo hΩc hg ha hx hax (by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith), ih (hg.of_le (by norm_cast; omega))]

/-- Riesz's construction is holomorphic on `re ν > -n`. -/
theorem differentiableOn_rieszIntegral {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {n : ℕ}
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω) (hax : a < x) :
    DifferentiableOn ℂ (rieszIntegral n g a x) {ν | -(n : ℝ) < ν.re} := by
  have hxa : ((x - a : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero, sub_ne_zero]; exact hax.ne'
  have hsum : Differentiable ℂ fun ν : ℂ => ∑ j ∈ range n,
      iteratedDeriv j g a * ((x - a : ℝ) : ℂ) ^ (ν + j) * (Gamma (ν + j + 1))⁻¹ := by
    intro ν
    refine DifferentiableAt.fun_sum fun j _ => ?_
    have hp : DifferentiableAt ℂ (fun ν : ℂ => ((x - a : ℝ) : ℂ) ^ (ν + j)) ν :=
      ((hasStrictDerivAt_const_cpow (y := ν + j) (Or.inl hxa)).hasDerivAt.differentiableAt).comp
        ν (differentiableAt_id.add_const _)
    exact (differentiableAt_const _).mul hp |>.mul
      ((differentiable_one_div_Gamma _).comp ν ((differentiableAt_id.add_const _).add_const _))
  have hrl : DifferentiableOn ℂ (fun ν : ℂ => rlIntegral (iteratedDeriv n g) a x (ν + n))
      {ν | -(n : ℝ) < ν.re} := by
    refine (differentiableOn_rlIntegral hax ((hg.continuousOn_iteratedDeriv_of_isOpen hΩo
      le_rfl).mono (Icc_subset_of_convex hΩc ha hx))).comp
      (differentiableOn_id.add_const _) fun ν hν => ?_
    simp only [Set.mem_ofPred_eq, add_re, natCast_re] at hν ⊢
    linarith
  exact hsum.differentiableOn.add hrl

/-- **(5.5-16), case (i)**: Riesz's continuation of order `m + 1` takes the value `g⁽ᵐ⁾(x)` at
`ν = -m`. -/
theorem rieszIntegral_neg_nat {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {m : ℕ}
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ (m + 1 : ℕ) g Ω) {a x : ℝ} (ha : a ∈ Ω) (hx : x ∈ Ω)
    (hax : a ≤ x) : rieszIntegral (m + 1) g a x (-(m : ℂ)) = iteratedDeriv m g x := by
  have hI := Icc_subset_of_convex hΩc ha hx
  have hzero : ∀ j ∈ range m, iteratedDeriv j g a * ((x - a : ℝ) : ℂ) ^ (-(m : ℂ) + j) *
      (Gamma (-(m : ℂ) + j + 1))⁻¹ = 0 := by
    intro j hj
    have hjm : j < m := mem_range.mp hj
    rw [show -(m : ℂ) + j + 1 = -((m - j - 1 : ℕ) : ℂ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring,
      Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  have hftc : ∫ t in a..x, iteratedDeriv (m + 1) g t =
      iteratedDeriv m g x - iteratedDeriv m g a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
    · rw [Set.uIcc_of_le hax] at ht
      exact hg.hasDerivAt_iteratedDeriv_of_isOpen hΩo (k := m) (by norm_cast; omega) (hI ht)
    · exact ((hg.continuousOn_iteratedDeriv_of_isOpen hΩo le_rfl).mono
        (by rw [Set.uIcc_of_le hax]; exact hI)).intervalIntegrable
  rw [rieszIntegral, sum_range_succ, sum_eq_zero hzero, rlIntegral]
  simp only [neg_add_cancel, cpow_zero, zero_add, Gamma_one, inv_one, mul_one]
  rw [show -(m : ℂ) + ((m + 1 : ℕ) : ℂ) = 1 by push_cast; ring, Gamma_one, inv_one, one_mul,
    sub_self]
  simp only [cpow_zero, mul_one]
  rw [hftc]
  ring

/-- **Carlson's fractional integral continued in its order, case (i)** (Section 5.5, after
M. Riesz): for `g` that is `n` times continuously differentiable on an open interval containing
`a < x`, there is a function holomorphic on `re ν > -n` that equals the Riemann–Liouville
integral `I^ν g(x)` (5.5-15) for `re ν > 0` and equals `g⁽ᵐ⁾(x)` at `ν = -m` for `m < n` (5.5-16).
It is unique by the identity theorem. -/
theorem exists_real_fractionalIntegral_continuation {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {n : ℕ} {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g Ω) {a x : ℝ} (ha : a ∈ Ω)
    (hx : x ∈ Ω) (hax : a < x) :
    ∃ J : ℂ → ℂ, DifferentiableOn ℂ J {ν | -(n : ℝ) < ν.re} ∧
      (∀ ν : ℂ, 0 < ν.re → J ν = rlIntegral g a x ν) ∧
      ∀ m : ℕ, m < n → J (-(m : ℂ)) = iteratedDeriv m g x := by
  refine ⟨rieszIntegral n g a x, differentiableOn_rieszIntegral hΩo hΩc hg ha hx hax,
    fun ν hν => rieszIntegral_eq_rlIntegral hΩo hΩc hg ha hx hax.le hν, fun m hm => ?_⟩
  rw [rieszIntegral_eq_of_le hΩo hΩc hg ha hx hax.le (m := m + 1) hm (by simp),
    rieszIntegral_neg_nat hΩo hΩc (hg.of_le (by norm_cast)) ha hx hax.le]

end Carlson.TwoVariable
